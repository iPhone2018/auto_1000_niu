import json
import os
import socket
import subprocess
import sys
import time
import hashlib
import urllib.parse
import re
import requests
import threading
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
from datetime import datetime, timedelta
from queue import Queue, Empty

from playwright.sync_api import sync_playwright
from requests.cookies import RequestsCookieJar

# ==================== 配置区域 ====================

TARGET_URL = (
    "https://myseller.taobao.com/home.htm/QnworkbenchHome/"
    "?spm=a21bo.jianhua/a.1997525073.1.5af92a892zcUYK"
)

COOKIE_FILE = "taobao_cookies.json"
DEBUG_PORT = 9222
MAX_WAIT = 300
RUN_MODE = 0

APP_KEY = "12574478"
COMMON_PARAMS = {
    "jsv": "2.6.1",
    "appKey": APP_KEY,
    "api": "mtop.com.taobao.order.sold.returnaddress",
    "v": "1.0",
    "ttid": "11320@taobao_WEB_9.9.99",
    "type": "originaljson",
    "dataType": "json",
}

QZ_HOST = "vip.quezhongzhuan.com"

BASE_HEADERS = {
    "Accept": "*/*",
    "Accept-Encoding": "gzip, deflate",
    "Accept-Language": "zh-CN,zh;q=0.9",
    "Cache-Control": "no-cache",
    "Connection": "keep-alive",
    "Host": QZ_HOST,
    "Pragma": "no-cache",
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/148.0.0 Safari/537.36"
    ),
}

QZ_JSON_HEADERS = {
    "Accept": "application/json, text/javascript, */*; q=0.01",
    "Accept-Encoding": "gzip, deflate",
    "Accept-Language": "zh-CN,zh;q=0.9",
    "Cache-Control": "no-cache",
    "Connection": "keep-alive",
    "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    "Host": QZ_HOST,
    "Origin": f"http://{QZ_HOST}",
    "Pragma": "no-cache",
    "User-Agent": BASE_HEADERS["User-Agent"],
    "X-Requested-With": "XMLHttpRequest",
}

TB_API_HEADERS = {
    "accept": "application/json, text/plain, */*",
    "accept-encoding": "gzip, deflate, br, zstd",
    "accept-language": "zh-CN,zh;q=0.9",
    "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
    "origin": "https://myseller.taobao.com",
    "referer": "https://myseller.taobao.com/home.htm/trade-platform/tp/sold",
    "sec-ch-ua": '"Not;A=Brand";v="8", "Chromium";v="150", "Google Chrome";v="150"',
    "sec-ch-ua-mobile": "?0",
    "sec-ch-ua-platform": '"macOS"',
    "sec-fetch-dest": "empty",
    "sec-fetch-mode": "cors",
    "sec-fetch-site": "same-site",
    "user-agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/150.0.0.0 Safari/537.36"
    ),
}

WL_HEADERS = {
    "accept": "application/json",
    "accept-language": "zh-CN,zh;q=0.9",
    "origin": "https://qn.taobao.com",
    "sec-ch-ua": '"Not;A=Brand";v="8", "Chromium";v="150", "Google Chrome";v="150"',
    "sec-ch-ua-mobile": "?0",
    "sec-ch-ua-platform": '"macOS"',
    "sec-fetch-dest": "empty",
    "sec-fetch-mode": "cors",
    "sec-fetch-site": "same-site",
    "user-agent": TB_API_HEADERS["user-agent"],
}

session = requests.Session()
USERNAME = ""
PASSWORD = ""

# ==================== 全局停止控制 ====================
_task_stop_event = threading.Event()


class TaskStoppedException(Exception):
    """用于快速跳出多层循环的任务停止异常"""
    pass


def check_stop():
    """检查是否已收到停止信号，是则抛出 TaskStoppedException 立即中断"""
    if _task_stop_event.is_set():
        raise TaskStoppedException()


def safe_sleep(seconds: float):
    """可被立即中断的 sleep；任务停止时抛出 TaskStoppedException"""
    if _task_stop_event.wait(timeout=seconds):
        raise TaskStoppedException()


# ==================== 【修复】线程安全日志队列 代替直接print操作控件 ====================
LOG_QUEUE = Queue(maxsize=2000)

def log_print(text):
    """线程安全打印，投递到队列，禁止直接print写入UI"""
    LOG_QUEUE.put(text)

# ==================== 执行记录文件管理 ====================
SUCCESS_FILE = "success.txt"
FAIL_FILE = "fail.txt"
CLEANUP_DAYS = 30


def read_order_records(filepath: str):
    records = {}
    if not os.path.exists(filepath):
        return records
    with open(filepath, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(",", 1)
            if len(parts) == 2:
                tid, ts = parts[0].strip(), parts[1].strip()
                records[tid] = ts
    return records


def cleanup_old_records(filepath: str):
    """清理超过30天的记录，保留30天内的"""
    if not os.path.exists(filepath):
        return
    records = read_order_records(filepath)
    cutoff = datetime.now() - timedelta(days=CLEANUP_DAYS)
    new_lines = []
    for tid, ts in records.items():
        try:
            dt = datetime.strptime(ts, "%Y-%m-%d %H:%M:%S")
            if dt >= cutoff:
                new_lines.append(f"{tid},{ts}\n")
        except Exception:
            # 时间格式异常则保留，避免误删
            new_lines.append(f"{tid},{ts}\n")
    with open(filepath, "w", encoding="utf-8") as f:
        f.writelines(new_lines)


def append_order_record(filepath: str, tid):
    """追加订单记录，时间精确到秒"""
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(filepath, "a", encoding="utf-8") as f:
        f.write(f"{tid},{ts}\n")


def get_filtered_tids() -> set:
    return set(read_order_records(SUCCESS_FILE).keys()) | set(read_order_records(FAIL_FILE).keys())


# ==================== 雀手平台接口 ====================

def login(username: str, password: str):
    login_page_url = (
        f"http://{QZ_HOST}/LoginUI/index"
        f"?redirectURL=%2FAutoOrder%2FAllTradeNew"
    )
    session.get(login_page_url, headers=BASE_HEADERS, timeout=15)
    safe_sleep(0.5)
    check_stop()

    login_url = f"http://{QZ_HOST}/LoginUI/doLogin"
    login_data = {
        "userName": username,
        "password": password,
        "remember": False,
    }

    resp = session.post(login_url, headers=BASE_HEADERS, data=login_data, timeout=15)
    login_result = resp.json()
    log_print("登录返回：" + str(login_result))
    safe_sleep(0.5)
    check_stop()

    log_print("\n==== 当前会话Cookie列表 ====")
    cookie_dict = session.cookies.get_dict()
    log_print(str(cookie_dict))

    if login_result.get("isOk") or login_result.get("ok"):
        log_print("✅ 登录成功")
        return True
    else:
        log_print("❌ 登录失败")
        return False


def get_shop_list():
    shop_url = f"http://{QZ_HOST}/AutoOrder/getRelationUser"
    headers = {**BASE_HEADERS, "X-Requested-With": "XMLHttpRequest"}
    resp = session.get(shop_url, headers=headers, timeout=15)
    res_json = resp.json()
    safe_sleep(0.5)
    check_stop()

    if not res_json.get("isOk"):
        log_print("❌ 获取店铺失败，登录会话失效！")
        return None

    shop_list = res_json.get("res", [])
    log_print(f"\n✅ 获取店铺总数：{len(shop_list)}")
    shop_ids = [str(item["shopId"]) for item in shop_list]
    log_print("所有shopId列表：" + str(shop_ids))
    return shop_ids


def get_trade_list(
        session: requests.Session,
        shop_ids: list,
        start_date: str,
        end_date: str,
        page_num: int = 1,
):
    url = f"http://{QZ_HOST}/AutoOrder/getTradeListForAutoOrder"

    form_data = []
    for sid in shop_ids:
        form_data.append(("relationShopIds[]", str(sid)))

    form_data.extend([
        ("timeType", "created"),
        ("start", start_date),
        ("end", end_date),
        ("tid", ""),
        ("orderId", ""),
        ("memoType", "seller"),
        ("buyerNick", ""),
        ("receiverMobile", ""),
        ("status", ""),
        ("targetOrderId", ""),
        ("waybillCode", ""),
        ("receiverInclude", "1"),
        ("receiverState", ""),
        ("receiverCity", ""),
        ("titleInclude", "true"),
        ("itemTitle", ""),
        ("numlidInclude", "false"),
        ("itemNumlid", ""),
        ("outerIdInclude", "true"),
        ("itemOuterId", ""),
        ("colorInclude", "true"),
        ("itemColor", ""),
        ("sellerMemo", ""),
        ("orderFlag", "0"),
        ("deliverFlag", "0"),
        ("orderBy", "0"),
        ("is_cloud_order", "0"),
        ("cloud_send", "0"),
        ("storeName", ""),
        ("tradeType", "-1"),
        ("cgFailType", ""),
        ("gtPaymentMin", ""),
        ("gtPaymentMax", ""),
        ("profitRateMin", ""),
        ("orderUser", ""),
        ("autoOrderTradeId", ""),
        ("isQianNiuFaHuo", "0"),
        ("pn", str(page_num)),
        ("sync", "true"),
    ])

    cookies_before = session.cookies.get_dict().copy()
    resp = session.post(url, headers=QZ_JSON_HEADERS, data=form_data, timeout=15)
    safe_sleep(0.5)
    check_stop()

    cookies_after = session.cookies.get_dict()
    if cookies_before != cookies_after:
        log_print("⚠️ 警告：get_trade_list 修改了Cookie！")
        log_print("  之前：" + str(cookies_before))
        log_print("  之后：" + str(cookies_after))
        for k, v in cookies_before.items():
            session.cookies.set(k, v)
        log_print("  已恢复原始Cookie")

    try:
        return resp.json()
    except Exception as e:
        log_print("JSON解析失败！" + str(e))
        log_print("原始响应：" + resp.text[:500])
        return None


def get_shop_addr(session: requests.Session, target_shop_list: list):
    url = f"http://{QZ_HOST}/AutoOrder/batchQueryTargetRefundAddr"
    headers = {
        **QZ_JSON_HEADERS,
        "Referer": f"http://{QZ_HOST}/AutoOrder/AllTradeNew",
    }

    clean_list = []
    for item in target_shop_list:
        try:
            clean_list.append({
                "targetShopId": int(item["targetShopId"]),
                "plat": int(item.get("plat", 4)),
            })
        except (ValueError, TypeError):
            continue

    form_data = {"data": json.dumps(clean_list, separators=(",", ":"))}

    log_print("==== 调用地址接口前 Cookie ====")
    log_print(str(session.cookies.get_dict()))
    log_print("==== 发送的Payload ====")
    log_print(form_data["data"])

    resp = session.post(url, headers=headers, data=form_data, timeout=12)
    safe_sleep(0.5)
    check_stop()
    log_print("查询供应商退货地址返回：" + resp.text[:500])

    try:
        res_json = resp.json()
        if res_json.get("isOk"):
            return res_json.get("res", {})
        else:
            log_print("❌ 查询地址失败" + str(res_json))
            return {}
    except Exception as e:
        log_print("❌ 地址接口解析异常" + str(e) + resp.text[:500])
        return {}


# ==================== 浏览器与登录辅助 ====================

def is_port_open(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(1)
        return s.connect_ex(("127.0.0.1", port)) == 0


def find_chrome_executable():
    if sys.platform == "darwin":
        candidates = [
            "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
            "/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary",
        ]
    elif sys.platform == "win32":
        candidates = [
            r"C:\Program Files\Google\Chrome\Application\chrome.exe",
            r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
        ]
    else:
        candidates = [
            "/usr/bin/google-chrome",
            "/usr/bin/chromium-browser",
            "/usr/bin/chromium",
        ]
    for path in candidates:
        if os.path.exists(path):
            return path
    return None


def ensure_chrome_debugging() -> bool:
    if is_port_open(DEBUG_PORT):
        log_print(f"[*] 检测到 Chrome 调试端口 {DEBUG_PORT} 已开启")
        return True

    chrome_path = find_chrome_executable()
    if not chrome_path:
        log_print("[!] 未找到 Chrome，请手动启动：")
        if sys.platform == "darwin":
            log_print(r'    /Applications/Google\ Chrome.app/Contents/MacOS/Google\ Chrome --remote-debugging-port=9222')
        elif sys.platform == "win32":
            log_print(r'    "C:\Program Files\Google\Chrome\Application\chrome.exe" --remote-debugging-port=9222')
        return False

    log_print(f"[*] 尝试启动 Chrome（调试端口 {DEBUG_PORT}）...")
    user_data_dir = os.path.expanduser("~/playwright_chrome_profile")
    os.makedirs(user_data_dir, exist_ok=True)

    cmd = [
        chrome_path,
        f"--remote-debugging-port={DEBUG_PORT}",
        f"--user-data-dir={user_data_dir}",
        "--no-first-run",
        "--no-default-browser-check",
    ]
    subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    for i in range(10):
        safe_sleep(1)
        if is_port_open(DEBUG_PORT):
            log_print("[+] Chrome 启动成功")
            return True
        log_print(f"    等待 Chrome 就绪... ({i + 1}/10)")

    log_print("[!] Chrome 启动后端口未就绪")
    return False


def find_login_frame(page):
    try:
        if page.locator("#fm-login-id").count() > 0:
            return page, "当前页面"
    except Exception:
        pass

    for frame in page.frames:
        url = frame.url or ""
        if "login" in url or "passport" in url or "havanalogin" in url:
            try:
                if frame.locator("#fm-login-id").count() > 0:
                    return frame, f"iframe({url[:60]}...)"
            except Exception:
                pass
    return None, ""


def is_still_on_login_page(page) -> bool:
    frame, _ = find_login_frame(page)
    return frame is not None


def is_logged_in(page) -> tuple[bool, str]:
    if is_still_on_login_page(page):
        return False, "仍存在登录框"

    try:
        title = page.title()
        if "工作台" in title or "千牛" in title or "卖家中心" in title:
            return True, f"登录框消失且标题为: {title}"
    except Exception:
        pass

    try:
        selectors = [
            ".workbench-container",
            ".seller-nav",
            ".qn-workbench",
            "[data-spm*='workbench']",
        ]
        for sel in selectors:
            if page.locator(sel).count() > 0:
                return True, f"登录框消失且出现工作台元素: {sel}"
    except Exception:
        pass

    return True, "登录框已消失（可能已登录，正在加载）"


def get_unique_cookies(cookies: list) -> list:
    seen = {}
    for c in cookies:
        key = (c["name"], c.get("domain", ""), c.get("path", "/"))
        seen[key] = c
    return list(seen.values())


# ==================== Cookie 与地址工具 ====================

def load_cookies(filepath: str) -> RequestsCookieJar:
    with open(filepath, "r", encoding="utf-8") as f:
        raw_cookies = json.load(f)

    jar = RequestsCookieJar()
    for c in raw_cookies:
        jar.set(
            name=c["name"],
            value=c["value"],
            domain=c.get("domain", ""),
            path=c.get("path", "/"),
        )
    return jar


def parse_refund_address(addr_str: str, session: requests.Session) -> dict:
    url = "https://wuliu2.taobao.com/user/structAddress"
    headers = {
        **WL_HEADERS,
        "referer": (
            "https://qn.taobao.com/home.htm/"
            "addressstore-optimize2/edit"
        ),
    }

    try:
        full_url = f"{url}?fullAddress={urllib.parse.quote(addr_str)}"
        resp = session.get(full_url, headers=headers, timeout=15)
        resp_data = resp.json().get("data", "")
        safe_sleep(0.5)
        check_stop()
    except Exception as e:
        log_print(f"        ⚠️ 结构化地址接口调用失败: {e}")
        return {}

    return {
        "contactName": resp_data.get("name", ""),
        "mobilePhone": resp_data.get("mobilePhone", ""),
        "adr": resp_data.get("detailAddress", ""),
        "provinceName": resp_data.get("province", ""),
        "cityName": resp_data.get("city", ""),
        "districtName": resp_data.get("county", ""),
        "townName": resp_data.get("town", ""),
        "divisionId": resp_data.get("divisionId", ""),
    }


# ==================== 淘宝订单与地址接口 ====================

def query_order_by_tid(session: requests.Session, tid: int):
    url = "https://trade.taobao.com/trade/itemlist/asyncSold.htm"
    params = {"event_submit_do_query": "1", "_input_charset": "utf8"}

    data = {
        "isQnNew": "true",
        "isHideNick": "true",
        "prePageNo": "1",
        "sifg": "0",
        "action": "itemlist/SoldQueryAction",
        "close": "0",
        "pageNum": "1",
        "tabCode": "haveSendGoods",
        "useCheckcode": "false",
        "errorCheckcode": "false",
        "payDateBegin": "0",
        "rateStatus": "ALL",
        "unionSearch": str(tid),
        "buyerNick": "",
        "orderStatus": "SEND",
        "pageSize": "15",
        "dateEnd": "0",
        "endTimeBegin": "0",
        "endTimeEnd": "0",
        "rxOldFlag": "0",
        "rxSendFlag": "0",
        "dateBegin": "0",
        "tradeTag": "0",
        "rxHasSendFlag": "0",
        "auctionType": "0",
        "sellerNick": "",
        "notifySendGoodsType": "ALL",
        "sellerMemoFlag": "0",
        "useOrderInfo": "false",
        "logisticsService": "ALL",
        "o2oDeliveryType": "ALL",
        "rxAuditFlag": "0",
        "auctionId": "",
        "queryOrder": "desc",
        "holdStatus": "0",
        "rxElectronicAuditFlag": "0",
        "bizOrderId": "",
        "queryMore": "false",
        "payDateEnd": "0",
        "rxWaitSendflag": "0",
        "sellerMemo": "0",
        "queryBizType": "ALL",
        "rxElectronicAllFlag": "0",
        "rxSuccessflag": "0",
        "unionSearchTotalNum": "0",
        "yushouStatus": "ALL",
        "deliveryTimeType": "ALL",
        "payMethodType": "ALL",
        "orderType": "ALL",
        "appName": "ALL",
        "isRiskOrder": "0",
    }

    try:
        resp = session.post(
            url,
            params=params,
            data=urllib.parse.urlencode(data),
            headers=TB_API_HEADERS,
            timeout=30,
        )
        safe_sleep(0.5)
        check_stop()
    except Exception as e:
        log_print(f"    [!] 请求订单接口异常: {e}")
        return None

    if resp.status_code != 200:
        log_print(f"    [!] 订单接口状态码异常: {resp.status_code}")
        return None

    try:
        result = resp.json()
    except Exception as e:
        log_print(f"    [!] 订单接口 JSON 解析失败: {e}")
        return None

    orders = result.get("mainOrders", [])
    if not orders:
        return None
    return orders[0]


def get_address_list(session: requests.Session) -> list:
    url = "https://wuliu2.taobao.com/user/querySellerContact.do"
    headers = {
        **WL_HEADERS,
        "referer": "https://qn.taobao.com/home.htm/addressstore-optimize2",
    }

    try:
        resp = session.get(url, headers=headers, timeout=30)
        safe_sleep(0.5)
        check_stop()
    except Exception as e:
        log_print(f"    [!] 请求地址列表异常: {e}")
        return []

    if resp.status_code != 200:
        log_print(f"    [!] 地址列表接口状态码异常: {resp.status_code}")
        return []

    try:
        data = resp.json()
        return data.get("data", [])
    except Exception as e:
        log_print(f"    [!] 地址列表 JSON 解析失败: {e}")
        return []


def get_csrf_token(session: requests.Session):
    for cookie in session.cookies:
        if cookie.name == "XSRF-TOKEN" and "wuliu2.taobao.com" in cookie.domain:
            return cookie.value
    for cookie in session.cookies:
        if cookie.name == "XSRF-TOKEN" and "qn.taobao.com" in cookie.domain:
            return cookie.value
    return None


def update_address(
        session: requests.Session,
        original: dict,
        new_info: dict,
        csrf: str,
) -> bool:
    url = "https://wuliu2.taobao.com/user/saveSellerContact.do"

    contact_name = new_info.get("contactName") or original.get("contactName", "")
    mobile = new_info.get("mobilePhone") or original.get("mobilePhone", "")
    adr = new_info.get("adr") or original.get("adr", "")

    provinceName = new_info.get("provinceName") or original.get("provinceName", "")
    cityName = new_info.get("cityName") or original.get("cityName", "")
    districtName = new_info.get("districtName") or original.get("districtName", "")
    townName = new_info.get("townName", "")
    divisionId = new_info.get("divisionId") or original.get("divisionId", "")
    countryName = new_info.get("countryName", "中国")

    data = {
        "_csrf": csrf,
        "adr": adr,
        "areaId": original.get("areaId", ""),
        "branch": original.get("branch", ""),
        "cityName": cityName,
        "contactId": original.get("contactId", ""),
        "contactName": contact_name,
        "countryName": countryName,
        "ddd": original.get("ddd", ""),
        "defFetcher": str(original.get("defFetcher", False)).lower(),
        "defRefunder": str(original.get("defRefunder", False)).lower(),
        "defaultFetcher": "false",
        "defaultRefunder": "false",
        "districtName": districtName,
        "divisionId": divisionId,
        "divisionId1": divisionId,
        "ignoreCheck": "false",
        "mobilePhone": mobile,
        "phone": original.get("phone", ""),
        "phones[0].type": "mobile",
        "phones[0].value": mobile,
        "provinceName": provinceName,
        "telephone": original.get("telephone", ""),
        "townName": townName,
        "userDefinitions": original.get("userDefinitions", ""),
    }

    headers = {
        **WL_HEADERS,
        "content-type": "application/x-www-form-urlencoded;charset=UTF-8",
        "referer": (
            "https://qn.taobao.com/home.htm/addressstore-optimize2/edit"
            f"?contactId={original.get('contactId', '')}"
        ),
        "X-XSRF-TOKEN": csrf,
    }

    log_print(f"    [*] 正在更新已有地址...")
    log_print(f"        contactId : {original.get('contactId')}")
    log_print(f"        新姓名    : {contact_name}")
    log_print(f"        新电话    : {mobile}")
    log_print(f"        省市区    : {provinceName} {cityName} {districtName} {townName}")
    log_print(f"        divisionId: {divisionId}")
    log_print(f"        新地址    : {adr[:60]}{'...' if len(adr) > 60 else ''}")

    try:
        resp = session.post(url, data=data, headers=headers, timeout=30)
        safe_sleep(0.5)
        check_stop()
    except Exception as e:
        log_print(f"    [!] 更新地址请求异常: {e}")
        return False

    log_print(f"    [*] saveSellerContact 状态码: {resp.status_code}")

    try:
        result = resp.json()
        log_print(f"    [*] 响应: {json.dumps(result, ensure_ascii=False)}")
        return result.get("success", False) is True
    except Exception as e:
        log_print(f"    [!] 解析响应失败: {e}")
        log_print(f"        响应文本: {resp.text[:500]}")
        return False


def update_order_address(session, cookie_jar, data_content):
    token = extract_m_h5_tk_token(cookie_jar)
    t_ms = str(int(time.time() * 1000))
    sign = calc_mtop_sign(token, t_ms, APP_KEY, data_content)

    query_params = {**COMMON_PARAMS, "t": t_ms, "sign": sign}
    post_data = {"data": data_content}

    headers = {
        "User-Agent": TB_API_HEADERS["user-agent"],
        "Accept": "application/json",
        "Content-Type": "application/x-www-form-urlencoded",
        "Origin": "https://myseller.taobao.com",
        "Referer": "https://myseller.taobao.com/home.htm/trade-platform/tp/sold",
        "Sec-Fetch-Site": "same-site",
        "Sec-Fetch-Mode": "cors",
        "Sec-Fetch-Dest": "empty",
        "Accept-Language": "zh-CN,zh;q=0.9",
    }

    API_URL = (
        "https://h5api.m.taobao.com/h5/"
        "mtop.com.taobao.order.sold.returnaddress/1.0/"
    )
    resp = session.post(
        url=API_URL,
        params=query_params,
        data=post_data,
        cookies=cookie_jar,
        headers=headers,
        timeout=15,
    )
    safe_sleep(0.5)
    check_stop()
    log_print(f"状态码: {resp.status_code}")
    log_print("响应内容：")
    log_print(resp.text)

    try:
        result = resp.json()
        if result.get("success") is True or result.get("isOk") is True:
            return True
        return False
    except Exception:
        return resp.status_code == 200


def extract_m_h5_tk_token(cookie_jar: requests.cookies.RequestsCookieJar):
    raw_val = cookie_jar.get("_m_h5_tk")
    if not raw_val:
        raise Exception("Cookie缺失 _m_h5_tk，登录失效！")
    return raw_val.split("_")[0]


def calc_mtop_sign(token: str, t_ms: str, appkey: str, data_raw: str) -> str:
    sign_str = f"{token}&{t_ms}&{appkey}&{data_raw}"
    return hashlib.md5(sign_str.encode("utf-8")).hexdigest()


# ==================== 核心流程 ====================

def run_main_process(qz_username: str, qz_password: str, qn_username: str, qn_password: str,
                     filtered_tids: set, start_date: str, end_date: str):
    global session, USERNAME, PASSWORD
    USERNAME = qn_username
    PASSWORD = qn_password

    # ---- 雀手：登录并获取订单 ----
    login_success = login(qz_username, qz_password)
    if not login_success:
        log_print("雀手登录失败！")
        return

    shops = get_shop_list()
    if not shops:
        log_print("没有店铺！")
        return

    GROUP_MAX = 30
    all_orders = []
    for group_idx in range(0, len(shops), GROUP_MAX):
        check_stop()
        shop_group = shops[group_idx: group_idx + GROUP_MAX]
        log_print(f"\n>>>>>>>>>> 当前分组：{group_idx + 1} ~ {group_idx + len(shop_group)} 号店铺，数量：{len(shop_group)}")

        page = 1
        while True:
            check_stop()
            res = get_trade_list(
                session, shop_group,
                start_date, end_date,
                page_num=page,
            )
            if not res:
                log_print(f"分组页面{page} 返回异常，跳出分页")
                break

            count = res.get("count", "无count字段")
            page_data = res.get("res", [])
            log_print(
                f"【分组{group_idx // GROUP_MAX + 1} 第{page}页】"
                f"接口count={count}，本页条数：{len(page_data)}"
            )

            if not page_data:
                log_print(f"分组 {shop_group} 第{page}页无数据，结束本组分页")
                break

            all_orders.extend(page_data)
            log_print(f"累计抓取全部订单：{len(all_orders)}")
            page += 1
            safe_sleep(0.3)

    log_print("\n==================== 全部抓取完成 ====================")
    log_print("全部订单总数：" + str(len(all_orders)))
    if not all_orders:
        log_print("没有订单！")
        return

    # ---- 提取需要查询地址的订单 ----
    new_orders = []
    targetShopIdList = []
    seen_shop_id = set()

    for row in all_orders:
        check_stop()
        tid = row.get("tid")
        printOrder = row.get("printOrder", [])
        for p_order in printOrder:
            check_stop()
            cgDanhao = p_order.get("cgDanhao")
            if not cgDanhao:
                continue
            targetShopId = p_order.get("targetShopId")
            if not targetShopId:
                continue
            try:
                targetShopId = int(targetShopId)
            except (ValueError, TypeError):
                continue

            new_orders.append({
                "tid": tid,
                "cgDanhao": cgDanhao,
                "targetShopId": targetShopId,
            })
            if targetShopId not in seen_shop_id:
                seen_shop_id.add(targetShopId)
                targetShopIdList.append({
                    "targetShopId": targetShopId,
                    "plat": 4,
                })

    if not targetShopIdList:
        log_print("没有需要查询地址的供应商！")
        return

    # ---- 批量查询供应商地址 ----
    BATCH_MAX = 20
    shop_address_map = {}
    for batch_start in range(0, len(targetShopIdList), BATCH_MAX):
        check_stop()
        batch_list = targetShopIdList[batch_start: batch_start + BATCH_MAX]
        log_print(
            f"\n👉 地址查询批次：{batch_start + 1} ~ "
            f"{batch_start + len(batch_list)}，数量 {len(batch_list)}"
        )
        batch_addr = get_shop_addr(session=session, target_shop_list=batch_list)
        shop_address_map.update(batch_addr)
        safe_sleep(0.2)

    log_print("\n==== 获取到供应商地址 ====")

    final_result = []
    for item in new_orders:
        check_stop()
        sid = str(item["targetShopId"])
        addr = shop_address_map.get(sid, "暂无退货地址")
        item["refund_address"] = addr
        final_result.append(item)

    # ---- 千牛：浏览器登录并获取 Cookie ----
    if not ensure_chrome_debugging():
        return

    with sync_playwright() as p:
        log_print("[*] 正在通过 CDP 连接到 Chrome...")
        browser = p.chromium.connect_over_cdp(f"http://127.0.0.1:{DEBUG_PORT}")

        if len(browser.contexts) == 0:
            log_print("[!] 未找到浏览器上下文")
            return

        context = browser.contexts[0]
        log_print(f"[*] 已连接，当前有 {len(context.pages)} 个标签页")

        page = context.new_page()
        log_print(f"[*] 访问: {TARGET_URL}")
        page.goto(TARGET_URL, wait_until="domcontentloaded", timeout=60000)
        safe_sleep(3)
        check_stop()

        log_print(f"[*] 当前 URL: {page.url}")
        log_print(f"[*] 当前标题: {page.title()}")

        logged, reason = is_logged_in(page)
        if logged:
            log_print(f"[+] 检测到已是登录状态！({reason})")
        else:
            log_print(f"[*] 未登录，开始自动填充... ({reason})")

            login_frame, source = find_login_frame(page)
            if not login_frame:
                log_print("[!] 未找到登录框")
                return

            log_print(f"[+] 找到登录框: {source}")

            try:
                tab = login_frame.locator(".password-login-tab-item")
                if tab.count() > 0 and tab.is_visible():
                    tab.click()
                    safe_sleep(1)
                    log_print("[+] 已切换到密码登录")
            except Exception:
                pass

            log_print("[*] 输入账号...")
            login_frame.fill("#fm-login-id", USERNAME)
            safe_sleep(1.5)
            check_stop()

            log_print("[*] 输入密码...")
            login_frame.fill("#fm-login-password", PASSWORD)
            safe_sleep(1)
            check_stop()

            log_print("[*] 点击登录...")
            login_frame.click(".fm-submit.password-login")
            safe_sleep(3)
            check_stop()

            log_print("\n" + "=" * 55)
            log_print("  请在浏览器窗口中完成验证码")
            log_print(f"  脚本将自动检测登录状态，最长等待 {MAX_WAIT} 秒")
            log_print("=" * 55 + "\n")

            logged_in = False
            start = time.time()
            last_reason = ""
            while time.time() - start < MAX_WAIT:
                check_stop()
                is_ok, reason = is_logged_in(page)
                if is_ok:
                    log_print(f"[+] 登录成功！({reason})")
                    logged_in = True
                    break
                if reason != last_reason:
                    log_print(f"    [检测中] {reason}")
                    last_reason = reason
                safe_sleep(2)
                elapsed = int(time.time() - start)
                if elapsed % 10 == 0:
                    log_print(f"    已等待 {elapsed} 秒...")

            if not logged_in:
                log_print("[!] 等待超时")
                log_print(f"[*] 当前 URL: {page.url}")
                log_print(f"[*] 当前标题: {page.title()}")
                log_print(f"[*] 是否仍存在登录框: {is_still_on_login_page(page)}")

            safe_sleep(2)
            check_stop()

        cookies = context.cookies()
        unique_cookies = get_unique_cookies(cookies)
        log_print(f"\n[+] 原始 Cookie 数: {len(cookies)}, 去重后: {len(unique_cookies)}")

        with open(COOKIE_FILE, "w", encoding="utf-8") as f:
            json.dump(unique_cookies, f, ensure_ascii=False, indent=2)
        log_print(f"[+] 已保存: {COOKIE_FILE}")

    # ---- 加载 Cookie 并处理订单 ----
    try:
        cookie_jar = load_cookies(COOKIE_FILE)
    except FileNotFoundError:
        log_print(f"[!] 找不到 Cookie 文件: {COOKIE_FILE}")
        return
    except Exception as e:
        log_print(f"[!] 加载 Cookie 失败: {e}")
        return

    session = requests.Session()
    session.cookies.update(cookie_jar)
    log_print(f"[*] 已加载 Cookie，Session 中共有 {len(session.cookies)} 条")
    mode_text = "【覆盖第3条地址】" if RUN_MODE == 0 else "【每条订单新建独立地址】"
    log_print(f"[*] 当前运行模式: {mode_text}")

    ORDERS = final_result
    total = len(ORDERS)
    success_count = 0
    skip_count = 0
    fail_count = 0

    for idx, order in enumerate(ORDERS, 1):
        check_stop()
        tid = order["tid"]
        refund_address = order["refund_address"]

        if str(tid) in filtered_tids:
            log_print(f"\n{'=' * 70}")
            log_print(f"[{idx}/{total}] 订单 tid={tid} 已在历史记录中，跳过")
            skip_count += 1
            continue

        log_print(f"\n{'=' * 70}")
        log_print(f"[{idx}/{total}] 处理订单 tid={tid}")

        log_print("    [*] 正在查询订单...")
        order_info = query_order_by_tid(session, tid)
        if not order_info:
            log_print("    [!] 未查询到订单，跳过")
            skip_count += 1
            continue

        sub_orders = order_info.get("subOrders", [])
        for sub_order in sub_orders:
            check_stop()
            return_address_vo = sub_order.get("returnAddressVO", {})
            expect_state_text = return_address_vo.get("expectStateText", "unKnown")
            if expect_state_text == "请退款":
                log_print(f"    [*] 订单 {tid} 状态为 {expect_state_text}，跳过")
                continue

        new_info = parse_refund_address(refund_address, session)
        log_print("    [*] 解析 refund_address:")
        log_print(f"        姓名: {new_info['contactName']}")
        log_print(f"        手机: {new_info['mobilePhone']}")
        log_print(f"        省份: {new_info['provinceName']}")
        log_print(f"        城市: {new_info['cityName']}")
        log_print(f"        区县: {new_info['districtName']}")
        log_print(f"        乡镇: {new_info['townName']}")
        log_print(f"        divisionId: {new_info['divisionId']}")
        log_print(f"        地址: {new_info['adr'][:60]}{'...' if len(new_info['adr']) > 60 else ''}")

        csrf = get_csrf_token(session)
        if not csrf:
            log_print("    [!] 无法从 Cookie 获取 XSRF-TOKEN，请重新抓取Cookie！")
            fail_count += 1
            append_order_record(FAIL_FILE, tid)
            continue

        safe_sleep(0.5)
        check_stop()

        log_print("    [*] 获取地址列表...")
        addresses = get_address_list(session)
        if not addresses:
            log_print("    [!] 获取地址列表失败，跳过")
            fail_count += 1
            append_order_record(FAIL_FILE, tid)
            continue
        if len(addresses) < 3:
            log_print("    [!] 地址总数不足3条，无法修改第3个地址，跳过")
            fail_count += 1
            append_order_record(FAIL_FILE, tid)
            continue

        target_addr = addresses[2]
        run_ok = update_address(session, target_addr, new_info, csrf)
        if not run_ok:
            log_print(f"    [!] ❌ 订单 {tid} 地址更新失败")
            fail_count += 1
            append_order_record(FAIL_FILE, tid)
            continue

        new_address_id = target_addr.get("contactId", "")
        for sub_order in sub_orders:
            check_stop()
            return_address_vo = sub_order.get("returnAddressVO", {})
            return_address_content_vo = return_address_vo.get("returnAddressContentVO", {})
            old_address_id = return_address_content_vo.get("addressId", "")

            data_content = {
                "orderId": tid,
                "operation": "update",
                "source": "qn",
                "params": json.dumps({
                    "orderId": tid,
                    "newAddressId": new_address_id,
                    "oldAddressId": old_address_id,
                }, ensure_ascii=False),
            }
            log_print(f"修改订单地址请求体：{data_content}")

            run_ok = update_order_address(
                session,
                cookie_jar,
                json.dumps(data_content, ensure_ascii=False),
            )
            if run_ok:
                log_print(f"    [+] ✅ 订单 {tid} 操作成功")
                success_count += 1
                append_order_record(SUCCESS_FILE, tid)
            else:
                log_print(f"    [!] ❌ 订单 {tid} 操作失败")
                fail_count += 1
                append_order_record(FAIL_FILE, tid)
            safe_sleep(0.8)

    log_print(f"\n{'=' * 70}")
    log_print(
        f"[✓] 处理完成: 总计 {total} | "
        f"成功 {success_count} | 跳过 {skip_count} | 失败 {fail_count}"
    )
    log_print(f"{'=' * 70}")


# ==================== GUI 界面 ====================
class App:
    def __init__(self, root):
        self.root = root
        self.root.title("订单地址自动修改工具")
        self.root.geometry("950x750")
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        input_frame = ttk.Frame(root, padding=10)
        input_frame.pack(fill=tk.X)

        ttk.Label(input_frame, text="雀手账号:").grid(row=0, column=0, sticky=tk.W, pady=3)
        self.qz_user = ttk.Entry(input_frame, width=30)
        self.qz_user.grid(row=0, column=1, padx=5)
        self.qz_user.insert(0, "17850939652")

        ttk.Label(input_frame, text="雀手密码:").grid(row=0, column=2, sticky=tk.W, pady=3)
        self.qz_pass = ttk.Entry(input_frame, width=30, show="*")
        self.qz_pass.grid(row=0, column=3, padx=5)
        self.qz_pass.insert(0, "qqq123123")

        ttk.Label(input_frame, text="千牛账号:").grid(row=1, column=0, sticky=tk.W, pady=3)
        self.qn_user = ttk.Entry(input_frame, width=30)
        self.qn_user.grid(row=1, column=1, padx=5)
        self.qn_user.insert(0, "smotouchmud旗舰店:测试")

        ttk.Label(input_frame, text="千牛密码:").grid(row=1, column=2, sticky=tk.W, pady=3)
        self.qn_pass = ttk.Entry(input_frame, width=30, show="*")
        self.qn_pass.grid(row=1, column=3, padx=5)
        self.qn_pass.insert(0, "qqq123123")

        ttk.Label(input_frame, text="执行间隔(分钟):").grid(row=2, column=0, sticky=tk.W, pady=3)
        self.interval = ttk.Entry(input_frame, width=10)
        self.interval.grid(row=2, column=1, sticky=tk.W, padx=5)
        self.interval.insert(0, "60")

        btn_frame = ttk.Frame(input_frame)
        btn_frame.grid(row=2, column=2, columnspan=2, pady=8)
        self.start_btn = ttk.Button(btn_frame, text="开始执行", command=self.start_task)
        self.start_btn.pack(side=tk.LEFT, padx=5)
        self.stop_btn = ttk.Button(btn_frame, text="停止执行", command=self.stop_task, state=tk.DISABLED)
        self.stop_btn.pack(side=tk.LEFT, padx=5)

        ttk.Label(root, text="运行日志:", font=("Arial", 10, "bold")).pack(anchor=tk.W, padx=10, pady=(10, 0))
        self.log_text = scrolledtext.ScrolledText(root, height=35, state=tk.NORMAL, wrap=tk.WORD)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.running = False
        self.timer = None
        self.worker_thread = None
        # 启动日志消费循环
        self.consume_log_queue()

    def consume_log_queue(self):
        """主线程定时读取日志队列，写入文本框【唯一线程安全方式】"""
        try:
            while True:
                msg = LOG_QUEUE.get_nowait()
                self.log_text.insert(tk.END, msg + "\n")
                self.log_text.see(tk.END)
        except Empty:
            pass
        # 每隔50ms再次执行
        self.root.after(50, self.consume_log_queue)

    def on_close(self):
        # 窗口关闭前停止任务
        self.stop_task()
        self.root.destroy()

    def start_task(self):
        if self.running:
            return
        self.running = True
        _task_stop_event.clear()
        self.start_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL)
        if self.timer:
            self.timer.cancel()
            self.timer = None

        cleanup_old_records(SUCCESS_FILE)
        cleanup_old_records(FAIL_FILE)

        self.worker_thread = threading.Thread(target=self.run_loop, daemon=True)
        self.worker_thread.start()

    def stop_task(self):
        self.running = False
        _task_stop_event.set()
        if self.timer:
            try:
                self.timer.cancel()
            except Exception:
                pass
            self.timer = None
        self.start_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        log_print("\n[!] 已发送停止信号，正在中断当前操作...\n")

    def run_loop(self):
        if _task_stop_event.is_set():
            log_print("[*] 检测到停止信号，本次 Timer 直接退出")
            return
        try:
            self.execute_once()
        except TaskStoppedException:
            log_print("\n[!] 任务已被用户中断\n")
        except Exception as e:
            log_print(f"[!] 执行异常: {e}")
            import traceback
            log_print(traceback.format_exc())

        if self.running and not _task_stop_event.is_set():
            try:
                mins = int(self.interval.get().strip())
                if mins <= 0:
                    mins = 60
            except Exception:
                mins = 60

            log_print(f"\n[*] 本次执行结束，下次将在 {mins} 分钟后执行...\n")
            self.timer = threading.Timer(mins * 60, self.run_loop)
            self.timer.start()
        else:
            self.running = False
            self.start_btn.config(state=tk.NORMAL)
            self.stop_btn.config(state=tk.DISABLED)
            log_print("\n[*] 定时任务已完全停止\n")

    def execute_once(self):
        if _task_stop_event.is_set():
            return
        qz_username = self.qz_user.get().strip()
        qz_password = self.qz_pass.get().strip()
        qn_username = self.qn_user.get().strip()
        qn_password = self.qn_pass.get().strip()

        if not all([qz_username, qz_password, qn_username, qn_password]):
            log_print("[!] 错误：请填写所有账号和密码")
            return

        filtered_tids = get_filtered_tids()
        log_print(f"\n[*] 当前已处理订单过滤数: {len(filtered_tids)}")

        now = datetime.now()
        end_date = now.strftime("%Y-%m-%d") + " 23:59"
        start_date = (now - timedelta(days=15)).strftime("%Y-%m-%d") + " 00:00"
        log_print(f"[*] 本次查询日期范围: {start_date} ~ {end_date}")

        run_main_process(qz_username, qz_password, qn_username, qn_password,
                         filtered_tids, start_date, end_date)

        cleanup_old_records(SUCCESS_FILE)
        cleanup_old_records(FAIL_FILE)
        log_print("\n[*] 本次执行完毕，已清理超30天的历史记录")


def main():
    root = tk.Tk()
    app = App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
