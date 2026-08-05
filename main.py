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
import shutil
import contextlib
from tkinter import ttk, scrolledtext, messagebox, filedialog
from datetime import datetime, timedelta
from queue import Queue, Empty

from playwright.sync_api import sync_playwright
from requests.cookies import RequestsCookieJar

# ==================== 配置区域 ====================

TARGET_URL = (
    "https://myseller.taobao.com/home.htm/QnworkbenchHome/"
    "?spm=a21bo.jianhua/a.1997525073.1.5af92a892zcUYK"
)

ACCOUNT_STORE_FILE = "account_store.json"
DEBUG_PORT_RANGE = (9222, 9322)
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
g_user_chrome_path = ""
INSTANCE_NAME = ""

# ==================== 全局停止控制 ====================
_task_stop_event = threading.Event()


class TaskStoppedException(Exception):
    pass


def check_stop():
    if _task_stop_event.is_set():
        raise TaskStoppedException()


def safe_sleep(seconds: float):
    if _task_stop_event.wait(timeout=seconds):
        raise TaskStoppedException()
    time.sleep(1)


# ==================== 线程安全日志队列 ====================
LOG_QUEUE = Queue(maxsize=2000)


def log_print(text):
    prefix = f"[{INSTANCE_NAME}] " if INSTANCE_NAME else ""
    LOG_QUEUE.put(prefix + text)


# ==================== 账号存储工具函数（新增并发保护）====================

try:
    from filelock import FileLock
    _ACCOUNT_LOCK = FileLock(ACCOUNT_STORE_FILE + ".lock", timeout=5)
except Exception:
    _ACCOUNT_LOCK = contextlib.nullcontext()


def load_account_store():
    with _ACCOUNT_LOCK:
        if not os.path.exists(ACCOUNT_STORE_FILE):
            return {"qz": {}, "qn": {}}
        try:
            with open(ACCOUNT_STORE_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {"qz": {}, "qn": {}}


def save_account_store(store_data):
    with _ACCOUNT_LOCK:
        tmp_file = ACCOUNT_STORE_FILE + ".tmp"
        with open(tmp_file, "w", encoding="utf-8") as f:
            json.dump(store_data, f, ensure_ascii=False, indent=2)
        if os.path.exists(ACCOUNT_STORE_FILE):
            os.replace(tmp_file, ACCOUNT_STORE_FILE)
        else:
            os.rename(tmp_file, ACCOUNT_STORE_FILE)


def save_one_account(acc_type: str, username: str, password: str):
    if not username.strip():
        return
    store = load_account_store()
    store[acc_type][username.strip()] = password
    save_account_store(store)


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
            parts = line.split(",")
            if len(parts) == 2:
                tid, ts = parts[0].strip(), parts[1].strip()
                records[tid] = (ts, '', '')
            elif len(parts) == 3:
                tid, ts, qn_username = parts[0].strip(), parts[1].strip(), parts[2].strip()
                records[tid] = (ts, qn_username, '')
            else:
                tid, ts, qn_username, reason = parts[0].strip(), parts[1].strip(), parts[2].strip(), parts[3].strip()
                records[tid] = (ts, '', reason)
    return records


def cleanup_old_records(filepath: str):
    if not os.path.exists(filepath):
        return
    records = read_order_records(filepath)
    cutoff = datetime.now() - timedelta(days=CLEANUP_DAYS)
    new_lines = []
    for tid, ts_all in records.items():
        ts, qn_username, reason = ts_all
        try:
            dt = datetime.strptime(ts, "%Y-%m-%d %H:%M:%S")
            if dt >= cutoff:
                new_lines.append(f"{tid},{ts},{qn_username},{reason}\n")
        except Exception:
            new_lines.append(f"{tid},{ts},{qn_username},{reason}\n")
    with open(filepath, "w", encoding="utf-8") as f:
        f.writelines(new_lines)


def append_order_record(filepath, tid, qn_username, reason=""):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    if reason:
        line = f"{tid},{ts},{qn_username},{reason}\n"
    else:
        line = f"{tid},{ts},{qn_username},\n"
    with open(filepath, "a", encoding="utf-8") as f:
        f.write(line)


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


def find_free_port(start_port: int = 9222, end_port: int = 9322) -> int:
    for port in range(start_port, end_port + 1):
        if not is_port_open(port):
            log_print(f"[*] 分配调试端口: {port}")
            return port
    raise RuntimeError(f"在 {start_port}-{end_port} 范围内未找到可用端口")


def _kill_chrome_by_port(port: int):
    """通过端口查找并强制结束对应的 Chrome 进程"""
    if not is_port_open(port):
        return
    try:
        if sys.platform == "win32":
            result = subprocess.run(
                f'netstat -ano | findstr :{port}',
                shell=True, capture_output=True, text=True
            )
            for line in result.stdout.splitlines():
                if f"127.0.0.1:{port}" in line or f"0.0.0.0:{port}" in line:
                    parts = line.strip().split()
                    if len(parts) >= 5:
                        pid = parts[-1]
                        subprocess.run(
                            f'taskkill /F /PID {pid}',
                            shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                        )
                        log_print(f"[*] 已强制结束 Chrome 进程 PID:{pid} (端口 {port})")
                        break
        else:
            result = subprocess.run(
                f"lsof -ti tcp:{port}",
                shell=True, capture_output=True, text=True
            )
            pid = result.stdout.strip()
            if pid:
                subprocess.run(
                    f"kill -9 {pid}",
                    shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                )
                log_print(f"[*] 已强制结束 Chrome 进程 PID:{pid} (端口 {port})")
    except Exception as e:
        log_print(f"[!] 强制结束 Chrome 进程失败: {e}")


def cleanup_instance(instance_config: dict, kill_browser: bool = True):
    """
    清理实例资源：
    - 重置雀手 requests.Session（清空 cookies）
    - 关闭 Chrome 浏览器（CDP优雅关闭 → 强制kill降级）
    - 删除独立 Cookie 文件
    - 可选删除 Profile 目录（切换账号时彻底清理）
    """
    global session

    # 1. 清理雀手 Session（全局 requests.Session）
    if session:
        session.cookies.clear()
        log_print("[*] 已清空雀手 Session Cookies")

    if not instance_config:
        return

    port = instance_config.get("port")
    cookie_file = instance_config.get("cookie_file")
    profile_dir = instance_config.get("profile_dir")

    # 2. 关闭 Chrome（千牛）
    if port and is_port_open(port):
        try:
            with sync_playwright() as p:
                browser = p.chromium.connect_over_cdp(f"http://127.0.0.1:{port}")
                browser.close()
                log_print(f"[*] 已通过 CDP 关闭 Chrome (端口 {port})")
        except Exception as e:
            log_print(f"[!] CDP 关闭 Chrome 失败，尝试强制结束: {e}")
            _kill_chrome_by_port(port)

    # 3. 删除 Cookie 文件
    if cookie_file and os.path.exists(cookie_file):
        try:
            os.remove(cookie_file)
            log_print(f"[*] 已删除 Cookie 文件: {cookie_file}")
        except Exception as e:
            log_print(f"[!] 删除 Cookie 文件失败: {e}")

    # 4. 切换账号时彻底删除 Profile（避免缓存串号）
    if kill_browser and profile_dir and os.path.exists(profile_dir):
        try:
            shutil.rmtree(profile_dir)
            log_print(f"[*] 已清理 Profile 目录: {profile_dir}")
        except Exception as e:
            log_print(f"[!] 清理 Profile 目录失败: {e}")


def get_instance_config(qn_username: str) -> dict:
    safe_name = re.sub(r'[^\w\u4e00-\u9fff]', '_', qn_username)[:30]
    port = find_free_port(DEBUG_PORT_RANGE[0], DEBUG_PORT_RANGE[1])
    profile_dir = os.path.expanduser(f"~/playwright_chrome_profile_{safe_name}_{port}")
    cookie_file = f"taobao_cookies_{safe_name}_{port}.json"
    os.makedirs(profile_dir, exist_ok=True)
    return {
        "port": port,
        "profile_dir": profile_dir,
        "cookie_file": cookie_file,
        "safe_name": safe_name,
    }


BASE_DIR = os.path.dirname(os.path.abspath(__file__))


def find_chrome_executable():
    global g_user_chrome_path
    if g_user_chrome_path and os.path.isfile(g_user_chrome_path):
        log_print(f"[*] 使用用户手动指定Chrome路径：{g_user_chrome_path}")
        return g_user_chrome_path

    if sys.platform == "darwin":
        candidates = [
            "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
            "/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary",
        ]
    elif sys.platform == "win32":
        local_chrome = os.path.join(BASE_DIR, "chrome", "chrome.exe")
        candidates = [
            r"C:\Program Files\Google\Chrome\Application\chrome.exe",
            r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
            local_chrome,
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


def ensure_chrome_debugging(port: int, profile_dir: str) -> bool:
    if is_port_open(port):
        log_print(f"[*] 检测到 Chrome 调试端口 {port} 已开启")
        return True

    chrome_path = find_chrome_executable()
    if not chrome_path:
        log_print("[!] 未找到 Chrome，请在界面点击【选择】按钮指定chrome.exe，或手动启动：")
        if sys.platform == "darwin":
            log_print(r'    /Applications/Google\ Chrome.app/Contents/MacOS/Google\ Chrome --remote-debugging-port=9222')
        elif sys.platform == "win32":
            log_print(r'    "C:\Program Files\Google\Chrome\Application\chrome.exe" --remote-debugging-port=9222')
            log_print(r'    .\chrome\chrome.exe --remote-debugging-port=9222')
        return False

    log_print(f"[*] 尝试启动 Chrome（调试端口 {port}）...")
    os.makedirs(profile_dir, exist_ok=True)

    cmd = [
        chrome_path,
        f"--remote-debugging-port={port}",
        f"--user-data-dir={profile_dir}",
        "--no-first-run",
        "--no-default-browser-check",
    ]
    subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    for i in range(10):
        safe_sleep(1)
        if is_port_open(port):
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
        log_print(f"        ✅ 地址识别接口调用成功: {resp.text}")
        resp_data = resp.json().get("data", {})
        safe_sleep(0.5)
        check_stop()
    except Exception as e:
        log_print(f"        ⚠️ 结构化地址接口调用失败: {e}")
        return {}

    return {
        "contactName": resp_data.get("name", ""),
        "mobilePhone": resp_data.get("mobilePhone", ""),
        "adr": resp_data.get("province", "")+resp_data.get("city", "")+resp_data.get("county", "")+resp_data.get("town", "")+resp_data.get("detailAddress", ""),
        "provinceName": resp_data.get("province", ""),
        "cityName": resp_data.get("city", ""),
        "districtName": resp_data.get("county", ""),
        "townName": resp_data.get("town", ""),
        "divisionId": resp_data.get("divisionId", ""),
    }


# ==================== 淘宝订单与地址接口 ====================

def query_order_by_tid(session: requests.Session, tids: str):
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
        "tabCode": "latest3Months",
        "useCheckcode": "false",
        "errorCheckcode": "false",
        "payDateBegin": "0",
        "rateStatus": "ALL",
        "buyerNick": "",
        "orderStatus": "",
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
        "logisticsService": "",
        "o2oDeliveryType": "ALL",
        "rxAuditFlag": "0",
        "queryOrder": "desc",
        "holdStatus": "0",
        "rxElectronicAuditFlag": "0",
        "queryMore": "false",
        "payDateEnd": "0",
        "rxWaitSendflag": "0",
        "sellerMemo": "0",
        "rxElectronicAllFlag": "0",
        "rxSuccessflag": "0",
        "unionSearchTotalNum": "0",
        "refund": "",
        "unionSearchPageNum": "",
        "bizOrderId": tids,
        "auctionId": "",
        "batchType": "bizOrderId",
        "isBatchSearch": "true"
    }

    try:
        resp = session.post(
            url,
            params=params,
            data=urllib.parse.urlencode(data),
            headers=TB_API_HEADERS,
            timeout=30,
        )
        safe_sleep(2)
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

    log_print(f"    [+] 订单接口传入条数： {len(tids.split(','))} 返回数据条数: {len(result.get('mainOrders', []))}")
    return result


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
        safe_sleep(1)
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
        ret = result.get("ret", [])
        for row in ret:
            if row == 'SUCCESS::调用成功':
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
                     filtered_tids: set, start_date: str, end_date: str, instance_config: dict):
    global session, USERNAME, PASSWORD
    USERNAME = qn_username
    PASSWORD = qn_password

    port = instance_config["port"]
    profile_dir = instance_config["profile_dir"]
    cookie_file = instance_config["cookie_file"]

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

    if not ensure_chrome_debugging(port, profile_dir):
        return

    with sync_playwright() as p:
        log_print("[*] 正在通过 CDP 连接到 Chrome...")
        browser = p.chromium.connect_over_cdp(f"http://127.0.0.1:{port}")

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
            log_print(f"[*] 未登录，开始自动填充账号密码... ({reason})")

            login_frame, source = find_login_frame(page)
            if not login_frame:
                log_print("[!] 未找到登录框，终止登录流程")
                return

            log_print(f"[+] 找到登录框: {source}")

            try:
                tab = login_frame.locator(".password-login-tab-item")
                if tab.count() > 0 and tab.is_visible():
                    tab.click()
                    safe_sleep(1)
                    log_print("[+] 已切换到密码登录方式")
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

            log_print("[*] 点击登录按钮...")
            login_frame.click(".fm-submit.password-login")
            safe_sleep(3)
            check_stop()

            log_print("\n" + "=" * 65)
            log_print("  ⚠️ 重要：请手动依次完成【滑块验证 + 短信验证码】全部校验！")
            log_print(f"  持续监测登录状态，最长总等待时长 {MAX_WAIT} 秒")
            log_print("=" * 65 + "\n")

            logged_in = False
            start_time = time.time()
            last_tip = ""
            while time.time() - start_time < MAX_WAIT:
                check_stop()
                is_login_success, msg = is_logged_in(page)
                if is_login_success:
                    log_print(f"\n[+] ✅ 全部验证完成，登录成功！({msg})")
                    logged_in = True
                    log_print("[*] 等待工作台页面加载完成...")
                    safe_sleep(4)
                    break

                if msg != last_tip:
                    log_print(f"    [等待验证] {msg}")
                    last_tip = msg

                elapsed_sec = int(time.time() - start_time)
                if elapsed_sec % 10 == 0:
                    log_print(f"    已等待 {elapsed_sec} / {MAX_WAIT} 秒，请完成滑块、短信验证码")
                safe_sleep(2)

            if not logged_in:
                log_print("\n[!] ❌ 登录等待超时！请检查是否完成全部验证")
                log_print(f"[*] 当前页面URL: {page.url}")
                log_print(f"[*] 当前页面标题: {page.title()}")
                log_print(f"[*] 是否仍然存在登录框: {is_still_on_login_page(page)}")
                return

        cookies = context.cookies()
        unique_cookies = get_unique_cookies(cookies)
        log_print(f"\n[+] 原始 Cookie 数: {len(cookies)}, 去重后: {len(unique_cookies)}")

        with open(cookie_file, "w", encoding="utf-8") as f:
            json.dump(unique_cookies, f, ensure_ascii=False, indent=2)
        log_print(f"[+] 已保存: {cookie_file}")

    try:
        cookie_jar = load_cookies(cookie_file)
    except FileNotFoundError:
        log_print(f"[!] 找不到 Cookie 文件: {cookie_file}")
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
    fail_count = 0
    wait_orders = []
    res_orders = []
    for idx, order in enumerate(ORDERS):
        check_stop()
        tid = order["tid"]

        if str(tid) in filtered_tids:
            log_print(f"\n{'=' * 70}")
            log_print(f"[{idx}/{total}] 订单 tid={tid} 已在历史记录中，跳过")
            continue

        log_print(f"\n{'=' * 70}")
        log_print(f"[{idx}/{total}] 处理订单 tid={tid}")
        wait_orders.append(order)
        if len(wait_orders) == 15:
            tids = [str(order["tid"]) for order in wait_orders]
            tids_str = ",".join(tids)
            log_print("    [*] 正在批量查询订单...")
            order_info = query_order_by_tid(session, tids_str)
            wait_orders = []
            if order_info:
                res_orders.extend(order_info.get("mainOrders", []))
    if wait_orders:
        tids = [str(order["tid"]) for order in wait_orders]
        tids_str = ",".join(tids)
        log_print("    [*] 批量查询订单...")
        order_info = query_order_by_tid(session, tids_str)
        wait_orders = []
        if order_info:
            res_orders.extend(order_info.get("mainOrders", []))

    for idx, order in enumerate(ORDERS):
        check_stop()
        tid = order["tid"]
        refund_address = order["refund_address"]
        for main_order in res_orders:
            check_stop()

            if str(tid) != str(main_order.get("id", 'unknown')):
                continue

            sub_orders = main_order.get("subOrders", [])
            if len(sub_orders) > 1:
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='订单有多个子订单')
                log_print(f"    [*] 订单 {tid} 有 {len(sub_orders)} 个子订单，跳过")
                continue

            sub_order = sub_orders[0]

            return_address_vo = sub_order.get("returnAddressVO", {})

            place_holder_info = return_address_vo.get("placeHolderInfo", "unknown")
            if place_holder_info == '订单不支持':
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='订单不支持')
                log_print(f"    [*] 订单 {tid} 不支持，跳过")
                continue

            expect_state_text = return_address_vo.get("expectStateText", "unknown")
            if expect_state_text == '已指定':
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='订单已指定')
                log_print(f"    [*] 订单 {tid} 已指定，跳过")
                continue

            expect_color = return_address_vo.get("expectColor", "")
            if expect_color != '#FF0000':
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='订单指定地址熄灭不支持修改')
                log_print(f"    [*] 订单 {tid} 状态颜色为 {expect_color}，跳过")
                continue

            new_info = parse_refund_address(refund_address, session)
            if not new_info:
                log_print(f"    [*] 订单 {tid} 识别地址失败，跳过")
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='识别地址失败')
                continue

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
                append_order_record(FAIL_FILE, tid, qn_username, reason='csrf_token获取失败')
                continue

            safe_sleep(0.5)
            check_stop()

            log_print("    [*] 获取地址列表...")
            addresses = get_address_list(session)
            if not addresses:
                log_print("    [!] 获取地址列表失败，跳过")
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='获取地址列表失败')
                continue
            if len(addresses) < 3:
                log_print("    [!] 地址总数不足3条，无法修改第3个地址，跳过")
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='地址列表不足3条')
                continue

            target_addr = addresses[2]
            run_ok = update_address(session, target_addr, new_info, csrf)
            if not run_ok:
                log_print(f"    [!] ❌ 订单 {tid} 地址更新失败")
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='地址更新失败')
                continue

            new_address_id = target_addr.get("contactId", "")
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
                append_order_record(SUCCESS_FILE, tid, qn_username, reason='修改成功')
            else:
                log_print(f"    [!] ❌ 订单 {tid} 操作失败")
                fail_count += 1
                append_order_record(FAIL_FILE, tid, qn_username, reason='订单地址修改失败')
            safe_sleep(0.8)

    log_print(f"\n{'=' * 70}")
    log_print(
        f"[✓] 处理完成: 总计 {total} | "
        f"成功 {success_count} | 失败 {fail_count}"
    )
    log_print(f"{'=' * 70}")


# ==================== GUI 界面 ====================
class App:
    def __init__(self, root):
        self.root = root
        self.root.title("订单地址自动修改工具")
        self.root.geometry("950x820")
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        input_frame = ttk.Frame(root, padding=10)
        input_frame.pack(fill=tk.X)

        self.acc_store = load_account_store()

        ttk.Label(input_frame, text="雀手账号:").grid(row=0, column=0, sticky=tk.W, pady=3)
        self.qz_user_var = tk.StringVar()
        self.qz_user = ttk.Combobox(input_frame, textvariable=self.qz_user_var, width=30)
        qz_list = list(self.acc_store["qz"].keys())
        self.qz_user['values'] = qz_list
        self.qz_user.grid(row=0, column=1, padx=5)
        self.qz_user.bind("<<ComboboxSelected>>", self.on_qz_account_select)
        self.qz_user_var.set("17850939652")

        ttk.Label(input_frame, text="雀手密码:").grid(row=0, column=2, sticky=tk.W, pady=3)
        self.qz_pass = ttk.Entry(input_frame, width=30, show="*")
        self.qz_pass.grid(row=0, column=3, padx=5)
        self.qz_pass.insert(0, "qqq123123")

        ttk.Label(input_frame, text="千牛账号:").grid(row=1, column=0, sticky=tk.W, pady=3)
        self.qn_user_var = tk.StringVar()
        self.qn_user = ttk.Combobox(input_frame, textvariable=self.qn_user_var, width=30)
        qn_list = list(self.acc_store["qn"].keys())
        self.qn_user['values'] = qn_list
        self.qn_user.grid(row=1, column=1, padx=5)
        self.qn_user.bind("<<ComboboxSelected>>", self.on_qn_account_select)
        self.qn_user_var.set("smotouchmud旗舰店:测试")

        ttk.Label(input_frame, text="千牛密码:").grid(row=1, column=2, sticky=tk.W, pady=3)
        self.qn_pass = ttk.Entry(input_frame, width=30, show="*")
        self.qn_pass.grid(row=1, column=3, padx=5)
        self.qn_pass.insert(0, "qqq123123")

        ttk.Label(input_frame, text="开始日期(YYYY‑MM‑DD):").grid(row=2, column=0, sticky=tk.W, pady=3)
        self.start_date_entry = ttk.Entry(input_frame, width=15)
        self.start_date_entry.grid(row=2, column=1, padx=5, sticky=tk.W)

        ttk.Label(input_frame, text="结束日期(YYYY‑MM‑DD):").grid(row=2, column=2, sticky=tk.W, pady=3)
        self.end_date_entry = ttk.Entry(input_frame, width=15)
        self.end_date_entry.grid(row=2, column=3, padx=5, sticky=tk.W)

        ttk.Label(input_frame, text="执行间隔(分钟):").grid(row=3, column=0, sticky=tk.W, pady=3)
        self.interval = ttk.Entry(input_frame, width=10)
        self.interval.grid(row=3, column=1, sticky=tk.W, padx=5)
        self.interval.insert(0, "60")

        ttk.Label(input_frame, text="Chrome程序路径:").grid(row=4, column=0, sticky=tk.W, pady=3)
        self.chrome_path_var = tk.StringVar()
        self.chrome_entry = ttk.Entry(input_frame, textvariable=self.chrome_path_var, width=45)
        self.chrome_entry.grid(row=4, column=1, columnspan=2, padx=5, sticky=tk.W)
        self.btn_select_chrome = ttk.Button(input_frame, text="选择", command=self.select_chrome_file)
        self.btn_select_chrome.grid(row=4, column=3, padx=3, sticky=tk.W)

        btn_frame = ttk.Frame(input_frame)
        btn_frame.grid(row=5, column=0, columnspan=4, pady=8)
        self.start_btn = ttk.Button(btn_frame, text="开始执行", command=self.start_task)
        self.start_btn.pack(side=tk.LEFT, padx=5)
        self.stop_btn = ttk.Button(btn_frame, text="停止执行", command=self.stop_task, state=tk.DISABLED)
        self.stop_btn.pack(side=tk.LEFT, padx=5)

        now = datetime.now()
        default_start = (now - timedelta(days=15)).strftime("%Y-%m-%d")
        default_end = now.strftime("%Y-%m-%d")
        self.start_date_entry.insert(0, default_start)
        self.end_date_entry.insert(0, default_end)

        ttk.Label(root, text="运行日志:", font=("Arial", 10, "bold")).pack(anchor=tk.W, padx=10, pady=(10, 0))
        self.log_text = scrolledtext.ScrolledText(root, height=34, state=tk.NORMAL, wrap=tk.WORD)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.running = False
        self.timer = None
        self.worker_thread = None
        self.instance_config = None
        self.prev_instance_config = None  # 用于跟踪上一个实例，切换账号时清理
        self.consume_log_queue()

    def on_qz_account_select(self, event):
        acc = self.qz_user_var.get().strip()
        pwd = self.acc_store["qz"].get(acc, "")
        self.qz_pass.delete(0, tk.END)
        self.qz_pass.insert(0, pwd)

    def on_qn_account_select(self, event):
        acc = self.qn_user_var.get().strip()
        pwd = self.acc_store["qn"].get(acc, "")
        self.qn_pass.delete(0, tk.END)
        self.qn_pass.insert(0, pwd)

    def select_chrome_file(self):
        global g_user_chrome_path
        file_path = filedialog.askopenfilename(
            title="请选择 chrome.exe",
            filetypes=[("Chrome可执行文件", "chrome.exe"), ("可执行程序", "*.exe"), ("全部文件", "*.*")]
        )
        if file_path:
            g_user_chrome_path = file_path
            self.chrome_path_var.set(file_path)
            log_print(f"[*] 用户已设置Chrome路径：{file_path}")

    def consume_log_queue(self):
        try:
            while True:
                msg = LOG_QUEUE.get_nowait()
                self.log_text.insert(tk.END, msg + "\n")
                self.log_text.see(tk.END)
        except Empty:
            pass
        self.root.after(50, self.consume_log_queue)

    def on_close(self):
        self.stop_task()
        # 窗口关闭时彻底清理所有资源
        cleanup_instance(self.instance_config, kill_browser=True)
        self.instance_config = None
        self.root.destroy()

    def refresh_account_combobox(self):
        self.acc_store = load_account_store()
        self.qz_user['values'] = list(self.acc_store["qz"].keys())
        self.qn_user['values'] = list(self.acc_store["qn"].keys())

    def start_task(self):
        global g_user_chrome_path, INSTANCE_NAME
        g_user_chrome_path = self.chrome_path_var.get().strip()
        if self.running:
            return

        qz_acc = self.qz_user_var.get().strip()
        qz_pwd = self.qz_pass.get().strip()
        qn_acc = self.qn_user_var.get().strip()
        qn_pwd = self.qn_pass.get().strip()
        save_one_account("qz", qz_acc, qz_pwd)
        save_one_account("qn", qn_acc, qn_pwd)
        self.refresh_account_combobox()

        # 【关键】如果已有旧实例（切换账号/重新执行），先彻底清理旧会话
        if self.instance_config:
            log_print("[*] 检测到已有实例，正在清理旧会话...")
            cleanup_instance(self.instance_config, kill_browser=True)
            self.prev_instance_config = self.instance_config
            self.instance_config = None

        # 【关键】设置实例标识，用于日志前缀和窗口标题
        INSTANCE_NAME = qn_acc

        # 【关键】为当前实例分配独立端口、Profile、Cookie文件
        try:
            self.instance_config = get_instance_config(qn_acc)
        except RuntimeError as e:
            log_print(f"[!] {e}")
            return

        self.root.title(
            f"订单地址自动修改工具 - {qn_acc} (端口:{self.instance_config['port']})"
        )

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
        log_print("\n[!] 已发送停止信号，正在中断当前操作并清理会话...")
        # 【关键】停止时彻底清理雀手+千牛会话
        cleanup_instance(self.instance_config, kill_browser=True)
        self.instance_config = None
        log_print("[*] 会话清理完成\n")

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
            # 【关键】单次执行完毕或停止后，清理会话避免Cookie残留
            cleanup_instance(self.instance_config, kill_browser=True)
            self.instance_config = None
            log_print("\n[*] 定时任务已完全停止，会话已清理\n")

    def execute_once(self):
        if _task_stop_event.is_set():
            return
        qz_username = self.qz_user_var.get().strip()
        qz_password = self.qz_pass.get().strip()
        qn_username = self.qn_user_var.get().strip()
        qn_password = self.qn_pass.get().strip()

        ui_start_date = self.start_date_entry.get().strip()
        ui_end_date = self.end_date_entry.get().strip()

        if not all([qz_username, qz_password, qn_username, qn_password, ui_start_date, ui_end_date]):
            log_print("[!] 错误：请填写账号密码以及开始、结束日期（格式 YYYY‑MM‑DD）")
            return

        start_date = f"{ui_start_date} 00:00"
        end_date = f"{ui_end_date} 23:59"

        filtered_tids = get_filtered_tids()
        log_print(f"\n[*] 当前已处理订单过滤数: {len(filtered_tids)}")
        log_print(f"[*] 本次查询日期范围: {start_date} ~ {end_date}")

        run_main_process(qz_username, qz_password, qn_username, qn_password,
                         filtered_tids, start_date, end_date, self.instance_config)

        cleanup_old_records(SUCCESS_FILE)
        cleanup_old_records(FAIL_FILE)
        log_print("\n[*] 本次执行完毕，已清理超30天的历史记录")
        # 【关键】单次执行完毕后清理会话，避免切换账号时Cookie串用
        cleanup_instance(self.instance_config, kill_browser=True)
        self.instance_config = None


def main():
    root = tk.Tk()
    app = App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
