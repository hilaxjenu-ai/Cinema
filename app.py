from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
import re
import socket
import time
from urllib.parse import quote, unquote, urljoin, urlparse
import uuid

from bs4 import BeautifulSoup
from flask import Flask, Response, jsonify, render_template, request, stream_with_context
import requests
from requests.adapters import HTTPAdapter
import urllib3
from urllib3.util.retry import Retry

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

app = Flask(__name__)

DEFAULT_PRIMARY_URL = os.environ.get(
    "MOVIESDA_SEED_URL", "https://moviesda36.com/movies.php"
)
DEFAULT_DUBBED_URL = os.environ.get(
    "ISAIDUB_SEED_URL", "https://isaidub.green/"
)
DUBBED_SECTION_KEY = "__tamil_dubbed_movies__"
ADMIN_KEY = os.environ.get("MEDIA_HUB_ADMIN_KEY", "admin123")

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

MEDIA_EXT_RE = re.compile(r"\.(mp4|m3u8|mkv|webm|mpd|avi)(\?|$)", re.I)
STREAM_HINT_RE = re.compile(r"(stream|play|watch|embed|player|dl=|download\.php)", re.I)
PAGINATION_URL_RE = re.compile(r"([?&](page|p|pg)=\d+|/(page|p)[/-]?\d+)", re.I)
PAGINATION_TEXT_RE = re.compile(
    r"^(next|prev|previous|first|last|\d+|page\s*\d+|»|«|>|<)$", re.I
)
QUALITY_LABEL_RE = re.compile(
    r"\b(2160p|4k|1080p|720p|480p|360p|240p|hd|cam|hq|dvdrip|webrip)\b", re.I
)
NOISE_WORDS_RE = re.compile(
    r"\b(tamil|dubbed|movie|movies|hd|cam|hq|dvdrip|webrip|bluray|predvd|"
    r"2160p|4k|1080p|720p|480p|360p|240p|x264|x265|hevc|aac|mp4|mkv|sample|"
    r"full|official|trailer|teaser|part\s*\d+|season\s*\d+|episode\s*\d+|ep\s*\d+)\b",
    re.I,
)
SOURCE_BRAND_RE = re.compile(
    r"\b(moviesda(?:\.(?:mobi|com|net|org|in|cv|one|live|pro))?|isaidub(?:\.(?:green|com|net|one))?|tamilrockers|tamilyogi|kuttymovies)\b\s*[-:|/]*\s*",
    re.I,
)
PRIMARY_DUBBED_CAT_RE = re.compile(r"\b(tamil\s*dubbed|dubbed\s*movies?)\b", re.I)
PROMO_JUNK_RE = re.compile(
    r"^(download\s*now|watch\s*now|play\s*now|click\s*here|get\s*app|install|telegram|join\s*now|home)$",
    re.I,
)
BAD_IMG_RE = re.compile(
    r"(logo|icon|favicon|sprite|banner|ads?|promo|telegram|whatsapp|spinner|loading|blank|avatar|arrow|folder)",
    re.I,
)
FALLBACK_IPS = {"moviesda36.com": "104.21.79.215"}

_HOME_PRIMARY_URL = DEFAULT_PRIMARY_URL
_ACTIVE_PRIMARY_URL = DEFAULT_PRIMARY_URL
_ACTIVE_DUBBED_URL = DEFAULT_DUBBED_URL
_SESSION_MODE = "primary"

_IP_CACHE: dict[str, str] = {}
_HTML_CACHE: dict[str, tuple[float, str]] = {}
_PAGE_ENTRIES_CACHE: dict[str, tuple[float, list[dict]]] = {}
_MEDIA_TOKENS: dict[str, dict] = {}
_POSTER_CACHE: dict[str, tuple[float, tuple[str | None, str | None]]] = {}
_ORIG_GETADDRINFO = socket.getaddrinfo

CACHE_TTL_SEC = 600


def is_admin_request() -> bool:
    provided = (
        request.headers.get("X-Admin-Key")
        or request.args.get("admin_key")
        or ""
    ).strip()
    return bool(ADMIN_KEY) and provided == ADMIN_KEY


def normalize_http_url(raw: str) -> str:
    val = (raw or "").strip()
    if not val:
        return ""
    if not re.match(r"^https?://", val, re.I):
        val = "https://" + val
    return val


def update_active_sources(
    seed_override: str | None = None, dubbed_override: str | None = None
) -> tuple[str, str]:
    global _HOME_PRIMARY_URL, _ACTIVE_PRIMARY_URL, _ACTIVE_DUBBED_URL
    raw_seed = (seed_override or "").strip()
    raw_dubbed = (dubbed_override or "").strip()

    if raw_seed or raw_dubbed:
        if not is_admin_request():
            raise PermissionError("Admin access required to change site URLs")
        changed = False
        if raw_seed:
            norm_seed = normalize_http_url(raw_seed)
            if norm_seed and (
                norm_seed != _HOME_PRIMARY_URL or norm_seed != _ACTIVE_PRIMARY_URL
            ):
                _HOME_PRIMARY_URL = norm_seed
                if _SESSION_MODE == "primary":
                    _ACTIVE_PRIMARY_URL = norm_seed
                changed = True
        if raw_dubbed:
            norm_dubbed = normalize_http_url(raw_dubbed)
            if norm_dubbed and norm_dubbed != _ACTIVE_DUBBED_URL:
                _ACTIVE_DUBBED_URL = norm_dubbed
                if _SESSION_MODE == "dubbed":
                    _ACTIVE_PRIMARY_URL = norm_dubbed
                changed = True
        if changed:
            _HTML_CACHE.clear()
            _PAGE_ENTRIES_CACHE.clear()
            _POSTER_CACHE.clear()

    return _HOME_PRIMARY_URL, _ACTIVE_DUBBED_URL


def switch_primary_source(mode: str) -> str:
    global _ACTIVE_PRIMARY_URL, _SESSION_MODE
    target_mode = "dubbed" if mode == "dubbed" else "primary"
    new_url = (
        _ACTIVE_DUBBED_URL if target_mode == "dubbed" else _HOME_PRIMARY_URL
    )
    _SESSION_MODE = target_mode
    _ACTIVE_PRIMARY_URL = new_url
    return _ACTIVE_PRIMARY_URL


def is_dubbed_host_url(url: str) -> bool:
    if url == DUBBED_SECTION_KEY:
        return True
    try:
        u_host = urlparse(url).netloc.lower()
        p_host = urlparse(_HOME_PRIMARY_URL).netloc.lower()
        d_host = urlparse(_ACTIVE_DUBBED_URL).netloc.lower()
        if u_host and p_host and u_host == p_host and p_host != d_host:
            return False
        if u_host and d_host and u_host == d_host:
            return True
        return _SESSION_MODE == "dubbed"
    except Exception:
        return _SESSION_MODE == "dubbed"


def resolve_browse_target(url: str) -> str:
    if url == DUBBED_SECTION_KEY:
        return switch_primary_source("dubbed")
    return url


def _build_session() -> requests.Session:
    sess = requests.Session()
    retry = Retry(
        total=1,
        connect=1,
        read=1,
        backoff_factor=0.2,
        status_forcelist=(502, 503, 504),
        allowed_methods=("GET",),
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=24, pool_maxsize=24)
    sess.mount("https://", adapter)
    sess.mount("http://", adapter)
    return sess


_HTTP = _build_session()


def sanitize_display_title(raw_title: str, fallback: str = "Movie") -> str:
    txt = unquote(raw_title or "")
    txt = SOURCE_BRAND_RE.sub("", txt)
    txt = re.sub(r"\s*[-:|/]+\s*$", "", txt)
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt or fallback


def register_media_token(
    media_url: str, referer: str | None = None, filename: str = "video.mp4"
) -> str:
    token = uuid.uuid4().hex
    _MEDIA_TOKENS[token] = {
        "url": media_url,
        "referer": referer,
        "filename": filename,
    }
    return token


def resolve_ip_via_doh(host: str) -> str | None:
    for ep, params in [
        ("https://1.1.1.1/dns-query", {"name": host, "type": "A"}),
        ("https://8.8.8.8/resolve", {"name": host, "type": "A"}),
    ]:
        try:
            r = _HTTP.get(
                ep,
                params=params,
                headers={"Accept": "application/dns-json"},
                timeout=4,
            )
            if r.ok:
                for ans in r.json().get("Answer", []):
                    if ans.get("type") == 1 and ans.get("data"):
                        return ans["data"].strip()
        except Exception:
            continue
    return None


def resolve_host_ip(host: str) -> str | None:
    key = (host or "").lower().strip()
    if not key:
        return None
    if key in _IP_CACHE:
        return _IP_CACHE[key]
    try:
        infos = _ORIG_GETADDRINFO(
            key, 443, family=socket.AF_INET, type=socket.SOCK_STREAM
        )
        if infos:
            _IP_CACHE[key] = infos[0][4][0]
            return _IP_CACHE[key]
    except Exception:
        pass
    ip = resolve_ip_via_doh(key) or FALLBACK_IPS.get(key)
    if ip:
        _IP_CACHE[key] = ip
    return ip


def patched_getaddrinfo(host, port, family=0, type=0, proto=0, flags=0):
    try:
        return _ORIG_GETADDRINFO(host, port, family, type, proto, flags)
    except OSError:
        ip = resolve_host_ip(str(host))
        if ip:
            return _ORIG_GETADDRINFO(ip, port, socket.AF_INET, type, proto, flags)
        raise


socket.getaddrinfo = patched_getaddrinfo


def req_get(
    url, referer=None, headers=None, allow_redirects=True, timeout=9, stream=False
):
    req_headers = {
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Connection": "keep-alive",
    }
    if referer:
        req_headers["Referer"] = referer
    if headers:
        req_headers.update(headers)
    try:
        return _HTTP.get(
            url,
            headers=req_headers,
            allow_redirects=allow_redirects,
            timeout=timeout,
            verify=True,
            stream=stream,
        )
    except requests.exceptions.SSLError:
        return _HTTP.get(
            url,
            headers=req_headers,
            allow_redirects=allow_redirects,
            timeout=timeout,
            verify=False,
            stream=stream,
        )


def fetch_html(url, referer=None, timeout=9):
    now = time.monotonic()
    cached = _HTML_CACHE.get(url)
    if cached and (now - cached[0]) < CACHE_TTL_SEC:
        return cached[1]
    r = req_get(url, referer=referer, timeout=timeout)
    r.raise_for_status()
    html = r.text
    _HTML_CACHE[url] = (now, html)
    return html


def clean_movie_query(raw_title: str) -> str:
    txt = sanitize_display_title(raw_title, "")
    txt = re.sub(r"\[[^\]]*\]|\([^\)]*\)", " ", txt)
    txt = NOISE_WORDS_RE.sub(" ", txt)
    txt = re.sub(r"\b(19|20)\d{2}\b", " ", txt)
    txt = re.sub(r"[^a-zA-Z0-9\s]", " ", txt)
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt


def extract_page_poster_url(
    page_url: str | None, referer: str | None = None
) -> tuple[str | None, str | None]:
    target = (page_url or "").strip()
    if not target:
        return None, None

    cache_key = f"{target}|{referer or ''}"
    now = time.monotonic()
    cached = _POSTER_CACHE.get(cache_key)
    if cached and (now - cached[0]) < CACHE_TTL_SEC:
        return cached[1]

    best_img: str | None = None
    best_ref: str | None = target
    try:
        html = fetch_html(target, referer=referer, timeout=7)
        soup = BeautifulSoup(html, "html.parser")

        info_imgs: set[int] = set()
        for tag in soup.find_all(
            ["h1", "h2", "h3", "h4", "div", "p", "span", "strong", "td", "th"]
        ):
            txt = re.sub(r"\s+", " ", tag.get_text(" ", strip=True)).strip()
            if re.fullmatch(r"movie\s*information", txt, re.I):
                curr = tag
                for _ in range(4):
                    parent = curr.parent
                    if not parent:
                        break
                    imgs_in_box = parent.find_all("img")
                    if 1 <= len(imgs_in_box) <= 4:
                        for im in imgs_in_box:
                            info_imgs.add(id(im))
                        break
                    curr = parent

        candidates: list[tuple[int, str]] = []
        for img in soup.find_all("img"):
            raw_src = (
                img.get("src")
                or img.get("data-src")
                or img.get("data-lazy-src")
                or img.get("data-original")
                or ""
            ).strip()
            if not raw_src or raw_src.startswith("data:image"):
                continue

            full_img = urljoin(target, raw_src)
            parsed_img = urlparse(full_img)
            if parsed_img.scheme not in ("http", "https"):
                continue

            cls_self = " ".join(img.get("class", []))
            parent_cls = (
                " ".join(img.parent.get("class", [])) if img.parent else ""
            )
            alt_txt = (img.get("alt") or "").strip()
            combined_meta = f"{full_img} {cls_self} {parent_cls} {alt_txt}"

            is_info_poster = id(img) in info_imgs
            if not is_info_poster and BAD_IMG_RE.search(combined_meta):
                continue

            w_attr = int(re.sub(r"\D", "", img.get("width") or "0") or "0")
            h_attr = int(re.sub(r"\D", "", img.get("height") or "0") or "0")
            if not is_info_poster and ((w_attr and w_attr < 50) or (h_attr and h_attr < 50)):
                continue

            score = 10
            if is_info_poster:
                score += 120
            if re.search(
                r"\b(poster|thumb|thumbnail|cover|movie|film|movie-?info)\b",
                combined_meta,
                re.I,
            ):
                score += 40
            if re.search(r"\.(jpe?g|png|webp)(\?|$)", full_img, re.I):
                score += 25
            if w_attr >= 100 or h_attr >= 100:
                score += 20
            if h_attr > w_attr:
                score += 15
            if not is_info_poster and img.find_parent(["header", "nav", "footer"]):
                score -= 50

            if score > 0:
                candidates.append((score, full_img))

        candidates.sort(key=lambda pair: pair[0], reverse=True)
        if candidates:
            best_img = candidates[0][1]
            best_ref = target
    except Exception:
        best_img = None

    _POSTER_CACHE[cache_key] = (now, (best_img, best_ref))
    return best_img, best_ref


def build_poster_proxy_url(
    title: str, page_url: str | None = None, referer: str | None = None
) -> str:
    params = [f"title={quote(sanitize_display_title(title, 'Movie'))}"]
    if page_url:
        params.append(f"url={quote(page_url)}")
    if referer:
        params.append(f"referer={quote(referer)}")
    return "/api/poster-proxy?" + "&".join(params)


def fallback_poster_svg(title: str) -> Response:
    safe_title = clean_movie_query(title) or sanitize_display_title(title, "HILAX")
    words = safe_title.upper().split()
    line1 = " ".join(words[:2])[:18] or "HILAX CINEMA"
    line2 = " ".join(words[2:4])[:18]
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" width="300" height="450" viewBox="0 0 300 450">
  <defs>
    <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#1c212b"/>
      <stop offset="100%" stop-color="#0b0d12"/>
    </linearGradient>
  </defs>
  <rect width="300" height="450" fill="url(#bg)"/>
  <rect x="14" y="14" width="272" height="422" rx="10" fill="none" stroke="#e50914" stroke-width="2" opacity="0.7"/>
  <text x="150" y="205" fill="#ffffff" font-family="system-ui, sans-serif" font-size="22" font-weight="700" text-anchor="middle">{line1}</text>
  <text x="150" y="236" fill="#b3b3b3" font-family="system-ui, sans-serif" font-size="16" font-weight="500" text-anchor="middle">{line2}</text>
</svg>"""
    return Response(svg, status=200, mimetype="image/svg+xml")


def is_ignored_path(full_url):
    parsed = urlparse(full_url)
    path = parsed.path.rstrip("/")
    if not path and not parsed.query:
        return True
    return False


def _is_top_or_promo_link(el, raw_title: str, full_url: str) -> bool:
    if PROMO_JUNK_RE.match((raw_title or "").strip()):
        return True
    cls_self = " ".join(el.get("class", [])) if getattr(el, "get", None) else ""
    if re.search(r"\b(ad|ads|promo|banner|download-?btn|cta|top-?link)\b", cls_self, re.I):
        return True
    if re.search(r"/(ads|promo|banner|download-app|apk|telegram)\b", full_url, re.I):
        return True
    for parent in el.parents:
        if getattr(parent, "name", None) in ("header", "nav"):
            return True
        cls = " ".join(parent.get("class", [])) if getattr(parent, "get", None) else ""
        pid = parent.get("id") or ""
        if re.search(
            r"\b(header|navbar|top-?bar|menu-?bar|breadcrumb|promo|banner|ad-?box)\b",
            f"{cls} {pid}",
            re.I,
        ):
            return True
    return False


def _extract_dubbed_folder_section(soup: BeautifulSoup, base_url: str, base_host: str) -> list[dict]:
    section_anchor = None
    for tag in soup.find_all(["h1", "h2", "h3", "h4", "div", "p", "span", "strong"]):
        txt = re.sub(r"\s+", " ", tag.get_text(" ", strip=True)).strip()
        if re.fullmatch(r"tamil\s*dubbed\s*movies", txt, re.I):
            section_anchor = tag
            break

    container = None
    if section_anchor:
        curr = section_anchor
        for _ in range(4):
            parent = curr.parent
            if not parent:
                break
            links = parent.find_all("a", href=True)
            folder_like = [
                a
                for a in links
                if re.search(
                    r"\b(a-z|all\s*dubbed|20\d\d|web\s*series|yearly|collections|games|hd\s*dubbed|chinese|hollywood)\b",
                    f"{a.get_text(' ', strip=True)} {a.get('href', '')}",
                    re.I,
                )
            ]
            if len(folder_like) >= 4:
                container = parent
                break
            curr = parent

    search_root = container or soup
    found_items, seen = [], set()
    for a in search_root.find_all("a", href=True):
        raw_title = re.sub(r"\s+", " ", a.get_text(" ", strip=True)).strip()
        href = (a.get("href") or "").strip()
        if not href or href.startswith("#") or href.startswith("javascript:"):
            continue
        full_url = urljoin(base_url, href)
        if _is_top_or_promo_link(a, raw_title, full_url):
            continue
        parsed = urlparse(full_url)
        if parsed.scheme not in ("http", "https"):
            continue
        if base_host and parsed.netloc and parsed.netloc.lower() != base_host:
            continue
        if full_url in seen or len(raw_title) < 2:
            continue
        if re.fullmatch(r"(isaidub\s*website|page\s*keywords|home)", raw_title, re.I):
            continue
        seen.add(full_url)
        found_items.append(
            {
                "title": sanitize_display_title(raw_title, "Folder"),
                "url": full_url,
                "is_pagination": bool(PAGINATION_URL_RE.search(full_url)),
            }
        )

    folder_only = [
        it
        for it in found_items
        if re.search(
            r"\b(dubbed|series|collections|games|hollywood|chinese|20\d\d|a-z|yearly)\b",
            f"{it['title']} {it['url']}",
            re.I,
        )
    ]
    return folder_only if len(folder_only) >= 3 else found_items


def extract_div_f_links(html, base_url):
    soup = BeautifulSoup(html, "html.parser")
    base_host = urlparse(base_url).netloc.lower()
    dubbed_mode = is_dubbed_host_url(base_url)

    if dubbed_mode:
        dubbed_folders = _extract_dubbed_folder_section(soup, base_url, base_host)
        if dubbed_folders:
            return dubbed_folders

    items, seen = [], set()
    selectors = ["div.f a[href]", "main a[href]", "article a[href]", "a[href]"]
    chosen = []
    for sel in selectors:
        found = soup.select(sel)
        if found:
            chosen = found
            break

    raw_candidates = []
    for a in chosen:
        raw_title = re.sub(r"\s+", " ", a.get_text(" ", strip=True)).strip()
        href = (a.get("href") or "").strip()
        if (
            not href
            or href.startswith("#")
            or href.startswith("javascript:")
            or href.startswith("mailto:")
        ):
            continue
        full_url = urljoin(base_url, href)
        if _is_top_or_promo_link(a, raw_title, full_url):
            continue
        parsed = urlparse(full_url)
        if parsed.scheme not in ("http", "https"):
            continue
        if base_host and parsed.netloc and parsed.netloc.lower() != base_host:
            continue
        if is_ignored_path(full_url) or full_url in seen:
            continue
        if len(raw_title) < 2 and not PAGINATION_URL_RE.search(full_url):
            continue
        seen.add(full_url)
        raw_candidates.append(
            {
                "title": sanitize_display_title(raw_title, "Item"),
                "url": full_url,
                "is_pagination": bool(PAGINATION_URL_RE.search(full_url)),
            }
        )

    for item in raw_candidates:
        if (
            not dubbed_mode
            and not item["is_pagination"]
            and PRIMARY_DUBBED_CAT_RE.search(item["title"])
        ):
            continue
        items.append(item)

    return items


def extract_pagination_links(html, base_url):
    soup = BeautifulSoup(html, "html.parser")
    pages, seen = [], set()
    for a in soup.select(
        "div.f a[href], div.pagination a[href], div.paging a[href], a[href]"
    ):
        href = (a.get("href") or "").strip()
        if not href or href.startswith("#") or href.startswith("javascript:"):
            continue
        full_url = urljoin(base_url, href)
        if is_ignored_path(full_url) or full_url in seen:
            continue
        title = re.sub(r"\s+", " ", a.get_text(" ", strip=True)).strip()
        parent_cls = " ".join(a.parent.get("class", [])) if a.parent else ""
        in_pager_box = bool(re.search(r"(pagin|paging|page)", parent_cls, re.I))
        if (
            PAGINATION_URL_RE.search(full_url)
            or PAGINATION_TEXT_RE.match(title)
            or (in_pager_box and re.fullmatch(r"\d+", title))
        ):
            seen.add(full_url)
            pages.append(
                {
                    "title": sanitize_display_title(title, "Page"),
                    "url": full_url,
                    "is_pagination": True,
                }
            )
    return pages


def detect_quality_tag(text: str) -> str:
    m = QUALITY_LABEL_RE.search(text or "")
    if not m:
        return "Standard"
    q = m.group(1).lower()
    if q in ("2160p", "4k"):
        return "4K"
    if q in ("1080p",):
        return "1080p"
    if q in ("720p",):
        return "720p"
    if q in ("480p",):
        return "480p"
    if q in ("360p",):
        return "360p"
    if q in ("240p",):
        return "240p"
    return q.upper()


def extract_download_items(html, base_url):
    soup = BeautifulSoup(html, "html.parser")
    results, seen = [], set()
    for a in soup.select("a.coral[href], a[href*='/download/'], a[href*='dl=']"):
        href = (a.get("href") or "").strip()
        if not href:
            continue
        full_url = urljoin(base_url, href)
        if full_url in seen:
            continue
        seen.add(full_url)
        raw_label = re.sub(r"\s+", " ", a.get_text(" ", strip=True)).strip()
        clean_label = sanitize_display_title(raw_label, "Stream Option")
        parent_text = re.sub(
            r"\s+",
            " ",
            a.parent.get_text(" ", strip=True) if a.parent else "",
        ).strip()
        m = re.search(r"File Size:\s*[^|]+", parent_text, re.I)
        combined = f"{raw_label} {parent_text} {full_url}"
        results.append(
            {
                "title": clean_label,
                "url": full_url,
                "quality": detect_quality_tag(combined),
                "meta": m.group(0).strip() if m else "",
            }
        )
    return results


def is_direct_media_url(url, content_type=""):
    ct = (content_type or "").lower()
    return bool(MEDIA_EXT_RE.search(url)) or any(
        k in ct for k in ("video/", "mpegurl", "octet-stream", "force-download")
    )


def find_next_hop_links(html, base_url, current_host):
    soup = BeautifulSoup(html, "html.parser")
    candidates, seen = [], set()
    for el in soup.select("a[href], video[src], video source[src], iframe[src]"):
        raw = (el.get("href") or el.get("src") or "").strip()
        if not raw or raw.startswith("#") or raw.startswith("javascript:"):
            continue
        full_url = urljoin(base_url, raw)
        if full_url in seen or is_ignored_path(full_url):
            continue
        text = re.sub(r"\s+", " ", el.get_text(" ", strip=True)).strip()
        is_ext = (
            bool(urlparse(full_url).netloc)
            and urlparse(full_url).netloc.lower() != current_host.lower()
        )
        score = (
            (100 if is_direct_media_url(full_url) else 0)
            + (
                40
                if STREAM_HINT_RE.search(full_url) or STREAM_HINT_RE.search(text)
                else 0
            )
            + (30 if "download" in full_url.lower() or "download" in text.lower() else 0)
            + (20 if is_ext else 0)
        )
        if score > 0:
            seen.add(full_url)
            candidates.append(
                {
                    "title": sanitize_display_title(text, "Next"),
                    "url": full_url,
                    "tag": el.name,
                    "score": score,
                }
            )
    candidates.sort(key=lambda x: x["score"], reverse=True)
    return candidates


def resolve_redirect_or_media(url, referer=None, max_hops=4):
    curr, ref, hops = url, referer, []
    for _ in range(max_hops):
        extra = (
            {"Range": "bytes=0-1"}
            if (STREAM_HINT_RE.search(curr) or MEDIA_EXT_RE.search(curr))
            else {}
        )
        r = req_get(
            curr, referer=ref, headers=extra, allow_redirects=False, timeout=8
        )
        ct = r.headers.get("Content-Type", "")
        loc = r.headers.get("Location", "")
        hops.append(
            {
                "url": curr,
                "status": r.status_code,
                "content_type": ct,
                "location": loc,
            }
        )
        if loc:
            nxt = urljoin(curr, loc)
            if is_direct_media_url(nxt, ct):
                return {"media_url": nxt, "html": None, "hops": hops}
            ref, curr = curr, nxt
            continue
        if is_direct_media_url(curr, ct):
            return {"media_url": curr, "html": None, "hops": hops}
        if "html" in ct.lower() or not ct:
            return {"media_url": None, "html": r.text, "hops": hops}
        break
    return {"media_url": None, "html": None, "hops": hops}


def resolve_single_quality_stream(dl_page_url, referer=None, movie_title=""):
    media_url = None
    has_watch_candidate = False
    seen_cands = []
    curr_url, curr_ref = dl_page_url, referer
    page_heading = sanitize_display_title(movie_title, "")

    for _ in range(4):
        res = resolve_redirect_or_media(curr_url, referer=curr_ref)
        if res["media_url"]:
            media_url = res["media_url"]
            break
        html = res["html"] or fetch_html(curr_url, referer=curr_ref)
        soup = BeautifulSoup(html, "html.parser")
        if not page_heading:
            h = soup.select_one("h1, h2, title")
            if h:
                page_heading = sanitize_display_title(
                    re.sub(r"\s+", " ", h.get_text(" ", strip=True)).strip(),
                    "",
                )

        for el in soup.select("video[src], video source[src], iframe[src], a[href]"):
            raw = (el.get("src") or el.get("href") or "").strip()
            if not raw:
                continue
            full = urljoin(curr_url, raw)
            if is_direct_media_url(full):
                media_url = full
                break
            if re.search(r"(stream|play|watch|embed)", full, re.I):
                has_watch_candidate = True

        if media_url:
            break
        nxt = next(
            (
                c["url"]
                for c in find_next_hop_links(
                    html, curr_url, urlparse(curr_url).netloc
                )
                if c["url"] not in seen_cands
            ),
            None,
        )
        if not nxt:
            break
        seen_cands.append(nxt)
        curr_ref, curr_url = curr_url, nxt

    safe_name = (
        re.sub(
            r"[^a-zA-Z0-9._-]",
            "_",
            clean_movie_query(page_heading) or "movie",
        )
        + ".mp4"
    )
    stream_proxy_url = None
    download_proxy_url = None
    if media_url:
        tok = register_media_token(media_url, referer=curr_ref, filename=safe_name)
        stream_proxy_url = f"/api/stream-proxy/{tok}"
        download_proxy_url = f"/api/download-proxy/{tok}"

    return {
        "media_url": media_url,
        "has_stream": bool(media_url or has_watch_candidate),
        "stream_url": stream_proxy_url,
        "download_url": download_proxy_url,
        "page_heading": sanitize_display_title(page_heading, "Movie"),
    }


def _normalize_search_text(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", (text or "").lower()).strip()


def _score_search_entry(entry: dict, query: str) -> int:
    q_norm = _normalize_search_text(query)
    if not q_norm:
        return 0
    title_raw = (entry.get("title") or "").lower()
    url_raw = unquote(entry.get("url") or "").lower()
    t_norm = _normalize_search_text(f"{title_raw} {url_raw}")

    if query in title_raw or q_norm in t_norm:
        return 100

    tokens = [tok for tok in q_norm.split() if len(tok) > 1]
    if not tokens:
        tokens = q_norm.split()
    if not tokens:
        return 0

    matched = sum(1 for tok in tokens if tok in t_norm)
    if matched == len(tokens):
        return 75
    if matched > 0:
        return 35 + int((matched / len(tokens)) * 25)
    return 0


def _build_letter_priority_urls(query: str) -> list[str]:
    clean_q = _normalize_search_text(query)
    if not clean_q:
        return []
    first_char = clean_q[0]
    if not first_char.isalpha():
        return []

    priority = []

    dub_base = _ACTIVE_DUBBED_URL.rstrip("/")
    priority.append(f"{dub_base}/tamil-atoz-dubbed-movies/{first_char}/")
    for p in range(2, 16):
        priority.append(f"{dub_base}/tamil-atoz-dubbed-movies/{first_char}/{p}")

    pri_parsed = urlparse(_HOME_PRIMARY_URL)
    pri_root = f"{pri_parsed.scheme}://{pri_parsed.netloc}"
    priority.append(f"{pri_root}/tamil-movies/{first_char}/")
    for p in range(2, 16):
        priority.append(f"{pri_root}/tamil-movies/{first_char}/?page={p}")
        priority.append(f"{pri_root}/tamil-movies/{first_char}/page/{p}/")
        priority.append(f"{pri_root}/tamil-movies/{first_char}/{p}/")

    for yr in ("2026", "2025", "2024", "2023"):
        priority.append(f"{pri_root}/tamil-{yr}-movies/")
        for p in range(2, 6):
            priority.append(f"{pri_root}/tamil-{yr}-movies/?page={p}")

    return priority


def _expand_numeric_pagination(pages: list[dict]) -> list[str]:
    urls = [p["url"] for p in pages]
    max_num = 1
    template_prefix = None
    template_suffix = ""

    for u in urls:
        m = re.search(r"^(.*?/(?:page/)?)(\d+)(/?)$", u)
        if m:
            num = int(m.group(2))
            if 1 <= num <= 30 and num > max_num:
                max_num = num
                template_prefix = m.group(1)
                template_suffix = m.group(3)
            continue

        mq = re.search(r"^(.*[?&](?:page|p|pg)=)(\d+)(.*)$", u)
        if mq:
            num = int(mq.group(2))
            if 1 <= num <= 30 and num > max_num:
                max_num = num
                template_prefix = mq.group(1)
                template_suffix = mq.group(3)

    if template_prefix and max_num > 1:
        for n in range(1, max_num + 1):
            gen = f"{template_prefix}{n}{template_suffix}"
            if gen not in urls:
                urls.append(gen)
    return urls


def _crawl_single_page(page_url: str, page_ref: str | None) -> tuple[list[dict], list[str]]:
    try:
        html = fetch_html(page_url, referer=page_ref, timeout=7)
    except Exception:
        return [], []

    all_f = extract_div_f_links(html, page_url)
    pages = extract_pagination_links(html, page_url)
    page_urls = {p["url"] for p in pages}

    entries = []
    next_urls = []
    for item in all_f:
        if not item["is_pagination"] and item["url"] not in page_urls:
            entries.append(
                {
                    "title": item["title"],
                    "url": item["url"],
                    "page_url": page_url,
                }
            )
            next_urls.append(item["url"])

    for pg in pages:
        next_urls.append(pg["url"])

    return entries, next_urls


def crawl_category_pages(
    start_url: str,
    referer: str | None = None,
    max_pages: int = 120,
    include_categories: bool = True,
    priority_urls: list[str] | None = None,
) -> list[dict]:
    resolved_start = resolve_browse_target(start_url)
    prio_tag = ",".join((priority_urls or [])[:3])
    cache_key = f"{resolved_start}|cat={include_categories}|max={max_pages}|p={prio_tag}"
    now = time.monotonic()
    cached = _PAGE_ENTRIES_CACHE.get(cache_key)
    if cached and (now - cached[0]) < CACHE_TTL_SEC:
        return cached[1]

    visited_pages: set[str] = set()
    queue: deque[tuple[str, str | None]] = deque()
    queue.append((resolved_start, referer))
    for pu in (priority_urls or []):
        queue.append((pu, resolved_start))

    all_entries: list[dict] = []
    seen_entry_urls: set[str] = set()

    with ThreadPoolExecutor(max_workers=10) as pool:
        while queue and len(visited_pages) < max_pages:
            batch = []
            while (
                queue
                and len(visited_pages) + len(batch) < max_pages
                and len(batch) < 10
            ):
                u, r = queue.popleft()
                if u not in visited_pages:
                    visited_pages.add(u)
                    batch.append((u, r))
            if not batch:
                break

            futures = [pool.submit(_crawl_single_page, u, r) for u, r in batch]
            for fut in as_completed(futures):
                entries, next_urls = fut.result()
                for ent in entries:
                    if ent["url"] not in seen_entry_urls:
                        seen_entry_urls.add(ent["url"])
                        all_entries.append(ent)
                if include_categories:
                    expanded = _expand_numeric_pagination(
                        [{"url": u} for u in next_urls]
                    )
                    for nu in expanded:
                        if nu not in visited_pages:
                            queue.append((nu, resolved_start))

    _PAGE_ENTRIES_CACHE[cache_key] = (now, all_entries)
    return all_entries


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/categories")
def api_categories():
    try:
        update_active_sources(
            request.args.get("seed_url"),
            request.args.get("dubbed_url"),
        )
        mode = (request.args.get("mode") or "").strip().lower()
        if mode == "primary":
            switch_primary_source("primary")
        elif mode == "dubbed":
            switch_primary_source("dubbed")

        active_url = _ACTIVE_PRIMARY_URL
        html = fetch_html(active_url, timeout=9)
        cats = [
            c for c in extract_div_f_links(html, active_url) if not c["is_pagination"]
        ]
        if _SESSION_MODE == "primary":
            cats.append(
                {
                    "title": "Tamil Dubbed Movies",
                    "url": DUBBED_SECTION_KEY,
                    "is_pagination": False,
                }
            )
        return jsonify(
            {
                "ok": True,
                "mode": _SESSION_MODE,
                "can_go_back": _SESSION_MODE == "dubbed",
                "items": cats,
            }
        )
    except PermissionError as e:
        return jsonify({"ok": False, "error": str(e)}), 403
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/switch-mode")
def api_switch_mode():
    mode = (request.args.get("mode") or "primary").strip().lower()
    active_url = switch_primary_source("dubbed" if mode == "dubbed" else "primary")
    return jsonify(
        {
            "ok": True,
            "mode": _SESSION_MODE,
            "can_go_back": _SESSION_MODE == "dubbed",
            "active_url_set": bool(active_url),
        }
    )


@app.route("/api/browse")
def api_browse():
    raw_url = request.args.get("url", "").strip()
    referer = request.args.get("referer", "").strip() or None
    if not raw_url:
        return jsonify({"ok": False, "error": "Missing url parameter"}), 400
    target_url = resolve_browse_target(raw_url)
    try:
        html = fetch_html(target_url, referer=referer, timeout=9)
        downloads = extract_download_items(html, target_url)
        all_f = extract_div_f_links(html, target_url)
        pages = extract_pagination_links(html, target_url)
        page_urls = {p["url"] for p in pages}
        entries = [
            x
            for x in all_f
            if not x["is_pagination"] and x["url"] not in page_urls
        ]
        return jsonify(
            {
                "ok": True,
                "mode": _SESSION_MODE,
                "can_go_back": _SESSION_MODE == "dubbed",
                "downloads": downloads,
                "entries": entries,
                "pages": pages,
            }
        )
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/search-debug")
def api_search_debug():
    q = request.args.get("q", "").strip().lower()
    refresh = request.args.get("refresh", "0").strip() in ("1", "true", "yes")
    if refresh:
        _HTML_CACHE.clear()
        _PAGE_ENTRIES_CACHE.clear()
        _POSTER_CACHE.clear()

    prio_urls = _build_letter_priority_urls(q) if q else []
    dub_prio = [u for u in prio_urls if urlparse(_ACTIVE_DUBBED_URL).netloc in u]
    pri_prio = [u for u in prio_urls if urlparse(_HOME_PRIMARY_URL).netloc in u]

    report = {}
    for label, target, p_list in [
        ("primary", _HOME_PRIMARY_URL, pri_prio),
        ("dubbed", _ACTIVE_DUBBED_URL, dub_prio),
    ]:
        try:
            html = fetch_html(target, timeout=9)
            top_links = extract_div_f_links(html, target)
            entries = crawl_category_pages(
                target,
                referer=None,
                max_pages=130,
                include_categories=True,
                priority_urls=p_list,
            )
            hits = [
                e for e in entries if (_score_search_entry(e, q) > 0 if q else False)
            ]
            report[label] = {
                "target_ok": True,
                "top_links_count": len(top_links),
                "top_sample": [x["title"] for x in top_links[:8]],
                "crawled_entries_count": len(entries),
                "matches": hits[:15],
            }
        except Exception as e:
            report[label] = {
                "target_ok": False,
                "error": str(e),
            }

    return jsonify({"ok": True, "query": q, "report": report})


@app.route("/api/search")
def api_search():
    q = request.args.get("q", "").strip().lower()
    scope = (request.args.get("scope") or "all").strip().lower()
    referer = request.args.get("referer", "").strip() or None
    refresh = request.args.get("refresh", "0").strip() in ("1", "true", "yes")

    if not q:
        return jsonify({"ok": False, "error": "Missing search query q"}), 400

    if refresh:
        _HTML_CACHE.clear()
        _PAGE_ENTRIES_CACHE.clear()
        _POSTER_CACHE.clear()

    try:
        update_active_sources(
            request.args.get("seed_url"),
            request.args.get("dubbed_url"),
        )
        url = (request.args.get("url") or _ACTIVE_PRIMARY_URL).strip()
        prio_urls = _build_letter_priority_urls(q)

        if scope == "category":
            entries = crawl_category_pages(
                url,
                referer=referer,
                max_pages=90,
                include_categories=True,
                priority_urls=prio_urls,
            )
        else:
            dub_prio = [
                u for u in prio_urls if urlparse(_ACTIVE_DUBBED_URL).netloc in u
            ]
            pri_prio = [
                u for u in prio_urls if urlparse(_HOME_PRIMARY_URL).netloc in u
            ]
            with ThreadPoolExecutor(max_workers=2) as pool:
                f_primary = pool.submit(
                    crawl_category_pages,
                    _HOME_PRIMARY_URL,
                    None,
                    130,
                    True,
                    pri_prio,
                )
                f_dubbed = pool.submit(
                    crawl_category_pages,
                    _ACTIVE_DUBBED_URL,
                    None,
                    130,
                    True,
                    dub_prio,
                )
                primary_entries = f_primary.result()
                dubbed_entries = f_dubbed.result()

            seen_urls = {e["url"] for e in primary_entries}
            entries = list(primary_entries)
            for item in dubbed_entries:
                if item["url"] not in seen_urls:
                    seen_urls.add(item["url"])
                    entries.append(item)

        scored = []
        for e in entries:
            sc = _score_search_entry(e, q)
            if sc > 0:
                scored.append((sc, e))
        scored.sort(key=lambda pair: pair[0], reverse=True)
        matches = [e for _, e in scored]

        return jsonify(
            {
                "ok": True,
                "query": q,
                "scope": scope,
                "total_scanned_entries": len(entries),
                "count": len(matches),
                "results": matches,
            }
        )
    except PermissionError as e:
        return jsonify({"ok": False, "error": str(e)}), 403
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/poster-proxy")
def api_poster_proxy():
    title = request.args.get("title", "").strip()
    page_url = request.args.get("url", "").strip() or None
    referer = request.args.get("referer", "").strip() or None

    remote_img, img_ref = extract_page_poster_url(page_url, referer=referer)
    if remote_img:
        try:
            r = req_get(remote_img, referer=img_ref or page_url, timeout=6)
            ct = (r.headers.get("Content-Type") or "").lower()
            if r.ok and ct.startswith("image/"):
                return Response(r.content, status=200, mimetype=ct)
        except Exception:
            pass
    return fallback_poster_svg(title)


@app.route("/api/resolve")
def api_resolve():
    dl_page_url = request.args.get("url", "").strip()
    referer = request.args.get("referer", "").strip() or None
    movie_title = sanitize_display_title(request.args.get("title", "").strip(), "")
    if not dl_page_url:
        return jsonify({"ok": False, "error": "Missing url parameter"}), 400
    try:
        resolved_ref = resolve_browse_target(referer) if referer else None
        qualities = []
        if resolved_ref:
            try:
                ref_html = fetch_html(resolved_ref, timeout=8)
                dl_items = extract_download_items(ref_html, resolved_ref)
                for item in dl_items:
                    qualities.append(
                        {
                            "quality": item.get("quality") or "Standard",
                            "label": sanitize_display_title(
                                item.get("title") or "Stream", "Stream"
                            ),
                            "url": item.get("url"),
                        }
                    )
            except Exception:
                pass

        if not any(q.get("url") == dl_page_url for q in qualities):
            qualities.insert(
                0,
                {
                    "quality": detect_quality_tag(f"{movie_title} {dl_page_url}"),
                    "label": movie_title or "Selected Quality",
                    "url": dl_page_url,
                },
            )

        primary = resolve_single_quality_stream(
            dl_page_url,
            referer=resolved_ref,
            movie_title=movie_title,
        )
        clean_heading = sanitize_display_title(
            primary["page_heading"] or movie_title, "Movie"
        )
        poster_proxy = build_poster_proxy_url(
            clean_heading,
            page_url=resolved_ref or dl_page_url,
            referer=dl_page_url,
        )

        if not primary["has_stream"]:
            return (
                jsonify(
                    {
                        "ok": False,
                        "error": "Could not resolve media stream",
                        "shot_url": poster_proxy,
                    }
                ),
                404,
            )

        return jsonify(
            {
                "ok": True,
                "shot_url": poster_proxy,
                "stream_url": primary["stream_url"],
                "download_url": primary["download_url"],
                "has_stream": primary["has_stream"],
                "qualities": qualities,
            }
        )
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/resolve-quality")
def api_resolve_quality():
    dl_page_url = request.args.get("url", "").strip()
    referer = request.args.get("referer", "").strip() or None
    movie_title = sanitize_display_title(request.args.get("title", "").strip(), "")
    if not dl_page_url:
        return jsonify({"ok": False, "error": "Missing url parameter"}), 400
    try:
        res = resolve_single_quality_stream(
            dl_page_url,
            referer=resolve_browse_target(referer) if referer else None,
            movie_title=movie_title,
        )
        if not res["has_stream"]:
            return jsonify({"ok": False, "error": "Quality stream unavailable"}), 404
        return jsonify(
            {
                "ok": True,
                "stream_url": res["stream_url"],
                "download_url": res["download_url"],
            }
        )
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/stream-proxy/<token>")
def api_stream_proxy(token):
    meta = _MEDIA_TOKENS.get(token)
    if not meta:
        return "Stream link expired or invalid", 404

    headers = {}
    if request.headers.get("Range"):
        headers["Range"] = request.headers.get("Range")

    upstream = req_get(
        meta["url"],
        referer=meta.get("referer"),
        headers=headers,
        timeout=25,
        stream=True,
    )
    ct = upstream.headers.get("Content-Type") or "video/mp4"
    resp_headers = {
        "Cache-Control": "public, max-age=3600",
    }
    for hdr in ("Content-Range", "Accept-Ranges", "Content-Length"):
        if upstream.headers.get(hdr):
            resp_headers[hdr] = upstream.headers.get(hdr)

    def generate():
        try:
            for chunk in upstream.iter_content(chunk_size=262144):
                if chunk:
                    yield chunk
        finally:
            upstream.close()

    return Response(
        stream_with_context(generate()),
        status=upstream.status_code,
        mimetype=ct,
        headers=resp_headers,
    )


@app.route("/api/download-proxy/<token>")
def api_download_proxy(token):
    meta = _MEDIA_TOKENS.get(token)
    if not meta:
        return "Download link expired or invalid", 404

    upstream = req_get(
        meta["url"],
        referer=meta.get("referer"),
        timeout=25,
        stream=True,
    )
    ct = upstream.headers.get("Content-Type") or "application/octet-stream"
    fname = meta.get("filename") or "movie.mp4"
    resp_headers = {
        "Content-Disposition": f'attachment; filename="{fname}"',
    }
    if upstream.headers.get("Content-Length"):
        resp_headers["Content-Length"] = upstream.headers.get("Content-Length")

    def generate():
        try:
            for chunk in upstream.iter_content(chunk_size=262144):
                if chunk:
                    yield chunk
        finally:
            upstream.close()

    return Response(
        stream_with_context(generate()),
        status=200,
        mimetype=ct,
        headers=resp_headers,
    )


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=False, threaded=True)
