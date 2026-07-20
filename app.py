from __future__ import annotations

import base64
import collections
import html
import mimetypes
import os
import re
import secrets
import shutil
import subprocess
import tempfile
import threading
import time
import zipfile
from pathlib import Path
from typing import Any
from urllib.parse import urlparse

import yt_dlp
from flask import Flask, Response, jsonify, render_template, request, send_file
from itsdangerous import BadSignature, SignatureExpired, URLSafeTimedSerializer
from werkzeug.exceptions import HTTPException


app = Flask(__name__, template_folder=".")
app.config["MAX_CONTENT_LENGTH"] = 16 * 1024
app.config["JSON_AS_ASCII"] = False
app.secret_key = os.environ.get("SECRET_KEY") or secrets.token_hex(32)

TOKEN_MAX_AGE = int(os.environ.get("TOKEN_MAX_AGE", "1800"))
MAX_FILE_MB = max(25, min(int(os.environ.get("MAX_FILE_MB", "250")), 1000))
MAX_FILE_BYTES = MAX_FILE_MB * 1024 * 1024
MAX_MEDIA_FILES = max(1, min(int(os.environ.get("MAX_MEDIA_FILES", "20")), 50))
APP_PIN = os.environ.get("APP_PIN", "").strip()
USER_AGENT = (
    "Mozilla/5.0 (Linux; Android 14; Mobile) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36"
)

serializer = URLSafeTimedSerializer(app.secret_key, salt="social-media-download-v1")

_COOKIE_FILE: str | None = None
_RATE_BUCKETS: dict[str, collections.deque[float]] = collections.defaultdict(collections.deque)
_RATE_LOCK = threading.Lock()


class CaptureLogger:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def debug(self, message: str) -> None:
        return None

    def warning(self, message: str) -> None:
        self.warnings.append(str(message))

    def error(self, message: str) -> None:
        self.errors.append(str(message))


def prepare_cookie_file() -> str | None:
    """Create a temporary Netscape cookie file from an optional environment variable."""
    global _COOKIE_FILE
    if _COOKIE_FILE:
        return _COOKIE_FILE

    explicit_path = os.environ.get("COOKIES_FILE", "").strip()
    if explicit_path and Path(explicit_path).is_file():
        _COOKIE_FILE = explicit_path
        return _COOKIE_FILE

    encoded = os.environ.get("COOKIES_BASE64", "").strip()
    if not encoded:
        return None

    try:
        raw = base64.b64decode(encoded, validate=True)
        if not raw or len(raw) > 2 * 1024 * 1024:
            return None
        path = Path("/tmp/social_downloader_cookies.txt")
        path.write_bytes(raw)
        path.chmod(0o600)
        _COOKIE_FILE = str(path)
    except Exception:
        _COOKIE_FILE = None
    return _COOKIE_FILE


def client_ip() -> str:
    forwarded = request.headers.get("X-Forwarded-For", "")
    if forwarded:
        return forwarded.split(",", 1)[0].strip()
    return request.remote_addr or "unknown"


def rate_limited(action: str, limit: int, window_seconds: int = 600) -> bool:
    now = time.time()
    key = f"{action}:{client_ip()}"
    with _RATE_LOCK:
        bucket = _RATE_BUCKETS[key]
        while bucket and bucket[0] <= now - window_seconds:
            bucket.popleft()
        if len(bucket) >= limit:
            return True
        bucket.append(now)
        return False


def host_matches(host: str, domain: str) -> bool:
    return host == domain or host.endswith("." + domain)


def validate_social_url(raw_url: str) -> tuple[str, str]:
    url = (raw_url or "").strip()
    if not url or len(url) > 2048:
        raise ValueError("الرابط غير صحيح أو طويل جدًا.")

    try:
        parsed = urlparse(url)
    except Exception as exc:
        raise ValueError("تعذر قراءة الرابط.") from exc

    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        raise ValueError("استخدم رابطًا كاملًا يبدأ بـ https://")
    if parsed.username or parsed.password:
        raise ValueError("الرابط غير مسموح.")

    host = parsed.hostname.lower().strip(".")
    path = parsed.path or "/"

    if any(host_matches(host, d) for d in ("tiktok.com", "vm.tiktok.com", "vt.tiktok.com")):
        valid_path = (
            host in {"vm.tiktok.com", "vt.tiktok.com"}
            or re.search(r"/@[^/]+/(video|photo)/\d+", path, re.I)
            or re.match(r"^/t/[A-Za-z0-9_-]+", path, re.I)
        )
        if not valid_path:
            raise ValueError("استخدم رابط فيديو أو صورة محددة من TikTok، وليس رابط الحساب.")
        return url, "tiktok"

    if host_matches(host, "x.com") or host_matches(host, "twitter.com"):
        if not re.match(r"^/[^/]+/status/\d+", path, re.I):
            raise ValueError("استخدم رابط منشور محدد من X بالشكل x.com/user/status/...")
        return url, "x"

    if host_matches(host, "reddit.com"):
        if "/comments/" not in path.lower():
            raise ValueError("استخدم رابط منشور محدد من Reddit فيه /comments/.")
        return url, "reddit"

    if host_matches(host, "pinterest.com") or host_matches(host, "pin.it"):
        if host_matches(host, "pin.it"):
            if len(path.strip("/")) == 0:
                raise ValueError("رابط Pinterest غير صحيح.")
            return url, "pinterest"
        if not re.match(r"^/pin/[A-Za-z0-9_-]+", path, re.I):
            raise ValueError("استخدم رابط Pin محدد من Pinterest.")
        return url, "pinterest"

    if host_matches(host, "dailymotion.com") or host_matches(host, "dai.ly"):
        if host_matches(host, "dai.ly"):
            if len(path.strip("/")) == 0:
                raise ValueError("رابط Dailymotion غير صحيح.")
            return url, "dailymotion"
        if not re.match(r"^/video/[A-Za-z0-9]+", path, re.I):
            raise ValueError("استخدم رابط فيديو محدد من Dailymotion.")
        return url, "dailymotion"

    if host_matches(host, "vimeo.com"):
        if not re.match(r"^/\d+", path):
            raise ValueError("استخدم رابط فيديو محدد من Vimeo.")
        return url, "vimeo"

    if host_matches(host, "rumble.com"):
        if not re.match(r"^/v[A-Za-z0-9]+", path, re.I):
            raise ValueError("استخدم رابط فيديو محدد من Rumble.")
        return url, "rumble"

    if host_matches(host, "soundcloud.com"):
        segments = [s for s in path.split("/") if s]
        is_short_link = host_matches(host, "on.soundcloud.com") or host == "on.soundcloud.com"
        min_segments = 1 if is_short_link else 2
        if len(segments) < min_segments:
            raise ValueError("استخدم رابط مقطع صوتي محدد من SoundCloud.")
        return url, "soundcloud"

    if host_matches(host, "twitch.tv"):
        if not (host_matches(host, "clips.twitch.tv") or "/clip/" in path.lower()):
            raise ValueError("الأداة تدعم مقاطع (Clips) تويتش فقط، مش البث المباشر.")
        return url, "twitch"

    if host_matches(host, "imgur.com"):
        if len(path.strip("/")) == 0:
            raise ValueError("استخدم رابط صورة أو ألبوم محدد من Imgur.")
        return url, "imgur"

    if host_matches(host, "9gag.com"):
        if not re.match(r"^/gag/[A-Za-z0-9]+", path, re.I):
            raise ValueError("استخدم رابط منشور محدد من 9GAG.")
        return url, "ninegag"

    if host_matches(host, "snapchat.com"):
        is_spotlight = "/spotlight/" in path.lower()
        is_short_link = re.match(r"^/t/[A-Za-z0-9_-]+", path, re.I)
        if not (is_spotlight or is_short_link):
            raise ValueError("الأداة تدعم Spotlight العام فقط من Snapchat (رابط عادي أو مختصر).")
        return url, "snapchat"

    if host_matches(host, "bsky.app"):
        if not re.match(r"^/profile/[^/]+/post/[A-Za-z0-9]+", path, re.I):
            raise ValueError("استخدم رابط منشور محدد من Bluesky.")
        return url, "bluesky"

    raise ValueError(
        "الأداة تدعم TikTok وX وReddit وPinterest وDailymotion وVimeo وRumble "
        "وSoundCloud وTwitch (Clips) وImgur و9GAG وSnapchat (Spotlight) وBluesky."
    )



def pin_is_valid() -> bool:
    if not APP_PIN:
        return True
    supplied = request.headers.get("X-App-Pin", "").strip()
    return secrets.compare_digest(supplied, APP_PIN)


def ydl_common_options(logger: CaptureLogger | None = None) -> dict[str, Any]:
    options: dict[str, Any] = {
        "quiet": True,
        "no_warnings": True,
        "noplaylist": False,
        "playlistend": MAX_MEDIA_FILES,
        "socket_timeout": 15,
        "retries": 1,
        "fragment_retries": 1,
        "extractor_retries": 1,
        "cachedir": False,
        "http_headers": {
            "User-Agent": USER_AGENT,
            "Accept-Language": "ar,en-US;q=0.9,en;q=0.8",
        },
    }
    if logger:
        options["logger"] = logger
    cookie_file = prepare_cookie_file()
    if cookie_file:
        options["cookiefile"] = cookie_file
    return options


def limited_entries(info: dict[str, Any]) -> list[dict[str, Any]]:
    raw_entries = info.get("entries")
    if raw_entries:
        entries: list[dict[str, Any]] = []
        for item in raw_entries:
            if item:
                entries.append(item)
            if len(entries) >= MAX_MEDIA_FILES:
                break
        return entries
    return [info]


def first_nonempty(entries: list[dict[str, Any]], *keys: str) -> Any:
    for entry in entries:
        for key in keys:
            value = entry.get(key)
            if value not in (None, "", [], {}):
                return value
    return None


def inspect_with_ytdlp(url: str) -> dict[str, Any]:
    logger = CaptureLogger()
    options = ydl_common_options(logger)
    options["skip_download"] = True

    with yt_dlp.YoutubeDL(options) as ydl:
        raw_info = ydl.extract_info(url, download=False)
        if not raw_info:
            raise RuntimeError("لم يتم العثور على محتوى قابل للتنزيل.")
        info = ydl.sanitize_info(raw_info)

    entries = limited_entries(info)
    title = info.get("title") or first_nonempty(entries, "title", "description") or "محتوى جاهز للتنزيل"
    author = (
        info.get("uploader")
        or info.get("channel")
        or first_nonempty(entries, "uploader", "channel", "creator")
        or ""
    )
    thumbnail = info.get("thumbnail") or first_nonempty(entries, "thumbnail") or ""

    has_video = False
    has_audio = False
    for entry in entries:
        formats = entry.get("formats") or []
        vcodec = entry.get("vcodec")
        acodec = entry.get("acodec")
        if vcodec and vcodec != "none":
            has_video = True
        if acodec and acodec != "none":
            has_audio = True
        for fmt in formats:
            if fmt.get("vcodec") not in (None, "none"):
                has_video = True
            if fmt.get("acodec") not in (None, "none"):
                has_audio = True

    duration = info.get("duration") or first_nonempty(entries, "duration")
    return {
        "method": "ytdlp",
        "title": str(title)[:220],
        "author": str(author)[:120],
        "thumbnail": thumbnail,
        "count": len(entries),
        "has_video": has_video or True,
        "has_audio": has_audio or has_video,
        "duration": duration,
    }


def gallery_command_base() -> list[str]:
    command = [
        "gallery-dl",
        "--config-ignore",
        "--no-input",
        "--http-timeout",
        "20",
        "--retries",
        "1",
    ]
    cookie_file = prepare_cookie_file()
    if cookie_file:
        command.extend(["--cookies", cookie_file])
    return command


def inspect_with_gallery_dl(url: str) -> dict[str, Any]:
    command = gallery_command_base() + ["--get-urls", url]
    completed = subprocess.run(
        command,
        capture_output=True,
        text=True,
        timeout=45,
        check=False,
    )
    urls = [
        line.strip()
        for line in completed.stdout.splitlines()
        if line.strip().startswith(("https://", "http://"))
    ][:MAX_MEDIA_FILES]
    if completed.returncode != 0 or not urls:
        raise RuntimeError("تعذر استخراج الوسائط من المنشور العام.")

    image_extensions = {".jpg", ".jpeg", ".png", ".webp", ".gif"}
    video_extensions = {".mp4", ".mov", ".webm", ".m3u8"}
    extensions = {Path(urlparse(item).path).suffix.lower() for item in urls}
    has_video = bool(extensions & video_extensions) or not bool(extensions & image_extensions)

    return {
        "method": "gallery",
        "title": "محتوى جاهز للتنزيل",
        "author": "",
        "thumbnail": next((u for u in urls if Path(urlparse(u).path).suffix.lower() in image_extensions), ""),
        "count": len(urls),
        "has_video": has_video,
        "has_audio": False,
        "duration": None,
    }


GALLERY_FIRST_PLATFORMS = {"reddit", "pinterest", "imgur", "ninegag"}


def inspect_media(url: str, platform: str) -> dict[str, Any]:
    # Image/gallery-style platforms are usually faster through gallery-dl;
    # video/audio platforms are usually better through yt-dlp.
    methods = (
        (inspect_with_gallery_dl, inspect_with_ytdlp)
        if platform in GALLERY_FIRST_PLATFORMS
        else (inspect_with_ytdlp, inspect_with_gallery_dl)
    )
    errors: list[str] = []
    for method in methods:
        try:
            return method(url)
        except Exception as exc:
            errors.append(str(exc))

    message = " | ".join(errors).lower()
    if any(word in message for word in ("login", "cookie", "private", "checkpoint")):
        raise RuntimeError("المنشور عام لكن المنصة طلبت تسجيل دخول. سنحتاج إضافة Cookies للحساب لاحقًا.")
    raise RuntimeError("تعذر جلب المنشور الآن. تأكد أن الرابط عام وصحيح ثم جرّب مرة أخرى.")


def safe_files(directory: str) -> list[Path]:
    excluded_suffixes = {".part", ".ytdl", ".json", ".description"}
    files = []
    for path in Path(directory).rglob("*"):
        if not path.is_file():
            continue
        if path.suffix.lower() in excluded_suffixes:
            continue
        if path.name.startswith("."):
            continue
        files.append(path)
    return sorted(files)[:MAX_MEDIA_FILES]


def download_with_ytdlp(url: str, mode: str, directory: str) -> list[Path]:
    logger = CaptureLogger()
    options = ydl_common_options(logger)
    options.update(
        {
            "outtmpl": str(Path(directory) / "%(title).80s [%(id)s].%(ext)s"),
            "paths": {"home": directory, "temp": directory},
            "windowsfilenames": True,
            "overwrites": True,
            "continuedl": False,
            "nopart": True,
            "max_filesize": MAX_FILE_BYTES,
            "concurrent_fragment_downloads": 3,
        }
    )

    if mode == "audio":
        options.update(
            {
                "format": "bestaudio/best",
                "postprocessors": [
                    {
                        "key": "FFmpegExtractAudio",
                        "preferredcodec": "mp3",
                        "preferredquality": "192",
                    }
                ],
            }
        )
    else:
        options.update(
            {
                "format": "bv*[ext=mp4]+ba[ext=m4a]/b[ext=mp4]/bv*+ba/b",
                "merge_output_format": "mp4",
            }
        )

    with yt_dlp.YoutubeDL(options) as ydl:
        code = ydl.download([url])
        if code:
            raise RuntimeError("فشل تنزيل الملف.")

    files = safe_files(directory)
    if not files:
        raise RuntimeError("لم يتم إنشاء ملف قابل للتنزيل.")
    return files


def download_with_gallery_dl(url: str, directory: str) -> list[Path]:
    command = gallery_command_base() + [
        "--directory",
        directory,
        "--filesize-max",
        f"{MAX_FILE_MB}M",
        url,
    ]
    completed = subprocess.run(
        command,
        capture_output=True,
        text=True,
        timeout=240,
        check=False,
    )
    files = safe_files(directory)
    if completed.returncode != 0 or not files:
        raise RuntimeError("تعذر تنزيل الوسائط من المنشور.")
    return files


def ensure_size_limit(files: list[Path]) -> None:
    total = sum(path.stat().st_size for path in files)
    if total <= 0:
        raise RuntimeError("الملف الناتج فارغ.")
    if total > MAX_FILE_BYTES:
        raise RuntimeError(f"حجم المحتوى أكبر من الحد المسموح ({MAX_FILE_MB} MB).")


def build_download_file(files: list[Path], directory: str, platform: str) -> Path:
    if len(files) == 1:
        return files[0]

    archive = Path(directory) / f"{platform}-media.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_STORED) as output:
        used_names: set[str] = set()
        for index, file_path in enumerate(files, start=1):
            name = file_path.name
            if name in used_names:
                name = f"{index}-{name}"
            used_names.add(name)
            output.write(file_path, arcname=name)
    return archive


def clean_download_name(path: Path, platform: str, mode: str) -> str:
    suffix = path.suffix.lower() or (".mp3" if mode == "audio" else ".mp4")
    if path.suffix.lower() == ".zip":
        return f"{platform}-media.zip"
    return f"{platform}-{int(time.time())}{suffix}"


def friendly_download_error(message: str, status: int = 400) -> Response:
    safe_message = html.escape(message)
    markup = f"""<!doctype html><html lang='ar' dir='rtl'><meta charset='utf-8'> <meta name='viewport' content='width=device-width,initial-scale=1'> <title>تعذر التنزيل</title><style> body{{font-family:Arial,sans-serif;background:#f6f5f2;margin:0;padding:30px;color:#16181c}} main{{max-width:560px;margin:60px auto;background:white;padding:28px;border-radius:18px;border:1px solid #e4e2dd}} h1{{font-size:23px}}p{{line-height:1.8;color:#5b5f66}}a{{display:block;text-align:center;padding:13px;background:#ff2450;color:white;text-decoration:none;border-radius:12px;font-weight:bold}} </style><main><h1>تعذر إكمال التنزيل</h1><p>{safe_message}</p><a href='/'>العودة إلى الأداة</a></main></html>"""
    return Response(markup, status=status, mimetype="text/html")


@app.after_request
def security_headers(response: Response) -> Response:
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "SAMEORIGIN")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy", "camera=(), microphone=(), geolocation=()")
    response.headers.setdefault("Cache-Control", "no-store")
    return response


@app.get("/")
def home() -> str:
    return render_template("index.html", max_file_mb=MAX_FILE_MB)


@app.get("/health")
def health() -> Response:
    return jsonify({"ok": True})


@app.get("/api/config")
def config() -> Response:
    return jsonify(
        {
            "pin_required": bool(APP_PIN),
            "max_file_mb": MAX_FILE_MB,
            "cookies_enabled": bool(prepare_cookie_file()),
        }
    )


@app.post("/api/extract")
def extract() -> Response:
    if rate_limited("extract", limit=15):
        return jsonify({"ok": False, "error": "طلبات كثيرة. انتظر عدة دقائق ثم جرّب مرة أخرى."}), 429
    if not pin_is_valid():
        return jsonify({"ok": False, "error": "رمز الدخول غير صحيح."}), 401

    payload = request.get_json(silent=True) or {}
    try:
        url, platform = validate_social_url(str(payload.get("url", "")))
        result = inspect_media(url, platform)
        token = serializer.dumps({"url": url, "platform": platform, "method": result["method"]})
        return jsonify(
            {
                "ok": True,
                "platform": platform,
                "title": result["title"],
                "author": result["author"],
                "thumbnail": result["thumbnail"],
                "count": result["count"],
                "has_video": result["has_video"],
                "has_audio": result["has_audio"],
                "duration": result["duration"],
                "download_url": f"/download/{token}?mode=video",
                "audio_url": f"/download/{token}?mode=audio" if result["has_audio"] else None,
            }
        )
    except ValueError as exc:
        return jsonify({"ok": False, "error": str(exc)}), 400
    except Exception as exc:
        return jsonify({"ok": False, "error": str(exc)}), 422


@app.get("/download/<token>")
def download(token: str) -> Response:
    if rate_limited("download", limit=10):
        return friendly_download_error("طلبات كثيرة. انتظر عدة دقائق ثم جرّب مرة أخرى.", 429)

    try:
        data = serializer.loads(token, max_age=TOKEN_MAX_AGE)
        url, platform = validate_social_url(str(data.get("url", "")))
        if platform != data.get("platform"):
            raise ValueError("رابط التنزيل غير صالح.")
    except SignatureExpired:
        return friendly_download_error("انتهت صلاحية رابط التنزيل. ارجع للأداة وحلّل الرابط مرة أخرى.", 410)
    except (BadSignature, ValueError):
        return friendly_download_error("رابط التنزيل غير صالح.", 400)

    mode = request.args.get("mode", "video").lower()
    if mode not in {"video", "audio"}:
        return friendly_download_error("نوع التنزيل غير صالح.", 400)

    temp_dir = tempfile.mkdtemp(prefix="social-download-")
    response_created = False
    try:
        preferred_method = data.get("method", "ytdlp")
        files: list[Path]

        if mode == "audio":
            files = download_with_ytdlp(url, "audio", temp_dir)
        elif preferred_method == "gallery":
            files = download_with_gallery_dl(url, temp_dir)
        else:
            try:
                files = download_with_ytdlp(url, "video", temp_dir)
            except Exception:
                shutil.rmtree(temp_dir, ignore_errors=True)
                temp_dir = tempfile.mkdtemp(prefix="social-download-")
                files = download_with_gallery_dl(url, temp_dir)

        ensure_size_limit(files)
        output_path = build_download_file(files, temp_dir, platform)
        download_name = clean_download_name(output_path, platform, mode)
        mimetype = mimetypes.guess_type(output_path.name)[0] or "application/octet-stream"
        response = send_file(
            output_path,
            mimetype=mimetype,
            as_attachment=True,
            download_name=download_name,
            conditional=True,
        )
        response.headers["Cache-Control"] = "no-store"
        response.call_on_close(lambda: shutil.rmtree(temp_dir, ignore_errors=True))
        response_created = True
        return response
    except subprocess.TimeoutExpired:
        return friendly_download_error("استغرق الموقع وقتًا طويلًا ولم يستجب. جرّب مرة أخرى.", 504)
    except Exception as exc:
        return friendly_download_error(str(exc) or "تعذر تنزيل الملف.", 422)
    finally:
        if not response_created:
            shutil.rmtree(temp_dir, ignore_errors=True)


@app.errorhandler(Exception)
def handle_unexpected_error(exc: Exception):
    if isinstance(exc, HTTPException):
        status = exc.code or 500
        if request.path.startswith("/api/"):
            return jsonify({"ok": False, "error": exc.description or "حدث خطأ في الطلب."}), status
        return exc

    app.logger.exception("Unhandled server error")
    if request.path.startswith("/api/"):
        return jsonify({"ok": False, "error": "حدث خطأ داخل الخادم أثناء تحليل الرابط. جرّب مرة أخرى."}), 500
    return friendly_download_error("حدث خطأ داخل الخادم. جرّب مرة أخرى.", 500)


@app.errorhandler(413)
def too_large(_: Exception) -> tuple[Response, int]:
    return jsonify({"ok": False, "error": "الطلب أكبر من الحد المسموح."}), 413


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "10000"))
    app.run(host="0.0.0.0", port=port, debug=False)
