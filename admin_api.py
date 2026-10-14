"""
admin_api.py — backend for the Admin Mini App (admin.html)

Routes (all under /api/admin, all require Telegram initData of an admin):
    GET  /meta                    rarities, anime list, is_owner flag
    GET  /cards/anime?name=       existing cards of an anime (duplicate check)
    POST /cards/upload            add ONE card (image bytes in body)
    POST /eval                    run /eval code (SUPREME OWNER only)
    GET  /info/summary            totals + rarity breakdown
    GET  /info/users|groups       paginated / searchable lists
    GET  /info/user/{id}|group/{id}
    GET  /vlog/user/{id}          vault activity log of any user (structured, filterable)
    POST /vlog/user/{id}/send     DM the .logs file to the calling admin

Also registers the /admin bot command, which opens the panel.

HOW TO WIRE IT IN (same place you already include deck_api):
    from admin_api import admin_api
    app.include_router(admin_api)
and make sure `import admin_api` runs somewhere so the /admin command registers.
"""
import re
import time
import uuid
import html
import copy
import asyncio
import traceback
import io
import sys
import os

from fastapi import APIRouter, Request, HTTPException, Header
from fastapi.responses import JSONResponse
from pydantic import BaseModel
from aiogram.types import (
    BufferedInputFile, InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo, Message,
)
from aiogram.filters import Command
from aiogram.enums import ParseMode, ChatType
from aiogram.exceptions import (
    TelegramRetryAfter, TelegramAPIError, TelegramMigrateToChat, TelegramNetworkError,
)

import config
from config import (
    bot, main_router, ADMIN_IDS, SUPREME_OWNER_ID, DB_GROUP_ID,
    RARITIES, format_rarity, load_db, save_db, get_mention, perform_backup,
)
from deck import _chicken_verify_init_data      # Telegram initData HMAC check
import a_handlers                                # eval safety check + admin log
import vlog                                      # vault activity log storage

# Where admin.html is hosted (same place as index.html / chicken.html).
ADMIN_WEB_URL = "https://animenexuss.netlify.app/admin.html"

admin_api = APIRouter(prefix="/api/admin", tags=["Admin"])

MAX_IMAGE_BYTES = 10 * 1024 * 1024      # Telegram's sendPhoto limit
INIT_MAX_AGE = 6 * 3600                 # panel stays valid for 6h
EVAL_INIT_MAX_AGE = 3600                # eval needs a fresher login (1h)


# ------------------------------------------------------------------ auth
def _require_admin(init_data: str, owner_only: bool = False, max_age: int = INIT_MAX_AGE) -> dict:
    user = _chicken_verify_init_data(init_data, max_age=max_age)
    if not user or "id" not in user:
        raise HTTPException(status_code=401, detail="Invalid or expired Telegram session. Reopen the panel.")
    uid = int(user["id"])
    if uid not in ADMIN_IDS:
        raise HTTPException(status_code=403, detail="Admins only.")
    if owner_only and uid != SUPREME_OWNER_ID:
        raise HTTPException(status_code=403, detail="Owner only.")
    return user


def _log(user: dict, action: str, details: str = ""):
    try:
        a_handlers.log_admin_action(int(user["id"]), user.get("first_name", "Admin") + " (web)", action, details)
    except Exception as e:
        print(f"[ADMIN_API] log failed: {e}")


def _norm_rarity(raw: str):
    raw = (raw or "").strip()
    if raw in RARITIES:
        return raw
    fr = format_rarity(raw)
    return fr if fr in RARITIES else None


def _sniff_image(b: bytes):
    if b[:3] == b"\xff\xd8\xff":
        return "jpg"
    if b[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if b[:4] == b"RIFF" and b[8:12] == b"WEBP":
        return "webp"
    return None


# ------------------------------------------------------------------ telegram helpers
_db_chat_id = DB_GROUP_ID       # follows a group -> supergroup migration at runtime
_db_send_lock = None            # created lazily inside the running loop
_db_last_send = 0.0
DB_SEND_GAP = 3.2               # seconds between posts into the DB group (< 20/min)


def _tg_hint(msg: str) -> str:
    """Turns Telegram's terse error text into something an admin can act on."""
    m = (msg or "").lower()
    if "chat not found" in m:
        return "chat not found. Check DB_GROUP_ID and make sure the bot was added to that chat."
    if "not enough rights" in m or "have no rights" in m or "administrator rights" in m:
        return "the bot has no permission to post there. Make it an admin with 'Post messages'."
    if "kicked" in m or "not a member" in m or "forbidden" in m:
        return "the bot was removed from that chat. Add it back as an admin."
    if "thread" in m or "topic" in m:
        return "topic problem. The chat is a forum and its topic is missing or closed."
    return msg or "unknown error"


def _tg_msg(e: Exception) -> str:
    return getattr(e, "message", None) or str(e)


async def _post_to_db_group(photo: bytes, filename: str, caption: str):
    """send_photo to the DB group. Retries network blips and follows a group
    that was upgraded to a supergroup (its chat id changes when that happens)."""
    global _db_chat_id, _db_send_lock, _db_last_send
    if _db_send_lock is None:
        _db_send_lock = asyncio.Lock()
    last = None
    # One send at a time, spaced out: Telegram caps a group at ~20 messages/min,
    # and a burst (or two admins uploading together) otherwise hits 429 errors.
    async with _db_send_lock:
        wait = DB_SEND_GAP - (time.monotonic() - _db_last_send)
        if wait > 0:
            await asyncio.sleep(wait)
        try:
            for attempt in range(3):
                try:
                    return await bot.send_photo(
                        _db_chat_id,
                        photo=BufferedInputFile(photo, filename=filename),
                        caption=caption,
                        parse_mode=ParseMode.HTML,
                    )
                except TelegramMigrateToChat as e:
                    print(f"[ADMIN_API] DB group migrated: {_db_chat_id} -> {e.migrate_to_chat_id}. Update DB_GROUP_ID.")
                    _db_chat_id = e.migrate_to_chat_id
                    last = e
                except TelegramNetworkError as e:
                    last = e
                    await asyncio.sleep(1.5 * (attempt + 1))
        finally:
            _db_last_send = time.monotonic()
    raise last


# One backup per burst of uploads instead of one per card.
_backup_deadline = 0.0
_backup_task = None


async def _backup_worker():
    global _backup_task
    try:
        while True:
            while time.time() < _backup_deadline:
                await asyncio.sleep(max(0.5, _backup_deadline - time.time()))
            started = time.time()
            try:
                await perform_backup()
            except Exception as e:
                print(f"[ADMIN_API] backup failed: {type(e).__name__}: {e}")
            if _backup_deadline <= started:
                break
    finally:
        _backup_task = None


def _schedule_backup(delay: float = 20.0):
    global _backup_deadline, _backup_task
    _backup_deadline = time.time() + delay
    if _backup_task is None or _backup_task.done():
        _backup_task = asyncio.create_task(_backup_worker())


# ------------------------------------------------------------------ meta
@admin_api.get("/meta")
async def meta(x_init_data: str = Header("")):
    user = _require_admin(x_init_data)
    db = load_db()
    counts = {}
    for c in db.get("global_cards", {}).values():
        a = str(c.get("anime", "")).strip()
        if a:
            counts[a] = counts.get(a, 0) + 1
    animes = sorted(counts.items(), key=lambda kv: kv[0].lower())
    return {
        "user": {"id": user["id"], "name": user.get("first_name", "")},
        "is_owner": int(user["id"]) == SUPREME_OWNER_ID,
        "rarities": list(RARITIES),
        "animes": [{"name": n, "count": c} for n, c in animes],
    }


@admin_api.get("/diagnose")
async def diagnose(x_init_data: str = Header("")):
    """Checks that the bot can really post to the DB group and the backup chat."""
    _require_admin(x_init_data)
    me = await bot.get_me()
    targets = [("DB group", _db_chat_id)]
    backup_id = getattr(config, "DATABASE_BACKUP_ID", None)
    if backup_id and backup_id != _db_chat_id:
        targets.append(("Backup chat", backup_id))

    out = []
    for label, cid in targets:
        row = {"label": label, "id": str(cid), "ok": False, "detail": ""}
        try:
            chat = await bot.get_chat(cid)
            member = await bot.get_chat_member(cid, me.id)
            st = member.status
            row["title"] = chat.title or ""
            if st in ("left", "kicked"):
                row["detail"] = "The bot is not in this chat. Add it as an admin."
            elif chat.type == "channel" and not (
                st == "creator" or (st == "administrator" and getattr(member, "can_post_messages", False))
            ):
                row["detail"] = "The bot is in the channel but cannot post. Give it 'Post messages'."
            elif st == "restricted" and not getattr(member, "can_send_photos", getattr(member, "can_send_messages", False)):
                row["detail"] = "The bot is restricted from sending photos in this chat."
            else:
                row["ok"] = True
        except TelegramMigrateToChat as e:
            row["detail"] = f"This group was upgraded to a supergroup. Set its id to {e.migrate_to_chat_id}."
        except TelegramAPIError as e:
            row["detail"] = _tg_hint(_tg_msg(e))
        except Exception as e:
            row["detail"] = f"{type(e).__name__}"
        out.append(row)
    return {"chats": out}


@admin_api.get("/cards/anime")
async def cards_of_anime(name: str, x_init_data: str = Header("")):
    _require_admin(x_init_data)
    want = name.strip().lower()
    db = load_db()
    out = [
        {"id": cid, "name": c.get("name", ""), "rarity": c.get("rarity", "")}
        for cid, c in db.get("global_cards", {}).items()
        if str(c.get("anime", "")).strip().lower() == want
    ]
    out.sort(key=lambda x: x["name"].lower())
    return {"cards": out}


# ------------------------------------------------------------------ card upload
_recent_uploads: dict = {}      # idempotency: upload_key -> (timestamp, card_id)


@admin_api.post("/cards/upload")
async def upload_card(
    request: Request,
    name: str,
    anime: str,
    rarity: str,
    force: int = 0,
    x_init_data: str = Header(""),
    x_upload_key: str = Header(""),
):
    """Adds ONE card. Body = raw image bytes (jpeg/png/webp). Same result as /add_card."""
    try:
        return await _upload_card(request, name, anime, rarity, force, x_init_data, x_upload_key)
    except HTTPException:
        raise
    except Exception as e:
        traceback.print_exc()
        return JSONResponse({"detail": f"Server error ({type(e).__name__}): {e}"}, status_code=500)


async def _upload_card(request, name, anime, rarity, force, x_init_data, x_upload_key):
    user = _require_admin(x_init_data)

    # Idempotency: a retry after a timeout must not create a second card.
    now = time.time()
    for k in [k for k, (ts, _) in _recent_uploads.items() if now - ts > 3600]:
        _recent_uploads.pop(k, None)
    if x_upload_key and x_upload_key in _recent_uploads:
        return {"ok": True, "card_id": _recent_uploads[x_upload_key][1], "repeat": True}

    name, anime = name.strip(), anime.strip()
    if not name or not anime:
        raise HTTPException(400, "Name and anime are required.")
    if len(name) > 80 or len(anime) > 100:
        raise HTTPException(400, "Name/anime too long.")
    rar = _norm_rarity(rarity)
    if not rar:
        raise HTTPException(400, "Invalid rarity.")

    body = await request.body()
    if not body:
        raise HTTPException(400, "Empty image.")
    if len(body) > MAX_IMAGE_BYTES:
        raise HTTPException(413, "Image over 10 MB.")
    ext = _sniff_image(body)
    if not ext:
        raise HTTPException(415, "Only JPEG, PNG or WEBP images are supported.")

    if not force:
        db0 = load_db()
        for cid, c in db0.get("global_cards", {}).items():
            if (str(c.get("name", "")).strip().lower() == name.lower()
                    and str(c.get("anime", "")).strip().lower() == anime.lower()):
                return JSONResponse(
                    {"detail": f"'{name}' already exists in {anime} ({cid}).", "duplicate": True, "card_id": cid},
                    status_code=409,
                )

    db = load_db()
    card_id = f"DB-{str(uuid.uuid4())[:6].upper()}"
    while card_id in db.get("global_cards", {}):
        card_id = f"DB-{str(uuid.uuid4())[:6].upper()}"

    added_by = int(user["id"])
    added_by_mention = get_mention(added_by, html.escape(str(user.get("first_name", "Admin")), quote=False))
    log_text = (
        "<b>「 📥 DATABASE LOG : NEW CARD 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        "<blockquote><i>A new collectable character card has been registered globally.</i></blockquote>\n\n"
        f"• 🆔 <b>Card ID:</b> <code>{card_id}</code>\n"
        f"• 👤 <b>Character:</b> <b>{html.escape(name)}</b>\n"
        f"• 📺 <b>Anime:</b> <i>{html.escape(anime)}</i>\n"
        f"• 🌟 <b>Rarity:</b> <b>{rar}</b>\n"
        f"• — <b>Added By:</b> {added_by_mention}\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    # Uploading to the DB group is how we obtain a Telegram file_id.
    try:
        msg = await _post_to_db_group(body, f"{card_id}.{ext}", log_text)
    except TelegramRetryAfter as e:
        return JSONResponse({"detail": "Telegram rate limit", "retry_after": int(e.retry_after)}, status_code=429)
    except TelegramMigrateToChat as e:
        raise HTTPException(502, f"The DB group was upgraded to a supergroup. Set DB_GROUP_ID to {e.migrate_to_chat_id}.")
    except TelegramAPIError as e:
        print(f"[ADMIN_API] send_photo failed: {type(e).__name__}: {_tg_msg(e)}")
        raise HTTPException(502, f"Telegram refused the upload: {_tg_hint(_tg_msg(e))}")
    except Exception as e:
        print(f"[ADMIN_API] send_photo failed: {type(e).__name__}: {e}")
        raise HTTPException(502, f"Upload to the DB group failed ({type(e).__name__}).")

    file_id = msg.photo[-1].file_id
    db = load_db()
    db["global_cards"][card_id] = {
        "name": name, "anime": anime, "rarity": rar,
        "file_id": file_id, "msg_id": msg.message_id, "added_by": added_by,
    }
    save_db()

    if x_upload_key:
        _recent_uploads[x_upload_key] = (time.time(), card_id)
    _log(user, "ADD CARD", f"{name} [{anime}] ({rar}) — ID: {card_id}")
    _schedule_backup()      # pushes database.json to the backup chat once the burst ends
    return {"ok": True, "card_id": card_id, "group": True, "backup": "queued"}


# ------------------------------------------------------------------ banner upload
def _circle_of(src):
    """Runs banners.detect_circle on a path or file-like object (blocking; call via to_thread)."""
    from PIL import Image
    import banners
    img = Image.open(src)
    img.load()
    return banners.detect_circle(img)


@admin_api.post("/banners/upload")
async def upload_banner(
    request: Request,
    name: str,
    make_default: int = 0,
    x_init_data: str = Header(""),
    x_upload_key: str = Header(""),
):
    """Adds ONE profile banner (same result as /ab). Body = raw image bytes."""
    try:
        return await _upload_banner(request, name, make_default, x_init_data, x_upload_key)
    except HTTPException:
        raise
    except Exception as e:
        traceback.print_exc()
        return JSONResponse({"detail": f"Server error ({type(e).__name__}): {e}"}, status_code=500)


async def _upload_banner(request, name, make_default, x_init_data, x_upload_key):
    import banners
    user = _require_admin(x_init_data)

    key = ("banner:" + x_upload_key) if x_upload_key else ""
    if key and key in _recent_uploads:
        return {"ok": True, "banner_id": _recent_uploads[key][1], "repeat": True}

    name = name.strip()
    if not name or len(name) > 60:
        raise HTTPException(400, "Banner name is required (max 60 characters).")

    body = await request.body()
    if not body:
        raise HTTPException(400, "Empty image.")
    if len(body) > MAX_IMAGE_BYTES:
        raise HTTPException(413, "Image over 10 MB.")
    ext = _sniff_image(body)
    if not ext:
        raise HTTPException(415, "Only JPEG, PNG or WEBP images are supported.")

    no_circle = ("Couldn't find a white circle placeholder in that image. It needs one solid, "
                 "roughly-circular pure-white area for the profile picture to go into.")

    # Cheap early check on the original, so a bad template never gets posted to the DB group.
    try:
        pre = await asyncio.to_thread(_circle_of, io.BytesIO(body))
    except Exception:
        raise HTTPException(415, "Couldn't read that image.")
    if not pre:
        raise HTTPException(422, no_circle)

    added_by = int(user["id"])
    added_by_mention = get_mention(added_by, html.escape(str(user.get("first_name", "Admin")), quote=False))
    log_text = (
        "<b>「 📥 DATABASE LOG : NEW BANNER 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        "<blockquote><i>A new profile banner template has been registered globally.</i></blockquote>\n\n"
        f"• 🏷️ <b>Name:</b> <b>{html.escape(name)}</b>\n"
        f"• ⭕ <b>Circle:</b> ~{int(pre['radius'] * 2)}px diameter\n"
        f"• — <b>Added By:</b> {added_by_mention}\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    try:
        msg = await _post_to_db_group(body, f"banner.{ext}", log_text)
    except TelegramRetryAfter as e:
        return JSONResponse({"detail": "Telegram rate limit", "retry_after": int(e.retry_after)}, status_code=429)
    except TelegramMigrateToChat as e:
        raise HTTPException(502, f"The DB group was upgraded to a supergroup. Set DB_GROUP_ID to {e.migrate_to_chat_id}.")
    except TelegramAPIError as e:
        print(f"[ADMIN_API] banner send_photo failed: {type(e).__name__}: {_tg_msg(e)}")
        raise HTTPException(502, f"Telegram refused the upload: {_tg_hint(_tg_msg(e))}")
    except Exception as e:
        print(f"[ADMIN_API] banner send_photo failed: {type(e).__name__}: {e}")
        raise HTTPException(502, f"Upload to the DB group failed ({type(e).__name__}).")

    # Telegram re-encodes/downsizes photos. Save THAT copy (what /ab does and what
    # ensure_banner_file() restores later) and measure the circle on it.
    file_id = msg.photo[-1].file_id
    os.makedirs(banners.BANNERS_DIR, exist_ok=True)
    tmp_path = os.path.join(banners.BANNERS_DIR, f"tmp_{uuid.uuid4().hex[:8]}.png")
    circle = None
    try:
        await bot.download(file_id, destination=tmp_path)
        circle = await asyncio.to_thread(_circle_of, tmp_path)
    except Exception as e:
        print(f"[ADMIN_API] banner download/detect failed: {type(e).__name__}: {e}")
    if not circle:
        try:
            os.remove(tmp_path)
        except Exception:
            pass
        try:
            await bot.delete_message(_db_chat_id, msg.message_id)
        except Exception:
            pass
        raise HTTPException(422, no_circle)

    # No awaits from here to save_db(): the new id can't be taken by a parallel upload.
    db = load_db()
    banner_id = banners.next_banner_id(db)
    file_path = os.path.join(banners.BANNERS_DIR, f"{banner_id}.png")
    os.replace(tmp_path, file_path)
    db.setdefault("banners", {})[banner_id] = {
        "name": name,
        "file_path": file_path,
        "file_id": file_id,
        "circle": circle,
        "msg_id": msg.message_id,
        "added_by": str(added_by),
        "added_at": int(time.time()),
    }
    if make_default:
        db.setdefault("settings", {})["default_banner_id"] = banner_id
    save_db()

    if key:
        _recent_uploads[key] = (time.time(), banner_id)
    _log(user, "ADD BANNER", f"{name} — ID: {banner_id}" + (" (set as default)" if make_default else ""))
    _schedule_backup()
    return {"ok": True, "banner_id": banner_id, "name": name,
            "diameter": int(circle["radius"] * 2), "default": bool(make_default)}


# ------------------------------------------------------------------ eval (owner only)
class EvalReq(BaseModel):
    code: str


_eval_lock = asyncio.Lock()     # stdout redirection is global, so run one at a time


@admin_api.post("/eval")
async def web_eval(req: EvalReq, x_init_data: str = Header("")):
    user = _require_admin(x_init_data, owner_only=True, max_age=EVAL_INIT_MAX_AGE)
    code = req.code
    if not code.strip():
        raise HTTPException(400, "No code.")

    violations = a_handlers._eval_safety_check(code)
    if violations:
        _log(user, "WEB EVAL BLOCKED", code[:200].replace("\n", " ⏎ "))
        return {"ok": False, "blocked": True, "violations": violations[:20]}

    async with _eval_lock:
        old_stdout = sys.stdout
        buf = sys.stdout = io.StringIO()
        eval_db = load_db()
        db_before = copy.deepcopy(eval_db)
        uid = int(user["id"])

        async def send(text):           # handy helper: DM the result to yourself
            return await bot.send_message(uid, str(text))

        variables = {
            "bot": bot, "message": None, "command": None, "config": config,
            "db": eval_db, "save_db": save_db, "asyncio": asyncio, "sys": sys,
            "os": os, "time": time, "me": uid, "send": send,
        }
        wrapped = "async def _eval_expr():\n" + "".join(f"    {l}\n" for l in code.split("\n"))
        started = time.perf_counter()
        ok = True
        try:
            exec(wrapped, variables)
            result = await asyncio.wait_for(variables["_eval_expr"](), timeout=a_handlers.EVAL_TIMEOUT_SECONDS)
            stdout_val = buf.getvalue()
        except asyncio.TimeoutError:
            ok = False
            stdout_val = buf.getvalue()
            result = f"Timed out after {a_handlers.EVAL_TIMEOUT_SECONDS}s and was cancelled."
        except Exception:
            ok = False
            stdout_val = buf.getvalue()
            result = traceback.format_exc()
        finally:
            elapsed = time.perf_counter() - started
            sys.stdout = old_stdout

    output = stdout_val.strip() or str(result)
    if len(output) > 6000:
        output = output[:6000] + "\n... truncated ..."
    try:
        changes = a_handlers._eval_describe_changes(db_before, load_db())
        changes = html.unescape(re.sub(r"<[^>]+>", "", str(changes)))
    except Exception:
        changes = "unknown"

    _log(user, "WEB EVAL", code[:200].replace("\n", " ⏎ "))
    return {
        "ok": ok, "output": output, "data_changes": changes,
        "time": f"{elapsed * 1000:.1f} ms" if elapsed < 1 else f"{elapsed:.2f} s",
    }


# ------------------------------------------------------------------ info
def _page(items: list, page: int, per: int = 20):
    total = len(items)
    pages = max(1, (total - 1) // per + 1)
    page = min(max(page, 0), pages - 1)
    return items[page * per:(page + 1) * per], page, pages, total


@admin_api.get("/info/summary")
async def info_summary(x_init_data: str = Header("")):
    _require_admin(x_init_data)
    db = load_db()
    by_rarity = {}
    for c in db.get("global_cards", {}).values():
        r = c.get("rarity", "?")
        by_rarity[r] = by_rarity.get(r, 0) + 1
    return {
        "users": len(db.get("users", {})),
        "groups": len(db.get("groups", {})),
        "cards": len(db.get("global_cards", {})),
        "banners": len(db.get("banners", {})),
        "by_rarity": by_rarity,
    }


@admin_api.get("/info/users")
async def info_users(page: int = 0, q: str = "", x_init_data: str = Header("")):
    _require_admin(x_init_data)
    db = load_db()
    q = q.strip().lower()
    rows = []
    for uid, u in db.get("users", {}).items():
        if q and q not in str(uid) and q not in str(u.get("name", "")).lower() \
                and q not in str(u.get("username", "")).lower():
            continue
        rows.append((uid, u))
    rows.sort(key=lambda x: x[1].get("joined", 0), reverse=True)
    sliced, page, pages, total = _page(rows, page)
    return {
        "page": page, "pages": pages, "total": total,
        "items": [{
            "id": uid, "name": u.get("name", "User"), "username": u.get("username"),
            "cards": len(u.get("cards", {})), "claimed": u.get("total_claimed", 0),
        } for uid, u in sliced],
    }


@admin_api.get("/info/groups")
async def info_groups(page: int = 0, q: str = "", x_init_data: str = Header("")):
    _require_admin(x_init_data)
    db = load_db()
    q = q.strip().lower()
    rows = [(gid, g) for gid, g in db.get("groups", {}).items()
            if not q or q in str(gid) or q in str(g.get("title", "")).lower()]
    rows.sort(key=lambda x: x[1].get("joined", 0), reverse=True)
    sliced, page, pages, total = _page(rows, page)
    return {
        "page": page, "pages": pages, "total": total,
        "items": [{
            "id": gid, "title": g.get("title", "Unknown"),
            "drops": g.get("drops", 0), "claims": g.get("claims", 0),
        } for gid, g in sliced],
    }


@admin_api.get("/info/user/{user_id}")
async def info_user(user_id: str, x_init_data: str = Header("")):
    _require_admin(x_init_data)
    db = load_db()
    u = db.get("users", {}).get(user_id)
    if not u:
        raise HTTPException(404, "User not registered.")
    try:
        ghost = int(user_id) in config.ghost_banned
    except Exception:
        ghost = False
    try:
        shadow = bool(config.is_shadow_banned(int(user_id)))
    except Exception:
        shadow = False
    return {
        "id": user_id, "name": u.get("name", "User"), "username": u.get("username"),
        "unique_cards": len(u.get("cards", {})),
        "total_cards": sum(int(c.get("amount", 0) or 0) for c in u.get("cards", {}).values()),
        "claimed": u.get("total_claimed", 0),
        "banners": len([1 for b in u.get("banners", {}).values() if b.get("amount", 0) > 0]),
        "ghost_banned": ghost, "shadow_banned": shadow,
    }


@admin_api.get("/info/group/{group_id}")
async def info_group(group_id: str, x_init_data: str = Header("")):
    _require_admin(x_init_data)
    db = load_db()
    g = db.get("groups", {}).get(group_id)
    if not g:
        raise HTTPException(404, "Group not registered.")
    return {"id": group_id, "title": g.get("title", "Unknown"),
            "drops": g.get("drops", 0), "claims": g.get("claims", 0)}


# ------------------------------------------------------------------ vault log (/vlog on the web)
_VLOG_META = {
    # type: (category, icon, short title)
    "sgive_sent":         ("shards", "💠", "Shard gift sent"),
    "sgive_received":     ("shards", "💠", "Shard gift received"),
    "weekly_claim":       ("shards", "📅", "Weekly claim"),
    "promo_shards":       ("shards", "🎫", "Promo code"),
    "gift_sent":          ("cards",  "🎁", "Card gift sent"),
    "gift_received":      ("cards",  "🎁", "Card gift received"),
    "trade_sent":         ("cards",  "🔄", "Card trade"),
    "burn":               ("cards",  "🔥", "Card burned"),
    "web_burn":           ("cards",  "🔥", "Card burned (web)"),
    "ad_reward":          ("cards",  "📺", "Ad reward card"),
    "store_buy_online":   ("store",  "🛒", "Store purchase (online)"),
    "store_buy_offline":  ("store",  "🛍️", "Store purchase (offline)"),
    "store_sell_offline": ("store",  "💰", "Store sale (offline)"),
    "bowling_win":        ("games",  "🎳", "Bowling win"),
    "basketball_win":     ("games",  "🏀", "Basketball win"),
    "mines_win":          ("games",  "💣", "Mines win"),
    "scramble_win":       ("games",  "🧩", "Scramble solved (chat)"),
    "scramble_web_win":   ("games",  "🧩", "Scramble solved (web)"),
    "market_sell":        ("market", "📈", "Stock sale"),
    "market_liquidation": ("market", "📉", "Forced liquidation"),
}
VLOG_PER_PAGE = 25


def _int(v, default=0) -> int:
    try:
        return int(v)
    except (TypeError, ValueError):
        return default


def _vlog_view(e: dict) -> dict:
    """Turns one raw vlog entry into a display-ready dict (mirrors vlog._format_entry)."""
    t = e.get("type")
    cat, icon, title = _VLOG_META.get(t, ("other", "📄", str(t or "Unknown")))
    fields, delta, sub = [], 0, ""

    def add(k, v):
        fields.append([k, str(v)])

    cp = f"{e.get('cp_name', 'Unknown')} ({e.get('cp_id', '?')})"
    card = e.get("card_name", "Unknown")
    rar = e.get("rarity", "Unknown")

    if t in ("sgive_sent", "sgive_received"):
        amt = _int(e.get("amount"))
        delta = -amt if t == "sgive_sent" else amt
        sub = e.get("cp_name", "Unknown")
        add("Amount", f"{amt:,} shards"); add("Counterparty", cp)
    elif t in ("gift_sent", "gift_received", "trade_sent"):
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Counterparty", cp)
    elif t in ("burn", "web_burn"):
        delta = _int(e.get("shards_earned"))
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Shards earned", f"+{delta:,}")
    elif t == "store_buy_online":
        delta = -_int(e.get("price"))
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Price paid", f"{-delta:,}")
    elif t == "store_buy_offline":
        delta = -_int(e.get("price"))
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Price paid", f"{-delta:,}"); add("Seller", cp)
    elif t == "store_sell_offline":
        delta = _int(e.get("price"))
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Price earned", f"+{delta:,}"); add("Buyer", cp)
    elif t == "weekly_claim":
        delta = _int(e.get("amount"))
        add("Shards earned", f"+{delta:,}")
        if e.get("bio_bonus"):
            add("Bio bonus", "Yes")
    elif t in ("bowling_win", "basketball_win"):
        delta = _int(e.get("amount"))
        add("Shards earned", f"+{delta:,}")
    elif t == "promo_shards":
        delta = _int(e.get("amount"))
        sub = str(e.get("code", ""))
        add("Promo code", e.get("code", "Unknown")); add("Shards earned", f"+{delta:,}")
    elif t in ("market_sell", "market_liquidation"):
        delta = _int(e.get("amount"))
        profit = _int(e.get("profit"))
        sub = f"{e.get('symbol', '?')} × {e.get('shares', 0)}"
        add("Symbol", e.get("symbol", "Unknown")); add("Shares sold", e.get("shares", 0))
        add("Net payout", f"+{delta:,}"); add("P/L", f"{'+' if profit >= 0 else ''}{profit:,}")
        if t == "market_liquidation":
            add("Reason", "Nightly forced liquidation")
    elif t == "mines_win":
        delta = _int(e.get("amount"))
        sub = f"{e.get('multiplier', 0)}x · {e.get('mines', 0)} mines"
        add("Bet", f"{_int(e.get('bet')):,}"); add("Mines", e.get("mines", 0))
        add("Gems found", e.get("gems_found", 0)); add("Multiplier", f"{e.get('multiplier', 0)}x")
        add("Payout", f"+{delta:,}")
    elif t in ("scramble_win", "scramble_web_win"):
        delta = _int(e.get("amount"))
        sub = f"{card} · {rar}"
        add("Card", card); add("Rarity", rar); add("Solve time", f"{e.get('time', 0)}s")
        if e.get("moves") is not None:
            add("Moves", e.get("moves"))
        add("Shards earned", f"+{delta:,}")
        if _int(e.get("earned")) > delta:
            add("Note", f"Daily cap reached (tier worth {_int(e.get('earned')):,})")
    elif t == "ad_reward":
        sub = f"{card} · {rar}"
        add("Card earned", card); add("Rarity", rar)

    add("Chat", f"{e.get('chat_title', 'Unknown')} ({e.get('chat_id', '?')})")
    return {"ts": e.get("ts", 0), "type": t, "cat": cat, "icon": icon, "title": title,
            "sub": sub, "delta": delta, "fields": fields}


def _vlog_logs_for(user_id: str):
    if not re.fullmatch(r"-?\d+", user_id or ""):
        raise HTTPException(400, "Use a numeric user ID.")
    if vlog._purge_all_vlogs():
        vlog.save_vlogs()
    return vlog.load_vlogs().get(user_id, [])


# ---- vlog search ---------------------------------------------------------
# Query language (all terms are ANDed; a leading "-" excludes):
#   naruto               free text, matches title / card / people / chat / code / values
#   "uzumaki naruto"     exact phrase
#   card:naruto          card name           rarity:divine     rarity
#   with:1234 / with:sam counterparty, buyer or seller (name or id)
#   chat:anime           chat title or id    code:WELCOME      promo code
#   symbol:xyz           stock symbol        type:burn         type, title or category
#   amount>1000  >=500  <50k  =250   shard amount (k / m suffixes ok; bare ">500" works too)
#   -gift                hide anything matching "gift"
_Q_TOKEN = re.compile(r'(-?)(?:([A-Za-z]+)(:|>=|<=|>|<|=))?(?:"([^"]*)"|(\S+))')
_Q_FIELDS = {
    "card": ("Card", "Card earned"), "rarity": ("Rarity",),
    "with": ("Counterparty", "Seller", "Buyer"), "chat": ("Chat",),
    "code": ("Promo code",), "symbol": ("Symbol",),
}


def _qnum(txt):
    t = str(txt or "").strip().lower().replace(",", "").replace("_", "")
    mult = 1
    if t.endswith("k"):
        mult, t = 1_000, t[:-1]
    elif t.endswith("m"):
        mult, t = 1_000_000, t[:-1]
    try:
        return float(t) * mult
    except ValueError:
        return None


def _parse_vlog_query(q: str):
    terms = []
    for m in _Q_TOKEN.finditer((q or "")[:200]):
        neg, key, op, quoted, bare = m.groups()
        val = (quoted if quoted is not None else (bare or "")).strip()
        if not val:
            continue
        key = key.lower() if key else None
        if key is None:
            mm = re.fullmatch(r"(>=|<=|>|<|=)(.+)", val)
            if mm and _qnum(mm.group(2)) is not None:
                key, op, val = "amount", mm.group(1), mm.group(2)
        elif key not in _Q_FIELDS and key not in ("amount", "type"):
            # unknown "word:thing" -> just plain text
            val, key, op = f"{key}{op}{val}", None, None
        terms.append((bool(neg), key, op, val.lower()))
    return terms


def _vlog_match(v: dict, terms) -> bool:
    hay = " ".join([v["title"], v["sub"], str(v["type"] or ""), v["cat"]]
                   + [f"{k} {val}" for k, val in v["fields"]]).lower()
    amt = abs(v["delta"])
    for neg, key, op, val in terms:
        if key == "amount":
            n = _qnum(val)
            if n is None:
                ok = False
            elif op in (">",):
                ok = amt > n
            elif op == ">=":
                ok = amt >= n
            elif op == "<":
                ok = 0 < amt < n
            elif op == "<=":
                ok = 0 < amt <= n
            else:
                ok = amt == n
        elif key in _Q_FIELDS:
            ok = any(val in str(fv).lower() for fk, fv in v["fields"] if fk in _Q_FIELDS[key])
        elif key == "type":
            ok = val in str(v["type"] or "").lower() or val in v["title"].lower() or val in v["cat"]
        else:
            ok = val in hay
        if ok == neg:
            return False
    return True


@admin_api.get("/vlog/user/{user_id}")
async def vlog_user(user_id: str, cat: str = "all", page: int = 0, q: str = "", dir: str = "all",
                    days: int = 0, sort: str = "new", x_init_data: str = Header("")):
    user = _require_admin(x_init_data)
    logs = _vlog_logs_for(user_id)
    db = load_db()
    u = db.get("users", {}).get(user_id) or {}

    views = [_vlog_view(e) for e in sorted(logs, key=lambda e: e.get("ts", 0), reverse=True)]
    counts = {}
    inflow = outflow = 0
    for v in views:
        counts[v["cat"]] = counts.get(v["cat"], 0) + 1
        if v["delta"] > 0:
            inflow += v["delta"]
        else:
            outflow += -v["delta"]

    shown = views if cat in ("", "all") else [v for v in views if v["cat"] == cat]
    if dir == "in":
        shown = [v for v in shown if v["delta"] > 0]
    elif dir == "out":
        shown = [v for v in shown if v["delta"] < 0]
    days = max(0, min(int(days or 0), 3650))
    if days:
        cutoff = time.time() - days * 86400
        shown = [v for v in shown if v["ts"] >= cutoff]
    terms = _parse_vlog_query(q)
    if terms:
        shown = [v for v in shown if _vlog_match(v, terms)]
    if sort == "old":
        shown = sorted(shown, key=lambda v: v["ts"])
    elif sort == "big":
        shown = sorted(shown, key=lambda v: (abs(v["delta"]), v["ts"]), reverse=True)

    items, page, pages, total = _page(shown, page, VLOG_PER_PAGE)
    if page == 0 and not terms and dir == "all" and not days:
        _log(user, "VLOG VIEW", f"user {user_id}")
    return {
        "user": {"id": user_id, "name": u.get("name") or "Unknown", "username": u.get("username"),
                 "registered": bool(u)},
        "retention_days": vlog.LOG_RETENTION_DAYS,
        "all_total": len(views), "counts": counts, "in": inflow, "out": outflow,
        "page": page, "pages": pages, "total": total, "items": items,
    }


@admin_api.post("/vlog/user/{user_id}/send")
async def vlog_send(user_id: str, x_init_data: str = Header("")):
    """DMs the same .logs file /vlog produces to the calling admin."""
    user = _require_admin(x_init_data)
    logs = _vlog_logs_for(user_id)
    if not logs:
        raise HTTPException(404, "No activity logged for this user.")
    db = load_db()
    name = (db.get("users", {}).get(user_id) or {}).get("name", "Unknown")
    report = vlog._build_report(user_id, name, logs)
    try:
        await bot.send_document(
            int(user["id"]),
            BufferedInputFile(report.encode("utf-8"), filename=f"{user_id}.logs"),
            caption=f"📄 <b>Vault log</b> for <b>{html.escape(str(name))}</b> (<code>{user_id}</code>) — {len(logs)} entries.",
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        raise HTTPException(502, f"Could not DM the file: {type(e).__name__}")
    _log(user, "VLOG SEND", f"user {user_id}")
    return {"ok": True, "entries": len(logs)}


# ------------------------------------------------------------------ /admin command
@main_router.message(Command("admin"))
async def admin_panel_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return
    if message.chat.type != ChatType.PRIVATE:
        await message.reply("Open the admin panel in my DM: send /admin there.")
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛠 Open Admin Panel", web_app=WebAppInfo(url=ADMIN_WEB_URL))],
    ])
    await message.reply("<b>Admin Panel</b>\nCards upload · Vlog · Info · Eval", reply_markup=kb, parse_mode=ParseMode.HTML)
