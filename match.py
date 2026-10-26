"""
match.py — /match card-matching (memory) game, played in a Telegram Mini App.

The server picks MATCH_PAIRS random cards, doubles and shuffles them, and the player
flips tiles two at a time to find every pair. Faster clears pay Shards, and those Shards
count toward the SAME daily minigame cap that /gcard, Versus and Scramble use
(get_daily_minigame_rewards / DAILY_MINIGAME_REWARD_CAP from config).

The board layout never leaves the server: the Mini App asks for a tile with
/match/flip and only then learns which card sits there, so players can't read the answer
out of the network traffic. The server also times the run and verifies Telegram's signed
initData, so players can't send fake times.

Load it once at startup, next to scramble:   import match
IMPORTANT: import it BEFORE the app calls include_router(deck_api); routes added after
that are not picked up. Check it: open <BACKEND>/api/deck/match/ping -> {"ok": true}
BotFather -> /newapp -> short name "match" -> Web App URL = where match.html is hosted.
"""
import io
import math
import time
import random
import asyncio
import secrets
import base64
import traceback
from collections import deque
from html import escape as _html_esc

from PIL import Image   # pip install pillow
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup
)
from aiogram.filters import Command
from aiogram.enums import ParseMode
from fastapi import HTTPException
from pydantic import BaseModel

from config import (
    bot, main_router, ensure_user, save_db,
    is_ghost_banned, is_shadow_banned,
    get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)
from vlog import log_action   # /vlog activity log
from halloween import quest_progress
from deck import dlog, deck_api   # same FastAPI router the deck / scramble Mini Apps use
from scramble import (   # shared helpers: Telegram initData check, coloured buttons, avatars
    ScrWebReq, scramble_web_avatar, _scramble_web_user,
    _scr_btn, _scr_url_btn, _scramble_fmt_best,
)

# ==========================================
# SETTINGS
# ==========================================
MATCH_WEB_LINK = "https://t.me/Animenx_bot/match"      # Mini App direct link
MATCH_IMAGE = "https://i.ibb.co/zVsQZwfr/IMG-20261026-235720.jpg"   # banner shown on /match
MATCH_LBD_IMAGE = MATCH_IMAGE                           # banner shown on /match_lbd (set a different URL if you like)

MATCH_PAIRS = 6                     # 6 pairs = 12 tiles (3 x 4 on a phone)
MATCH_REWARD_TIERS = [(30, 50), (60, 25)]   # (clear under N seconds, shards). Slower pays nothing.
MATCH_WEB_MIN_SECONDS = 4           # 12 flips can't be done faster than this by hand, so it's a bot
MATCH_RUN_TTL = 15 * 60             # idle seconds before a run expires
MATCH_MAX_RUNS = 300                # hard cap on runs held in memory
MATCH_MAX_FLIPS = 300               # a 6-pair board never needs more; stops request spamming

# Card thumbnails (portrait 3:4). Small on purpose: the Mini App receives all of them in one response.
MATCH_THUMB_W = 240
MATCH_THUMB_H = 320

# Card pool: prepared thumbnails kept ready so a game starts without downloading anything.
# Each game CONSUMES MATCH_PAIRS cards. When the pool drops to MATCH_POOL_LOW it is refilled in
# the background up to MATCH_POOL_SIZE, using cards that are neither in the pool nor among the
# last MATCH_RECENT_MAX cards played.
MATCH_POOL_SIZE = 80
MATCH_POOL_LOW = 30
MATCH_RECENT_MAX = 60
MATCH_REFILL_PARALLEL = 4           # simultaneous Telegram downloads while refilling

_match_runs: dict = {}              # run token -> game state (see match_web_start)
_match_pool: dict = {}              # card_id -> prepared JPEG thumbnail
_match_recent: deque = deque(maxlen=MATCH_RECENT_MAX)
_match_refilling = False
_match_inflight: set = set()        # card ids being downloaded right now
_match_bg: set = set()              # keeps background tasks alive


# ==========================================
# CARD POOL
# ==========================================
def _match_prepare(raw: bytes) -> bytes:
    """Cover-crop the art to a 3:4 thumbnail (biased toward the top, where faces are). Returns JPEG bytes."""
    img = Image.open(io.BytesIO(raw)).convert("RGB")
    scale = max(MATCH_THUMB_W / img.width, MATCH_THUMB_H / img.height)
    nw, nh = max(MATCH_THUMB_W, math.ceil(img.width * scale)), max(MATCH_THUMB_H, math.ceil(img.height * scale))
    img = img.resize((nw, nh), Image.LANCZOS)
    left = (nw - MATCH_THUMB_W) // 2
    top = int((nh - MATCH_THUMB_H) * 0.3)
    img = img.crop((left, top, left + MATCH_THUMB_W, top + MATCH_THUMB_H))
    out = io.BytesIO()
    img.save(out, "JPEG", quality=80, optimize=True)
    return out.getvalue()


async def _match_fetch(file_id: str) -> bytes:
    """Download a card and prepare its thumbnail."""
    buf = io.BytesIO()
    await bot.download(file_id, destination=buf)
    return await asyncio.to_thread(_match_prepare, buf.getvalue())


def _match_valid_ids(db: dict) -> list:
    """Card ids with art. Locked series are included too, same as /gcard and Scramble."""
    return [c for c, g in db.get("global_cards", {}).items() if g.get("file_id")]


def _match_candidates(db: dict) -> list:
    """Cards eligible to enter the pool: not in it, and not played recently.
    A tiny catalogue relaxes the 'recent' rule so the pool can still fill."""
    valid = _match_valid_ids(db)
    taken = set(_match_pool) | _match_inflight
    fresh = [c for c in valid if c not in taken and c not in _match_recent]
    return fresh or [c for c in valid if c not in taken]


async def _match_refill(db: dict):
    """Top the pool back up to MATCH_POOL_SIZE in the background."""
    global _match_refilling
    if _match_refilling:
        return
    _match_refilling = True
    try:
        sem = asyncio.Semaphore(MATCH_REFILL_PARALLEL)

        async def load(cid):
            async with sem:
                thumb = await _match_fetch(db["global_cards"][cid]["file_id"])
            if (cid not in _match_pool and cid not in _match_recent
                    and len(_match_pool) < MATCH_POOL_SIZE):
                _match_pool[cid] = thumb
                return True
            return False

        while len(_match_pool) < MATCH_POOL_SIZE:
            cands = _match_candidates(db)
            if not cands:
                break
            batch = random.sample(cands, min(MATCH_POOL_SIZE - len(_match_pool), len(cands)))
            _match_inflight.update(batch)
            try:
                results = await asyncio.gather(*(load(c) for c in batch), return_exceptions=True)
            finally:
                _match_inflight.difference_update(batch)
            for r in results:
                if isinstance(r, Exception):
                    dlog.error(f"[match_refill] {r}")
            if not any(r is True for r in results):   # nothing added - stop instead of looping forever
                break
    except Exception as e:
        dlog.error(f"[match_refill] {e}", exc_info=True)
    finally:
        _match_refilling = False


def _match_kick_refill(db: dict):
    """Start a background refill when the pool is at/below the low-water mark."""
    if len(_match_pool) <= MATCH_POOL_LOW and not _match_refilling:
        task = asyncio.create_task(_match_refill(db))
        _match_bg.add(task)
        task.add_done_callback(_match_bg.discard)


async def _match_draw(db: dict, n: int):
    """n distinct ready cards -> [(card_id, thumb)], or None if the catalogue is too small."""
    valid = set(_match_valid_ids(db))
    picked = []
    for cid in random.sample(list(_match_pool), len(_match_pool)):
        if len(picked) >= n:
            break
        thumb = _match_pool.pop(cid)
        if cid in valid:   # card may have been removed since it was pooled
            picked.append((cid, thumb))
    for _ in range(3):   # cold pool: build the missing ones on demand
        need = n - len(picked)
        if need <= 0:
            break
        have = {c for c, _t in picked}
        rest = [c for c in valid if c not in have]
        if not rest:
            break
        # Prefer cards that aren't pooled, downloading or recently played; top up from the rest if short.
        fresh = [c for c in rest if c not in _match_recent and c not in _match_pool and c not in _match_inflight]
        if len(fresh) >= need:
            batch = random.sample(fresh, need)
        else:
            others = [c for c in rest if c not in fresh]
            batch = fresh + random.sample(others, min(need - len(fresh), len(others)))
        results = await asyncio.gather(
            *(_match_fetch(db["global_cards"][c]["file_id"]) for c in batch), return_exceptions=True)
        for c, r in zip(batch, results):
            if isinstance(r, Exception):
                dlog.error(f"[match_draw] {r}")
            else:
                picked.append((c, r))
    if len(picked) < n:
        for c, t in picked:   # not enough cards: give them back
            _match_pool.setdefault(c, t)
        return None
    return picked


# ==========================================
# REWARDS + RECORDS
# ==========================================
def _match_reward_for(elapsed: float) -> int:
    for limit, shards in MATCH_REWARD_TIERS:
        if elapsed < limit:
            return shards
    return 0


def _match_settle(user_id: str, name: str, username, elapsed: float, earned: int,
                  moves: int, cards: list) -> int:
    """Records the win (rounds, best time, best moves, shards) and credits `earned` shards,
    limited by the daily minigame cap shared with /gcard, Versus and Scramble.
    Returns shards actually paid."""
    db = ensure_user(user_id, name, username)
    user_data = db["users"][user_id]

    paid = 0
    if earned > 0:
        rewards = get_daily_minigame_rewards(user_data)
        used = rewards.get("shards", 0)
        if used < DAILY_MINIGAME_REWARD_CAP:
            paid = min(earned, DAILY_MINIGAME_REWARD_CAP - used)
            user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + paid
            rewards["shards"] = used + paid

    rec = user_data.setdefault("match", {})
    rec["rounds"] = rec.get("rounds", 0) + 1
    rec["shards"] = rec.get("shards", 0) + paid
    best = rec.get("best_time")
    if best is None or elapsed < best:
        rec["best_time"] = round(elapsed, 2)
    best_m = rec.get("best_moves")
    if best_m is None or moves < best_m:
        rec["best_moves"] = moves

    try:   # every clear goes into /vlog (a logging error must never block the reward)
        log_action(db, user_id, {
            "type": "match_win",
            "card_name": ", ".join(str(c.get("name", "Card")) for c in cards)[:60],
            "rarity": "Match",
            "time": round(elapsed, 2), "moves": moves, "earned": earned, "amount": paid,
            "chat_id": "web", "chat_title": "Match Web App",
        })
    except Exception as e:
        dlog.error(f"[match_vlog] {e}", exc_info=True)
    if paid:
        try:
            quest_progress(user_id, "shards", paid, db=db)   # 🎃 quest
        except Exception as e:
            dlog.error(f"[match_quest] {e}", exc_info=True)
    save_db()
    return paid


# ==========================================
# WEB MODE — Telegram Mini App (match.html)
# ==========================================
# Routes live on deck_api (FastAPI) at /api/deck/match/*
#   GET  /match/ping
#   POST /match/start   -> {ok, run, pairs, tiles, pics[], tiers}   (pics = data-URL thumbnails)
#   POST /match/begin   -> clock starts (call once the board is on screen)
#   POST /match/flip    -> {index} -> {pic, ...}; the 2nd flip of a pair also says match true/false;
#                          the final matching flip returns done:true with the reward
#   POST /match/giveup  -> reveals the cards, no shards
#   POST /match/lb      -> {tab: time|moves|rounds|shards} top 10 + caller's rank
#   POST /match/avatar  -> profile picture fallback
class MatchReq(BaseModel):
    init_data: str = ""
    run: str = ""
    tab: str = "time"
    index: int = -1


def _match_web_auth(req: MatchReq) -> dict:
    u = _scramble_web_user(req.init_data)
    if not u or "id" not in u:
        raise HTTPException(status_code=401, detail="Invalid Telegram session.")
    if is_ghost_banned(int(u["id"])) or is_shadow_banned(int(u["id"])):
        raise HTTPException(status_code=403, detail="Not allowed.")
    return u


def _match_web_run(req: MatchReq, u: dict, pop: bool = False) -> dict:
    run = _match_runs.get(req.run)
    if not run or run["uid"] != str(u["id"]):
        raise HTTPException(status_code=401, detail="Unknown run.")
    if time.time() - run["touched"] > MATCH_RUN_TTL:
        _match_runs.pop(req.run, None)
        raise HTTPException(status_code=401, detail="This game has expired.")
    run["touched"] = time.time()
    if pop:
        _match_runs.pop(req.run, None)   # one-time token: no replays
    return run


@deck_api.get("/match/ping")
async def match_web_ping():
    return {"ok": True}


@deck_api.post("/match/start")
async def match_web_start(req: MatchReq):
    """Pick MATCH_PAIRS real cards; the layout stays on the server, the clock starts at /begin."""
    u = _match_web_auth(req)
    try:
        uid = str(u["id"])
        db = ensure_user(uid, u.get("first_name", "User"), u.get("username"))
        picked = await _match_draw(db, MATCH_PAIRS)
        if picked is None:
            _match_kick_refill(db)
            return {"ok": False, "error": "no_cards"}
        _match_recent.extend(c for c, _t in picked)   # not offered again until it ages out
        _match_kick_refill(db)

        now = time.time()
        for k, v in list(_match_runs.items()):   # expire old runs + one run per player
            if now - v["touched"] > MATCH_RUN_TTL or v["uid"] == uid:
                _match_runs.pop(k, None)
        while len(_match_runs) >= MATCH_MAX_RUNS:
            _match_runs.pop(min(_match_runs, key=lambda k: _match_runs[k]["touched"]), None)

        cards = []
        for cid, _t in picked:
            g = db["global_cards"].get(cid, {})
            cards.append({"name": str(g.get("name", "Card")), "rarity": str(g.get("rarity", "Common")),
                          "anime": str(g.get("anime", "Unknown"))})
        tiles = list(range(MATCH_PAIRS)) * 2
        random.shuffle(tiles)   # tiles[i] = which card sits on tile i (never sent to the client)

        run = secrets.token_hex(8)
        _match_runs[run] = {
            "uid": uid, "started": now, "touched": now, "begun": False,
            "tiles": tiles, "cards": cards, "matched": set(), "open": None,
            "moves": 0, "flips": 0,
        }
        return {
            "ok": True, "run": run, "pairs": MATCH_PAIRS, "tiles": len(tiles),
            "pics": ["data:image/jpeg;base64," + base64.b64encode(t).decode() for _c, t in picked],
            "tiers": [[s, p] for s, p in MATCH_REWARD_TIERS],
        }
    except Exception as e:
        print(f"[match_web_start] {e}")
        dlog.error(f"[match_web_start] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't build the board.")


@deck_api.post("/match/begin")
async def match_web_begin(req: MatchReq):
    """Client calls this once, when the board is on screen: that is when the clock starts.
    Calling it again does nothing, so the clock can't be reset mid-game."""
    u = _match_web_auth(req)
    run = _match_web_run(req, u)
    if not run["begun"]:
        run["begun"] = True
        run["started"] = time.time()
    return {"ok": True}


@deck_api.post("/match/flip")
async def match_web_flip(req: MatchReq):
    u = _match_web_auth(req)
    run = _match_web_run(req, u)
    tiles, n = run["tiles"], len(run["tiles"])
    if not run["begun"]:
        raise HTTPException(status_code=400, detail="Game not started.")
    if not 0 <= req.index < n:
        raise HTTPException(status_code=400, detail="Bad tile.")
    run["flips"] += 1
    if run["flips"] > MATCH_MAX_FLIPS:
        _match_runs.pop(req.run, None)
        raise HTTPException(status_code=400, detail="Too many flips.")

    i = req.index
    if i in run["matched"] or i == run["open"]:   # double tap on a tile that's already up
        return {"ok": False, "error": "already"}

    # First tile of a pair: just show it.
    if run["open"] is None:
        run["open"] = i
        return {"ok": True, "pic": tiles[i], "second": False}

    # Second tile: this is one move.
    j, run["open"] = run["open"], None
    run["moves"] += 1
    if tiles[i] != tiles[j]:
        return {"ok": True, "pic": tiles[i], "second": True, "match": False, "a": j, "b": i, "done": False}

    run["matched"].update((i, j))
    if len(run["matched"]) < n:
        return {"ok": True, "pic": tiles[i], "second": True, "match": True, "a": j, "b": i, "done": False}

    # Last pair found: stop the clock and pay out.
    _match_runs.pop(req.run, None)
    try:
        elapsed = time.time() - run["started"]
        if elapsed < MATCH_WEB_MIN_SECONDS:
            raise HTTPException(status_code=400, detail="Too fast.")
        earned = _match_reward_for(elapsed)
        paid = _match_settle(str(u["id"]), u.get("first_name", "User"), u.get("username"),
                             elapsed, earned, run["moves"], run["cards"])
        return {"ok": True, "pic": tiles[i], "second": True, "match": True, "a": j, "b": i, "done": True,
                "earned": earned, "paid": paid, "capped": earned > 0 and paid < earned,
                "time": round(elapsed, 2), "moves": run["moves"], "cards": run["cards"]}
    except HTTPException:
        raise
    except Exception as e:
        print(f"[match_web_flip] {e}")
        dlog.error(f"[match_web_flip] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't save the result.")


@deck_api.post("/match/giveup")
async def match_web_giveup(req: MatchReq):
    """Reveal the cards. No shards."""
    u = _match_web_auth(req)
    run = _match_web_run(req, u, pop=True)
    return {"ok": True, "cards": run["cards"]}


@deck_api.post("/match/avatar")
async def match_web_avatar(req: MatchReq):
    """Same profile-picture fallback Scramble uses (shares its cache)."""
    _match_web_auth(req)
    return await scramble_web_avatar(ScrWebReq(init_data=req.init_data))


# ==========================================
# /match — opens the Mini App
# ==========================================
@main_router.message(Command("match"))
async def match_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        _scr_url_btn("Play Match", MATCH_WEB_LINK, "primary")]])
    text = (
        "<b>「 MATCH 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Flip the cards and find every matching pair!\n"
        "Under 30 sec : <b>50</b> Shards\nUnder 60 sec : <b>25</b> Shards\n"
        "━━━━━━━━━━━━━━━━━\n<i>Tap the button to open the Mini App.</i>"
    )
    try:
        await message.reply_photo(photo=MATCH_IMAGE, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:   # image unreachable: still give the button
        dlog.error(f"[match_cmd_photo] {e}", exc_info=True)
        await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)


# ==========================================
# /match_lbd — LEADERBOARD
# ==========================================
MATCH_LB_TABS = {"time": "Best Time", "moves": "Fewest Moves", "rounds": "Rounds", "shards": "Total Shards"}
MATCH_LB_TITLES = {"time": "FASTEST TIME", "moves": "FEWEST MOVES", "rounds": "ROUNDS CLEARED",
                   "shards": "TOTAL SHARDS"}
_MATCH_LOWER_WINS = ("time", "moves")


def _match_board(db: dict, tab: str):
    """[(value, uid, name)] best first. Time / Moves: lowest wins; Rounds / Shards: highest wins."""
    key = {"time": "best_time", "moves": "best_moves", "rounds": "rounds", "shards": "shards"}[tab]
    rows = []
    for uid, u in (db.get("users") or {}).items():
        rec = u.get("match") if isinstance(u, dict) else None
        if not isinstance(rec, dict):
            continue
        v = rec.get(key)
        if v and v > 0:
            rows.append((v, str(uid), str(u.get("name") or "User")[:24]))
    if tab in _MATCH_LOWER_WINS:
        rows.sort(key=lambda r: (r[0], r[1]))
    else:
        rows.sort(key=lambda r: (-r[0], r[1]))
    return rows


def _match_fmt_value(tab: str, v) -> str:
    if tab == "time":
        return _scramble_fmt_best(v)
    if tab == "moves":
        return f"{int(v)} move" + ("" if int(v) == 1 else "s")
    if tab == "rounds":
        return f"{int(v):,} round" + ("" if int(v) == 1 else "s")
    return f"{int(v):,} shards"


def _match_lb_text(db: dict, tab: str, uid) -> str:
    rows = _match_board(db, tab)
    text = f"<b>「 MATCH - {MATCH_LB_TITLES[tab]} 」</b>\n━━━━━━━━━━━━━━━━━\n"
    if rows:
        text += "\n".join(
            f"<b>{i + 1}.</b> <b>{_html_esc(name[:18])}</b> - {_match_fmt_value(tab, v)}"
            for i, (v, _u, name) in enumerate(rows[:10])
        )
    else:
        text += "Nobody has cleared a match board yet. Be the first with /match"
    text += "\n━━━━━━━━━━━━━━━━━\n"
    me = str(uid)
    idx = next((i for i, r in enumerate(rows) if r[1] == me), None)
    if idx is None:
        text += "<b>Your rank:</b> Unranked"
    else:
        text += f"<b>Your rank:</b> #{idx + 1} with {_match_fmt_value(tab, rows[idx][0])}"
    return text


def _match_lb_kb(owner, active: str) -> InlineKeyboardMarkup:
    def btn(tab):
        return _scr_btn(MATCH_LB_TABS[tab], f"mtlb:{tab}:{owner}",
                        "success" if tab == active else "primary")
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("time"), btn("moves")],
        [btn("rounds"), btn("shards")],
    ])


@deck_api.post("/match/lb")
async def match_web_lb(req: MatchReq):
    """Top 10 + the caller's own rank for one tab (time / moves / rounds / shards)."""
    u = _match_web_auth(req)
    if req.tab not in MATCH_LB_TABS:
        raise HTTPException(status_code=400, detail="Bad tab.")
    db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    rows = _match_board(db, req.tab)
    me = next((i for i, x in enumerate(rows) if x[1] == str(u["id"])), None)
    return {
        "ok": True,
        "rows": [{"name": n, "value": _match_fmt_value(req.tab, v)} for v, _u, n in rows[:10]],
        "me": None if me is None else {"rank": me + 1, "value": _match_fmt_value(req.tab, rows[me][0])}}


@main_router.message(Command("match_lbd"))
async def match_lbd_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    try:
        db = ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
        text = _match_lb_text(db, "time", uid_int)
        kb = _match_lb_kb(uid_int, "time")
        try:   # banner image with the leaderboard as its caption
            await message.reply_photo(photo=MATCH_LBD_IMAGE, caption=text,
                                      reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception as e:   # image unreachable: still show the leaderboard as text
            dlog.error(f"[match_lbd_photo] {e}", exc_info=True)
            await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[match_lbd_CRASH] {e}")
        traceback.print_exc()
        dlog.error(f"[match_lbd_CRASH] {e}", exc_info=True)
        await message.reply("The leaderboard is unavailable right now. Please try again in a moment.")


@main_router.callback_query(F.data.startswith("mtlb:"))
async def match_lbd_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id): return
    try:
        _, tab, owner = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return
    if tab not in MATCH_LB_TABS:
        await cq.answer()
        return
    if str(cq.from_user.id) != owner:
        await cq.answer("This leaderboard belongs to someone else. Send /match_lbd for your own.", show_alert=True)
        return
    try:
        db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
        text = _match_lb_text(db, tab, cq.from_user.id)
        kb = _match_lb_kb(owner, tab)
        if cq.message.photo:   # banner image: the leaderboard lives in the caption
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:                  # text-only fallback message
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[match_lbd_cb] failed: {e}")
            dlog.error(f"[match_lbd_cb] failed: {e}", exc_info=True)
    await cq.answer()
