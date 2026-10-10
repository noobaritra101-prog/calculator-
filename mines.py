import asyncio
import hashlib
import hmac
import json
import os
import random
import time
from urllib.parse import parse_qsl
from datetime import date
from typing import Dict, Any

from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel

from config import main_router, load_db, save_db, ensure_user, ADMIN_IDS
from vlog import log_action

# ==========================================
# SETTINGS
# ==========================================
BOARD_SIZE = 25            # fixed 5x5 board
MIN_MINES = 3              # Min bomb count
MAX_MINES = 23             # Max bomb count
MIN_BET = 10
MAX_BET = 30000            # Max bet 30,000 Shards
HOUSE_EDGE_PCT = 0.15      # Disclosed flat house edge
MAX_MULTIPLIER = 20.0      # Multiplier ceiling
MIN_CASHOUT_GEMS = 3       # Gems needed to unlock cash out
GAME_TIMEOUT = 600         # 10 minutes limit in seconds

DEFAULT_WEBAPP_URL = "https://famous-centaur-493f76.netlify.app"

GEM_EMOJI = "💎"
BOMB_EMOJI = "💣"
BOOM_EMOJI = "💥"
HIDDEN_TILE = "•"

# ------------------------------------------
# RUBBER-BAND DDA CONFIGURATION
# ------------------------------------------
TARGET_NET = 0
RECOVERY_SCALE = 5000

# In-memory active round state, keyed by str(user_id).
active_games: dict = {}

# Telegram Mini App auth. Set BOT_TOKEN in your environment to enforce it.
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
INITDATA_MAX_AGE = 86400


def verify_init_data(init_data: str, uid: str) -> None:
    """Rejects requests whose Telegram initData is missing, forged, stale or for another user."""
    if not BOT_TOKEN:
        return  # verification stays off until BOT_TOKEN is configured
    try:
        pairs = dict(parse_qsl(init_data or "", keep_blank_values=True))
        got = pairs.pop("hash", "")
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not got or not hmac.compare_digest(calc, got):
            raise ValueError("bad hash")
        if time.time() - int(pairs.get("auth_date", "0")) > INITDATA_MAX_AGE:
            raise ValueError("stale")
        if str(json.loads(pairs["user"])["id"]) != str(uid):
            raise ValueError("uid mismatch")
    except Exception:
        raise HTTPException(status_code=401, detail="Session invalid. Reopen the Mini App from Telegram.")


def expire_game(uid: str, game: dict) -> None:
    """Ends a timed-out round: the bet is forfeited and counted as house take."""
    active_games.pop(uid, None)
    db = load_db()
    gs = db.setdefault("mines_global", {})
    gs["total_taken"] = gs.get("total_taken", 0) + game["bet"]
    save_db()

# FastAPI Router for Web Mini App
mines_router = APIRouter(prefix="/api/mines", tags=["Mines Web App"])


# ==========================================
# PYDANTIC SCHEMAS (FOR REST API)
# ==========================================
class StartGameReq(BaseModel):
    user_id: str
    bet: int
    mines: int
    init_data: str = ""

class RevealTileReq(BaseModel):
    user_id: str
    tile_index: int
    init_data: str = ""

class CashoutReq(BaseModel):
    user_id: str
    init_data: str = ""


# ==========================================
# GAME MATH & HELPER FUNCTIONS
# ==========================================
def fair_multiplier(mines: int, gems_found: int) -> float:
    """Calculates fair-odds multiplier minus house edge, capped at MAX_MULTIPLIER."""
    if gems_found <= 0:
        return 1.0
    safe_tiles = BOARD_SIZE - mines
    prob_survive = 1.0
    for i in range(gems_found):
        prob_survive *= (safe_tiles - i) / (BOARD_SIZE - i)
    fair = 1 / prob_survive
    final = fair * (1 - HOUSE_EDGE_PCT)
    return min(final, MAX_MULTIPLIER)


def generate_board(mines: int) -> list:
    """Returns a 25-length list, True = mine, False = safe gem tile."""
    board = [False] * BOARD_SIZE
    for pos in random.sample(range(BOARD_SIZE), mines):
        board[pos] = True
    return board


def apply_dda_balancing(uid: str, idx: int, game: dict) -> None:
    """
    Applies Dynamic Difficulty Balancing (DDA) on tile reveals for BOTH Bot and Web.
      1. High bet scaling
      2. Rich player correction (> 80,000 Shards balance)
      3. Personal net profit surplus rubber-band correction
    """
    bet, board = game["bet"], game["board"]
    db = load_db()
    user_data = db["users"].get(uid, {})
    shards = user_data.get("nexus_shards", 0)
    mines_bet = user_data.get("mines_bet", 0)
    mines_won = user_data.get("mines_won", 0)
    net_profit = mines_won - mines_bet

    # Only balance from the 4th tap onwards (gems_found >= 3)
    if not board[idx] and game["gems_found"] >= 3:
        # 1. Bet Scaling (adds up to 60% probability at 30k bet)
        bet_contribution = (bet / MAX_BET) * 0.60
        
        # 2. Rich player correction (> 80k balance)
        balance_contribution = 0.50 if shards > 80000 else 0.0
        
        # 3. Personal profit surplus rubber-band recovery
        profit_contribution = max(0.0, net_profit / RECOVERY_SCALE) if net_profit > TARGET_NET else 0.0

        force_prob = bet_contribution + balance_contribution + profit_contribution

        if bet_contribution > 0.05 or balance_contribution > 0 or profit_contribution > 0:
            force_prob = min(0.90, force_prob)  # Cap forced loss chance at 90%
            if random.random() < force_prob:
                unrevealed_mines = [i for i in range(BOARD_SIZE) if board[i] and i not in game["revealed"]]
                if unrevealed_mines:
                    swap_idx = random.choice(unrevealed_mines)
                    board[idx] = True
                    board[swap_idx] = False


# ==========================================
# BOT TELEGRAM KEYBOARDS & MESSAGES
# ==========================================
def styled_button(text: str, callback_data: str, style: str = None) -> InlineKeyboardButton:
    """Inline button with an optional Telegram colour style ('success' = green, 'danger' = red, 'primary' = blue).
    Falls back to a plain button if the installed aiogram version doesn't support styles."""
    if style:
        try:
            return InlineKeyboardButton(text=text, callback_data=callback_data, style=style)
        except Exception:
            pass
    return InlineKeyboardButton(text=text, callback_data=callback_data)


def build_keyboard(uid: str, board: list, revealed: set, boom_at=None, game_over=False, can_cash_out=False) -> InlineKeyboardMarkup:
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx == boom_at:
                # The bomb that was clicked
                row.append(styled_button(BOOM_EMOJI, "mnoop", "danger"))
            elif game_over:
                if board[idx]:
                    # Every bomb placement is shown in red
                    row.append(styled_button(BOMB_EMOJI, "mnoop", "danger"))
                elif idx in revealed:
                    # Gems the player found stay green
                    row.append(styled_button(GEM_EMOJI, "mnoop", "success"))
                else:
                    # Gems the player never reached stay neutral
                    row.append(styled_button(GEM_EMOJI, "mnoop"))
            elif idx in revealed:
                row.append(styled_button(BOMB_EMOJI if board[idx] else GEM_EMOJI, "mnoop", "danger" if board[idx] else "success"))
            else:
                row.append(styled_button(HIDDEN_TILE, f"mtile_{uid}_{idx}"))
        rows.append(row)

    if not game_over:
        # Always visible: red while locked, green once cash out is unlocked
        rows.append([styled_button("Cash Out", f"mcash_{uid}", "success" if can_cash_out else "danger")])

    return InlineKeyboardMarkup(inline_keyboard=rows)


def build_status_text(bet: int, mines: int, gems_found: int, current_mult: float) -> str:
    if gems_found < MIN_CASHOUT_GEMS:
        remaining = MIN_CASHOUT_GEMS - gems_found
        unlock_note = f"\n🔒 <b>Cash Out unlocks in:</b> {remaining} more reveal{'s' if remaining != 1 else ''}"
    else:
        unlock_note = "\n🔓 <b>Cash Out unlocked!</b>"

    return (
        "<b>「 💣 MINES 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet:</b> {bet} 💠\n"
        f"💣 <b>Mines:</b> {mines}\n"
        f"💎 <b>Gems Found:</b> {gems_found}\n"
        f"📈 <b>Current Multiplier:</b> {current_mult:.2f}x\n"
        f"✅ <b>Cash Out Value:</b> {int(bet * current_mult)} 💠"
        f"{unlock_note}\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<i>Tap a tile to reveal it.</i>"
    )


def build_win_text(bet: int, mines: int, gems_found: int, final_mult: float, payout: int) -> str:
    return (
        "<b>「 🎉 CASHED OUT! 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet:</b> {bet} 💠\n"
        f"💣 <b>Mines:</b> {mines}\n"
        f"💎 <b>Gems Found:</b> {gems_found}\n"
        f"📈 <b>Final Multiplier:</b> {final_mult:.2f}x\n"
        f"✅ <b>Payout:</b> +{payout} 💠\n"
        "━━━━━━━━━━━━━━━━━"
    )


def build_loss_text(bet: int, mines: int, gems_found: int) -> str:
    return (
        "<b>「 💥 BOOM! YOU HIT A MINE! 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet Lost:</b> {bet} 💠\n"
        f"💣 <b>Mines:</b> {mines}\n"
        f"💎 <b>Gems Found:</b> {gems_found}\n"
        "━━━━━━━━━━━━━━━━━"
    )


async def edit_game_message(cq: CallbackQuery, text: str, reply_markup: InlineKeyboardMarkup):
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text=text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
    except Exception:
        pass


# ==========================================
# REST API ENDPOINTS (FOR WEB MINI APP)
# ==========================================
@mines_router.get("/state/{user_id}")
async def api_get_state(user_id: str, init_data: str = ""):
    verify_init_data(init_data, user_id)
    db = load_db()
    ensure_user(user_id, "User", None)
    user_data = db["users"].get(user_id, {})
    balance = user_data.get("nexus_shards", 0)

    game = active_games.get(str(user_id))
    if not game:
        return {"balance": balance, "active": False}

    if time.time() - game["start_time"] > GAME_TIMEOUT:
        active_games.pop(str(user_id), None)
        global_stats = db.setdefault("mines_global", {})
        global_stats["total_taken"] = global_stats.get("total_taken", 0) + game["bet"]
        save_db()
        return {"balance": balance, "active": False}

    current_mult = fair_multiplier(game["mines"], game["gems_found"])
    cashout_val = int(game["bet"] * current_mult)
    can_cash = game["gems_found"] >= MIN_CASHOUT_GEMS

    revealed_map = {idx: ("mine" if game["board"][idx] else "gem") for idx in game["revealed"]}

    return {
        "balance": balance,
        "active": True,
        "current_mult": current_mult,
        "cashout_value": cashout_val,
        "can_cash_out": can_cash,
        "gems_found": game["gems_found"],
        "bet": game["bet"],
        "mines": game["mines"],
        "revealed": revealed_map
    }


@mines_router.post("/start")
async def api_start_game(req: StartGameReq):
    uid = str(req.user_id)
    verify_init_data(req.init_data, uid)
    db = load_db()
    ensure_user(uid, "User", None)

    if uid in active_games:
        game = active_games[uid]
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            active_games.pop(uid, None)
            global_stats = db.setdefault("mines_global", {})
            global_stats["total_taken"] = global_stats.get("total_taken", 0) + game["bet"]
            save_db()
        else:
            raise HTTPException(status_code=400, detail="Active round already in progress!")

    if req.bet < MIN_BET or req.bet > MAX_BET:
        raise HTTPException(status_code=400, detail=f"Bet must be between {MIN_BET} and {MAX_BET:,} 💠")
    if req.mines < MIN_MINES or req.mines > MAX_MINES:
        raise HTTPException(status_code=400, detail=f"Mines must be between {MIN_MINES} and {MAX_MINES}")

    user_data = db["users"][uid]
    if user_data.get("nexus_shards", 0) < req.bet:
        raise HTTPException(status_code=400, detail="Insufficient Shards for this bet.")

    user_data["nexus_shards"] -= req.bet
    user_data["mines_bet"] = user_data.get("mines_bet", 0) + req.bet

    global_stats = db.setdefault("mines_global", {})
    global_stats["total_bet"] = global_stats.get("total_bet", 0) + req.bet
    global_stats["total_games"] = global_stats.get("total_games", 0) + 1

    today_str = date.today().isoformat()
    daily_games = global_stats.setdefault("daily_games", {})
    daily_games[today_str] = daily_games.get(today_str, 0) + 1
    save_db()

    board = generate_board(req.mines)
    active_games[uid] = {
        "bet": req.bet,
        "mines": req.mines,
        "board": board,
        "revealed": set(),
        "gems_found": 0,
        "safe_tiles": BOARD_SIZE - req.mines,
        "lock": asyncio.Lock(),
        "start_time": time.time(),
    }

    return {"balance": user_data["nexus_shards"]}


@mines_router.post("/reveal")
async def api_reveal_tile(req: RevealTileReq):
    uid = str(req.user_id)
    verify_init_data(req.init_data, uid)
    game = active_games.get(uid)
    if not game:
        raise HTTPException(status_code=400, detail="No active round found.")

    idx = req.tile_index
    if idx < 0 or idx >= BOARD_SIZE:
        raise HTTPException(status_code=400, detail="Invalid tile index.")

    async with game["lock"]:
        # A queued request can wake up after the round already ended (e.g. mine hit) - never act on a dead round.
        if active_games.get(uid) is not game:
            raise HTTPException(status_code=400, detail="No active round found.")
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            expire_game(uid, game)
            raise HTTPException(status_code=400, detail="Round expired.")
        if idx in game["revealed"]:
            raise HTTPException(status_code=400, detail="Tile already revealed.")

        apply_dda_balancing(uid, idx, game)
        db = load_db()

        # HIT MINE
        if game["board"][idx]:
            game["revealed"].add(idx)
            active_games.pop(uid, None)

            global_stats = db.setdefault("mines_global", {})
            global_stats["total_taken"] = global_stats.get("total_taken", 0) + game["bet"]
            save_db()

            full_board = ["mine" if b else "gem" for b in game["board"]]
            return {
                "result": "mine",
                "full_board": full_board,
                "boom_at": idx,
                "bet": game["bet"],
                "balance": db["users"][uid].get("nexus_shards", 0)
            }

        # SAFE GEM FOUND
        game["revealed"].add(idx)
        game["gems_found"] += 1
        current_mult = fair_multiplier(game["mines"], game["gems_found"])

        # BOARD CLEARED AUTO-WIN
        if game["gems_found"] >= game["safe_tiles"]:
            payout = int(game["bet"] * current_mult)
            net_profit_round = payout - game["bet"]

            db["users"][uid]["nexus_shards"] = db["users"][uid].get("nexus_shards", 0) + payout
            db["users"][uid]["mines_won"] = db["users"][uid].get("mines_won", 0) + payout

            global_stats = db.setdefault("mines_global", {})
            global_stats["total_won"] = global_stats.get("total_won", 0) + net_profit_round
            save_db()

            log_action(db, uid, {
                "type": "mines_win",
                "amount": payout,
                "bet": game["bet"],
                "mines": game["mines"],
                "gems_found": game["gems_found"],
                "multiplier": current_mult,
                "chat_title": "Mines WebApp"
            })

            full_board = ["mine" if b else "gem" for b in game["board"]]
            active_games.pop(uid, None)

            return {
                "result": "cleared",
                "payout": payout,
                "bet": game["bet"],
                "full_board": full_board,
                "balance": db["users"][uid].get("nexus_shards", 0)
            }

        cashout_val = int(game["bet"] * current_mult)
        can_cash = game["gems_found"] >= MIN_CASHOUT_GEMS

        return {
            "result": "gem",
            "current_mult": current_mult,
            "cashout_value": cashout_val,
            "can_cash_out": can_cash,
            "gems_found": game["gems_found"]
        }


@mines_router.post("/cashout")
async def api_cashout(req: CashoutReq):
    uid = str(req.user_id)
    verify_init_data(req.init_data, uid)
    game = active_games.get(uid)
    if not game:
        raise HTTPException(status_code=400, detail="No active round found.")

    async with game["lock"]:
        if active_games.get(uid) is not game:
            raise HTTPException(status_code=400, detail="No active round found.")
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            expire_game(uid, game)
            raise HTTPException(status_code=400, detail="Round expired.")
        if game["gems_found"] < MIN_CASHOUT_GEMS:
            raise HTTPException(status_code=400, detail="Must reveal at least 3 gems before cashing out.")

        current_mult = fair_multiplier(game["mines"], game["gems_found"])
        payout = int(game["bet"] * current_mult)
        net_profit_round = payout - game["bet"]

        db = load_db()
        db["users"][uid]["nexus_shards"] = db["users"][uid].get("nexus_shards", 0) + payout
        db["users"][uid]["mines_won"] = db["users"][uid].get("mines_won", 0) + payout

        global_stats = db.setdefault("mines_global", {})
        global_stats["total_won"] = global_stats.get("total_won", 0) + net_profit_round
        save_db()

        log_action(db, uid, {
            "type": "mines_win",
            "amount": payout,
            "bet": game["bet"],
            "mines": game["mines"],
            "gems_found": game["gems_found"],
            "multiplier": current_mult,
            "chat_title": "Mines WebApp"
        })

        full_board = ["mine" if b else "gem" for b in game["board"]]
        active_games.pop(uid, None)

        return {
            "payout": payout,
            "bet": game["bet"],
            "full_board": full_board,
            "balance": db["users"][uid].get("nexus_shards", 0)
        }


# ==========================================
# /webmine COMMAND (OPENS MINI APP)
# ==========================================
@main_router.message(Command("webmine"))
async def webmine_cmd(message: Message):
    uid = str(message.from_user.id)
    db = load_db()
    ensure_user(uid, message.from_user.first_name, message.from_user.username)

    keyboard = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="💣 Open Mines Mini App",
                    url="http://t.me/Animenx_bot/webmine"
                )
            ]
        ]
    )

    await message.reply(
        "<b>「 💣 MINES WEB MINI APP 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Click the button below to launch the Mini App interface and play Mines seamlessly!",
        reply_markup=keyboard,
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /mines COMMAND (INLINE BUTTON GAME)
# ==========================================
@main_router.message(Command("mines"))
async def mines_cmd(message: Message, command: CommandObject):
    uid = str(message.from_user.id)
    db = load_db()
    ensure_user(uid, message.from_user.first_name, message.from_user.username)

    if uid in active_games:
        game = active_games[uid]
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            active_games.pop(uid, None)
            global_stats = db.setdefault("mines_global", {})
            global_stats["total_taken"] = global_stats.get("total_taken", 0) + game["bet"]
            save_db()
        else:
            await message.reply("⚠️ You already have an active round in progress.", parse_mode=ParseMode.HTML)
            return

    args = (command.args or "").split()
    if len(args) != 2:
        await message.reply(
            "<b>「 💣 MINES — HOW TO PLAY 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            f"<b>Usage:</b> <code>/mines &lt;bet&gt; &lt;mines&gt;</code>\n"
            f"<b>Example:</b> <code>/mines 50 3</code>\n\n"
            f"💡 Or play the Mini App: <code>/webmine</code>\n\n"
            f"Bet: {MIN_BET} – {MAX_BET:,} 💠\n"
            f"💣 Mines: {MIN_MINES} – {MAX_MINES} (on a 25-tile board)",
            parse_mode=ParseMode.HTML
        )
        return

    try:
        bet = int(args[0])
        mines = int(args[1])
    except ValueError:
        await message.reply("Bet and mines must both be whole numbers.", parse_mode=ParseMode.HTML)
        return

    if bet < MIN_BET or bet > MAX_BET:
        await message.reply(f"Bet must be between {MIN_BET} and {MAX_BET:,} Shards 💠.", parse_mode=ParseMode.HTML)
        return
    if mines < MIN_MINES or mines > MAX_MINES:
        await message.reply(f"Mines must be between {MIN_MINES} and {MAX_MINES}.", parse_mode=ParseMode.HTML)
        return

    user_data = db["users"][uid]
    if user_data.get("nexus_shards", 0) < bet:
        await message.reply("You don't have enough Shards for that bet.", parse_mode=ParseMode.HTML)
        return

    user_data["nexus_shards"] -= bet
    user_data["mines_bet"] = user_data.get("mines_bet", 0) + bet

    global_stats = db.setdefault("mines_global", {})
    global_stats["total_bet"] = global_stats.get("total_bet", 0) + bet
    global_stats["total_games"] = global_stats.get("total_games", 0) + 1

    today_str = date.today().isoformat()
    daily_games = global_stats.setdefault("daily_games", {})
    daily_games[today_str] = daily_games.get(today_str, 0) + 1
    save_db()

    board = generate_board(mines)
    active_games[uid] = {
        "bet": bet,
        "mines": mines,
        "board": board,
        "revealed": set(),
        "gems_found": 0,
        "safe_tiles": BOARD_SIZE - mines,
        "lock": asyncio.Lock(),
        "chat_id": message.chat.id,
        "start_time": time.time(),
    }

    mines_image = db.get("settings", {}).get("mines_image")
    status_text = build_status_text(bet, mines, 0, 1.0)
    reply_markup = build_keyboard(uid, board, set(), can_cash_out=False)

    if mines_image:
        try:
            await message.reply_photo(photo=mines_image, caption=status_text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
        except Exception:
            await message.reply(text=status_text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
    else:
        await message.reply(text=status_text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)


# ==========================================
# BOT TILE TAP CALLBACK
# ==========================================
@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("mtile_"))
async def mines_tile_cb(cq: CallbackQuery):
    _, owner_id, idx_str = cq.data.split("_")
    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your round!", show_alert=True)
        return

    game = active_games.get(owner_id)
    if not game:
        await cq.answer("This round has already ended.", show_alert=True)
        return

    idx = int(idx_str)

    async with game["lock"]:
        if active_games.get(owner_id) is not game:
            await cq.answer("This round has already ended.", show_alert=True)
            return
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            expire_game(owner_id, game)
            await cq.answer("This round expired.", show_alert=True)
            return
        if idx in game["revealed"]:
            await cq.answer()
            return

        bet, mines, board = game["bet"], game["mines"], game["board"]
        apply_dda_balancing(owner_id, idx, game)

        # HIT MINE
        if board[idx]:
            game["revealed"].add(idx)
            active_games.pop(owner_id, None)

            db = load_db()
            global_stats = db.setdefault("mines_global", {})
            global_stats["total_taken"] = global_stats.get("total_taken", 0) + bet
            save_db()

            await cq.answer("💥 Boom!", show_alert=False)
            await edit_game_message(
                cq,
                build_loss_text(bet, mines, game["gems_found"]),
                build_keyboard(owner_id, board, game["revealed"], boom_at=idx, game_over=True)
            )
            return

        # SAFE GEM
        game["revealed"].add(idx)
        game["gems_found"] += 1
        current_mult = fair_multiplier(mines, game["gems_found"])

        # BOARD CLEARED
        if game["gems_found"] >= game["safe_tiles"]:
            payout = int(bet * current_mult)
            net_profit_round = payout - bet

            db = load_db()
            db["users"][owner_id]["nexus_shards"] = db["users"][owner_id].get("nexus_shards", 0) + payout
            db["users"][owner_id]["mines_won"] = db["users"][owner_id].get("mines_won", 0) + payout

            global_stats = db.setdefault("mines_global", {})
            global_stats["total_won"] = global_stats.get("total_won", 0) + net_profit_round

            save_db()

            log_action(db, owner_id, {
                "type": "mines_win",
                "amount": payout,
                "bet": bet,
                "mines": mines,
                "gems_found": game["gems_found"],
                "multiplier": current_mult,
                "chat_id": cq.message.chat.id,
                "chat_title": cq.message.chat.title or cq.message.chat.first_name or "DM"
            })

            active_games.pop(owner_id, None)
            await cq.answer("🎉 Board cleared!", show_alert=False)
            await edit_game_message(
                cq,
                build_win_text(bet, mines, game["gems_found"], current_mult, payout),
                build_keyboard(owner_id, board, game["revealed"], game_over=True)
            )
            return

        await cq.answer()
        await edit_game_message(
            cq,
            build_status_text(bet, mines, game["gems_found"], current_mult),
            build_keyboard(owner_id, board, game["revealed"], can_cash_out=game["gems_found"] >= MIN_CASHOUT_GEMS)
        )


# ==========================================
# BOT CASH OUT CALLBACK
# ==========================================
@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("mcash_"))
async def mines_cashout_cb(cq: CallbackQuery):
    owner_id = cq.data.split("_")[1]
    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your round!", show_alert=True)
        return

    game = active_games.get(owner_id)
    if not game:
        await cq.answer("This round has already ended.", show_alert=True)
        return

    async with game["lock"]:
        if active_games.get(owner_id) is not game:
            await cq.answer("This round has already ended.", show_alert=True)
            return
        if time.time() - game["start_time"] > GAME_TIMEOUT:
            expire_game(owner_id, game)
            await cq.answer("This round expired.", show_alert=True)
            return
        if game["gems_found"] < MIN_CASHOUT_GEMS:
            remaining = MIN_CASHOUT_GEMS - game["gems_found"]
            await cq.answer(f"Reveal {remaining} more tile{'s' if remaining != 1 else ''} before cashing out!", show_alert=True)
            return

        bet, mines, board = game["bet"], game["mines"], game["board"]
        final_mult = fair_multiplier(mines, game["gems_found"])
        payout = int(bet * final_mult)
        net_profit_round = payout - bet

        db = load_db()
        db["users"][owner_id]["nexus_shards"] = db["users"][owner_id].get("nexus_shards", 0) + payout
        db["users"][owner_id]["mines_won"] = db["users"][owner_id].get("mines_won", 0) + payout

        global_stats = db.setdefault("mines_global", {})
        global_stats["total_won"] = global_stats.get("total_won", 0) + net_profit_round

        save_db()

        log_action(db, owner_id, {
            "type": "mines_win",
            "amount": payout,
            "bet": bet,
            "mines": mines,
            "gems_found": game["gems_found"],
            "multiplier": final_mult,
            "chat_id": cq.message.chat.id,
            "chat_title": cq.message.chat.title or cq.message.chat.first_name or "DM"
        })

        active_games.pop(owner_id, None)

        await cq.answer(f"✅ Cashed out: +{payout} 💠")
        await edit_game_message(
            cq,
            build_win_text(bet, mines, game["gems_found"], final_mult, payout),
            build_keyboard(owner_id, board, game["revealed"], game_over=True)
        )


@main_router.callback_query(lambda cq: cq.data == "mnoop")
async def mines_noop_cb(cq: CallbackQuery):
    await cq.answer()


# ==========================================
# ADMIN COMMANDS
# ==========================================
@main_router.message(Command("gmstats"))
async def gmstats_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    db = load_db()
    global_stats = db.get("mines_global", {})
    total_won = global_stats.get("total_won", 0)
    total_taken = global_stats.get("total_taken", 0)
    total_games = global_stats.get("total_games", 0)

    today_str = date.today().isoformat()
    games_today = global_stats.get("daily_games", {}).get(today_str, 0)

    text = (
        "<b>「 📊 MINES GLOBAL STATS 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"💠 <b>Total Shards Generated -</b> {total_won:,}\n"
        f"<b>Total Shards Taken -</b> {total_taken:,}\n"
        f"🎮 <b>Total Games Played -</b> {total_games:,}\n"
        f"📅 <b>Games Played Today -</b> {games_today:,}\n"
        "━━━━━━━━━━━━━━━━━"
    )
    await message.reply(text, parse_mode=ParseMode.HTML)


@main_router.message(Command("setweb"))
async def setweb_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args:
        await message.reply("⚠️ Usage: <code>/setweb https://your-netlify-url.netlify.app</code>", parse_mode=ParseMode.HTML)
        return

    url = command.args.strip()
    db = load_db()
    db.setdefault("settings", {})["mines_webapp_url"] = url
    save_db()

    await message.reply(f"✅ Mines Web App URL updated to:\n<code>{url}</code>", parse_mode=ParseMode.HTML)


@main_router.message(Command("imm"))
async def imm_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not message.reply_to_message or not message.reply_to_message.photo:
        await message.reply("⚠️ Reply to an image with <code>/imm</code> to set the Mines background photo.", parse_mode=ParseMode.HTML)
        return

    file_id = message.reply_to_message.photo[-1].file_id
    db = load_db()
    db.setdefault("settings", {})["mines_image"] = file_id
    save_db()

    await message.reply("✅ Mines background image saved.", parse_mode=ParseMode.HTML)
