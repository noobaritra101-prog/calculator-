import asyncio
import random
import time
import traceback
from datetime import date
from html import escape as _html_esc

from aiogram import F
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode

from config import main_router, load_db, save_db, ensure_user, ADMIN_IDS, is_ghost_banned, is_shadow_banned
from vlog import log_action

# ==========================================
# SETTINGS
# ==========================================
TREE_LEVEL1_MULTIPLIER = 0.80  # Multiplier at level 1; each next level multiplies by the mode's growth
TREE_MAX_MULTIPLIER = 15.0   # Multiplier ceiling (was 20.0)
TREE_MIN_CASHOUT_STEPS = 3   # Levels needed to unlock cash out
TREE_GAME_TIMEOUT = 600      # 10 minutes limit in seconds

# ------------------------------------------
# RUBBER-BAND DDA CONFIGURATION (same rules as Mines)
# ------------------------------------------
TREE_DDA_START_LEVELS = 3    # Balancing only applies once 3 levels are climbed (from the 4th pick onwards)
TREE_TARGET_NET = 0
TREE_RECOVERY_SCALE = 5000
TREE_BET_FORCE_SCALE = 0.60  # Extra forced-loss chance at the max bet
TREE_RICH_BALANCE = 80000    # Balance above this triggers rich-player correction
TREE_RICH_FORCE = 0.50
TREE_FORCE_CAP = 0.90        # Cap on forced-loss chance

# Modes. Edit the numbers here to change the odds or the bet limits.
#   lanes   = branches (buttons) on every level - the same in every mode
#   height  = levels to reach the golden apple at the top
#   snakes  = number of snakes hiding on each level, one entry per level (so len(snakes) == height)
#   growth  = multiplier growth per level (level 1 is TREE_LEVEL1_MULTIPLIER)
#   min_bet / max_bet = allowed bet range (Shards) for that mode
TREE_MODES = {
    "mid":  {"label": "Mid",  "lanes": 3, "height": 8, "snakes": [1, 1, 1, 1, 2, 2, 2, 2], "growth": 1.5,
             "min_bet": 10,  "max_bet": 10000, "style": "success"},
    "high": {"label": "High", "lanes": 3, "height": 5, "snakes": [2, 2, 2, 2, 2], "growth": 2.0,
             "min_bet": 100, "max_bet": 30000, "style": "danger"},
}
for _m in TREE_MODES.values():
    assert len(_m["snakes"]) == _m["height"], "snakes list must have one entry per level"
    assert all(1 <= n < _m["lanes"] for n in _m["snakes"]), "each level needs at least 1 safe branch"
#   style = mode button colour: green = safer, red = riskier
TREE_PICK_TIMEOUT = 120      # Seconds the player has to choose a mode after /tree

BRANCH_EMOJI = "🌿"      # branch you can tap
CLIMBED_EMOJI = "🍃"     # branch you climbed
TRAP_EMOJI = "🐍"        # snake hiding on a branch
BOOM_EMOJI = "🩸"        # the snake you stepped on
EMPTY_TILE = "•"

TREE_LBD_IMAGE = "https://i.ibb.co/93Stcg3C/IMG-20261011-003453.jpg"   # /tree_lbd banner (caption limit: 1024 chars)

# Bets waiting for a mode choice, keyed by str(user_id). Nothing is charged until a mode is picked.
pending_trees: dict = {}

# In-memory active round state, keyed by str(user_id).
active_trees: dict = {}


# ==========================================
# GAME MATH & HELPERS
# ==========================================
def tree_multiplier(growth: float, steps: int) -> float:
    """Multiplier after `steps` climbed levels: starts at TREE_LEVEL1_MULTIPLIER on level 1 and grows by
    `growth` on every further level, capped at TREE_MAX_MULTIPLIER."""
    if steps <= 0:
        return 1.0
    return min(TREE_LEVEL1_MULTIPLIER * growth ** (steps - 1), TREE_MAX_MULTIPLIER)


def tree_snake_summary(snakes: list) -> str:
    """e.g. '1 snake (levels 1–4) then 2 snakes (levels 5–8)' or '2 snakes per level'."""
    runs = []
    for lvl, n in enumerate(snakes, 1):
        if runs and runs[-1][0] == n:
            runs[-1][2] = lvl
        else:
            runs.append([n, lvl, lvl])
    word = lambda n: f"{n} snake{'s' if n != 1 else ''}"
    if len(runs) == 1:
        return f"{word(runs[0][0])} per level"
    return " then ".join(
        f"{word(n)} ({'level ' + str(a) if a == b else f'levels {a}–{b}'})" for n, a, b in runs
    )


def tree_snake_short(snakes: list) -> str:
    """e.g. '1→2 snakes' or '2 snakes' (for button labels)."""
    nums = []
    for n in snakes:
        if not nums or nums[-1] != n:
            nums.append(n)
    return f"{'→'.join(map(str, nums))} snake{'' if nums == [1] else 's'}"


def generate_traps(lanes: int, snakes: list) -> list:
    """For every level, the list of branch indexes that hide a snake."""
    return [random.sample(range(lanes), n) for n in snakes]


def tree_apply_dda_balancing(uid: str, row: int, lane: int, game: dict) -> None:
    """
    Dynamic Difficulty Balancing (DDA) on branch picks, same rules as Mines:
      1. High bet scaling
      2. Rich player correction (> TREE_RICH_BALANCE Shards)
      3. Personal net profit surplus rubber-band correction
    When it fires, one of this level's snakes is moved onto the branch the player picked.
    """
    snakes = game["traps"][row]
    if lane in snakes or game["steps"] < TREE_DDA_START_LEVELS:
        return

    db = load_db()
    user_data = db["users"].get(uid, {})
    shards = user_data.get("nexus_shards", 0)
    net_profit = user_data.get("tree_won", 0) - user_data.get("tree_bet", 0)

    # 1. Bet scaling (adds up to TREE_BET_FORCE_SCALE at the max bet)
    bet_contribution = (game["bet"] / tree_bet_limits()[1]) * TREE_BET_FORCE_SCALE

    # 2. Rich player correction
    balance_contribution = TREE_RICH_FORCE if shards > TREE_RICH_BALANCE else 0.0

    # 3. Personal profit surplus rubber-band recovery
    profit_contribution = max(0.0, net_profit / TREE_RECOVERY_SCALE) if net_profit > TREE_TARGET_NET else 0.0

    force_prob = bet_contribution + balance_contribution + profit_contribution

    if bet_contribution > 0.05 or balance_contribution > 0 or profit_contribution > 0:
        force_prob = min(TREE_FORCE_CAP, force_prob)
        if random.random() < force_prob:
            snakes[random.randrange(len(snakes))] = lane


def _tree_inc(t: dict, key: str, n=1) -> None:
    t[key] = t.get(key, 0) + n


def _tree_stat(db: dict, event: str, uid=None, name: str = "", mode: str = "?", bet: int = 0,
               payout: int = 0, steps: int = 0, mult: float = 0.0, apple: bool = False) -> None:
    """Counters for /tstats: one bucket for all time plus one per day (30 days kept), each with a per-mode split.
    events: start | win | loss | expire. A stats error must never block a payout."""
    try:
        root = db.setdefault("tree_stats", {})
        days = root.setdefault("days", {})
        today = days.setdefault(date.today().isoformat(), {})
        for b in (root.setdefault("all", {}), today):
            m = b.setdefault("modes", {}).setdefault(mode, {})
            for t in (b, m):
                if event == "start":
                    _tree_inc(t, "started")
                    _tree_inc(t, "wagered", bet)
                elif event == "win":
                    _tree_inc(t, "wins")
                    _tree_inc(t, "paid", payout)
                    _tree_inc(t, "generated", payout - bet)   # shards created for the player
                    _tree_inc(t, "levels", steps)
                    if apple:
                        _tree_inc(t, "apples")
                    if payout > t.get("biggest_win", 0):
                        t["biggest_win"], t["biggest_win_name"] = payout, name
                    if mult > t.get("best_mult", 0):
                        t["best_mult"] = round(mult, 2)
                elif event == "loss":
                    _tree_inc(t, "losses")
                    _tree_inc(t, "taken", bet)                # shards taken by the house
                    _tree_inc(t, "levels", steps)
                elif event == "expire":
                    _tree_inc(t, "expired")
                    _tree_inc(t, "taken", bet)
        if uid is not None:
            players = today.setdefault("players", [])
            if str(uid) not in players:
                players.append(str(uid))
        for k in sorted(days)[:-30]:
            days.pop(k, None)
    except Exception as e:
        print(f"[tree_stat] {e}")
        traceback.print_exc()


def tree_expire(uid: str, game: dict) -> None:
    """Ends a timed-out round: the bet is forfeited and counted as house take."""
    active_trees.pop(uid, None)
    db = load_db()
    gs = db.setdefault("tree_global", {})
    gs["total_taken"] = gs.get("total_taken", 0) + game["bet"]
    _tree_stat(db, "expire", uid=uid, mode=game["mode"], bet=game["bet"], steps=game["steps"])
    save_db()


def tree_record_loss(game: dict) -> None:
    db = load_db()
    gs = db.setdefault("tree_global", {})
    gs["total_taken"] = gs.get("total_taken", 0) + game["bet"]
    _tree_stat(db, "loss", uid=game.get("uid"), mode=game["mode"], bet=game["bet"], steps=game["steps"])
    save_db()


def tree_credit_win(uid: str, game: dict, mult: float, chat_id, chat_title: str) -> int:
    """Pays the player and updates stats. Returns the payout."""
    bet = game["bet"]
    payout = int(bet * mult)

    db = load_db()
    db["users"][uid]["nexus_shards"] = db["users"][uid].get("nexus_shards", 0) + payout
    db["users"][uid]["tree_won"] = db["users"][uid].get("tree_won", 0) + payout

    gs = db.setdefault("tree_global", {})
    gs["total_won"] = gs.get("total_won", 0) + (payout - bet)

    # Personal record for /tree_lbd
    apple = game["steps"] >= game["height"]
    rec = db["users"][uid].setdefault("tree", {})
    rec["wins"] = rec.get("wins", 0) + 1
    if apple:
        rec["apples"] = rec.get("apples", 0) + 1
    if payout > rec.get("biggest_win", 0):
        rec["biggest_win"] = payout
    if mult > rec.get("best_mult", 0):
        rec["best_mult"] = round(mult, 2)

    _tree_stat(db, "win", uid=uid, name=str(db["users"][uid].get("name") or "User"), mode=game["mode"],
               bet=bet, payout=payout, steps=game["steps"], mult=mult, apple=apple)
    save_db()

    log_action(db, uid, {
        "type": "tree_win",
        "mode": game["mode"],
        "amount": payout,
        "bet": bet,
        "steps": game["steps"],
        "multiplier": mult,
        "chat_id": chat_id,
        "chat_title": chat_title,
    })
    return payout


# ==========================================
# KEYBOARD & MESSAGES
# ==========================================
def tree_button(text: str, callback_data: str, style: str = None) -> InlineKeyboardButton:
    """Inline button with an optional Telegram colour style ('success' green, 'danger' red, 'primary' blue).
    Falls back to a plain button if the installed aiogram version doesn't support styles."""
    if style:
        try:
            return InlineKeyboardButton(text=text, callback_data=callback_data, style=style)
        except Exception:
            pass
    return InlineKeyboardButton(text=text, callback_data=callback_data)


def tree_keyboard(uid: str, lanes: int, height: int, traps: list, picks: list, steps: int,
                    game_over: bool = False, boom=None, can_cash_out: bool = False) -> InlineKeyboardMarkup:
    """
    Draws the tree with the top level first and level 1 at the bottom.
      blue   = the level you are on now (tap a branch)
      green  = branches you climbed
      red    = snakes (only revealed when the round is over)
      neutral = everything else
    """
    rows = []
    for r in range(height - 1, -1, -1):
        row = []
        for c in range(lanes):
            if boom == (r, c):
                row.append(tree_button(BOOM_EMOJI, "trnoop", "danger"))
            elif r < steps:
                if c == picks[r]:
                    row.append(tree_button(CLIMBED_EMOJI, "trnoop", "success"))
                elif game_over and c in traps[r]:
                    row.append(tree_button(TRAP_EMOJI, "trnoop", "danger"))
                else:
                    row.append(tree_button(EMPTY_TILE, "trnoop"))
            elif r == steps and not game_over:
                # row index is in the callback so a stale double-tap can't hit the next level
                row.append(tree_button(BRANCH_EMOJI, f"trstep_{uid}_{r}_{c}", "primary"))
            elif game_over and c in traps[r]:
                row.append(tree_button(TRAP_EMOJI, "trnoop", "danger"))
            else:
                row.append(tree_button(EMPTY_TILE, "trnoop"))
        rows.append(row)

    if not game_over:
        # Always visible: red while locked, green once cash out is unlocked
        rows.append([tree_button("Cash Out", f"trcash_{uid}", "success" if can_cash_out else "danger")])

    return InlineKeyboardMarkup(inline_keyboard=rows)


def tree_status_text(game: dict) -> str:
    bet, height, steps = game["bet"], game["height"], game["steps"]
    cur_mult = tree_multiplier(game["growth"], steps)
    next_mult = tree_multiplier(game["growth"], steps + 1)
    snakes_here = game["snakes"][min(steps, height - 1)]

    if steps < TREE_MIN_CASHOUT_STEPS:
        remaining = TREE_MIN_CASHOUT_STEPS - steps
        unlock_note = f"\n🔒 <b>Cash Out unlocks in:</b> {remaining} more level{'s' if remaining != 1 else ''}"
    else:
        unlock_note = "\n🔓 <b>Cash Out unlocked!</b>"

    return (
        "<b>「 🌳 TREE CLIMB 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet:</b> {bet} 💠\n"
        f"<b>Mode:</b> {game['label']}\n"
        f"<b>Level:</b> {steps}/{height}\n"
        f"📈 <b>Current Multiplier:</b> {cur_mult:.2f}x\n"
        f"⏭ <b>Next Level:</b> {next_mult:.2f}x\n"
        f"✅ <b>Cash Out Value:</b> {int(bet * cur_mult)} 💠"
        f"{unlock_note}\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"🐍 <b>Snakes on this level:</b> {snakes_here} of {game['lanes']} branches\n"
        "<i>Pick a branch to climb. Don't step on a snake!</i>"
    )


def tree_win_text(game: dict, final_mult: float, payout: int, reached_top: bool) -> str:
    title = "🍎 GOLDEN APPLE!" if reached_top else "🎉 CASHED OUT!"
    return (
        f"<b>「 {title} 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet:</b> {game['bet']} 💠\n"
        f"<b>Mode:</b> {game['label']}\n"
        f"<b>Levels Climbed:</b> {game['steps']}/{game['height']}\n"
        f"📈 <b>Final Multiplier:</b> {final_mult:.2f}x\n"
        f"✅ <b>Payout:</b> +{payout} 💠\n"
        "━━━━━━━━━━━━━━━━━"
    )


def tree_loss_text(game: dict) -> str:
    return (
        "<b>「 🐍 A SNAKE BIT YOU! 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet Lost:</b> {game['bet']} 💠\n"
        f"<b>Mode:</b> {game['label']}\n"
        f"<b>Levels Climbed:</b> {game['steps']}/{game['height']}\n"
        "━━━━━━━━━━━━━━━━━"
    )


async def tree_edit_message(cq: CallbackQuery, text: str, reply_markup: InlineKeyboardMarkup):
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text=text, reply_markup=reply_markup, parse_mode=ParseMode.HTML)
    except Exception:
        pass


def _chat_info(cq: CallbackQuery):
    chat = cq.message.chat
    return chat.id, (chat.title or chat.first_name or "DM")


def _final_keyboard(owner_id: str, game: dict, boom=None) -> InlineKeyboardMarkup:
    return tree_keyboard(
        owner_id, game["lanes"], game["height"], game["traps"], game["picks"], game["steps"],
        game_over=True, boom=boom,
    )


# ==========================================
# /tree COMMAND  (bet -> mode buttons -> game)
# ==========================================
def tree_bet_limits() -> tuple:
    """Lowest and highest bet allowed in any mode."""
    return (min(m["min_bet"] for m in TREE_MODES.values()),
            max(m["max_bet"] for m in TREE_MODES.values()))


def tree_mode_text(bet: int) -> str:
    mode_lines = "\n".join(
        f"• <b>{m['label']}</b> — {m['height']} levels, {m['lanes']} branches: "
        f"{tree_snake_summary(m['snakes'])} (bet {m['min_bet']:,} – {m['max_bet']:,})"
        for m in TREE_MODES.values()
    )
    return (
        "<b>「 🌳 TREE CLIMB 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<b>Bet:</b> {bet} 💠\n\n"
        "<b>Choose a mode:</b>\n"
        f"{mode_lines}\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<i>Green is safer, red is riskier. Nothing is charged until you pick.</i>"
    )


def tree_mode_keyboard(uid: str, bet: int) -> InlineKeyboardMarkup:
    """Mode buttons: green (safer) / red (riskier). Modes that don't accept this bet are greyed and locked."""
    rows = []
    for key, m in TREE_MODES.items():
        if m["min_bet"] <= bet <= m["max_bet"]:
            text = f"{m['label']} · {m['height']} levels · {tree_snake_short(m['snakes'])}"
            style = m["style"]
        else:
            text = f"🔒 {m['label']} · bet {m['min_bet']:,} – {m['max_bet']:,}"
            style = None
        rows.append([tree_button(text, f"trmode_{uid}_{key}", style)])
    rows.append([tree_button("Cancel", f"trcancel_{uid}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


@main_router.message(Command("tree"))
async def tree_cmd(message: Message, command: CommandObject):
    uid = str(message.from_user.id)
    load_db()
    ensure_user(uid, message.from_user.first_name, message.from_user.username)

    if uid in active_trees:
        game = active_trees[uid]
        if time.time() - game["start_time"] > TREE_GAME_TIMEOUT:
            tree_expire(uid, game)
        else:
            await message.reply("⚠️ You already have an active tree climb in progress.", parse_mode=ParseMode.HTML)
            return

    lo, hi = tree_bet_limits()
    args = (command.args or "").split()
    if len(args) != 1:
        mode_lines = "\n".join(
            f"• <b>{m['label']}</b> — {m['height']} levels, {m['lanes']} branches: "
            f"{tree_snake_summary(m['snakes'])}, bet {m['min_bet']:,} – {m['max_bet']:,} 💠"
            for m in TREE_MODES.values()
        )
        await message.reply(
            "<b>「 🌳 TREE CLIMB — HOW TO PLAY 」</b>\n"
            "━━━━━━━━━━━━━━━━━\n"
            "<b>Usage:</b> <code>/tree &lt;bet&gt;</code>\n"
            "<b>Example:</b> <code>/tree 50</code>\n\n"
            f"{mode_lines}\n\n"
            "After you send your bet, pick a mode with the buttons. Climb one level at a time — every level has "
            "snakes hiding on some branches, so pick a safe one and your multiplier grows. "
            f"Cash Out unlocks after {TREE_MIN_CASHOUT_STEPS} levels.",
            parse_mode=ParseMode.HTML
        )
        return

    try:
        bet = int(args[0])
    except ValueError:
        await message.reply("Bet must be a whole number.", parse_mode=ParseMode.HTML)
        return

    if bet < lo or bet > hi:
        await message.reply(f"Bet must be between {lo:,} and {hi:,} Shards 💠.", parse_mode=ParseMode.HTML)
        return

    if load_db()["users"][uid].get("nexus_shards", 0) < bet:
        await message.reply("You don't have enough Shards for that bet.", parse_mode=ParseMode.HTML)
        return

    sent = await message.reply(
        text=tree_mode_text(bet),
        reply_markup=tree_mode_keyboard(uid, bet),
        parse_mode=ParseMode.HTML
    )
    # A newer /tree replaces any older pending choice (the old message's buttons stop working)
    pending_trees[uid] = {"bet": bet, "message_id": sent.message_id, "time": time.time()}


@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("trmode_"))
async def tree_mode_cb(cq: CallbackQuery):
    try:
        _, owner_id, mode_key = cq.data.split("_")
    except ValueError:
        await cq.answer()
        return

    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your tree!", show_alert=True)
        return

    # ---- no awaits from here until the game is created, so a double tap can't start two rounds ----
    pend = pending_trees.get(owner_id)
    if not pend or pend["message_id"] != cq.message.message_id:
        # Already used, cancelled, or an older selection message: leave everything untouched
        await cq.answer("This selection is no longer active. Send /tree again.", show_alert=True)
        return
    if time.time() - pend["time"] > TREE_PICK_TIMEOUT:
        pending_trees.pop(owner_id, None)
        await cq.answer("This selection expired. Send /tree again.", show_alert=True)
        await tree_edit_message(cq, "⌛ <b>Selection expired.</b> No Shards were taken.", InlineKeyboardMarkup(inline_keyboard=[]))
        return

    cfg = TREE_MODES.get(mode_key)
    if not cfg:
        await cq.answer()
        return
    bet = pend["bet"]

    if bet < cfg["min_bet"] or bet > cfg["max_bet"]:
        await cq.answer(
            f"{cfg['label']} mode bet must be between {cfg['min_bet']:,} and {cfg['max_bet']:,}.",
            show_alert=True
        )
        return

    if owner_id in active_trees:
        game = active_trees[owner_id]
        if time.time() - game["start_time"] > TREE_GAME_TIMEOUT:
            tree_expire(owner_id, game)
        else:
            await cq.answer("You already have an active tree climb.", show_alert=True)
            return

    db = load_db()
    user_data = db["users"][owner_id]
    if user_data.get("nexus_shards", 0) < bet:
        await cq.answer("You don't have enough Shards for that bet.", show_alert=True)
        return

    pending_trees.pop(owner_id, None)

    user_data["nexus_shards"] -= bet
    user_data["tree_bet"] = user_data.get("tree_bet", 0) + bet

    gs = db.setdefault("tree_global", {})
    gs["total_bet"] = gs.get("total_bet", 0) + bet
    gs["total_games"] = gs.get("total_games", 0) + 1
    today_str = date.today().isoformat()
    daily = gs.setdefault("daily_games", {})
    daily[today_str] = daily.get(today_str, 0) + 1
    _tree_stat(db, "start", uid=owner_id, mode=mode_key, bet=bet)
    save_db()

    game = {
        "uid": owner_id,
        "bet": bet,
        "mode": mode_key,
        "label": cfg["label"],
        "lanes": cfg["lanes"],
        "height": cfg["height"],
        "snakes": list(cfg["snakes"]),
        "growth": cfg["growth"],
        "traps": generate_traps(cfg["lanes"], cfg["snakes"]),
        "picks": [],
        "steps": 0,
        "lock": asyncio.Lock(),
        "chat_id": cq.message.chat.id,
        "start_time": time.time(),
    }
    active_trees[owner_id] = game
    # -------------------------------------------------------------------------------------------

    await cq.answer(f"{cfg['label']} mode — good luck!")
    await tree_edit_message(
        cq,
        tree_status_text(game),
        tree_keyboard(owner_id, game["lanes"], game["height"], game["traps"], game["picks"], 0)
    )


@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("trcancel_"))
async def tree_cancel_cb(cq: CallbackQuery):
    owner_id = cq.data.split("_")[1]
    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your tree!", show_alert=True)
        return

    pend = pending_trees.get(owner_id)
    if pend and pend["message_id"] == cq.message.message_id:
        pending_trees.pop(owner_id, None)
    await cq.answer("Cancelled.")
    await tree_edit_message(cq, "❌ <b>Cancelled.</b> No Shards were taken.", InlineKeyboardMarkup(inline_keyboard=[]))


# ==========================================
# BRANCH TAP CALLBACK
# ==========================================
@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("trstep_"))
async def tree_step_cb(cq: CallbackQuery):
    try:
        _, owner_id, row_str, lane_str = cq.data.split("_")
        row, lane = int(row_str), int(lane_str)
    except ValueError:
        await cq.answer()
        return

    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your tree!", show_alert=True)
        return

    game = active_trees.get(owner_id)
    if not game:
        await cq.answer("This round has already ended.", show_alert=True)
        return

    async with game["lock"]:
        if active_trees.get(owner_id) is not game:
            await cq.answer("This round has already ended.", show_alert=True)
            return
        if time.time() - game["start_time"] > TREE_GAME_TIMEOUT:
            tree_expire(owner_id, game)
            await cq.answer("This round expired.", show_alert=True)
            return
        # Stale tap from an old keyboard (already climbed this level) or invalid lane
        if row != game["steps"] or lane < 0 or lane >= game["lanes"]:
            await cq.answer()
            return

        game["picks"].append(lane)
        tree_apply_dda_balancing(owner_id, row, lane, game)

        # SNAKE
        if lane in game["traps"][row]:
            active_trees.pop(owner_id, None)
            tree_record_loss(game)
            await cq.answer("🐍 A snake was hiding there!", show_alert=False)
            await tree_edit_message(cq, tree_loss_text(game), _final_keyboard(owner_id, game, boom=(row, lane)))
            return

        # SAFE BRANCH
        game["steps"] += 1
        mult = tree_multiplier(game["growth"], game["steps"])

        # GOLDEN APPLE REACHED
        if game["steps"] >= game["height"]:
            chat_id, chat_title = _chat_info(cq)
            payout = tree_credit_win(owner_id, game, mult, chat_id, chat_title)
            active_trees.pop(owner_id, None)
            await cq.answer("🍎 You reached the golden apple!", show_alert=False)
            await tree_edit_message(cq, tree_win_text(game, mult, payout, True), _final_keyboard(owner_id, game))
            return

        await cq.answer()
        await tree_edit_message(
            cq,
            tree_status_text(game),
            tree_keyboard(
                owner_id, game["lanes"], game["height"], game["traps"], game["picks"], game["steps"],
                can_cash_out=game["steps"] >= TREE_MIN_CASHOUT_STEPS
            )
        )


# ==========================================
# CASH OUT CALLBACK
# ==========================================
@main_router.callback_query(lambda cq: cq.data and cq.data.startswith("trcash_"))
async def tree_cashout_cb(cq: CallbackQuery):
    owner_id = cq.data.split("_")[1]
    if str(cq.from_user.id) != owner_id:
        await cq.answer("⚠️ This isn't your tree!", show_alert=True)
        return

    game = active_trees.get(owner_id)
    if not game:
        await cq.answer("This round has already ended.", show_alert=True)
        return

    async with game["lock"]:
        if active_trees.get(owner_id) is not game:
            await cq.answer("This round has already ended.", show_alert=True)
            return
        if time.time() - game["start_time"] > TREE_GAME_TIMEOUT:
            tree_expire(owner_id, game)
            await cq.answer("This round expired.", show_alert=True)
            return
        if game["steps"] < TREE_MIN_CASHOUT_STEPS:
            remaining = TREE_MIN_CASHOUT_STEPS - game["steps"]
            await cq.answer(f"Climb {remaining} more level{'s' if remaining != 1 else ''} before cashing out!", show_alert=True)
            return

        mult = tree_multiplier(game["growth"], game["steps"])
        chat_id, chat_title = _chat_info(cq)
        payout = tree_credit_win(owner_id, game, mult, chat_id, chat_title)
        active_trees.pop(owner_id, None)

        await cq.answer(f"✅ Cashed out: +{payout} 💠")
        await tree_edit_message(cq, tree_win_text(game, mult, payout, False), _final_keyboard(owner_id, game))


@main_router.callback_query(lambda cq: cq.data == "trnoop")
async def tree_noop_cb(cq: CallbackQuery):
    await cq.answer()


# ==========================================
# /tree_lbd — LEADERBOARD
# ==========================================
TREE_LB_TABS = {"win": "Biggest win", "mult": "Best multiplier", "total": "Total won", "apples": "Golden apples"}
TREE_LB_TITLES = {"win": "BIGGEST WIN", "mult": "BEST MULTIPLIER", "total": "TOTAL SHARDS WON", "apples": "GOLDEN APPLES"}


def _tree_board(db: dict, tab: str) -> list:
    """[(value, uid, name)] best first. Every tab: highest wins."""
    rows = []
    for uid, u in (db.get("users") or {}).items():
        if not isinstance(u, dict):
            continue
        rec = u.get("tree") if isinstance(u.get("tree"), dict) else {}
        if tab == "win":
            v = rec.get("biggest_win", 0)
        elif tab == "mult":
            v = rec.get("best_mult", 0)
        elif tab == "total":
            v = u.get("tree_won", 0)
        else:
            v = rec.get("apples", 0)
        if v and v > 0:
            rows.append((v, str(uid), str(u.get("name") or "User")[:24]))
    rows.sort(key=lambda r: (-r[0], r[1]))
    return rows


def _tree_fmt_value(tab: str, v) -> str:
    if tab == "mult":
        return f"{v:.2f}x"
    if tab == "apples":
        return f"{int(v):,} apple" + ("" if int(v) == 1 else "s")
    return f"{int(v):,} 💠"


def _tree_lb_text(db: dict, tab: str, uid) -> str:
    rows = _tree_board(db, tab)
    text = f"<b>「 🌳 TREE CLIMB - {TREE_LB_TITLES[tab]} 」</b>\n━━━━━━━━━━━━━━━━━\n"
    if rows:
        text += "\n".join(
            f"<b>{i + 1}.</b> <b>{_html_esc(name[:18])}</b> - {_tree_fmt_value(tab, v)}"
            for i, (v, _u, name) in enumerate(rows[:10])
        )
    else:
        text += "Nobody has cashed out yet. Be the first with /tree"
    text += "\n━━━━━━━━━━━━━━━━━\n"
    me = str(uid)
    idx = next((i for i, r in enumerate(rows) if r[1] == me), None)
    if idx is None:
        text += "<b>Your rank:</b> Unranked"
    else:
        text += f"<b>Your rank:</b> #{idx + 1} with {_tree_fmt_value(tab, rows[idx][0])}"
    return text


def _tree_lb_kb(owner, active: str) -> InlineKeyboardMarkup:
    def btn(tab):
        return tree_button(TREE_LB_TABS[tab], f"tlb:{tab}:{owner}", "success" if tab == active else "primary")
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("win"), btn("mult")],
        [btn("total"), btn("apples")],
    ])


@main_router.message(Command("tree_lbd"))
async def tree_lbd_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int):
        return
    try:
        db = ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
        text = _tree_lb_text(db, "win", uid_int)
        kb = _tree_lb_kb(uid_int, "win")
        try:   # banner image with the leaderboard as its caption
            await message.reply_photo(photo=TREE_LBD_IMAGE, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception as e:   # image unreachable: still show the leaderboard as text
            print(f"[tree_lbd_photo] {e}")
            await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[tree_lbd_CRASH] {e}")
        traceback.print_exc()
        await message.reply("The leaderboard is unavailable right now. Please try again in a moment.")


@main_router.callback_query(F.data.startswith("tlb:"))
async def tree_lbd_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id):
        return
    try:
        _, tab, owner = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return
    if tab not in TREE_LB_TABS:
        await cq.answer()
        return
    if str(cq.from_user.id) != owner:
        await cq.answer("This leaderboard belongs to someone else. Send /tree_lbd for your own.", show_alert=True)
        return
    try:
        db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
        text = _tree_lb_text(db, tab, cq.from_user.id)
        kb = _tree_lb_kb(owner, tab)
        if cq.message.photo:   # banner image: the leaderboard lives in the caption
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:                  # text-only leaderboard message
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[tree_lbd_cb] failed: {e}")
    await cq.answer()


# ==========================================
# /tstats — ADMIN ONLY  (Today's stats | Global stats | Detailed)
# ==========================================
TREE_STATS_TABS = {"today": "Today's stats", "global": "Global stats", "detail": "Detailed"}
_LINE = "━━━━━━━━━━━━━━━━━"


def _tree_pct(a, b) -> str:
    return f"{a / b * 100:.0f}%" if b else "-"


def _tree_section(title: str, b: dict) -> str:
    started, wins, losses, expired = b.get("started", 0), b.get("wins", 0), b.get("losses", 0), b.get("expired", 0)
    finished = wins + losses
    gen, taken = b.get("generated", 0), b.get("taken", 0)
    best = f"{b.get('best_mult', 0):.2f}x" if b.get("best_mult") else "-"
    big = f"{b.get('biggest_win', 0):,} 💠" if b.get("biggest_win") else "-"
    if b.get("biggest_win") and b.get("biggest_win_name"):
        big += f" ({_html_esc(str(b['biggest_win_name'])[:18])})"
    lines = [
        f"<b>{title}</b>",
        f"🎮 Games started : <b>{started:,}</b>",
        f"✅ Cash outs     : <b>{wins - b.get('apples', 0):,}</b>",
        f"🍎 Golden apples : <b>{b.get('apples', 0):,}</b>",
        f"🐍 Snake bites   : <b>{losses:,}</b>",
        f"⌛ Expired       : <b>{expired:,}</b>",
        f"📈 Win rate      : <b>{_tree_pct(wins, finished)}</b>",
        f"💰 Wagered       : <b>{b.get('wagered', 0):,}</b> 💠",
        f"💠 Generated     : <b>{gen:,}</b>",
        f"💠 Taken         : <b>{taken:,}</b>",
        f"🏦 House net     : <b>{taken - gen:+,}</b> 💠",
        f"🏆 Biggest win   : <b>{big}</b>",
        f"🚀 Best mult     : <b>{best}</b>",
    ]
    if "players" in b:
        lines.insert(1, f"👥 Players       : <b>{len(b['players']):,}</b>")
    return "\n".join(lines)


def _tree_mode_block(title: str, b: dict) -> str:
    out = [f"<b>{title}</b>"]
    for key, cfg in TREE_MODES.items():
        m = (b.get("modes") or {}).get(key, {})
        started, wins, losses = m.get("started", 0), m.get("wins", 0), m.get("losses", 0)
        out.append(
            f"<b>{cfg['label']}</b>: {started:,} games | {wins:,} won ({m.get('apples', 0):,} 🍎) | "
            f"{losses:,} bitten | win {_tree_pct(wins, wins + losses)} | "
            f"wagered {m.get('wagered', 0):,} | house {m.get('taken', 0) - m.get('generated', 0):+,}"
        )
    return "\n".join(out)


def tree_stats_text(db: dict, view: str) -> str:
    root = db.get("tree_stats") or {}
    today_key = date.today().isoformat()
    today = (root.get("days") or {}).get(today_key, {})
    head = "<b>「 📊 TREE CLIMB STATS 」</b>\n" + _LINE + "\n"

    if view == "today":
        return head + _tree_section(f"TODAY ({today_key})", today)

    gs = db.get("tree_global", {})
    if view == "global":
        players = sum(1 for u in (db.get("users") or {}).values() if isinstance(u, dict) and u.get("tree_bet", 0) > 0)
        wagered = gs.get("total_bet", 0)
        net = gs.get("total_taken", 0) - gs.get("total_won", 0)
        return (
            head + "<b>GLOBAL (ALL TIME)</b>\n"
            f"👥 Players            : <b>{players:,}</b>\n"
            f"🎮 Total games        : <b>{gs.get('total_games', 0):,}</b>\n"
            f"📅 Games today        : <b>{gs.get('daily_games', {}).get(today_key, 0):,}</b>\n"
            f"💰 Total wagered      : <b>{wagered:,}</b> 💠\n"
            f"💠 Shards generated   : <b>{gs.get('total_won', 0):,}</b>\n"
            f"💠 Shards taken       : <b>{gs.get('total_taken', 0):,}</b>\n"
            f"🏦 House net          : <b>{net:+,}</b> 💠\n"
            f"📉 House edge         : <b>{(f'{net / wagered * 100:.1f}%' if wagered else '-')}</b>"
        )

    # detailed: tracked counters (they start the day this feature went live) + per-mode split + recent days
    allb = root.get("all") or {}
    days = root.get("days") or {}
    recent = sorted(days)[-7:]
    day_lines = "\n".join(
        f"{d[5:]}: {days[d].get('started', 0):,} games | {len(days[d].get('players', [])):,} players | "
        f"house {days[d].get('taken', 0) - days[d].get('generated', 0):+,}"
        for d in reversed(recent)
    ) or "No data yet."
    return (
        head
        + _tree_section("ALL TIME - SINCE TRACKING STARTED", allb) + "\n" + _LINE + "\n"
        + _tree_mode_block(f"BY MODE - TODAY ({today_key})", today) + "\n" + _LINE + "\n"
        + _tree_mode_block("BY MODE - ALL TIME", allb) + "\n" + _LINE + "\n"
        + "<b>LAST 7 DAYS</b>\n" + day_lines
    )


def tree_stats_kb(owner, active: str) -> InlineKeyboardMarkup:
    def btn(view):
        return tree_button(TREE_STATS_TABS[view], f"tst:{view}:{owner}", "success" if view == active else "primary")
    return InlineKeyboardMarkup(inline_keyboard=[[btn("today"), btn("global")], [btn("detail")]])


@main_router.message(Command("tstats"))
async def tstats_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return
    try:
        db = load_db()
        await message.reply(tree_stats_text(db, "today"), reply_markup=tree_stats_kb(message.from_user.id, "today"),
                            parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[tstats_CRASH] {e}")
        traceback.print_exc()
        await message.reply("Stats are unavailable right now.")


@main_router.callback_query(F.data.startswith("tst:"))
async def tstats_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer()
        return
    try:
        _, view, owner = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return
    if view not in TREE_STATS_TABS:
        await cq.answer()
        return
    if str(cq.from_user.id) != owner:
        await cq.answer("These stats belong to another admin. Send /tstats for your own.", show_alert=True)
        return
    try:
        await cq.message.edit_text(tree_stats_text(load_db(), view), reply_markup=tree_stats_kb(owner, view),
                                   parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[tstats_cb] failed: {e}")
    await cq.answer()
