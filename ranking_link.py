"""
ranking_link.py  —  Anime Nexus side of the link with the Nexus Racers (ranking) bot.

When an owner taps "Credited" on a withdrawal in the ranking bot, that bot calls
    POST {this backend}/api/ranking/credit
with a shared secret, and the shards land in the user's balance here
(users[uid]["nexus_shards"]) straight away. The two bots run on different servers,
so this plain HTTPS call is the only thing connecting them.

Setup: the key is written in the code below (same value as CARD_BOT_LINK_KEY in the
ranking bot), so nothing needs to be set. To use a different one, set the env variable:
    RANKING_LINK_KEY   long random string, the same value as CARD_BOT_LINK_KEY on the ranking bot
    RANKING_MAX_CREDIT optional, biggest single credit accepted (default 200000)

Hook it up in card_aio.py:
    from ranking_link import ranking_link_api
    app.include_router(ranking_link_api)

Safe to retry: every request carries a `ref` (the withdrawal id). A ref that was
already credited is answered "already" and credits nothing a second time, so a
timeout on the ranking bot's side can never pay out twice.
"""
import hmac
import logging
import os
import time
from typing import Optional

from fastapi import APIRouter, Header, HTTPException
from pydantic import BaseModel, Field

from config import load_db, save_db

logger = logging.getLogger("AnimeNexus")

ranking_link_api = APIRouter(prefix="/api/ranking", tags=["ranking-link"])

RANKING_LINK_KEY = os.environ.get("RANKING_LINK_KEY", "4OMdQG9e6uUoCh3T__CgpzGHSAmDHw9L0VBvBCZUmt8")   # same value as CARD_BOT_LINK_KEY in the ranking bot
RANKING_MAX_CREDIT = int(os.environ.get("RANKING_MAX_CREDIT", "200000"))
LEDGER_KEEP_SECONDS = 90 * 86400   # how long a ref is remembered for duplicate protection


class LinkError(Exception):
    """A refusal with an HTTP status and a short machine-readable reason."""

    def __init__(self, status: int, reason: str):
        super().__init__(reason)
        self.status = status
        self.reason = reason


def apply_credit(db: dict, uid: int, amount: int, ref: str) -> dict:
    """Credits `amount` shards to `uid` once per `ref`. Pure bookkeeping, no I/O.
    Raises LinkError if the credit can't be made."""
    if amount <= 0:
        raise LinkError(400, "bad_amount")
    if amount > RANKING_MAX_CREDIT:
        raise LinkError(400, "amount_too_large")

    ledger = db.setdefault("ranking_credits", {})
    user = db.get("users", {}).get(str(uid))

    previous = ledger.get(ref)
    if previous is not None:
        if previous.get("uid") != uid or previous.get("amount") != amount:
            raise LinkError(409, "ref_reused")   # same ref, different request: never guess
        return {"ok": True, "already": True, "balance": (user or {}).get("nexus_shards", 0)}

    if user is None:
        # They've never started this bot. Don't invent an account for them.
        raise LinkError(404, "no_account")

    user["nexus_shards"] = user.get("nexus_shards", 0) + amount
    now = int(time.time())
    ledger[ref] = {"uid": uid, "amount": amount, "ts": now}
    for old_ref in [r for r, e in ledger.items() if now - e.get("ts", now) > LEDGER_KEEP_SECONDS]:
        del ledger[old_ref]
    return {"ok": True, "already": False, "balance": user["nexus_shards"]}


def _check_key(key: Optional[str]) -> None:
    if not RANKING_LINK_KEY:
        raise HTTPException(status_code=503, detail="not_configured")
    if not key or not hmac.compare_digest(key.encode("utf-8"), RANKING_LINK_KEY.encode("utf-8")):
        raise HTTPException(status_code=401, detail="bad_key")


class CreditRequest(BaseModel):
    uid: int
    amount: int
    ref: str = Field(min_length=1, max_length=80)


@ranking_link_api.get("/ping")
async def ranking_ping(x_link_key: Optional[str] = Header(default=None)):
    """Lets the ranking bot (or you) check that the URL and key are right."""
    _check_key(x_link_key)
    return {"ok": True}


@ranking_link_api.post("/credit")
async def ranking_credit(body: CreditRequest, x_link_key: Optional[str] = Header(default=None)):
    _check_key(x_link_key)
    # No awaits between reading and writing the DB, so this can't interleave with
    # another request or with the bot's own handlers (they share one event loop).
    db = load_db()
    try:
        result = apply_credit(db, body.uid, body.amount, body.ref)
    except LinkError as e:
        logger.warning("ranking credit refused (uid=%s amount=%s ref=%s): %s", body.uid, body.amount, body.ref, e.reason)
        raise HTTPException(status_code=e.status, detail=e.reason)
    if not result["already"]:
        save_db(db)
        logger.info("ranking credit: +%s shards to %s (ref %s)", body.amount, body.uid, body.ref)
    return result
