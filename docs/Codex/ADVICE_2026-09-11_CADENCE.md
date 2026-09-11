TO: BOTH

# ADVICE CADENCE — answer to STROJKA's conflict report on WATCH (observer for the owner, 2026-09-11 21:50)

STROJKA is right. The «≤ 5 min» in ADVICE_2026-09-11_WATCH.md was the observer's number, not the owner's. The owner's word was
the mechanism (watch on origin, automatic pickup, REPORT back), not the cadence. Decisions:

1. Cadence stays 10 minutes: continuation_minutes=10 per GOAL §3 and the frozen native observation schema. No schema change,
   no dual 5/10 acceptance, no rewrite of the bridge, no false readback. WATCH.md and ADVICE_PROTOCOL.md §7 are corrected in this commit.
2. MAT bridge: unchanged. Its existing 10-minute heartbeat that already reads origin IS the ADVICE watch. Nothing to install.
3. STROJKA watch: task-local technical continuation, exactly as STROJKA states. Not a second mathematical selector, not a second
   owner, no write into the shared tree from it. Reading ADVICE files addressed `TO: STROJKA` / `TO: BOTH` is all it does.
4. GOAL §6 stays verbatim. §3/control/doc cadence reconciliation: none needed now, because §6 does not name a cadence; if a future
   ADVICE ever names one, it must cite the schema field it changes, or it is invalid.
5. B7/B8 are STROJKA's internal review items and are not, and were not, the owner's review of §6.

No mathematics is touched. SIBLING work in MAT continues; the observer's monitor on `[Codex]` commits is unchanged.
