# Historical Cognitive Governor

status: DORMANT_HISTORICAL
selector_effect: NONE
scope: historical Q3 proof-loop snapshot / Route B Muntz v3 plant frontier
date: 2026-07-31

This frozen snapshot has no current routing, review-transport, or next-action
authority. It must not select PL1, PL3, a physical goal, or a Proshka action.
Current behavior comes from `docs/CODEX_CONTROL.md`; current execution comes
from the physical task state and registered runtime. The former Muntz-v3
frontier, watchdog, Proshka fallback, loop traps, and next-action text are
available only in Git history for this file. None of them is a live instruction.

## Current use

This tombstone deliberately exports no governor front. A consumer that needs a
current route must read the physical task state; a consumer that needs loop
policy must read `docs/CODEX_CONTROL.md` and
`q3.lean.aristotle/COGNITIVE_OPERATORS.md`. Missing current governor data must
degrade to unavailable, never fall back to the historical Muntz-v3 snapshot.
