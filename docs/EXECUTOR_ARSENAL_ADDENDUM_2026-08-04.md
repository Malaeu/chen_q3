# EXECUTOR ARSENAL ADDENDUM (2026-08-04, thin)

Applies to WHICHEVER executor body is active — **Codex (Mac, home)** or **Claude Code
(Linux, work)**. One role, two bodies; both read this file (Codex via `AGENTS.md`, Claude
Code via the project `CLAUDE.md`). Dictated `[→CODEX]` steps are materialized by the active
body; on Linux, docs go through the direct channel, Codex dictation is the fallback.

Supplement to `q3.lean.aristotle/docs/CODEX_REORIENT_BRIEF_2026-07-10.md`. Bus mechanics unchanged.

## 0. SYNC
Fetch origin `rh_clean` (≥ `390fc4bd`). Goal 047 = **VOID** (number burned, never reuse);
the arsenal materialization went through the Linux channel as goal **053**.

## 1. SESSION PINS (fetch from repo, never inline into goals)
- kernel: `q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md` (SHA `a13dfbe1…`)
- deck: `q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md` (SHA `018dbf6b…`, cards C01..C12)
- Proshka mandate: `docs/routeB_bus/proshka/ARSENAL_MANDATE_2026-08-04.md` (SHA `2167a1f5…`)

## 2. CARD-ID IN ANSWER
If a goal file carries a card-ID (C01..C12), the answer duplicates it on a line
`ARSENAL_USED: Cxx`. If no card was used, omit the line.

## 3. AUTOPSY (K8 v3)
Any answer with status INCONCLUSIVE / WALL / KILLED MUST carry a line
`AUTOPSY: <one line — which structure was dropped>` (localization, sign position,
multiplicity, boundedness, coupling, measure vs algebra…). Without it the goal is NOT closed.

## 4. OBJECT PRE-COMMIT (K6 v3)
Auxiliary objects (profiles, cutoffs, weights, witness matrices, sampling schemes) are fixed
in the goal file BEFORE the run; the answer never introduces new "for all cases" objects
after seeing the cases. An object chosen post hoc proves a weaker theorem and must be relabeled.

## 5. ARSENAL-LEDGER IN STATE
On each gate update to `ROUTE_B_STATE.md`, add/refresh one status line
`ARSENAL: used=[...], killed=[...], untested=N` (data from answer files; glossary frozen —
this is a status line, not a new term). First insertion: Ф7. STATE is a last-step update.

## 6. COMMIT DISCIPLINE
Canon + mirror in one commit, as always. `[Linux][rh_clean]` / `[MacOS][rh_clean]` prefix by OS.
