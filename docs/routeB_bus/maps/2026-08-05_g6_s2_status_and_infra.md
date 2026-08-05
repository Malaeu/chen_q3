# Cartographer pass — `2026-08-05_g6_s2_status_and_infra.svg`

Map author: Mythos. Cartographer pass (claim-vs-fact against the repo): Claude Code, Linux body,
2026-08-05, at HEAD `ca2b724f`. Map SHA-256 prefix `26a54a4551cc6207`.

This is the **first live run of the cartographer discipline** ratified this session: every status
claim on a map is checked against the repository, and drift is reported rather than silently
inherited. The map itself is kept unchanged — a map is a dated artifact, not a living file.

## Verdict: 9 claims confirmed, 4 stale

The map was drawn **before Proshka's G6 verdict landed**, so its most load-bearing cell is out of date.

### Confirmed against the repo

| Map claim | Fact |
|---|---|
| S2-L2 gauge ≠ 0 + ξ identity — proved, 6 theorems, local, 0 Aristotle | `Q3/Proofs/RouteB/S2GaugeNonvanishing.lean`, `lake build` PASS 7746, standard axiom triple, 0 sorry |
| S2-L4 limit(0) ≠ 0, consumer lemma wired | `limit_at_zero_ne_zero` present, consumes `centeredXi_zero_ne_zero` |
| S2-L5 `sameCofinalGuard` proved | present in `CanonicalRHRouteSkeleton.lean` |
| Cartographer ratified, planted violations awaiting v1 | MAP.md still carries the two deliberate lies |
| Index v2 = env dump, upgrade of the same backend, feeds taint | matches the ratified plan |
| G2/CCM owner fork frozen, 055 held | `routeb_status.py --check` agrees |
| Lesson: local Linux compile is the default for small lemmas | confirmed — Mathlib cache in place, 3 Aristotle runs saved |
| Boundaries NOT_RH · 010 VOID · 055 held | unchanged |
| S2-L1 crosswalk contract open | still open — and now promoted to the main front |

### Stale — drift found

| Map claim | Actual state after Proshka's verdict / today's infra work |
|---|---|
| «Proshka · legality of C from a window — **open**, window held» | **Answered: FATAL.** `KILL_FIXED_WINDOW_MUNTZ_AS_CANONICAL_PSTAR_SURROGATE`. `Pstar` is source-locked to `centeredPstarFamily D.kTrial`; abstract `C` is interface polymorphism, not inheritance. C10 + C09 kills, C04 warning |
| «S2-L2b · the wall (2 conditions)» | **Demoted to auxiliary.** The real wall is now `G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK` (9 conditions). Fixed-window reading survives only as an auxiliary construction |
| «Declaration index v1 — open, grep today, R7 ~10–15k» | **Done, and not by grep.** No new index was built: `aristotle_proofs.db` was backfilled instead — 94→208 docs, 1410→2232 lemmas, RouteB 124/124 files (was 31%). Grep was demoted from organ to *judge of the organ*, per Mythos |
| «Receipt gate — in force after the index» | **Precondition now met.** Mythos required 100% RouteB coverage before `DB-SEARCH:` receipts become non-theatrical; that threshold is reached |

## Note for the map's author

Two of the four drifts are *good news* (the index is done; the receipt gate can switch on) and one
is a kill that shrinks the front rather than widening it. Only the L2b demotion changes what should
be worked on next. A refreshed map should show one wall — the same-family crosswalk — with the
fixed-window branch drawn as an auxiliary side road, not as the trunk.
