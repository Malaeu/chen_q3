# Historical retro table, 2026-01-01 .. 2026-10-22

Observer (Linux Claude), owner request 2026-10-28. Nine period agents (one per period) read sources read-only and wrote one TSV each.
06.10–22.10 comes from `../openai_math_2026-10-07/RETRO_EXACT_RETURN_2026-10-28/` (72 rows, blind design, different schema).
This sweep is descriptive, NOT blind: one agent read question and outcome together. Row budget 25–60 per period, decision-bearing rounds only.

Check: `python3 -I verify_hist.py .` from repo root → 485 rows, every quote found verbatim at its locator, 0 failures (2026-10-28).

## Counts (485 rows, Jan → 05.10)
| period | MAIN_GAIN | LEAN_CLOSED | SHAPE_KILL | ROUTE_KILL | RH_EQUIV | FALSE_GREEN | EXACT_RETURN | REMAINDER | UNKNOWN | n |
|---|---|---|---|---|---|---|---|---|---|---|
| Jan–Feb | 4 | 7 | 8 | 0 | 2 | 5 | 0 | 6 | 10 | 42 |
| Mar–Apr | 4 | 3 | 27 | 2 | 4 | 3 | 0 | 10 | 5 | 58 |
| May | 3 | 13 | 5 | 0 | 2 | 3 | 1 | 2 | 6 | 35 |
| Jun | 0 | 5 | 37 | 2 | 0 | 0 | 1 | 2 | 13 | 60 |
| Jul | 2 | 10 | 24 | 2 | 1 | 4 | 1 | 10 | 4 | 58 |
| Aug 1–15 | 2 | 13 | 21 | 1 | 1 | 5 | 0 | 12 | 3 | 58 |
| Aug 16–31 | 2 | 9 | 18 | 7 | 3 | 3 | 4 | 7 | 1 | 54 |
| Sep 1–15 | 12 | 3 | 17 | 1 | 12 | 2 | 5 | 6 | 0 | 60 |
| Sep 16–Oct 5 | 10 | 3 | 27 | 0 | 3 | 2 | 4 | 8 | 3 | 60 |
| Oct 6–22 (first table) | 4 borderline | – | 25 | – | – | – | 8 | 35 | 0 | 72 |

Plus EXTERNAL_ERROR_FOUND 2 (both Suzuki, 06.09). Rounds anchored to Proshka: 201/485.

## Θ-law test
Strict form ("no unconditional move of a main quantity without input on ζ-zeros") is REFUTED by the literal criterion: 11 rows YES_UNCOND with Z=NO.
All 11 are restricted classes, finite cells or supplier premises: P08_Sep1-12 (Zhu compact windows), -26/-27/-28 (scalar floor: neighbourhood, high modulation, H00),
-30/-32/-34 (two-lobe, three-lobe, six-centre slice), -52/-53/-59 (odd curvature, ODD2 two-node minor, rank-two V via Csordas–Varga), P09_Sep2Oct-31 (hmode rate).
The 4 rows YES_UNCOND with Z=YES: P02_MarApr-41 (explicit formula), P08_Sep1-25 (Lamzouri, external), P08_Sep1-44 (SATURATION T², upper side), P09_Sep2Oct-13 (Platt–Trudgian height).

## Refined candidate (observer, 0.85): the lift is the hole
- Restricted classes move without zero input (11 rows). No row lifts a restricted result to the uniform/cofinal/all-window statement without zero input.
- Each time the uniform version was written down, it was found RH-equivalent: 28 RH_EQUIVALENT_FOUND rows, from Jan (Weil Δ≥0) to Sep (all-order odd positivity, EULERHB SUPPORT, payment ΣM_j).
- Falsifier: one row with an unconditional uniform/cofinal statement on a route's decisive quantity and Z=NO.
- Steady error rate: FALSE_GREEN 27 rows, 2–5 every period.

## Suzuki
Defect in arXiv 2301.00421v3 p.3 ("For negative t, we set S_t(z) := S_{−t}(z)") makes P̂_{Dψ} ≡ 0 for even ψ, against Thm 1.4 (1.9).
Found 06.09 (Progress_Log.md:5613, :5632), letter sent 06.09 (Progress_Log.md:5658, paper_weil/ERRATUM_NOTE_SUZUKI_DRAFT.md).
The reply with thanks is NOT in the repo (SESSION_PROTOKOLL_2026-09-08_LINUX_CLAUDE.md:33: "still unanswered"); owner's word only.

## Limits
Classification is agent judgement; only quote verbatimness is machine-checked. Coverage is sampled (e.g. June: ~466 Step33 rows collapsed to ~38).
Proshka answers Jan 23–Feb 3, Mar (7 stub reports) and early July exist only as summaries.
