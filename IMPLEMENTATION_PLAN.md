# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`A1-pd.3 | gate=A1-pd | target=Freeze the exact proof skeleton for `A1-pd`: pre-square density on `C_c^\infty([-K/2,K/2])` plus autocorrelation continuity feeding the exact packet cone `\mathcal P_K` | files=full/sections/A1prime.tex; full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/insights/pd_mainline_blocks_2026_03_07.md | verify=rg -n "mathcal P_K|A1-pd|autocorrelation|packet-Rayleigh|L\\^1|widetilde" full/sections/A1prime.tex full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md && cd full && latexmk -pdf RH_Q3.tex | done_when=the exact packet cone, the `A1-pd` theorem block, and the `L^1 -> autocorrelation` proof skeleton are all written as the active mainline contract | if_fail_then=split the proof skeleton into pre-square density and autocorrelation continuity subtasks`

## QUEUED

`RAY-pd.1 | gate=packet-Rayleigh | target=Freeze the exact theorem statement connecting `\Phi_\Psi=\Psi*\widetilde\Psi` to the Toeplitz/RKHS quadratic form on the same packet family | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/insights/pd_mainline_blocks_2026_03_07.md | verify=rg -n "packet-Rayleigh|Phi_\\\\Psi|p_\\\\Psi|rayleigh" full/sections/Main_closure.tex full/sections/Weil_pack.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=one exact packet-Rayleigh theorem block is frozen on the same exact packet cone `\mathcal P_K` | if_fail_then=split the bridge into packet construction and quadratic-form identification subtasks`

`LEAN.1 | gate=T0-pd | target=Mark broad-cone Lean exports (`Weil_cone`, `W_K`, broad-cone RH wrappers) as frozen background narrative without renaming theorem identifiers yet | files=q3.lean.aristotle/Q3/Basic/Defs.lean; q3.lean.aristotle/Q3/Axioms.lean; q3.lean.aristotle/Q3/Main.lean; q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean | verify=cd q3.lean.aristotle && lake env lean Q3/Main.lean | done_when=active Lean docstrings no longer sound like the broad cone is the public RH contract | if_fail_then=move the wording freeze back into tracker/orchestrator and defer Lean docstring cleanup`

`G1.6-bg | gate=background | target=Monitor/download/triage Aristotle project ad4c74f1-764f-4cfb-a229-2bc0b2905b67 only for reusable local support lemmas; do not let it drive the public mainline while T0-pd/A1-pd are active | files=q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md; q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/docs/INSIGHTS.md | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('ad4c74f1-764f-4cfb-a229-2bc0b2905b67')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=its output is classified as reusable-local or superseded-background | if_fail_then=leave it background and continue the corrected-cone mainline`

## BLOCKED

`A3-pd.1 | gate=centered A3/RKHS | target=Bind the existing centered Toeplitz/RKHS positivity engine to the exact centered packet family chosen by A1-pd | files=full/sections/A3; full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=rg -n "A3-pd|centered packet|mathcal P_K|RKHS" full/sections/A3 full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | done_when=one exact positivity route on the chosen centered packet family is written | if_fail_then=keep centered positivity as analytic input only`

`LF-pd.1 | gate=LF-pd | target=Rewrite the LF lift so that it consumes local positivity on the corrected cone `\mathcal W_K^{pd}` rather than on the broad cone `W_K` | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; full/sections/Weil_linkage.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=rg -n "LF|mathcal W\\^\\{pd\\}|W_K|positive-definite" full/sections/Main_closure.tex full/sections/Weil_pack.tex full/sections/Weil_linkage.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | done_when=LF transfer is stated only on the corrected cone | if_fail_then=keep LF as conditional skeleton pending local corrected-cone positivity`
