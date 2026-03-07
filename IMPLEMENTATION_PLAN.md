# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`OP-pd.1 | gate=OP-pd | target=Freeze the post-obstruction blocker after the same-family failure: the naive centered Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` is too large, so the live task is to build a smaller operator-controlled packet family inside `\mathcal W_K^{pd}` and stop treating `SF-pd` as the active route | files=full/sections/A1prime.tex; full/sections/Main_closure.tex; full/sections/scope_notation.tex; full/sections/introduction.tex; full/sections/abstract.tex; full/sections/Weil_pack.tex; full/sections/Weil_linkage.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"OP-pd|packet-Rayleigh|same-family|G_\\{K,\\\\mathrm\\{Ray\\}\\}|too large|A1-pd\" full/sections q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md && cd full && latexmk -pdf RH_Q3.tex | done_when=source-of-truth says one honest blocker: exact smaller operator-controlled family inside the corrected cone, and the naive `\\Phi_{B,t}|p|^2` route is background-only | if_fail_then=split into `naive-rayleigh obstruction` and `exact operator family theorem shape` subtasks`

## QUEUED

`A1-pd.4 | gate=A1-pd | target=Turn the frozen `A1-pd` theorem block into a proof-ready route on the dense family `\mathcal G_{K,\mathrm{dens}}^{pd}`: pre-square density on `C_c^\infty([-K/2,K/2])` plus `L^1 -> autocorrelation` continuity | files=full/sections/A1prime.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G_\\{K,\\\\mathrm\\{dens\\}\\}|autocorrelation|L\\^1|t_0" full/sections/A1prime.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the density theorem is phrased and decomposed exactly on `\mathcal G_{K,\mathrm{dens}}^{pd}` with no hidden appeal to the broad cone | if_fail_then=split into pre-square density and autocorrelation continuity subtasks`

`OP-pd.2 | gate=OP-pd | target=Write the LaTeX-ready theorem shape for the exact operator-controlled family: `Q^\star(t;\Psi*\widetilde\Psi)=2\pi\langle \mathcal T_K\Psi,\Psi\rangle` on a smaller centered packet space that stays inside `\mathcal W_K^{pd}` and does not overgenerate broad local bumps | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"OP-pd|Psi\\*\\\\widetilde\\Psi|operator-controlled|packet family\" full/sections/Main_closure.tex full/sections/Weil_pack.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the exact next theorem is frozen as a smaller operator-family statement, not as density of `\\Phi_{B,t}|p|^2` | if_fail_then=split into `packet model space` and `quadratic-form identity` subtasks`

`LEAN.1 | gate=T0-pd | target=Mark broad-cone Lean exports (`Weil_cone`, `W_K`, broad-cone RH wrappers) as frozen background narrative without renaming theorem identifiers yet | files=q3.lean.aristotle/Q3/Basic/Defs.lean; q3.lean.aristotle/Q3/Axioms.lean; q3.lean.aristotle/Q3/Main.lean; q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean | verify=cd q3.lean.aristotle && lake env lean Q3/Main.lean | done_when=active Lean docstrings no longer sound like the broad cone is the public RH contract | if_fail_then=move the wording freeze back into tracker/orchestrator and defer Lean docstring cleanup`

## BLOCKED

`RAY-naive-bg | gate=background | target=Keep the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` only as an auxiliary quadratic-form candidate; do not let it drive the public closure route after the local-bump obstruction | files=full/sections/Main_closure.tex; full/sections/scope_notation.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"G_\\{K,\\\\mathrm\\{Ray\\}\\}|packet-Rayleigh|background\" full/sections q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the naive family is explicitly background-only everywhere active | if_fail_then=repeat the obstruction memo in the affected file`

`G1.6-bg | gate=background | target=Monitor/download/triage Aristotle project ad4c74f1-764f-4cfb-a229-2bc0b2905b67 only for reusable local support lemmas; do not let it drive the public mainline while `OP-pd` is active | files=q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md; q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/docs/INSIGHTS.md | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('ad4c74f1-764f-4cfb-a229-2bc0b2905b67')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=its output is classified as reusable-local or superseded-background | if_fail_then=leave it background and continue the corrected-cone mainline`
