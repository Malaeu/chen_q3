# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`SF-pd.1 | gate=SF-pd | target=Freeze the exact same-family blocker after the corrected-cone pivot: density lives on `\mathcal G_{K,\\mathrm{dens}}^{pd}`, positivity lives on `\mathcal G_{K,\\mathrm{Ray}}^{pd}`, and the live knife-edge is now the bridge between them or an enlarged operator model on the dense family | files=full/sections/A1prime.tex; full/sections/Main_closure.tex; full/sections/scope_notation.tex; full/sections/introduction.tex; full/sections/abstract.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"G_\\{K,\\\\mathrm\\{dens\\}\\}|G_\\{K,\\\\mathrm\\{Ray\\}\\}|same-family|packet-Rayleigh|A1-pd\" full/sections q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md && cd full && latexmk -pdf RH_Q3.tex | done_when=the corrected manuscript and control docs state one honest blocker: same-family bridge or enlarged operator model, with no claim that `A1-pd + packet-Rayleigh` alone close RH | if_fail_then=split the blocker into `same-family density` and `enlarged operator model` alternatives`

## QUEUED

`A1-pd.4 | gate=A1-pd | target=Turn the frozen `A1-pd` theorem block into a proof-ready route on the dense family `\mathcal G_{K,\mathrm{dens}}^{pd}`: pre-square density on `C_c^\infty([-K/2,K/2])` plus `L^1 -> autocorrelation` continuity | files=full/sections/A1prime.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G_\\{K,\\\\mathrm\\{dens\\}\\}|autocorrelation|L\\^1|t_0" full/sections/A1prime.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the density theorem is phrased and decomposed exactly on `\mathcal G_{K,\mathrm{dens}}^{pd}` with no hidden appeal to the broad cone | if_fail_then=split into pre-square density and autocorrelation continuity subtasks`

`RAY-pd.2 | gate=packet-Rayleigh | target=Turn the packet-Rayleigh theorem block into a proof-ready statement on the centered Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}` and stop phrasing it as if it already acts on the dense family | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "packet-Rayleigh|G_\\{K,\\\\mathrm\\{Ray\\}\\}|Phi_\\{B,t,p\\}|rayleigh" full/sections/Main_closure.tex full/sections/Weil_pack.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=packet-Rayleigh is frozen exactly on `\mathcal G_{K,\mathrm{Ray}}^{pd}` and no longer masquerades as a theorem on the dense family | if_fail_then=split the bridge into `general Rayleigh identity` and `local admissibility` subtasks`

`LEAN.1 | gate=T0-pd | target=Mark broad-cone Lean exports (`Weil_cone`, `W_K`, broad-cone RH wrappers) as frozen background narrative without renaming theorem identifiers yet | files=q3.lean.aristotle/Q3/Basic/Defs.lean; q3.lean.aristotle/Q3/Axioms.lean; q3.lean.aristotle/Q3/Main.lean; q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean | verify=cd q3.lean.aristotle && lake env lean Q3/Main.lean | done_when=active Lean docstrings no longer sound like the broad cone is the public RH contract | if_fail_then=move the wording freeze back into tracker/orchestrator and defer Lean docstring cleanup`

## BLOCKED

`G1.6-bg | gate=background | target=Monitor/download/triage Aristotle project ad4c74f1-764f-4cfb-a229-2bc0b2905b67 only for reusable local support lemmas; do not let it drive the public mainline while `SF-pd` is active | files=q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md; q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/docs/INSIGHTS.md | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('ad4c74f1-764f-4cfb-a229-2bc0b2905b67')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=its output is classified as reusable-local or superseded-background | if_fail_then=leave it background and continue the corrected-cone mainline`

`LF-pd.1 | gate=LF-pd | target=Rewrite the LF lift so that it consumes local positivity on the corrected cone `\mathcal W_K^{pd}` rather than on the broad cone `W_K` | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; full/sections/Weil_linkage.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=rg -n "LF|mathcal W\\^\\{pd\\}|W_K|positive-definite" full/sections/Main_closure.tex full/sections/Weil_pack.tex full/sections/Weil_linkage.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | done_when=LF transfer is stated only on the corrected cone | if_fail_then=keep LF as conditional skeleton pending local corrected-cone positivity`
