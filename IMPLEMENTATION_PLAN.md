# Implementation Plan

Updated: 2026-03-08

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`PSD-pd.9 | gate=PSD-pd | target=Sharpen the strict packet package to the finite-dictionary P7 form: symmetric packet extension `\\mathcal Q` -> exact sesquilinear identity -> finite Toeplitz reduction on admissible dictionaries -> desired prime-factorization (rejected by obstruction) -> sparse Gershgorin criterion/background-only -> Toeplitz/Herglotz criterion -> exact finite symbol `S_J=A_J-P_J` -> Poisson-regularized verification with explicit error budget -> PSD-pd | files=full/sections/Main_closure.tex; full/sections/Weil_pack.tex; full/sections/introduction.tex; full/sections/abstract.tex; full/sections/scope_notation.tex; full/sections/Notation/qstar_contract.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"\\\\mathcal Q|S_J|A_J|P_J|A_\\{J,r\\}|P_\\{J,r\\}|Poisson|Gershgorin|prime-block obstruction|Toeplitz--Herglotz\" full/sections/Main_closure.tex full/sections/Weil_pack.tex full/sections/introduction.tex full/sections/abstract.tex full/sections/scope_notation.tex full/sections/Notation/qstar_contract.tex q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=all active files present finite admissible dictionary `P7` as the immediate constructive target, with Poisson regularization only as a finite verification device and measure-level language demoted to secondary diagnostic notation | if_fail_then=split into `finite symbol identity`, `Poisson error budget`, and `compact closure wording` subtasks`

## QUEUED

`PSD-pd.H | gate=PSD-pd | target=Keep Herglotz/Bochner only as the diagnostic equivalence route: positive-definite sequence / Toeplitz section / measure representation for the packet coefficients, without letting it masquerade as the constructive mainline | files=full/sections/Main_closure.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "Herglotz|Bochner|diagnostic|secondary" full/sections/Main_closure.tex q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=Herglotz/Bochner is explicit secondary notation everywhere active | if_fail_then=move the wording into a dedicated remark only`

`A1-pd.4 | gate=A1-pd | target=Turn the frozen `A1-pd` theorem block into a proof-ready route on the dense family `\mathcal G_K^{pd}`: pre-square density on `C_c^\infty([-K/2,K/2])` plus `L^1 -> autocorrelation` continuity | files=full/sections/A1prime.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G_K\\^\\{pd\\}|autocorrelation|L\\^1|t_0" full/sections/A1prime.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the density theorem is phrased and decomposed exactly on `\mathcal G_K^{pd}` with no hidden appeal to the broad cone | if_fail_then=split into pre-square density and autocorrelation continuity subtasks`

`LEAN.1 | gate=T0-pd | target=Mark broad-cone Lean exports (`Weil_cone`, `W_K`, broad-cone RH wrappers) as frozen background narrative without renaming theorem identifiers yet | files=q3.lean.aristotle/Q3/Basic/Defs.lean; q3.lean.aristotle/Q3/Axioms.lean; q3.lean.aristotle/Q3/Main.lean; q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean | verify=cd q3.lean.aristotle && lake env lean Q3/Main.lean | done_when=active Lean docstrings no longer sound like the broad cone is the public RH contract | if_fail_then=move the wording freeze back into tracker/orchestrator and defer Lean docstring cleanup`

## BLOCKED

`RAY-naive-bg | gate=background | target=Keep the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` only as an auxiliary quadratic-form candidate; do not let it drive the public closure route after the local-bump obstruction | files=full/sections/Main_closure.tex; full/sections/scope_notation.tex; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n \"G_\\{K,\\\\mathrm\\{Ray\\}\\}|packet-Rayleigh-naive|background\" full/sections q3.lean.aristotle/PROJECT_ORCHESTRATOR.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the naive family is explicitly background-only everywhere active | if_fail_then=repeat the obstruction memo in the affected file`

`G1.6-bg | gate=background | target=Monitor/download/triage Aristotle project ad4c74f1-764f-4cfb-a229-2bc0b2905b67 only for reusable local support lemmas; do not let it drive the public mainline while `PSD-pd` is active | files=q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md; q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/docs/INSIGHTS.md | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('ad4c74f1-764f-4cfb-a229-2bc0b2905b67')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=its output is classified as reusable-local or superseded-background | if_fail_then=leave it background and continue the corrected-cone mainline`
