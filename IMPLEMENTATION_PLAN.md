# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`T0.1 | gate=T0/G6 | target=Audit whether the current target cone W_K / 𝒲 is mathematically too broad for the classical Weil criterion, and decide whether the reset-loop may continue on the present cone or must pivot to a positive-definite / convolution-square cone | files=q3.lean.aristotle/Q3/Basic/Defs.lean; q3.lean.aristotle/Q3/Axioms.lean; full/sections/Main_closure.tex; full/sections/Weil_linkage.tex; q3.lean.aristotle/docs/reviewed_notes/2026_03_07_target_cone_reset_review.md; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=rg -n \"def W_K|W_K :=|compactly supported|Weil criterion|positive definite|convolution-square|psi\\*psi\\^e\" q3.lean.aristotle/Q3/Basic/Defs.lean q3.lean.aristotle/Q3/Axioms.lean full/sections/Main_closure.tex full/sections/Weil_linkage.tex q3.lean.aristotle/docs/reviewed_notes/2026_03_07_target_cone_reset_review.md && source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport mpmath as mp\nmp.mp.dps = 50\nfor x in [1.5, 2, 3]:\n    a = mp.log(mp.pi) - mp.re(mp.digamma(mp.mpf('0.25') + 1j*mp.pi*x))\n    print(x, a)\nPY | done_when=the repo has a written verdict: either the current W_K contract survives the audit, or the project explicitly records that the target cone must be narrowed before further closure work | if_fail_then=freeze the audit as an unresolved architectural blocker and keep all G1-G3 work explicitly conditional on the current target cone`

## QUEUED

`G1.6 | gate=G1 | target=Monitor/download/triage Aristotle project ad4c74f1-764f-4cfb-a229-2bc0b2905b67 for atom_sum_mem_W_K_of_margin under the updated exact?-tolerant workflow | files=q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md; q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && python - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('ad4c74f1-764f-4cfb-a229-2bc0b2905b67')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=the downloaded result is classified by the new policy: hard-hole scan on sorry/admit, advisory scan on exact?, and compile-context verdict recorded | if_fail_then=promote the first blocked local sublemma as the new single active theorem target`

`G1.7 | gate=G1 | target=If the local W_K-membership brick lands, build the small AtomCone_K_fixed wrapper theorem on top of it | files=q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=cd q3.lean.aristotle && lake env lean Q3/Proofs/A1prime/A1_density_fixed_t0.lean | done_when=the stronger atom_sum_mem_atomcone_fixed_of_margin wrapper is stated on top of the landed W_K brick | if_fail_then=keep the W_K theorem as the honest stopping point and do not widen the claim`

`G1.8 | gate=G1 | target=If the local membership brick lands, build the small A2-facing error-budget wrapper for the frozen replacement route | files=q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=cd q3.lean.aristotle && lake env lean Q3/Proofs/A1prime/A1_density_fixed_t0.lean | done_when=the frozen G1.1 replacement route has both an admissible membership brick and an explicit A2 error-budget wrapper | if_fail_then=split the wrapper into a norm-transfer lemma and a final A2 application lemma`

## BLOCKED

`G2.1 | gate=G2 | target=List candidate admissible families G_K that could implement the chosen G1 route without reopening two dictionaries | files=q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; full/sections/Main_closure.tex | verify=rg -n "G_K|common admissible family|shifted evenized|support-compatible" q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md full/sections/Main_closure.tex | done_when=G2 has a short candidate list tied explicitly to the frozen G1 statement | if_fail_then=record why G1 still underspecifies the family choice`

`G3.1 | gate=G3 | target=Choose the positivity route on the eventual G_K (transport from centered A3/RKHS vs direct shifted theorem) without claiming closure yet | files=full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G3|positivity on G_K|transport|direct shifted theorem|A3|RKHS" full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the project has one declared G3 route conditioned on the frozen G1/G2 choices | if_fail_then=leave G3 blocked and keep the ambiguity explicit`
