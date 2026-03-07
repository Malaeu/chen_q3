# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`G1.3 | gate=G1 | target=Write the finite reuse map for the frozen replacement theorem as a small Aristotle-ready packet or manual proof packet | files=q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/aristotle_input/; q3.lean.aristotle/Q3/Proofs/A1_density.lean; q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean | verify=rg -n "G1.1|replacement theorem|hmargin|hg_supp|hat interpolation|support-preserving replacement|error-budget" q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/Q3/Proofs/A1_density.lean q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean | done_when=one proof packet exists with exact target, reuse list, and no overclaiming | if_fail_then=split the packet into a support lemma packet and an error-budget packet`

## QUEUED

`G2.1 | gate=G2 | target=List candidate admissible families G_K that could implement the chosen G1 route without reopening two dictionaries | files=q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; full/sections/Main_closure.tex | verify=rg -n "G_K|common admissible family|shifted evenized|support-compatible" q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md full/sections/Main_closure.tex | done_when=G2 has a short candidate list tied explicitly to the frozen G1 statement | if_fail_then=record why G1 still underspecifies the family choice`

`G3.1 | gate=G3 | target=Choose the positivity route on the eventual G_K (transport from centered A3/RKHS vs direct shifted theorem) without claiming closure yet | files=full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G3|positivity on G_K|transport|direct shifted theorem|A3|RKHS" full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the project has one declared G3 route conditioned on the frozen G1/G2 choices | if_fail_then=leave G3 queued and keep the ambiguity explicit`

## BLOCKED

None.
