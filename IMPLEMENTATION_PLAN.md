# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`G1.1 | gate=G1 | target=Freeze the first honest support-upgrade theorem statement on admissible W_K (support-density vs restriction-to-support replacement) | files=full/sections/A1prime.tex; full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "support upgrade|restriction-to-support|Q\\^\\* error|dense in W_K" full/sections/A1prime.tex full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=one exact G1 theorem statement is fixed in the tracker and mirrored in the manuscript dependency language | if_fail_then=keep G1 at statement-design level, record the narrower obstruction, and do not open G2`

## QUEUED

`G1.2 | gate=G1 | target=Collect reusable local lemmas and candidate formulations for the support upgrade route | files=q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; full/sections/A1prime.tex; full/sections/Main_closure.tex | verify=rg -n "G1|support upgrade|restriction-to-support|R_K|W_K" q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md full/sections/A1prime.tex full/sections/Main_closure.tex | done_when=the next proof search can point to one exact theorem target and a finite reuse list | if_fail_then=split the search into theorem-shape and error-budget subtasks`

`G2.1 | gate=G2 | target=List candidate admissible families G_K that could implement the chosen G1 route without reopening two dictionaries | files=q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; full/sections/Main_closure.tex | verify=rg -n "G_K|common admissible family|shifted evenized|support-compatible" q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md full/sections/Main_closure.tex | done_when=G2 has a short candidate list tied explicitly to the frozen G1 statement | if_fail_then=record why G1 still underspecifies the family choice`

`G3.1 | gate=G3 | target=Choose the positivity route on the eventual G_K (transport from centered A3/RKHS vs direct shifted theorem) without claiming closure yet | files=full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G3|positivity on G_K|transport|direct shifted theorem|A3|RKHS" full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the project has one declared G3 route conditioned on the frozen G1/G2 choices | if_fail_then=leave G3 queued and keep the ambiguity explicit`

## BLOCKED

None.
