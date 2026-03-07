# Implementation Plan

Updated: 2026-03-07

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`G1.5 | gate=G1 | target=Monitor, download, scan, and integrate the Aristotle result for the submitted support-replacement packet | files=q3.lean.aristotle/aristotle_input/project_ids.txt; q3.lean.aristotle/aristotle_output/; q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean; q3.lean.aristotle/docs/INSIGHTS.md | verify=source .venv/bin/activate && python3 - <<'PY'\nimport asyncio\nfrom aristotlelib import Project\nasync def main():\n    p = await Project.from_id('c315e2a4-5923-44fa-a18c-4ed90cb08375')\n    print(p.status, p.percent_complete)\nasyncio.run(main())\nPY | done_when=the Aristotle result is downloaded, scanned for holes, and either integrated cleanly or narrowed to the first blocked local lemma | if_fail_then=do not keep a partial patch; revert local integration and make the first blocked local lemma the next ACTIVE task`

## QUEUED

`G1.6 | gate=G1 | target=If the local membership brick lands, build the small A2-facing error-budget wrapper for the frozen replacement route | files=q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | verify=cd q3.lean.aristotle && lake env lean Q3/Proofs/A1prime/A1_density_fixed_t0.lean | done_when=the frozen G1.1 replacement route has both an admissible membership brick and an explicit A2 error-budget wrapper | if_fail_then=split the wrapper into a norm-transfer lemma and a final A2 application lemma`

`G2.1 | gate=G2 | target=List candidate admissible families G_K that could implement the chosen G1 route without reopening two dictionaries | files=q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md; full/sections/Main_closure.tex | verify=rg -n "G_K|common admissible family|shifted evenized|support-compatible" q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md full/sections/Main_closure.tex | done_when=G2 has a short candidate list tied explicitly to the frozen G1 statement | if_fail_then=record why G1 still underspecifies the family choice`

`G3.1 | gate=G3 | target=Choose the positivity route on the eventual G_K (transport from centered A3/RKHS vs direct shifted theorem) without claiming closure yet | files=full/sections/Main_closure.tex; q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n "G3|positivity on G_K|transport|direct shifted theorem|A3|RKHS" full/sections/Main_closure.tex q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md q3.lean.aristotle/docs/INSIGHTS.md | done_when=the project has one declared G3 route conditioned on the frozen G1/G2 choices | if_fail_then=leave G3 queued and keep the ambiguity explicit`

## BLOCKED

None.
