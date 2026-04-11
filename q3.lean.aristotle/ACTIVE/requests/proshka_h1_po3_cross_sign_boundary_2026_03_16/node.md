# Request Node — `proshka_h1_po3_cross_sign_boundary_2026_03_16`

## Status

Active phase worker request for the `PO3a` proof-packet audit.

## Source

- phase: `H1_real_proof_attack`
- owner: local orchestrator
- current step: `PO3`

## Phase/Sprint link

- monitor:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
- current artifact:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`

## Why we are here

`PO2` now lands in the admissible mixed-shell form
`\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`,
and the historical `PO3` note freezes the right shell.
But the actual proof packet for `PO3a` is still missing.

So the next narrow question is:

```tex
\text{what exact mathematical input would really imply }
\mathcal D_{a,\partial}^{+-}=0\ ?
```

If that packet is real, the rest of Door 1 and the packaged `PO4 -> H4`
chain can be synchronized and only then formalized. If not, `PO3a` remains the
live mathematical blocker.

## Exact task

Provide the cleanest proof-grade packet for `PO3a`:

1. state the exact missing lemma that would identify the mixed boundary term
   `\mathcal D_{a,\partial}^{+-}`;
2. list the minimal already-existing inputs that support this lemma;
3. name the sharpest blocker if those inputs still stop short of exact
   cancellation;
4. give the cleanest handoff from a real `PO3a` packet to `PO3b/PO3c` and
   then `PO4/PO5`.

## Required deliverables

- one exact missing-lemma recommendation;
- one smallest theorem packet to attack first;
- one short blocker table:
  `already supported` / `missing explicit formula` / `route-kill if absent`;
- one recommendation for the cleanest post-`PO3` sync into `PO4` and `PO5`.

## Supporting files

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
6. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_boundary_cap_reset_2026_03_14.md`
7. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_four_block_bulk_2026_03_08.md`

## Non-goals

- no same-sign `(++)` theorem work beyond handoff checking;
- no reopening of `PO2`;
- no premature Aristotle drafting;
- no new RH architecture;
- no numerics or basis-fit language.

## Write-back contract

Write result only to:

`/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md`

If you create extra artifacts, list exact absolute paths in the report.
