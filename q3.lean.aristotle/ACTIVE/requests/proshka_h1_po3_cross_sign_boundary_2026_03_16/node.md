# Request Node — `proshka_h1_po3_cross_sign_boundary_2026_03_16`

## Status

Active phase worker request for `PO3` formalization.

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
and the historical `PO3` note already freezes the right mathematical receiver.

So the next narrow question is:

```tex
\text{what is the first honest executable formalization receiver for }
PO3a/PO3b/PO3c\ ?
```

If that receiver is clean, the rest of Door 1 and the packaged `PO4 -> H4`
chain can be synchronized. If not, we have a real formalization blocker rather
than a new mathematical one.

## Exact task

Provide the cleanest formalization-grade receiver for `PO3`:

1. identify the smallest Lean landing zone or abstract shell file for
   `PO3a/PO3b/PO3c`;
2. state the exact theorem packet that should be sent to Aristotle first;
3. name the sharpest blocker if the current Q3 Lean objects are not yet
   aligned with the mathematical shell;
4. give the cleanest handoff from this receiver to `PO4/PO5`.

## Required deliverables

- one exact receiver recommendation (file path or new shell target);
- one smallest theorem packet to formalize first;
- one short blocker table:
  `already represented in Lean` / `needs shell` / `must not be invented ad hoc`;
- one recommendation for the cleanest post-`PO3` sync into `PO4` and `PO5`.

## Supporting files

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
6. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/refs/q3_structure_mapping.md`
7. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`

## Non-goals

- no same-sign `(++)` theorem work beyond handoff checking;
- no reopening of `PO2`;
- no new RH architecture;
- no numerics or basis-fit language.

## Write-back contract

Write result only to:

`/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md`

If you create extra artifacts, list exact absolute paths in the report.
