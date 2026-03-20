# Request Node — `proshka_h1_po2_cross_sign_bulk_2026_03_20`

## Status

Active phase worker request for the real proof-critical reset at `PO2`.

## Source

- phase: `H1_real_proof_attack`
- owner: local orchestrator
- current step: `PO2`

## Phase/Sprint link

- monitor:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
- current artifact:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`

## Why we are here

The upper bridge `H2^f -> H3^f -> H4^f` is already packaged tightly enough at
the theorem-shell level.

But RH is still not proved, because the whole bridge remains conditional on the
first unresolved `H1` proof input.

So the next narrow question is:

```tex
\text{does the cross-sign tail block carry any genuine bulk residue?}
```

## Exact task

Provide the cleanest theorem-grade receiver for `PO2`:

1. state the pure bulk-vanishing target
   `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
2. state the exact boundary/cap-only fallback;
3. state the sharpest route-kill condition if an unnamed bulk residue survives;
4. state the cleanest handoff from `PO2` to `PO3`;
5. explicitly explain why `H2/H3/H4` should be treated only as conditional
   consumers until this lands.

## Required deliverables

- one theorem-shaped `PO2` package;
- one short table:
  `pure bulk vanishing` / `boundary+cap fallback` / `route-kill` / `handoff`;
- one recommendation for the cleanest post-`PO2` move into `PO3`.

## Supporting files

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_four_block_bulk_2026_03_08.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_raw_entry_reduction_2026_03_08.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`

## Non-goals

- no reopening of `H2`;
- no reopening of `H3`;
- no more endpoint packaging;
- no new RH architecture.

## Write-back contract

Preferred native-worker mode:

- return a narrow theorem-shaped summary to the parent/orchestrator thread;
- let the orchestrator write the canonical report file.

Canonical report target:

`/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_20/report.md`

If you create extra artifacts, list exact absolute paths in the summary/report.
