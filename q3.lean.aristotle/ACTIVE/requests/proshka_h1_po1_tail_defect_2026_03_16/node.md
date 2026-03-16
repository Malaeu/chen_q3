# Request Node — `proshka_h1_po1_tail_defect_2026_03_16`

## Status

Active phase worker request for the first direct theorem packet after the
closed `Q_\zeta` sprint.

## Source

- phase: `H1_PO1_direct_attack`
- owner: local orchestrator
- current step: `P1`

## Phase/Sprint link

- monitor:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
- current artifact:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po1_tail_defect_attack_2026_03_16.md`

## Why we are here

The closed sprint already froze:

- the cross-sign receiver as exact-or-cap-only;
- the same-sign receiver as boundary-plus-cap;
- the `H1^\infty -> H1^\partial -> H1^f` proof ladder.

So the next honest move is no longer another classifier pass. It is to make
`PO1a/PO1b` theorem-grade:

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
-\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N.
```

and its blockwise split.

## Exact task

Give a structural-math receiver for `PO1a/PO1b`:

1. confirm or improve the exact tail-level definition of `\mathcal D_{a,N}`;
2. state the cleanest block-splitting lemma;
3. identify the minimal assumptions needed to justify the Hermitian mirror
   identities;
4. say whether `Q_\infty` and `S_{a,\infty,N}` should be treated as algebraic
   tail objects first, or whether a completed Hilbert-space formulation is
   already forced at `PO1`.

## Required deliverables

- one theorem-shaped statement for `PO1a`;
- one theorem-shaped statement for `PO1b`;
- one short table:
  `already frozen` / `still ambiguous` / `should be postponed to PO2+`;
- one recommendation on the correct ambient space language for the first proof.

## Supporting files

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po1_tail_defect_attack_2026_03_16.md`
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_proof_obligation_table_2026_03_16.md`
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_plus_boundary_inventory_2026_03_15.md`
5. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`

## Non-goals

- no new RH architecture;
- no rank/basis language;
- no finite-section numerics;
- no attempt to solve `PO2/PO3` already here.

## Write-back contract

Write result only to:

`/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/proshka_h1_po1_tail_defect_2026_03_16/report.md`

If you create extra artifacts, list exact absolute paths in the report.
