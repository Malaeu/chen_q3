# Track B Handoff: E5p Same-Unit Bridge

Status: task note for the `rh_clean` branch.

## Naming

Use `E5p` in filenames and task notes. Read `E5′` or `E5p` as `E five prime` / `E fuenf Strich`.

## Sync rule

Before editing this track, run:

```bash
git fetch origin
git rebase origin/rh_clean
```

Then read:

```text
docs/trackB/TRACKB_PRICE_TABLE.md
docs/trackB/S5C_LP_FINITE_DUAL_FEASIBILITY.md
docs/trackB/S5C_LP_NUMERICAL_GATE.md
docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md
```

## Core correction

Do not identify the `duality_gap` `d_K - p_K` with the analytic `mu_K` budget.

Use:

```text
certificate_gap_K = d_K - p_K - finite_guards_K
budget_slack_K    = mu_K - d_K - transfer_guards_K
```

A positive `certificate_gap_K` means only that the finite LP candidate has room over the finite primal worst direction.

E5p closure requires:

```text
budget_slack_K > 0
```

after a same-unit bridge proving that `mu_K` and `d_K` are measured in the same `G_K` / edge-defect units.

## Target inequality

For the current K-cell, certify:

```text
v^T E_edge,K v <= mu_K * v^T G_K v
```

for every boundary-null vector `v`, where:

```text
E_edge,K = P_edge,K - P0_edge,K
Q_K v = 0
```

Penalty receiver shape:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0
```

## Deliverables

1. Rename or annotate the old LP-mu-budget label as `certificate_gap_K` / `duality_gap_K`.
2. Define `budget_slack_K=mu_K-d_K-transfer_guards_K`.
3. State that finite LP success is `B2B_LP_CERT_READY`, not green E5p closure.
4. Reserve green closure for: same-unit bridge + positive `budget_slack_K` + proof-grade PSD or penalty certificate.
5. Keep old Step32F as an LDL/penalty method pattern only, not as free Track B edge budget.

## Further references

- [`CODEX_HANDOFF_E5P_DETAILED.md`](CODEX_HANDOFF_E5P_DETAILED.md) — operational
  handbook: atlas card mapping (020 / 028 / 009 / 029), D1–D5 priorities,
  compute discipline (no per-K interval grids as proof input), rebase protocol.
- [`TRACKB_E5P_THEOREM.md`](TRACKB_E5P_THEOREM.md) — paper-spec of
  `Theorem E5p_edge_closure_K`: four assumptions (A1–A4), implication proof,
  per-assumption status table, sub-lemma names.
- [`TRACKB_E5P_SAME_UNIT_BRIDGE_PATCH.md`](TRACKB_E5P_SAME_UNIT_BRIDGE_PATCH.md) —
  concrete diff plan for the naming sweep and bookkeeping harmonization
  (files to scan, regex checks, sanity commands).
