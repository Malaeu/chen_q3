# STATUS: GREEN — GOAL058 W5 INTERNAL SEAM SUM COFINAL DECAY

```yaml
schema: q3_linux_gate.v1
gate_id: LINUX_GATE_GOAL058_W5_INTERNAL_SEAM_SUM_RATE_20260825
body: LINUX_CLAUDE
role: OWN_WORK_KERNEL_RECEIPT_NOT_SEMANTIC_ADMISSION
answers_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_COFINAL_RATE_EDGE_LEDGER_2026-08-25.md
source_commit: ac43234e9638ea9f748d89c2457323ab4f69cfeb
source_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5JumpSeamRate.lean
source_git_blob: 7338295cf78314dbed47f0166c7c8ef319f0862f
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
route_promotion: false
rh_claim: false
```

## Kernel receipt

```
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5JumpSeamRate
Build completed successfully (7913 jobs).
LAKE_EXIT: 0
```

`selectedFerrersAbelLogInternalSeamSum_rate_of_modeAndChiRates` depends on
`propext, Classical.choice, Quot.sound`.  No `sorryAx`, no `sorry` in source.

## What the node delivers

```
eventually  Seam_k  <=  2 * (C + 132) / sqrt (lambda_k)   =  O((k+2)^(-1/4))
```

Conditional on the F72.6 mode and chi rate inputs, exactly as the verdict
scoped it.

Private reconstructions, all three requested by the verdict:

| Declaration | Content |
|---|---|
| `explicitCCMLimitH_inverse_four_decay` | on `1 <= abs x`, the literal CCM limit packet is below `33 / x^4` |
| `finite_inverse_sqrt_sum_le_two_sqrt` | `sum_{n=2}^{N} n^(-1/2) <= 2 * sqrt N` |
| `selectedFerrersLemma73SourcePacket_edge_rate` | `norm h_k(lambda_k) <= (C + 132) / lambda_k^2` eventually |

The target-decay proof spends only `t^4 / 4! <= exp t`.  The true constant is
near 4, so 33 carries a wide margin; no numerical evaluation appears anywhere.

## Scope, stated so it cannot be read wider

This closes the seam component of the W4 jump ledger and nothing else.  The
verdict lists the remaining components explicitly, and none of them is touched
here:

```
W5_L1_LOG_PACKET_MASS_RATE
W5_LOG_DERIVATIVE_BUDGET_RATE
W5_FULL_ENDPOINT_VALUE_RATE
```

`W5_COFINAL_PACKET_BUDGET_RATE` stays open.  The earlier Linux claim that the
whole rate reduces to the edge value was refuted by the verdict and is not
revived by this node.

## Prediction fate

The verdict registered `P_W5_SEAM_3` at 0.78: the first Lean failure would be
normal form, not mathematics, and most likely the finite inverse-square-root
sum.  Half right.  Every failure was normal form — a Mathlib signature, an
untyped `positivity`, a rewrite touching both sides, stuck instance resolution,
a recursive rewrite of `lam` inside its own square root.  But the inverse
square-root sum compiled first try; the trouble sat in the edge lemma instead.

LINUX_STANDING_GRANT_2026-08-25
