# STATUS: GREEN — GOAL058 W5 L1 LOG PACKET MASS RATE

```yaml
schema: q3_linux_gate.v1
gate_id: LINUX_GATE_GOAL058_W5_L1_MASS_RATE_20260825
body: LINUX_CLAUDE
role: OWN_WORK_KERNEL_RECEIPT_NOT_SEMANTIC_ADMISSION
answers_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_L1_LOG_PACKET_MASS_RATE_2026-08-25.md
source_commit: 96bba130f2efb37bd28dbd17eb89b0ff5739efee
source_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5L1MassRate.lean
source_git_blob: 2151175e95b733c002cb56e8302ca78db143b2c5
source_record: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_W5_L1_LOG_PACKET_MASS_RATE_2026-08-25.md
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
route_promotion: false
rh_claim: false
```

## Kernel receipt

```
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5L1MassRate
Build completed successfully (7916 jobs).
LAKE_EXIT: 0
```

Every printed declaration carries exactly `propext, Classical.choice,
Quot.sound`.  No `sorryAx`, no `sorry` in source (1009 lines).

## What the node delivers

```
eventually  L1_k  <=  B + A / sqrt (lambda_k)
B = 192 * exp (-pi / 2) * (pi - 1/2)^(-1)
A = 2 * C1 + C2
```

conditional on the F72.6 mode and chi rate inputs, exactly as the verdict
scoped it.  `C1` is the window bound of the full starred error, `C2` the
F72.6 constant paying the center shadow through `H(0) = 0`.

## Mechanism, verbatim from the verdict's selection

Exact `E_star` cancellation.  The committed inversion
`E_star_explicitCCMLimitH_inv` folds the left window half onto the right;
the half-Gaussian envelope becomes the plain exponential
`24 exp(-pi/2) exp(-(pi-1/2)|x - log lam|)` in the additive coordinate.  No
change of variables and no Poisson summation appears anywhere in the file.
The false Poisson wall from the queue is dead in Lean, not only in
adjudication.

## Prediction fate

`P_W5_L1_3` (0.82): first failure would be dStar/set-integral/change-of-
variables normal form.  Miss — the majorant route never touches `dStar` or a
change of variables, so that failure class was designed out.  The actual
failures were the usual signature drift (`inv_le_inv_of_le`,
`pow_le_pow_left`), a rewrite touching both sides, and one `continuity`
timeout replaced by explicit constructors.

## Scope

Closes `W5_L1_LOG_PACKET_MASS_RATE` only.  Remaining components:
`W5_LOG_DERIVATIVE_BUDGET_RATE`, `W5_FULL_ENDPOINT_VALUE_RATE`,
`W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK`.

LINUX_STANDING_GRANT_2026-08-25
