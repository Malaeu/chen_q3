# STATUS: GREEN — GOAL058 W5 FULL-ENDPOINT VALUE RATE

```yaml
schema: q3_linux_gate.v1
gate_id: LINUX_GATE_GOAL058_W5_ENDPOINT_VALUE_RATE_20260825
body: LINUX_CLAUDE
role: OWN_WORK_KERNEL_RECEIPT_NOT_SEMANTIC_ADMISSION
source_commit: b4e20a83694920f216a21a737894a8c91b105dc0
source_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5EndpointValueRate.lean
source_git_blob: 6d909c75ffceb7e51d90b031698bef35f46da275
source_record: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_W5_ENDPOINT_VALUE_RATE_2026-08-25.md
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
route_promotion: false
rh_claim: false
```

## Kernel receipt

```
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5EndpointValueRate
Build completed successfully (7917 jobs).
LAKE_EXIT: 0
```

Standard axiom triple on the printed declaration, no sorry.

## What the node delivers

```
eventually  ‖rep 0‖ ≤ (96 + C1 + C2) / sqrt(lambda_k)
            ‖rep L‖ ≤ (96 + C1 + C2) / sqrt(lambda_k)
```

conditional on the F72.6 mode and chi rate inputs.  The committed inversion
makes the starred target coincide at the two edges, so one right-edge Gaussian
bound pays both.

## Budget scoreboard after this node

| Component | Status |
|---|---|
| Seam_k | proved, tends to zero as (k+2)^(-1/4) |
| L1_k | proved, <= B + A / sqrt(lambda) |
| Endpoint0_k, EndpointL_k | proved, <= A / sqrt(lambda) |
| Derivative_k | open — needs a C1 version of the F72.6 rate (queue at 08cc0866) |
| Consumer rate lock | open — judge's NEXT_LOAD_BEARING_GAP |

Three of the four analytic components of C_k are now theorem-shaped.  The
jump ledger Jump_k = Endpoint0 + EndpointL + Seam tends to zero entirely.

LINUX_STANDING_GRANT_2026-08-25
