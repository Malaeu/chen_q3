# GOAL 056 / Phase 3A — Müntz-v3 production core Batch A — answer

```yaml
GOAL: 056
PHASE: 3A
NODE: MuntzV3ProductionCoreBatchA
STATUS: CLOSED
RESULT: G6_S2_MUNTZ_V3_PRODUCTION_CORE_BATCH_A_MATERIALIZED

SCOPE: PRODUCTION_SOURCE_PORT
VERIFIER: LEAN_4_26_PLUS_NORMALIZED_SOURCE_DIFF
ARSENAL_USED:
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The two independent roots of the audited Müntz-v3 receiver closure now exist
as production Lean-4.26 modules:

| Production module | Production SHA-256 | Source | Normalized body |
|---|---|---|---|
| `Q3.Proofs.RouteB.MuntzV3.Core` | `7df74238ff1462eb750b0f975f4b87f4b9eec5f1f46c104890d1345b8e2cf1ca` | request `Main.lean@0b2e52db207610f0e63c3dac3e61c5d14f26d0119ccd11756cdbeeab80f3b888` | byte-identical |
| `Q3.Proofs.RouteB.MuntzV3.R6BoundaryCellBridge` | `5de4af2acf4f703afa61c4b44dc1fa2915cf097c6d96bbdde7da9af01ddd8fe6` | request `R6Export/RiemannBoundaryCellBridge.lean@b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6` | byte-identical |

Each production file adds exactly one seven-line outer provenance block.
Removing that block makes `cmp` return zero against its pinned request source.
No import or namespace rewrite was required because both source roots import
only Mathlib.

## Public surface and trust

`Core` materializes the exact definitions `Estar`, `Mellin`, `Gwin`,
`Rminus`, `Rplus`, `MellinDivOne`, `ZetaResidueFactor`,
`ZetaMellinPoleSub`, and the three continued-window consumer theorems.

`R6BoundaryCellBridge` materializes the independent root `Estar` and the
finite-reduction, integrability, cell-error, zero-mass, and square-root
boundary estimates used by the exact E* bound.

The six public terminal theorems checked explicitly all have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No new axiom, source theorem, or mathematical strengthening was introduced.

## Plant results

```yaml
P056C_1:
  result: FIRED
  evidence: a one-import normalized mutation changes cmp exit from 0 to 1
P056C_2:
  result: FIRED
  evidence: forbidden-import scanner detects synthetic "import RequestProject.Main"; production imports have zero matches
P056C_3:
  result: FIRED
  evidence: synthetic axiom plant prints [batchAForbidden], while six production terminal theorems print only the standard triple
```

The temporary axiom plant was deleted.

## Validation

```yaml
DIRECT_LEAN_CORE: PASS
DIRECT_LEAN_R6_BOUNDARY: PASS
TARGET_BUILD: PASS_7744_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK_CORE: PASS
Q3_CHECK_R6_BOUNDARY: PASS
NORMALIZED_BODY_COMPARISON: TWO_OF_TWO_IDENTICAL
FORBIDDEN_IMPORTS: ZERO
TAINT_SCAN: ZERO
PUBLIC_AXIOMS: STANDARD_TRIPLE_ONLY
PROOF_DB_REIMPORT:
  MuntzV3Core: proven, 28 declarations, 247 lines
  MuntzV3R6BoundaryCellBridge: proven, 9 declarations, 352 lines
```

## Boundary

Batch A proves only that the first two existing source modules port without
semantic drift to production Lean 4.26.  It does not yet materialize the
exact-class suppliers, symmetric-trial crosswalk, prolate receiver, tail decay,
strict SlotS2, route promotion, or RH.

## Next executable object

`MuntzV3ProductionSupplierBatchB` ports four direct Batch-A consumers:

1. `MellinCompactSupportAnalyticity`;
2. `MellinConvergentSqrtTail`;
3. `MuntzV3EStarMellinAbsolutePayload`;
4. `MuntzV3EstarBoundExactClass`.

Their request imports will be replaced only by
`Q3.Proofs.RouteB.MuntzV3.Core` and
`Q3.Proofs.RouteB.MuntzV3.R6BoundaryCellBridge`, followed by the same
normalized-diff, Lean, taint, and axiom gates.

`CHALLENGER / NOT_RH`; Bus 010 `VOID`; Goal 055 `HOLD`;
`ARISTOTLE_SUBMISSION: NONE`; `PX_RH_CLAIM: NOT_MADE`.
