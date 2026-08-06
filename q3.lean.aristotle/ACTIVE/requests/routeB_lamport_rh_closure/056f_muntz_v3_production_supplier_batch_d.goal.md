# GOAL 056 / Phase 3D — Müntz-v3 production supplier Batch D

```yaml
GOAL: 056
PHASE: 3D
NODE: MuntzV3ProductionSupplierBatchD
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port `MuntzV3HabsExactClass` from the isolated Lean-4.28 request project as
`Q3.Proofs.RouteB.MuntzV3.HabsExactClass` under production Lean 4.26.

The only permitted body changes are the outer production provenance header and
replacement of its two request-project imports by the exact production module
paths.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MuntzV3HabsExactClass@60fd35f3c755c2a79c0c290f71e7a7a8e1c8e0d541a025e3a508eefc7496b9b7
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact Habs supplier port to production Lean 4.26
  preserved_invariants:
    - theorem name and full hypothesis list
    - half-plane threshold 1/2 < re s
    - exact Gwin equals zeta-Mellin minus Rminus minus Rplus identity
    - root Estar and Mellin versus namespaced window-tail definitions
    - all private decomposition lemmas and endpoint transports
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - weaken hb, support, Lipschitz, zero-mass, or half-plane hypotheses
    - edit request-project source
    - claim exact-class closure, receiver, tail, SlotS2, promotion, or RH closure
```

## Exact production import map

- `RequestProject.MuntzV3EStarMellinAbsolutePayload` becomes
  `Q3.Proofs.RouteB.MuntzV3.EStarMellinAbsolutePayload`.
- `RequestProject.MuntzV3RminusExactClass` becomes
  `Q3.Proofs.RouteB.MuntzV3.RminusExactClass`.

## Plants and validation

- `P056F_1`: normalized diff detects any non-import body mutation.
- `P056F_2`: forbidden-import scan detects request-project or roof imports.
- `P056F_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target build for the production module.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch D materializes the existing `Habs` supplier only. It does not yet
assemble the exact-class closure, symmetric crosswalk, prolate receiver, tail
decay, strict SlotS2, promotion, or RH.
