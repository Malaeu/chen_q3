# GOAL 056 / Phase 3E — Müntz-v3 production supplier Batch E

```yaml
GOAL: 056
PHASE: 3E
NODE: MuntzV3ProductionSupplierBatchE
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port `MuntzV3ExactClassClosure` from the isolated Lean-4.28 request project as
`Q3.Proofs.RouteB.MuntzV3.ExactClassClosure` under production Lean 4.26.

The only permitted body changes are the outer production provenance header and
replacement of its four request-project imports by the exact production module
paths.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MuntzV3ExactClassClosure@f4ea12e1497b37a809c27db35f95035111d0d126942ea8c7557ec435b0e3ebfd
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact four-supplier closure port to production Lean 4.26
  preserved_invariants:
    - all three theorem names and full hypothesis lists
    - continued identity domain -(1/2) < re s
    - raw off-pole exclusion s != 1/2
    - exact pole-value theorem at s = 1/2
    - Gwin, Rminus, Rplus, ZetaMellinPoleSub, and Mellin normalizations
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - weaken hb, support, Lipschitz, zero-mass, domain, or pole hypotheses
    - edit request-project source
    - claim symmetric crosswalk, receiver, tail, SlotS2, promotion, or RH closure
```

## Exact production import map

- `RequestProject.MuntzV3Unconditional` becomes `Q3.Proofs.RouteB.MuntzV3.Unconditional`.
- `RequestProject.MuntzV3GwinExactClass` becomes `Q3.Proofs.RouteB.MuntzV3.GwinExactClass`.
- `RequestProject.MuntzV3RplusExactClass` becomes `Q3.Proofs.RouteB.MuntzV3.RplusExactClass`.
- `RequestProject.MuntzV3HabsExactClass` becomes `Q3.Proofs.RouteB.MuntzV3.HabsExactClass`.

## Plants and validation

- `P056G_1`: normalized diff detects any non-import body mutation.
- `P056G_2`: forbidden-import scan detects request-project or roof imports.
- `P056G_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target build for the production module.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch E materializes the existing exact-class window identities only. It does
not yet assemble the symmetric crosswalk, prolate receiver, tail decay, strict
SlotS2, promotion, or RH.
