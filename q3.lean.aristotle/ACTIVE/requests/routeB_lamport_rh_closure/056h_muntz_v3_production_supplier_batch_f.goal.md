# GOAL 056 / Phase 3F — Müntz-v3 production supplier Batch F

```yaml
GOAL: 056
PHASE: 3F
NODE: MuntzV3ProductionSupplierBatchF
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port `MuntzV3SymmetricTrialCrosswalk` from the isolated Lean-4.28 request
project as `Q3.Proofs.RouteB.MuntzV3.SymmetricTrialCrosswalk` under production
Lean 4.26.

The only permitted body changes are the outer production provenance header and
replacement of its single request-project import by the production
`ExactClassClosure` path.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MuntzV3SymmetricTrialCrosswalk@ebede2df7ff55b811bafd1dcbbb55baea064658b406611bbec4e093fd94c6f9b
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact symmetric positive-half crosswalk port to production Lean 4.26
  preserved_invariants:
    - positiveHalf is exactly the Ici 0 indicator
    - pointwise Estar, Mellin, Gwin, Rminus, Rplus, and pole-subtracted transports
    - symmetric support Icc (-b) b to positive support Icc 0 b
    - final continued identity domain -(1/2) < re s
    - explicit nonclaim of finite-family identification or cofinal limit
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - identify positiveHalf with h globally
    - weaken symmetry, support, Lipschitz, mass, or domain hypotheses
    - edit request-project source
    - claim prolate receiver, tail, SlotS2, promotion, or RH closure
```

## Plants and validation

- `P056H_1`: normalized diff detects any non-import body mutation.
- `P056H_2`: forbidden-import scan detects request-project or roof imports.
- `P056H_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target build for the production module.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch F materializes only the existing positive-half symmetric crosswalk. It
does not yet identify the production prolate combination, prove tail decay,
close strict SlotS2, promote the route, or claim RH.
