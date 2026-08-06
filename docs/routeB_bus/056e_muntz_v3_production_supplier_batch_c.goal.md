# GOAL 056 / Phase 3C — Müntz-v3 production supplier Batch C

```yaml
GOAL: 056
PHASE: 3C
NODE: MuntzV3ProductionSupplierBatchC
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port the four Batch-C analytic suppliers from the isolated Lean-4.28 request
project into `Q3.Proofs.RouteB.MuntzV3`:

1. `MuntzV3GwinExactClass` as `GwinExactClass`;
2. `MuntzV3RplusExactClass` as `RplusExactClass`;
3. `MuntzV3Unconditional` as `Unconditional`;
4. `MuntzV3RminusExactClass` as `RminusExactClass`.

The only permitted body changes are the outer production provenance header and
replacement of request-project imports by the exact Batch-B production module
paths.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MuntzV3GwinExactClass@a433b05d9e798b98a45839b7510dab7199655110cc4de9a764568e2c3e13490c
    - MuntzV3RplusExactClass@e97f34aae6e851dc81a619587f3925c1e05a215fba90fe4d9f469441e6ee8144
    - MuntzV3Unconditional@7bc8e8dbec15ff87a067462a8e7e4cf5a6804c737d067fc046a5d4db3739bef2
    - MuntzV3RminusExactClass@c8a7d583ce60cbe6c75135ded8338a625466c6fb05e004135ddf2da990886847
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact analytic-supplier port to production Lean 4.26
  preserved_invariants:
    - theorem names and full hypothesis lists
    - shifted-half-plane domains for Gwin, Rplus, and Rminus
    - three unconditional continued-window identity statements
    - exact v3-class E-star measurability, local integrability, and support chain
    - root Estar versus namespaced Estar distinction
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - weaken support, Lipschitz, zero-mass, or convergence hypotheses
    - edit request-project source
    - claim Habs, exact-class closure, receiver, tail, SlotS2, promotion, or RH closure
```

## Exact production import map

- `RequestProject.MellinCompactSupportAnalyticity` becomes
  `Q3.Proofs.RouteB.MuntzV3.MellinCompactSupportAnalyticity`.
- `RequestProject.MuntzV3EstarBoundExactClass` becomes
  `Q3.Proofs.RouteB.MuntzV3.EstarBoundExactClass`.
- `RequestProject.MellinConvergentSqrtTail` becomes
  `Q3.Proofs.RouteB.MuntzV3.MellinConvergentSqrtTail`.

## Plants and validation

- `P056E_1`: normalized diff detects any non-import body mutation.
- `P056E_2`: forbidden-import scan detects request-project or roof imports.
- `P056E_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target builds for all four modules.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch C materializes existing analytic suppliers only. It does not yet assemble
`Habs`, the exact-class closure, the symmetric crosswalk, the prolate receiver,
tail decay, strict SlotS2, promotion, or RH.
