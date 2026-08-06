# GOAL 056 / Phase 3B — Müntz-v3 production supplier Batch B

```yaml
GOAL: 056
PHASE: 3B
NODE: MuntzV3ProductionSupplierBatchB
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port the four direct consumers of production Batch A from the isolated
Lean-4.28 request project into `Q3.Proofs.RouteB.MuntzV3`:

1. `MellinCompactSupportAnalyticity`;
2. `MellinConvergentSqrtTail`;
3. `MuntzV3EStarMellinAbsolutePayload` as
   `EStarMellinAbsolutePayload`;
4. `MuntzV3EstarBoundExactClass` as `EstarBoundExactClass`.

The only permitted body changes are the outer production provenance header and
replacement of request-project imports by the exact Batch-A production module
paths.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MellinCompactSupportAnalyticity@743e7cecf175a0be8c94d844c334ab66bfa5858696e6269a743b17ce0edfe148
    - MellinConvergentSqrtTail@dc91214ad1b7b09a37e0c90eae8891ddf8d1d743550d70380ad77cc6e31c9b04
    - MuntzV3EStarMellinAbsolutePayload@1f460d77a2404cbec83b739a188092e175cc73545fd8b31f5c493f62fafa6d89
    - MuntzV3EstarBoundExactClass@073497faa31264e8a769ccce148a9d3f54353ee3fe340e7004877cf479db769a
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact direct-supplier port to production Lean 4.26
  preserved_invariants:
    - theorem names and full hypothesis lists
    - Mellin half-plane and square-root exponents
    - exact explicit E-star bound constant
    - root Estar versus namespaced Estar distinction
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - weaken hb, support, Lipschitz, mass, or convergence hypotheses
    - edit request-project source
    - claim receiver, tail, SlotS2, promotion, or RH closure
```

## Plants and validation

- `P056D_1`: normalized diff detects any non-import body mutation.
- `P056D_2`: forbidden-import scan detects request-project or roof imports.
- `P056D_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target builds for all four modules.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch B materializes existing analytic suppliers only.  It does not yet
assemble `Gwin`, `Rminus`, `Rplus`, `Habs`, the continued identity,
the prolate receiver, tail decay, strict SlotS2, or RH.
