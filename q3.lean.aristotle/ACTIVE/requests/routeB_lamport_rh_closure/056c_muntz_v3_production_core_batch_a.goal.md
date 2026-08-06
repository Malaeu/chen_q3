# GOAL 056 / Phase 3A — Müntz-v3 production core Batch A

```yaml
GOAL: 056
PHASE: 3A
NODE: MuntzV3ProductionCoreBatchA
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port the two independent roots of the audited Müntz-v3 receiver closure from
the isolated Lean-4.28 request project into the Lean-4.26 production module
graph:

- `RequestProject/Main.lean` →
  `Q3/Proofs/RouteB/MuntzV3/Core.lean`;
- `RequestProject/R6Export/RiemannBoundaryCellBridge.lean` →
  `Q3/Proofs/RouteB/MuntzV3/R6BoundaryCellBridge.lean`.

Only provenance headers and module paths may differ.  Public declarations,
theorem statements, proof bodies, namespaces, options, and sign conventions
must remain unchanged.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - RequestProject.Main@0b2e52db207610f0e63c3dac3e61c5d14f26d0119ccd11756cdbeeab80f3b888
    - RequestProject.R6Export.RiemannBoundaryCellBridge@b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6
  terminal_consumer: MuntzV3ProlateCombinationReceiver
  relation_under_test: exact source-body port to production Lean 4.26
  preserved_invariants:
    - public declaration names and types
    - Gwin = window integral of Estar
    - Rminus and Rplus domains
    - ZetaMellinPoleSub convention
    - root Estar boundary-cell bridge
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - weaken statements or add axioms
    - edit source request files
    - claim receiver, tail, SlotS2, or RH closure
```

## Required plants

- `P056C_1`: normalized production body differs from source beyond the
  provenance header → fail.
- `P056C_2`: any production import contains `RequestProject`,
  `aristotle_output`, or a roof → fail.
- `P056C_3`: direct Lean-4.26 compilation fails or public axioms exceed the
  standard triple → fail.

## Validation

1. direct Lean for both production modules;
2. target `.olean` builds;
3. normalized SHA/body comparison;
4. `sorry|admit|exact?|axiom|native_decide` scan;
5. public axiom inventory;
6. full production build and `q3_check`.

## Boundary

Batch A materializes definitions and existing exact lemmas only.  It does not
connect the production prolate packet, prove tail decay, identify SlotS2, or
promote Route B.
