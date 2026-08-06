# GOAL 056 / Phase 3G — Müntz-v3 production receiver Batch G

```yaml
GOAL: 056
PHASE: 3G
NODE: MuntzV3ProductionReceiverBatchG
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Port `MuntzV3ProlateCombinationReceiver` from the isolated Lean-4.28 request
project as `Q3.Proofs.RouteB.MuntzV3.ProlateCombinationReceiver` under
production Lean 4.26.

The only permitted body changes are the outer production provenance header and
replacement of its three request-project imports by the exact production module
paths.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - MuntzV3ProlateCombinationReceiver@ab12e82fbf3993318b9e9a1dae850f20a81f944b4a71e0c9460a7d2e78212d84
    - Q3.Proofs.RouteB.ProlateCombinationMuntzRegularity@d3990c1be7288b49f6d63dec42bbfa12e7799a955d80bee24c3ca9dcea9624c0
    - Q3.Proofs.RouteB.ProlateModeRegularity@d09f80b47386afcddec890de959060e00961c57e19ca9db73a8bdcf507a06177
  terminal_consumer: strict SlotS2 bridge under Goal 056
  relation_under_test: exact prolate-combination receiver port to production Lean 4.26
  preserved_invariants:
    - canonical Q3.RouteB.D0Pstar.ProlatePair and prolateCombination objects
    - first theorem requires supplied mode measurability and positive-half Lipschitz
    - second theorem derives measurability from stored evenness and support
    - full hlambda, K0, K4, Lambda, and half-plane hypothesis lists
    - explicit nonclaim of mode construction, normalization, or cofinal ground family
  forbidden_shortcuts:
    - import RequestProject.*
    - import either roof
    - replace the provenance-locked production ProlatePair or combination
    - weaken mode Lipschitz, lambda, window, or half-plane hypotheses
    - edit request-project source
    - claim tail decay, strict SlotS2, promotion, or RH closure
```

## Exact production import map

- `RequestProject.MuntzV3SymmetricTrialCrosswalk` becomes
  `Q3.Proofs.RouteB.MuntzV3.SymmetricTrialCrosswalk`.
- `RequestProject.ProlateExport.ProlateCombinationMuntzRegularity` becomes
  `Q3.Proofs.RouteB.ProlateCombinationMuntzRegularity`.
- `RequestProject.ProlateExport.ProlateModeRegularity` becomes
  `Q3.Proofs.RouteB.ProlateModeRegularity`.

## Plants and validation

- `P056I_1`: normalized diff detects any non-import body mutation.
- `P056I_2`: forbidden-import scan detects request-project or roof imports.
- `P056I_3`: a synthetic added axiom is visible beyond the standard triple.
- Direct Lean-4.26 and target build for the production module.
- Full build, `q3_check`, taint scan, public axiom inventory, and proof-DB
  reimport.

## Boundary

Batch G closes the 14-module production export only. It does not prove the
XW.6 coordinate lock, construct a finite/cofinal prolate family, prove tail
decay, close strict SlotS2, promote the route, or claim RH.
