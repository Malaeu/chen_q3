# GOAL 056 / Phase 4B — named object-first Galerkin residual contract

```yaml
GOAL: 056
PHASE: 4B
NODE: D0PstarMuntzGalerkinResidualContract
STATUS: OPEN
OPERATIVE_CLASS: TRY_NAMED_RESIDUAL_CROSSWALK_CONTRACT
TRANSACTION: G6_S2_D0PSTAR_MUNTZ_NAMED_RESIDUAL_CROSSWALK_CONTRACT
STOP: G6_S2_NAMED_OBJECT_RESIDUAL_CROSSWALK_CONTRACT_MISSING
SUCCESS: G6_S2_NAMED_OBJECT_RESIDUAL_CONDITIONAL_RECEIVER_MATERIALIZED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 2
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

Proshka selected Path B under `CODEX_PLUS_PROSHKA` authority at source pin
`8487d4dc3557b8bfe4d57f61c3b67508d7d19f23`.  The exact verdict is archived
at `proshka/PROSHKA_VERDICT_GOAL056_OBJECT_FIRST_RESIDUAL_CONTRACT_2026-08-06.md`.
This transaction is representation progress: it names one missing object-first
identity and exposes it as an explicit hypothesis.  It does not prove the
identity, decay, or `SlotS2`.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock@ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
    - docs/CODEX_CONTROL.md@fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  terminal_consumer: Q3.RouteB.CanonicalRHRoute.SlotS2 under standing Goal 056
  relation_under_test: exact scalar-coordinate crosswalk for the literal normalized Galerkin object residual
  owned_file: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  sole_import: Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
  namespace: Q3.RouteB.D0Pstar
  preserved_invariants:
    - selected index is selectedPairIndex S k = (parent (extract k)).1
    - source trial is selectedProlateTrial S k
    - residual order is normalized projection minus normalized full object
    - normalizer is the exact selectedTrialNormalizer = sTrial_m_N
    - coordinate measure is dStar.restrict (I_m i)
    - Mellin kernel is (u : C)^(-I*z)
    - contract remains an explicit Prop hypothesis, never an axiom
  forbidden_shortcuts:
    - define the object residual from rawFplus minus scaled Gwin
    - reverse the residual sign or change parent/extract
    - replace dStar by volume or reverse the Mellin exponent
    - omit selectedTrialNormalizer
    - assert orthonormality, projection reconstruction, measure transport, decay, tails, or SlotS2
    - import Aristotle output or ACTIVE RequestProject modules
    - edit Q3.Main, Goal 055, or create Bus 010
```

## Exact production declarations

1. `selectedNormalizedGalerkinResidual S k` is literally
   ```text
   (selectedTrialNormalizer S k : C) •
     ((gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp)
   ```
   for `i := selectedPairIndex S k`, `h := selectedProlateTrial S k`, and
   `hLp := S.source.eStar_memLp i`.
2. `selectedGalerkinResidualMellinCoordinate S k z` is the integral of that
   literal object against `(u : C)^(-I*z)` under
   `dStar.restrict (I_m i)`.
3. `D0PstarMuntzGalerkinResidualCrosswalkContract S : Prop` states, for every
   `k,z`, that the Phase-4A coordinate defect equals this object coordinate.
   It is not proved or installed globally.
4. `selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate` is the
   sole direct consumer.  Its proof rewrites the Phase-4A decomposition and
   then the explicit contract at `k,-z`; it contains no estimate or limit.

## Load-bearing plants

```yaml
P056K_1_RESIDUAL_SIGN:
  mutation: reverse projection_minus_full
  expected: G6_S2_RESIDUAL_SIGN_ORIENTATION_MISMATCH
P056K_2_PARENT_EXTRACT:
  mutation: use parent_k_or_shifted_extract
  expected: G6_S2_RESIDUAL_PARENT_EXTRACT_MISMATCH
P056K_3_MEASURE_ORIENTATION:
  mutation: replace dStar by volume and minus-I-z by plus-I-z
  expected: G6_S2_RESIDUAL_MEASURE_KERNEL_MISMATCH
P056K_4_NORMALIZER:
  mutation: delete selectedTrialNormalizer
  expected: G6_S2_RESIDUAL_NORMALIZER_MISMATCH
```

All plants are temporary and must be removed after they fire.  Validation
requires direct Lean, target/full build, `q3_check`, hole and forbidden-import
scans, theorem/axiom inventory, proof-DB reimport, strict Spine, tests, SQLite
integrity, `git diff --check`, and an exact status report.

## Boundary

This leaf may close only with
`G6_S2_NAMED_OBJECT_RESIDUAL_CONDITIONAL_RECEIVER_MATERIALIZED`.  The full
`L2/Fourier/Mellin` bridge is the sole runner-up and is not bundled here.
Compact-open residual decay remains a separate wall.  No strict `SlotS2`,
route promotion, PX claim, or RH claim follows.
