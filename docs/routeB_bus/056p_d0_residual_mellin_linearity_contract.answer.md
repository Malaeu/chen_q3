# GOAL 056 / Phase 4G answer — residual Mellin linearity contract

```yaml
GOAL: 056
PHASE: 4G
NODE: D0PstarMuntzGalerkinResidualCrosswalk
STATUS: CLOSED
EXACT_RESULT: G6_S2_D0_RESIDUAL_MELLIN_CROSSWALK_CONTRACT_PROVED
OPERATIVE_CLASS: TRY_G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
ARSENAL_USED: [C04, C09, C10]

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 7
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated decision and exact object

The seventh batch in the same living Proshka phase chat selected Candidate
`A_MINIMAL_PRIVATE_HELPER` at pin
`1b1f36629b1236909c027891d4a8f68748c6134c`. The exact verdict is archived
canonically and in the bus mirror with SHA-256
`451152dc6f8adc54a7e35b6169bcfeb3c130d2e97121d7f6254955deda59495f`.

The transaction keeps the existing literal normalized object
`selectedNormalizedGalerkinResidual S k : H_m i`. It does not define the
residual coordinate from a scalar defect. The proof first establishes
integrability of the actual `Lp` representative times the Mellin kernel on
the finite positive log window, then transports `Lp` subtraction and scalar
multiplication only almost everywhere, and only afterward uses Bochner
integral linearity.

The Phase-4E projected/raw and Phase-4F full/Gwin identities are absent from
the jump proof. They are consumed only in the second theorem, which proves the
existing Phase-4B named contract unconditionally without editing or weakening
its original definition.

## Materialized production interface

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
PRODUCTION_SHA256: 73fabe1675476e47228730c3bb4bce07a11c8d351d679c9937f51ef3e3fc9723
PRODUCTION_LINES: 222
PRODUCTION_BYTES: 8656
PROJECT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualContract
  - Q3.Proofs.RouteB.D0PstarFullMellinGwinCrosswalk
PUBLIC_DEFINITIONS: 0
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 1
PROOF_DB_DECLARATIONS: 3
PROOF_DB_STATUS: proven
```

The public jump theorem is

```lean
theorem selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedGalerkinResidualMellinCoordinate S k z =
      selectedProjectedMellinCoordinate S k z -
        (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z
```

and the second public theorem is

```lean
theorem D0PstarMuntzGalerkinResidualCrosswalkContract_proved
    (S : ProlateCanonicalSourceData) :
    D0PstarMuntzGalerkinResidualCrosswalkContract S
```

The sole private helper proves integrability of an arbitrary `H_m i`
representative multiplied by `u ^ (-Complex.I * z)` on the exact restricted
`dStar` measure. No reusable continuous-linear Mellin functional was published.

## Load-bearing plant results

```yaml
P056P_1_OBJECT_SURROGATE:
  result: FIRED
  stop: G6_S2_RESIDUAL_SCALAR_SURROGATE
  evidence: selectedGalerkinCoordinateDefect surrogate is rejected by the scanner
P056P_2_FINITE_MEASURE:
  result: FIRED
  stop: G6_S2_RESIDUAL_FINITE_DSTAR_WINDOW_REQUIRED
  evidence: removing the finite-measure bridge leaves IsFiniteMeasure unsolved
P056P_3_POSITIVE_WINDOW:
  result: FIRED
  stop: G6_S2_RESIDUAL_CPOW_POSITIVE_WINDOW_REQUIRED
  evidence: global cpow continuity cannot replace the positive compact window
P056P_4_LP_QUOTIENT:
  result: FIRED
  stop: G6_S2_RESIDUAL_LP_POINTWISE_SURROGATE
  evidence: Lp.coeFn_sub supplies almost-everywhere equality, not function equality
P056P_5_LINEARITY_ORDER:
  result: FIRED
  stop: G6_S2_RESIDUAL_INTEGRABILITY_BEFORE_LINEARITY
  evidence: integral_sub leaves both integrability obligations open
P056P_6_NORMALIZER:
  result: FIRED
  stop: G6_S2_RESIDUAL_NORMALIZER_MISMATCH
  evidence: dropping the selected normalizer produces a type-correctness mismatch
P056P_7_PROJECTED_ORIENTATION:
  result: FIRED
  stop: G6_S2_RESIDUAL_PROJECTED_COORDINATE_ORIENTATION
  evidence: z-to-minus-z mutation breaks the Phase-4E crosswalk
P056P_8_FULL_ORIENTATION:
  result: FIRED
  stop: G6_S2_RESIDUAL_FULL_COORDINATE_ORIENTATION
  evidence: z-to-minus-z mutation breaks the Phase-4F crosswalk
P056P_9_RESIDUAL_ORDER:
  result: FIRED
  stop: G6_S2_RESIDUAL_SUBTRACTION_ORDER
  evidence: reversed subtraction cannot prove the named contract
TEMPORARY_PLANT_FILES: REMOVED
```

All nine plants fired independently after a valid target build. An earlier
pre-olean probe was rejected and is not counted.

## Validation

```yaml
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7780_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
HOLE_SCAN: ZERO
FORBIDDEN_IMPORTS: ZERO
PUBLIC_SURFACE: 0_definitions_2_theorems_1_private
PUBLIC_AXIOMS: [propext, Classical.choice, Quot.sound]
ORCHESTRATOR_TESTS: PASS_67_OF_67
PROOF_DB_REIMPORT: proven_3_declarations
STRICT_SPINE: P9_STRICT_PASS_goal-close
OBSERVABILITY_SNAPSHOT: OBS_c3d68aba1f7f386dd2ac
OBSERVABILITY_SOURCE_COMMIT: 470c02c43030
OBSERVABILITY: 8_sources_0_stale
OBSERVABILITY_FILES: 3338
OBSERVABILITY_IMPORT_EDGES: 5576
OBSERVABILITY_SORRY_SITES: 0
OBSERVABILITY_PROOF_ROOTS: 2
OBSERVABILITY_TAINT_EDGES: 1
OBSERVABILITY_DEGRADED: 1_numeric_ZERO_COVERAGE_not_PASS
SEMANTIC_INDEX: PRIOR_PASS_REUSED
SEMANTIC_REFRESH: DEFERRED_BEHIND_EXISTING_USER_QMD_EMBED_F
SQLITE_INTEGRITY:
  knowledge.db: ok
  aristotle_proofs.db: ok
  observability.db: ok
```

The non-semantic sensor bundle was refreshed without starting or disturbing
the existing user-owned semantic-index process. After the answer, manifest,
and state ledger were materialized, strict Spine passed at `goal-close` so its
final snapshot sees the complete transaction.

## Honest boundary and sole next node

This phase proves exactly the literal-object Mellin subtraction identity and
the pre-existing Phase-4B contract. It does not prove decay of the normalized
residual in `H_m`, compact-open convergence, strict `SlotS2`, route promotion,
PX, or RH.

The sole next node is
`G6_S2_D0_SELECTED_NORMALIZED_GALERKIN_RESIDUAL_L2_DECAY`, with exact target

```lean
Tendsto (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
  atTop (𝓝 0)
```

That node is a new delegated strategic boundary for Codex+Proshka and was not
authorized by the Phase-4G batch. No physical Bus 010, Goal-055 release,
Aristotle submission, route promotion, PX claim, or RH claim occurred.
