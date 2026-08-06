# GOAL 056 / Phase 4E answer — selected projected Mellin coordinate

```yaml
GOAL: 056
PHASE: 4E
NODE: D0PstarProjectedMellinCoordinate
STATUS: CLOSED
EXACT_RESULT: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_EQ_RAW_TRANSFORM_PROVED
OPERATIVE_CLASS: TRY_G6_S2_D0_ADDITIVE_FIRST_PROJECTED_MELLIN_COORDINATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 5
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
SEARCH_FLAGS:
  address: RouteB.G6.S2.ProjectedMellinCoordinate
  strong: [D0FiniteProjectionReconstruction, integral_comp_logWindow_dStar, D0PstarMuntzCenteredCoordinateLock]
  empty: [prior_projected_coordinate_theorem]
  false_friend: [define_from_rawFplus, pointwise_Lp_equality, global_cpow_without_positive_window]
  opens_branch: [selected_full_Mellin_coordinate_to_Gwin]
```

## Delegated decision and exact object

The fifth batch in the same living Proshka phase chat selected the
additive-first route at source pin
`9a8fb23054ab1f80209eb9f8920fc692d393977f`. The exact verdict is archived
canonically and in the bus mirror with SHA-256
`1cb03b92fde9a3f9983e4e80facce236e9d5cad3911490fdfd224dca65b2137d`.

The K6 precommit fixed the literal normalized projection `kTrial_m_N`, the
measure `dStar.restrict (I_m i)`, full `modeSet i`, coefficient orientation
`inner ℂ (V_n_m i n) kTrial`, the multiplicative kernel
`u ^ (-Complex.I * z)`, the centered phase
`exp(+Complex.I*z*L_m/2)`, and the reflected raw coordinate at `-z`.
No raw-defined surrogate, full-object substitution, global pointwise
representative claim, theorem weakening, or Aristotle submission was used.

## Materialized production interface

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate
PRODUCTION_SHA256: 8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e
PRODUCTION_LINES: 293
PRODUCTION_BYTES: 10742
PROJECT_IMPORTS:
  - Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
  - Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
PUBLIC_DEFINITIONS: 1
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 0
PROOF_DB_DECLARATIONS: 3
PROOF_DB_STATUS: proven
```

The additive theorem

```lean
theorem kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow ...
```

installs the exact finite-dimensional and complete-space instances for
`E_m_N i`, proves that the orthogonal projection fixes its own normalized
projected trial, consumes the Phase-4D finite reconstruction, and transports
the finite `Lp` sum only as an almost-everywhere representative. It preserves
the full source coefficient row and does not collapse `Lp` equality into a
global pointwise statement.

The selected wrapper

```lean
theorem selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) :
    selectedProjectedMellinCoordinate S k z =
      selectedRawTransformCoordinate S k z
```

derives positivity from the literal source window before rewriting
`Complex.cpow`, proves `Real.log (lambda_m i) = L_m i / 2`, applies the
Phase-4C log-window transport, preserves the positive centered phase, and
closes the existing double reflection through `rawFplus ... (-z)`.

## Load-bearing plant results

```yaml
P056N_1_PROJECTED_VS_FULL:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_FULL_OBJECT_SUBSTITUTION
  evidence: normalized_gTrial_m does not definitionally equal the projected coordinate
P056N_2_NORMALIZATION:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_NORMALIZATION_MISMATCH
  evidence: unnormalized_gTrial_m_N does not definitionally equal kTrial_m_N
P056N_3_COEFFICIENT_CONJUGATION:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_COEFFICIENT_CONJUGATION_MISMATCH
  evidence: reversed_inner_orientation does not match the proved representative row
P056N_4_MODESET_BOUNDARY:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_MODESET_BOUNDARY_MISMATCH
  evidence: erasing_positive_N changes the exact finite trial
P056N_5_DSTAR_WINDOW:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_DSTAR_WINDOW_MISMATCH
  evidence: volume_integral is not the literal dStar coordinate
P056N_6_CENTERING_PHASE:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_CENTERING_PHASE_MISMATCH
  evidence: negative_centered_phase leaves a nonzero algebraic mismatch
P056N_7_RAW_REFLECTION:
  result: FIRED
  stop: G6_S2_PROJECTED_MELLIN_RAW_REFLECTION_MISMATCH
  evidence: rawFplus_at_z does not definitionally equal rawFplus_at_minus_z
TEMPORARY_PLANT_FILES: REMOVED
```

## Validation

```yaml
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7777_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
HOLE_SCAN: ZERO
FORBIDDEN_IMPORTS: ZERO
PUBLIC_SURFACE: 1_definition_2_theorems_0_private
PUBLIC_AXIOMS: [propext, Classical.choice, Quot.sound]
ORCHESTRATOR_TESTS: PASS_67_OF_67
PROOF_DB_REIMPORT: proven_3_declarations
STRICT_SPINE: P9_STRICT_PASS_goal-close
OBSERVABILITY_SNAPSHOT: OBS_52c61a48ec857324cee8
OBSERVABILITY: 8_sources_0_stale
OBSERVABILITY_FILES: 3336
OBSERVABILITY_IMPORT_EDGES: 5573
OBSERVABILITY_DEGRADED: 1_numeric_ZERO_COVERAGE_not_PASS
SEMANTIC_INDEX: PRIOR_PASS_REUSED
SEMANTIC_REFRESH: DEFERRED_BEHIND_EXISTING_USER_QMD_EMBED_F
SQLITE_INTEGRITY:
  knowledge.db: ok
  aristotle_proofs.db: ok
  observability.db: ok
```

The requested complete sensor bundle was generated and atomically published.
Its internal strict Spine pass succeeded. The subsequent optional semantic
refresh was stopped only after it spawned a duplicate `qmd embed` beside the
pre-existing user-owned `qmd embed -f`; the user process was not interrupted.
The last recorded semantic-index plants remain `PASS` and are reported as
reused, not freshly regenerated.

## Honest boundary and next wall

This leaf removes exactly

```text
literal normalized projected Lp object
  -> source-locked finite raw transform coordinate.
```

It does not identify the selected full Mellin coordinate with `Gwin`,
discharge the Phase-4B residual crosswalk contract, prove residual decay or
compact-open convergence, or establish strict `SlotS2`. The sole next
mathematical node is
`selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate`; it requires
a new delegated strategic batch in the same living Proshka chat before
materialization. No route promotion, physical Bus 010, Goal-055 release,
Aristotle submission, PX claim, or RH claim occurred.
