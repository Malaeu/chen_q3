# GOAL 056 / Phase 4F answer — full Mellin/Gwin crosswalk

```yaml
GOAL: 056
PHASE: 4F
NODE: D0PstarFullMellinGwinCrosswalk
STATUS: CLOSED
EXACT_RESULT: G6_S2_SELECTED_FULL_MELLIN_AND_SCALED_GWIN_CROSSWALK_PROVED
OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
ARSENAL_USED: [C04, C09, C10]

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 6
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
SEARCH_FLAGS:
  address: RouteB.G6.S2.FullMellinCoordinate
  strong: [D0KTrialStage2, D0PstarMuntzCenteredCoordinateLock, D0LogWindowMeasureTransport, MuntzV3Core]
  empty: [prior_selected_full_coordinate_theorem]
  false_friend: [define_from_Gwin, pointwise_Lp_equality, drop_dStar_density, global_cpow_rewrite]
  opens_branch: [residual_Mellin_linearity_and_contract_discharge]
```

## Delegated decision and exact object

The sixth batch in the same living Proshka phase chat selected Candidate
`A_REPAIRED` at corrected source pin
`952d0760a2741ddc2766976295b684cddb26baa4`. The exact verdict is archived
canonically and in the bus mirror with SHA-256
`0e1363fdc611341a3036a3a19297ded593c93a04b5fd1205116b0d648fa18f5d`.

The K6 precommit fixed the literal unnormalized full object `gTrial_m`, the
stored `MemLp` witness, the measure `dStar.restrict (I_m i)`, density
`u⁻¹`, multiplicative kernel `u ^ (-Complex.I * z)`, Müntz argument
`-Complex.I * z`, exponent `(-Complex.I*z)-1`, closed/open endpoint
orientation, and left multiplication by the selected trial normalizer.
No projected-object substitution, Gwin-defined surrogate, global pointwise
representative claim, theorem weakening, or Aristotle submission was used.

Candidate B was deliberately deferred. Equality of the projected and full
scalar coordinates does not by itself justify subtraction under the literal
Bochner integral; the next node must prove bounded-kernel `Lp -> L1`
integrability/linearity or construct the exact continuous linear Mellin
functional.

## Materialized production interface

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0PstarFullMellinGwinCrosswalk
PRODUCTION_SHA256: 62cfcbdcc209a3da7fbb7d2dd3a58b24937209f1dde416a721d539e414769818
PRODUCTION_LINES: 138
PRODUCTION_BYTES: 5397
SOLE_PROJECT_IMPORT: Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate
PUBLIC_DEFINITIONS: 1
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 0
PROOF_DB_DECLARATIONS: 3
PROOF_DB_STATUS: proven
```

The new object is literal:

```lean
noncomputable def selectedFullMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ∫ u : ℝ,
      (gTrial_m i h hLp : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))
```

The base theorem uses `MemLp.coeFn_toLp` only as an almost-everywhere
representative, rewrites the integral with `integral_congr_ae`, expands the
exact `dStar` density through
`setIntegral_withDensity_eq_setIntegral_toReal_smul`, and derives positivity
from the selected `I_m` window.

On that positive branch, `Complex.cpow_sub` and `Complex.cpow_one` turn
`u⁻¹ * u^(-i*z)` into `u^((-i*z)-1)`. Unfolding the two definitions makes
the local `E_star` and ported `Estar` starred sums identical, including the
`PNat` coercion. The unconditional atomless-volume theorem
`integral_Icc_eq_integral_Ioo` removes exactly the two endpoints and the
result folds definitionally to `selectedGwinTransformCoordinate`.

The second theorem is only the definitionally algebraic scaled corollary:

```lean
theorem
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    (selectedTrialNormalizer S k : ℂ) *
        selectedFullMellinCoordinate S k z =
      selectedScaledGwinTransformCoordinate S k z
```

It does not distribute the normalizer through a residual integral.

## Load-bearing plant results

```yaml
P056O_1_FULL_NOT_PROJECTED:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_PROJECTED_OBJECT_SUBSTITUTION
  evidence: gTrial_m_N mutation breaks the exact representative seam
P056O_2_LP_REPRESENTATIVE:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_LP_POINTWISE_SURROGATE
  evidence: MemLp.coeFn_toLp cannot prove global function equality
P056O_3_DSTAR_DENSITY:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_DSTAR_DENSITY_MISMATCH
  evidence: volume mutation loses both the stored representative measure and density expansion
P056O_4_ENDPOINT_ATOM:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_ENDPOINT_ATOM_MISMATCH
  evidence: dirac endpoint fixture has no NoAtoms instance
P056O_5_CPOW_EXPONENT:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_CPOW_EXPONENT_OR_BRANCH_MISMATCH
  evidence: plus-one exponent breaks cpow_sub and final Gwin fold
P056O_6_ESTAR_SOURCE:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_ESTAR_SOURCE_MISMATCH
  evidence: unstarred h loses sqrt-times-PNat-sum identity
P056O_7_SCALE_LEVEL:
  result: FIRED
  stop: G6_S2_FULL_MELLIN_SCALE_LEVEL_MISMATCH
  evidence: unnormalized coordinate cannot fold to selectedScaledGwin
TEMPORARY_PLANT_FILES: REMOVED
```

## Validation

```yaml
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7778_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
HOLE_SCAN: ZERO
FORBIDDEN_IMPORTS: ZERO
PUBLIC_SURFACE: 1_definition_2_theorems_0_private
PUBLIC_AXIOMS: [propext, Classical.choice, Quot.sound]
ORCHESTRATOR_TESTS: PASS_67_OF_67
PROOF_DB_REIMPORT: proven_3_declarations
STRICT_SPINE: P9_STRICT_PASS_goal-close
OBSERVABILITY_SNAPSHOT: OBS_422c7bb60d7d700f482b
OBSERVABILITY_SOURCE_COMMIT: c776c191a7fc71ff80e2588c481d9bfd494703e4
OBSERVABILITY: 8_sources_0_stale
OBSERVABILITY_FILES: 3337
OBSERVABILITY_IMPORT_EDGES: 5574
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

The complete non-semantic sensor bundle was generated and atomically published,
then strict Spine passed again at `goal-close`. The existing user-owned
`qmd embed -f` process remained untouched; no duplicate semantic refresh was
started. The last recorded semantic-index plants remain `PASS` and are
reported as reused, not freshly regenerated.

## Honest boundary and next wall

This leaf removes exactly

```text
literal unnormalized full gTrial_m coordinate
  -> selected Gwin coordinate
  -> definitionally scaled selected Gwin corollary.
```

It does not prove linearity of the literal residual Mellin integral, discharge
`D0PstarMuntzGalerkinResidualCrosswalkContract S`, prove residual decay or
compact-open convergence, or establish strict `SlotS2`.

The sole next transaction is
`G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE`, with exact jump
target `selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull`.
That boundary remains delegated to Codex+Proshka and is not opened in this
answer. No route promotion, physical Bus 010, Goal-055 release, Aristotle
submission, PX claim, or RH claim occurred.
