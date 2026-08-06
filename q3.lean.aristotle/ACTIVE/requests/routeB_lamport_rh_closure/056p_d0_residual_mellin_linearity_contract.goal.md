# GOAL 056 / Phase 4G — residual Mellin linearity and contract discharge

```yaml
GOAL: 056
PHASE: 4G
NODE: D0PstarMuntzGalerkinResidualCrosswalk
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
TRANSACTION: G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
STOP: G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE_MISSING
SUCCESS: G6_S2_D0_RESIDUAL_MELLIN_CROSSWALK_CONTRACT_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 7
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The seventh batch in the same living Proshka phase chat ratified Candidate
`A_MINIMAL_PRIVATE_HELPER` under `CODEX_PLUS_PROSHKA` authority at pin
`1b1f36629b1236909c027891d4a8f68748c6134c`. The exact clipboard payload has
7,185 bytes and SHA-256
`d51c7a6a91561743f4d4ee108de67dc0b55d215902e68993b976b857f89a7895`;
its newline-normalized canonical archive has SHA-256
`451152dc6f8adc54a7e35b6169bcfeb3c130d2e97121d7f6254955deda59495f`.

The transaction proves the literal object-first residual coordinate identity
and then discharges the Phase-4B named contract unconditionally. It introduces
no public definition, hypothesis, structure field, axiom, decay theorem, or
strict `SlotS2` receiver. The generic bounded-kernel integrability theorem is
private production support only.

## Source lock

```yaml
HEAD: 1b1f36629b1236909c027891d4a8f68748c6134c
SUPPLIERS:
  D0PstarMuntzGalerkinResidualContract.lean: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  D0PstarProjectedMellinCoordinate.lean: 8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e
  D0PstarFullMellinGwinCrosswalk.lean: 62cfcbdcc209a3da7fbb7d2dd3a58b24937209f1dde416a721d539e414769818
ON_MISMATCH: G6_S2_RESIDUAL_MELLIN_SOURCE_LOCK_MISMATCH
```

No production edit is permitted if any source lock fails.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_object: selectedNormalizedGalerkinResidual
  selected_index: selectedPairIndex_S_k
  residual_order: projection_minus_full
  normalizer: selectedTrialNormalizer_left_scalar
  measure: dStar_restrict_I_m
  kernel: u_cpow_minus_I_z
  representative_relation: almost_everywhere
  projected_coordinate_argument: z
  full_coordinate_argument: z
  raw_coordinate: rawFplus_at_minus_z
  Gwin_coordinate: Gwin_at_minus_I_times_z
  contract_direction: scalar_defect_equals_object_residual_coordinate

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
EXACT_PROJECT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualContract
  - Q3.Proofs.RouteB.D0PstarFullMellinGwinCrosswalk
NAMESPACE: Q3.RouteB.D0Pstar
PUBLIC_DEFINITIONS: 0
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 1
```

These fields are frozen for this transaction. Any semantic change after a
plant fires requires a new named boundary.

## Exact production surface

```lean
private theorem integrable_H_m_mul_mellinKernel
    (i : PairIndex) (f : H_m i) (z : ℂ) :
    Integrable
      (fun u : ℝ => f u * (u : ℂ) ^ (-Complex.I * z))
      (dStar.restrict (I_m i)) := by
  ...

theorem selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedGalerkinResidualMellinCoordinate S k z =
      selectedProjectedMellinCoordinate S k z -
        (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z := by
  ...

theorem D0PstarMuntzGalerkinResidualCrosswalkContract_proved
    (S : ProlateCanonicalSourceData) :
    D0PstarMuntzGalerkinResidualCrosswalkContract S := by
  intro k z
  rw [selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull]
  rw [selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate]
  rw [
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate]
  rfl
```

The helper must reconstruct finiteness of `dStar.restrict (I_m i)`, lower the
`H_m` representative from `L²` to `L¹`, prove the arbitrary-complex Mellin
kernel continuous and bounded on the positive compact window, and apply
`Integrable.mul_bdd`.

The jump theorem must first establish the literal residual representative
almost everywhere through `Lp.coeFn_sub` and `Lp.coeFn_smul`, then prove both
product integrands integrable, and only then use `integral_sub` and
`integral_const_mul`. Phase-4E/4F transform equalities are forbidden inside
the jump theorem; they are consumed only by the contract theorem.

## Load-bearing plants

```yaml
P056P_1_OBJECT_SURROGATE:
  mutation: define_residual_coordinate_from_scalar_difference
  expected: G6_S2_RESIDUAL_OBJECT_SURROGATE
P056P_2_FINITE_MEASURE:
  mutation: remove_IsFiniteMeasure_reconstruction
  expected: G6_S2_RESIDUAL_FINITE_MEASURE_MISSING
P056P_3_POSITIVE_WINDOW:
  mutation: replace_positive_window_cpow_continuity_by_global_claim
  expected: G6_S2_RESIDUAL_CPOW_BRANCH_MISMATCH
P056P_4_LP_QUOTIENT:
  mutation: replace_ae_representative_by_global_pointwise_equality
  expected: G6_S2_RESIDUAL_LP_POINTWISE_SURROGATE
P056P_5_LINEARITY_ORDER:
  mutation: invoke_integral_sub_without_both_integrability_witnesses
  expected: G6_S2_RESIDUAL_LINEARITY_PRECONDITION_MISSING
P056P_6_NORMALIZER:
  mutation: move_duplicate_or_drop_selectedTrialNormalizer
  expected: G6_S2_RESIDUAL_NORMALIZER_MISMATCH
P056P_7_PHASE4E_ORIENTATION:
  mutation: flip_projected_coordinate_argument_or_raw_reflection
  expected: G6_S2_RESIDUAL_PROJECTED_ORIENTATION_MISMATCH
P056P_8_PHASE4F_ORIENTATION:
  mutation: flip_full_coordinate_argument_or_Gwin_argument
  expected: G6_S2_RESIDUAL_FULL_ORIENTATION_MISMATCH
P056P_9_RESIDUAL_ORDER:
  mutation: reverse_projection_minus_full
  expected: G6_S2_RESIDUAL_ORDER_MISMATCH
```

All nine plants must fire independently and all temporary mutation files must
be removed before closeout.

## Validation and boundary

Validation requires source-lock recheck, direct Lean, dedicated target build,
full build, `q3_check`, hole/taint/forbidden-import scans, exact 0/2/1 public
surface, all nine plants, the standard axiom triple, proof-DB reimport of all
three declarations with both public theorems proven, all 67 orchestration
tests, strict Spine, all three SQLite integrity checks, observability
source/stale counts, `git diff --check`, and exact status.

Aristotle is forbidden. This leaf removes only:

```text
literal selected normalized object residual
  -> projected Mellin coordinate minus scaled full Mellin coordinate
  -> scalar Galerkin coordinate defect
  -> Phase-4B contract proved unconditionally.
```

The sole next node, not authorized here, is
`G6_S2_D0_SELECTED_NORMALIZED_GALERKIN_RESIDUAL_L2_DECAY`, targeting
`Tendsto (fun k => ‖selectedNormalizedGalerkinResidual S k‖) atTop (𝓝 0)`.
Residual decay, compact-open convergence, strict `SlotS2`, Q3.Main, Goal 055,
Bus 010, Aristotle, route promotion, PX, and RH claims remain forbidden.
