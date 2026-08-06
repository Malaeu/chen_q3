# GOAL 056 / Phase 4H — selected residual L² decay two-premise receiver

```yaml
GOAL: 056
PHASE: 4H
NODE: D0PstarGalerkinResidualDecay
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER
TRANSACTION: G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER
STOP: G6_S2_SELECTED_RESIDUAL_L2_DECAY_CONDITIONAL_RECEIVER_MISSING
SUCCESS: G6_S2_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 8
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The eighth batch in the same living Proshka phase chat ratified repaired
Candidate `A_TWO_PREMISE_CONDITIONAL_REPAIRED` under
`CODEX_PLUS_PROSHKA` authority at pin
`c9447e28beff8dc18d525b8ea991781f67f81733`.

The exact clipboard payload has 27,373 bytes and SHA-256
`40adc75f94c0918f59702f8ad218777d601d0d0fe045c0a93e07c4504a87e2e6`;
the exact single-newline canon/mirror archive has the same SHA-256
`40adc75f94c0918f59702f8ad218777d601d0d0fe045c0a93e07c4504a87e2e6`.

Current registered source data does not establish unconditional selected
residual L² decay. The selected carrier, source vector, projection dimension,
and inverse normalizer all vary with `k`; independent cofinality and
pointwise `TrialNonzero` do not provide the two needed uniform estimates.
This is an analytic supplier stop, not a route kill.

## Source lock

```yaml
HEAD: c9447e28beff8dc18d525b8ea991781f67f81733
SUPPLIERS:
  D0PstarMuntzGalerkinResidualCrosswalk.lean: 73fabe1675476e47228730c3bb4bce07a11c8d351d679c9937f51ef3e3fc9723
  D0PstarMuntzGalerkinResidualContract.lean: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  D0KTrialStage3.lean: 924027a3dd9b95e75c776db552ad37779ed8dd75a7924d744a39cb1a613ebdfa
  D0ProlateKTrialSource.lean: 3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1
  D0CanonicalApproximation.lean: 60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
ON_MISMATCH: G6_S2_RESIDUAL_DECAY_SOURCE_LOCK_MISMATCH
```

No production edit is permitted if any source lock fails.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  selected_index: selectedPairIndex_S_k
  selected_index_expansion: parent_extract_k
  varying_carrier: H_m_of_selectedPairIndex
  projected_object: gTrial_m_N
  full_object: gTrial_m
  residual_order: projection_minus_full
  normalizer: selectedTrialNormalizer
  scalar_error: norm_of_literal_projection_minus_full
  conclusion: full_sequence_norm_tendsto_zero

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
EXACT_PROJECT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
EXACT_MATHLIB_IMPORTS:
  - Mathlib.Analysis.Normed.Ring.Lemmas
NAMESPACE: Q3.RouteB.D0Pstar
PUBLIC_DEFINITIONS: 3
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 0
```

These fields are frozen. Neither supplier proposition becomes a source-data
field, axiom, or theorem claimed unconditionally.

## Exact production surface

```lean
noncomputable def selectedUnnormalizedGalerkinResidualNorm
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ‖(gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp‖

def SelectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) : Prop :=
  Tendsto
    (selectedUnnormalizedGalerkinResidualNorm S)
    atTop
    (𝓝 0)

def SelectedTrialNormalizerBounded
    (S : ProlateCanonicalSourceData) : Prop :=
  IsBoundedUnder (· ≤ ·) atTop
    (fun k : ℕ => ‖(selectedTrialNormalizer S k : ℂ)‖)

theorem norm_selectedNormalizedGalerkinResidual_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    ‖selectedNormalizedGalerkinResidual S k‖ =
      ‖(selectedTrialNormalizer S k : ℂ)‖ *
        selectedUnnormalizedGalerkinResidualNorm S k := by
  ...

theorem selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded
    (S : ProlateCanonicalSourceData)
    (hTail : SelectedProjectionTailDecay S)
    (hNormalizer : SelectedTrialNormalizerBounded S) :
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop
      (𝓝 0) := by
  ...
```

The first theorem must be only the literal-object unfolding and `norm_smul`.
The second must rewrite pointwise with the first theorem and apply
`Filter.isBoundedUnder_le_mul_tendsto_zero`. It must not invoke fixed-space
projection convergence, prove either analytic premise, or consume any scalar
Mellin-coordinate estimate.

## Load-bearing plants

```yaml
P056Q_1_FIXED_SPACE_API:
  mutation: apply_fixed_space_projection_convergence_to_varying_selected_family
  expected: G6_S2_RESIDUAL_DECAY_FIXED_SPACE_API_MISMATCH
P056Q_2_COFINALITY_NOT_TAIL:
  control: l2_basis_vector_just_beyond_each_projection
  expected: G6_S2_RESIDUAL_DECAY_COFINALITY_NOT_TAIL
P056Q_3_NORMALIZER:
  control: a_k_eq_k_plus_one_error_eq_inverse_k_plus_one
  expected: G6_S2_RESIDUAL_DECAY_POINTWISE_NONZERO_NOT_BOUNDED
P056Q_4_PARENT_EXTRACT:
  mutation: parent_k_or_shifted_extract
  expected: G6_S2_RESIDUAL_DECAY_PARENT_EXTRACT_MISMATCH
P056Q_5_SCALAR_SURROGATE:
  mutation: replace_H_m_norm_by_one_coordinate
  expected: G6_S2_RESIDUAL_DECAY_SCALAR_SURROGATE
P056Q_6_ORDER:
  mutation: reverse_underlying_residual_order
  discriminator: Phase4G_signed_crosswalk_must_fail
  expected: G6_S2_RESIDUAL_DECAY_ORDER_SIGNED_CROSSWALK_MISMATCH
  invalid_detector: norm_identity_only
P056Q_7_WEIGHTED_RESTATEMENT:
  mutation: replace_two_props_by_target_product_tendsto
  expected: G6_S2_RESIDUAL_DECAY_WEIGHTED_TAIL_RESTATEMENT
```

All seven plants must fire independently and all temporary artifacts must be
removed before closeout.

## Validation and boundary

Validation requires source-lock recheck, direct Lean, dedicated target build,
full build, `q3_check`, hole/taint/forbidden-import scans, exact 3/2/0 public
surface, all seven plants, standard axiom triple for both public theorems,
proof-DB reimport of all five declarations, all 67 orchestration tests, strict
Spine, three SQLite integrity checks, observability source/stale counts plus
separate numeric `ZERO_COVERAGE`, `git diff --check`, and exact status.

After success, the two-premise implication is proved but unconditional decay
is not. The open analytic inputs remain `SelectedProjectionTailDecay` and
`SelectedTrialNormalizerBounded`.

The sole next node, not authorized in this transaction, is
`G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER`, targeting:

```lean
theorem selectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) :
    SelectedProjectionTailDecay S
```

Fixed-space density on the varying selected family, a new subsequence,
compact-open decay, strict `SlotS2`, Q3.Main, Goal 055, Bus 010, Aristotle,
route promotion, PX, and RH claims remain forbidden.
