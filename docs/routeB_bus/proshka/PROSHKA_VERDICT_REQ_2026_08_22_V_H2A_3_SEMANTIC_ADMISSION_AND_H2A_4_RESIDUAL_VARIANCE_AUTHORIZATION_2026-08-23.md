# STATUS: PROVED — H2A.3 SEMANTICALLY ADMITTED; ODD-MASS DECAY CLOSED; H2A.4 BROAD RATE SHAPE REPAIRED TO AN EXACT RESIDUAL-VARIANCE LOCK
```yaml
PRIMARY: ADMIT_H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 10e414dae0c134ef9f40310607f413dcc780c430
  SOURCE_COMMIT: 10e414dae0c134ef9f40310607f413dcc780c430
  ACTUAL_PARENT: 89f10e98385cd4621d3ccc54dc56ae631e6b8ec7
  CLAIMED_PARENT: 89f10e98385cd4621d3ccc54dc56ae631e6b8ec7
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
  LEAN_GIT_BLOB: 0b8e3f590a2b968b34f66eb52b9c4e40bf0eed70
  LEAN_SHA256_REPORTED: d64d350cc822db3e4bc4a9c25ff20f24ca56cedb8815c1f077ec9dc769ef7f02
  LEAN_LINES_REPORTED: 1247
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: dde195b04c35086e6e04876d1833301c98c62398
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7924_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS_FOR_ALL_6_PUBLIC_THEOREMS_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SELECTED_ODD_MASS_RATE
  CONDITIONAL_PORT: selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
  FINAL_SHELL: selectedFerrersCofinalSourceData
  FINITE_ROW: selectedFerrersFiniteCCMRow
  ODD_MASS: selectedFerrersFiniteCCMOddMass
  RECOVERED_PREANCHOR_RANK: selectedFerrersCofinalPreAnchorRank
  RANK_INDEX_CROSSWALK_PUBLIC: true
  RANK_PAIR_CROSSWALK_PUBLIC: true
  RANK_SOURCE_SCALE_CROSSWALK_PUBLIC: true
  RECOVERED_RANK_COFINAL: true
  TARGET_PACKET: factor_four_explicitCCMLimitH
  TARGET_INVERSION_EVEN: exact
  SELECTED_ROW_SYMMETRIZED: false
  CENTRAL_ANCHOR_USED_AS_DENOMINATOR_FLOOR: true
  SOURCE_SCALE_NE_USED_AS_UNIFORM_FLOOR: false
  NORMALIZATION_CONSTANT_FITTED: false
  C04_OBJECT_AUDIT: PASS
  C09_PRECOMMIT_AUDIT: PASS
  C10_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

RATE_AUDIT:
  POINTWISE_FULL_ESTAR_ERROR: "(C1+C2)/(lambda*sqrt(u))"
  MEASURE: "dStar = du/u on the literal source window"
  WINDOW_L2_ERROR_SQUARED: "O(1/lambda), with integral u^(-2) = lambda-lambda^(-1)"
  PROJECTED_NORM_SQUARED_FLOOR: "Omega(1/L_m) from the z=0 anchor"
  ODD_MASS_UPPER: "C*L_m/lambda_m"
  SCHEDULE_FORM: "C*log(m_k)/sqrt(m_k)"
  LIMIT: 0
  SOURCE_DERIVED_CONSTANT: "4*(C1+C2)^2/norm(centeredXi(0))^2"

PLANT_AUDIT:
  VANISHING_UNNORMALIZED_ERROR_WITHOUT_ANCHOR:
    STATUS: PASS
    CARRIER: Fin_2
    REFLECTION: diag_1_minus1
    RAW_VECTOR: "(0,1/(n+1))"
    RAW_NORM_LIMIT: 0
    NORMALIZED_VECTOR: odd_unit_vector
    NORMALIZED_ODD_MASS: 1
    CONCLUSION: central_anchor_floor_is_load_bearing

H2A_BOUNDARY_AFTER_ADMISSION:
  SELECTED_COMPLEX_REFLECTION_OBJECT: CLOSED
  SELECTED_RAYLEIGH_AND_RESIDUAL_OBJECTS: CLOSED
  SELECTED_ODD_MASS_OBJECT: CLOSED
  SELECTED_ODD_MASS_PHYSICAL_REPRESENTATION: CLOSED
  SELECTED_H2A1_LITERAL_RECEIVER: CLOSED
  SELECTED_ODD_MASS_LOG_OVER_SQRT_RATE: CLOSED
  SELECTED_ODD_MASS_DECAY: CLOSED
  SELECTED_FINITE_CCM_RESIDUAL_RATE: OPEN
  SELECTED_EVEN_SECTOR_FLOOR: OPEN
  SELECTED_ODD_SECTOR_FLOOR: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

H2A_4_ADJUDICATION:
  REQUESTED_NAME: H2A_4_SELECTED_FERRERS_RESIDUAL_RATE
  NAIVE_SHAPE: "the same hmode/hchi inputs imply a rate for selectedFerrersFiniteCCMResidual"
  NAIVE_SHAPE_STATUS: REJECTED_AS_UNSUPPORTED
  REASON:
    - odd_mass_controls_only_the_reflection_odd_component_of_the_selected_row
    - exact_evenness_does_not_make_the_row_an_eigenvector_of_the_CCM_matrix
    - L73_physical_Estar_error_is_not_a_finite_CCM_Rayleigh_residual
    - selectedNormalizedGalerkinResidual_is_projection_minus_full_gTrial_and_is_a_different_object
    - no_source_theorem_currently_identifies_the_finite_CCM_residual_with_an_ambient_operator_residual
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
  REPAIRED_SEQUENCE:
    - H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
    - H2A_4_1_SELECTED_FERRERS_RESIDUAL_VARIANCE_RATE

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED
  CODE: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_0_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
    - Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator
  PRIMARY_ROLE: >-
    Expose the exact selected finite CCM Rayleigh residual as one source-faithful
    nonnegative scalar variance and as the norm of the finite Riesz defect on
    the same selected kTrial. This is the mandatory object lock before any
    cofinal residual rate. It must not infer a rate from odd-mass decay.
  PUBLIC_SURFACE_REQUIRED:
    - selectedFerrersFiniteCCMResidualEnergy
    - selectedFerrersFiniteCCMSecondMoment
    - selectedFerrersFiniteCCMResidualEnergy_nonneg
    - selectedFerrersFiniteCCMResidualEnergy_eq_norm_sq
    - selectedFerrersFiniteCCMResidualEnergy_eq_secondMoment_sub_rayleigh_sq
    - ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect
    - selectedFerrersFiniteCCMResidualEnergy_eq_finiteRieszDefect_norm_sq
  REQUIRED_PRIVATE_PLANT:
    - exact_even_unit_row_can_have_nonzero_rayleigh_residual_plant
  CLOSES:
    - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_ENERGY_OBJECT_LOCK
    - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_IDENTITY
    - SELECTED_FERRERS_FINITE_RIESZ_RESIDUAL_CROSSWALK
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: H2A_4_1_SELECTED_FERRERS_RESIDUAL_VARIANCE_RATE

H2A_4_0_REQUIRED_THEOREM_SHAPES:
  RESIDUAL_ENERGY_DEF: |-
    noncomputable def selectedFerrersFiniteCCMResidualEnergy
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) : Real :=
      (star (selectedFerrersFiniteCCMResidual P k) dotProduct
        selectedFerrersFiniteCCMResidual P k).re
  SECOND_MOMENT_DEF: |-
    noncomputable def selectedFerrersFiniteCCMSecondMoment
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) : Real :=
      let i := (selectedFerrersCofinalSourceData P).index k
      let q := selectedFerrersFiniteCCMRow P k
      (star (sourceCCMFiniteMatrix i *v q) dotProduct
        (sourceCCMFiniteMatrix i *v q)).re
  NORM_SQ: |-
    theorem selectedFerrersFiniteCCMResidualEnergy_eq_norm_sq
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) :
      selectedFerrersFiniteCCMResidualEnergy P k =
        norm (WithLp.toLp 2 (selectedFerrersFiniteCCMResidual P k)) ^ 2
  VARIANCE: |-
    theorem selectedFerrersFiniteCCMResidualEnergy_eq_secondMoment_sub_rayleigh_sq
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) :
      selectedFerrersFiniteCCMResidualEnergy P k =
        selectedFerrersFiniteCCMSecondMoment P k -
          (selectedFerrersFiniteCCMRayleigh P k) ^ 2
  RIESZ_CROSSWALK: |-
    theorem ccmFiniteSynthesis_selectedFerrersFiniteCCMResidual_eq_finiteRieszDefect
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) :
      let i := (selectedFerrersCofinalSourceData P).index k
      let xE : E_m_N i :=
        kTrial_m_N i
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)
      ccmFiniteSynthesis i (selectedFerrersFiniteCCMResidual P k) =
        (((sourceCCMFiniteRieszOperator i xE -
          (((selectedFerrersFiniteCCMRayleigh P k : Real) : Complex) • xE) :
            E_m_N i) : H_m i)
  RIESZ_NORM: |-
    theorem selectedFerrersFiniteCCMResidualEnergy_eq_finiteRieszDefect_norm_sq
        (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
        (k : Nat) :
      let i := (selectedFerrersCofinalSourceData P).index k
      let xE : E_m_N i :=
        kTrial_m_N i
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)
      selectedFerrersFiniteCCMResidualEnergy P k =
        norm (sourceCCMFiniteRieszOperator i xE -
          (((selectedFerrersFiniteCCMRayleigh P k : Real) : Complex) • xE)) ^ 2
  NOTATION_POLICY: >-
    Use the repository Unicode notation in the actual Lean source. The ASCII
    forms above are semantic shapes, not text to paste blindly.

H2A_4_0_PROOF_ROUTE:
  - Run ask.sh preflight before editing and record the result.
  - Keep P, the selected final shell, PairIndex, row, matrix and exact Rayleigh
    shift definitionally identical to H2A.2.
  - Prove residual energy equals Euclidean norm squared from the exact complex
    dot product; do not realify the row.
  - Expand r = Kq - a*q only after importing unit normalization, Hermitian
    Rayleigh reality and residual orthogonality. Obtain exactly
    norm(r)^2 = norm(Kq)^2 - a^2.
  - Transport the selected row through ccmFiniteSynthesisEquiv. Re-prove only
    the generic conjugation application lemma that is private in
    D0PstarCCMFiniteRieszOperator. Do not use ProlateCanonicalSourceData as a
    substitute for the selected shell.
  - Use ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial to identify the
    selected finite synthesis with the same selected kTrial. The result must be
    an equality in H_m after coercing the exact E_m_N Riesz defect.
  - Derive the Riesz norm theorem from the isometry, not from an ambient
    associated Weil operator.
  - Print axioms for every public theorem and the plant.

H2A_4_0_PLANT:
  exact_even_unit_row_can_have_nonzero_rayleigh_residual_plant: >-
    On Fin 3 use reflection J swapping coordinates 0 and 2, q=(0,1,0), and
    K=[[0,1,0],[1,0,1],[0,1,0]]. Prove K is Hermitian, J is a Hermitian
    involution, KJ=JK, q is unit and exactly J-even, hence its odd mass is zero,
    while its exact Rayleigh value is zero and its Rayleigh residual is
    (1,0,1), with residual energy two. This kills the false implication
    oddMass=0 -> residual=0 and therefore also kills any attempt to derive
    H2A.4 solely from H2A.3.

FORBIDDEN:
  - infer_selected_CCM_residual_decay_from_odd_mass_decay
  - infer_selected_CCM_residual_decay_from_hmode_hchi_without_a_source_action_theorem
  - replace_selectedFerrersFiniteCCMResidual_by_selectedNormalizedGalerkinResidual
  - replace_the_finite_CCM_Rayleigh_residual_by_projection_minus_full_gTrial
  - use_ProlateCanonicalSourceData_as_definitionally_equal_to_the_selected_shell
  - invoke_or_define_an_ambient_associated_Weil_operator_A_m
  - claim_sourceCCMFiniteRieszOperator_is_an_ambient_operator_compression
  - replace_the_exact_Rayleigh_shift_by_zero_or_a_fixed_or_fitted_shift
  - use_a_matrix_operator_norm_or_absolute_row_sum_and_label_it_a_source_residual_rate
  - assume_a_residual_rate_or_a_second_moment_rate
  - add_even_or_odd_sector_floor_claims
  - bundle_H2A_4_1_H2A_5_simple_ground_or_Theorem510
  - edit_H2A_0_through_H2A_3_or_L73_3_through_L73_8
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

VALIDATION:
  WORKDIR_Q3:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
  WORKDIR_REPO_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
  EXPECTED_AXIOM_PROFILE_FOR_EVERY_PUBLIC_THEOREM_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound

SUCCESS: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
FAILURE: H2A_4_0_SELECTED_RIESZ_CARRIER_OR_COMPLEX_VARIANCE_NORMAL_FORM_GAP

NEXT_LOAD_BEARING_GAP: H2A_4_1_SELECTED_FERRERS_RESIDUAL_VARIANCE_RATE
NEXT_CHEAPEST_DECISIVE_TEST: >-
  After the variance lock, ask whether the existing L73 physical approximation
  controls this exact finite Riesz defect. If it does not, do not add a thin
  rate receiver: isolate the missing finite-form continuity or source-action
  theorem. No rate exponent is authorized before that test.

REGISTERED_PREDICTIONS:
  P_H2A4_0_1:
    claim: the_exact_selected_complex_residual_energy_closes_as_second_moment_minus_rayleigh_squared_by_finite_Hermitian_algebra
    probability: 0.97
  P_H2A4_0_2:
    claim: the_selected_shell_Riesz_crosswalk_closes_by_reusing_the_public_selected_synthesis_theorem_without_interface_substitution
    probability: 0.88
  P_H2A4_0_3:
    claim: the_even_unit_Fin3_plant_rejects_residual_from_parity_with_standard_axioms
    probability: 0.995
  LIKELIEST_FAILURE: DEPENDENT_E_M_N_SUBTYPE_COERCION_OR_COMPLEX_INNER_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A3_1:
    probability: 0.88
    fate: CONFIRMED
    result: exact_dStar_window_integration_gave_O_one_over_lambda
  P_H2A3_2:
    probability: 0.82
    fate: CONFIRMED
    result: central_anchor_gave_projected_norm_squared_Omega_one_over_log_m
  P_H2A3_3:
    probability: 0.94
    fate: CONFIRMED
    result: factor_four_target_inversion_gave_reflected_coefficients_without_source_symmetrization
  LIKELIEST_FAILURE:
    prediction: PRIVATE_TAIL_RANK_OR_MEMLP_LOG_WINDOW_NORMAL_FORM
    fate: PARTIALLY_OBSERVED
    observed: measurable_set_and_normal_form_API_friction_only
  RETROACTIVE_REPAIR: false

CLOSES:
  - SELECTED_FERRERS_FINAL_SHELL_TO_PREANCHOR_RANK_CROSSWALK
  - SELECTED_FERRERS_ODD_MASS_LOG_OVER_SQRT_RATE
  - SELECTED_FERRERS_ODD_MASS_DECAY
OPENS: []

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_AUTHORIZED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### H2A.3 admission

`selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates`
uses the exact selected shell, not the older `ProlateCanonicalSourceData`
interface.  The final-shell rank is recovered publicly and all three object
crosswalks are literal definitional equalities.  The eventual L73 error is
therefore pulled back along the same theorem-generated tail.  `[COFINAL_FAMILY][LEAN]`

The pointwise full `E_star` error is integrated against the actual
multiplicative measure.  The proof obtains an `O(1/lambda)` squared window
error; it does not lose a logarithm.  The factor-four target is exactly
inversion-even, so its retained reflected coefficients cancel inside the
selected coefficient difference.  The selected row is never projected onto
the even sector.  `[COFINAL_FAMILY][LEAN]`

The normalization floor is supplied by the selected-shell limit at `z=0` and
`centeredXi(0) != 0`.  It is not inferred from pointwise nonvanishing of the
source scale.  Thus the mandatory plant attacks the actual load-bearing step
and the source-scale cancellation is legitimate.  `[COFINAL_FAMILY][LEAN]`

Consequently

\[
  \eta_k\le C\frac{\log m_k}{\sqrt{m_k}}\longrightarrow0
\]

for the exact selected finite CCM row under the already explicit mode/chi
contracts.  This closes the odd-mass supplier and nothing beyond it.
`[COFINAL_FAMILY][LEAN]`

### Why the broad H2A.4 shape is rejected

The exact finite CCM residual is

\[
 r_k=K_kq_k-a_kq_k,
 \qquad
 a_k=\operatorname{Re}\langle q_k,K_kq_k\rangle.
\]

Odd mass controls the distance from `q_k` to the reflection-even sector.  It
does not control the action of `K_k` inside that sector.  The required Fin-3
plant has `eta=0` and a nonzero Rayleigh residual while preserving Hermiticity,
reflection, commutation and unit normalization.  Therefore neither H2A.3 nor
exact parity can imply a residual rate.  `[ABSTRACT][LEAN]` **[C10]**

There is a second, independent type firewall.  The existing
`selectedNormalizedGalerkinResidual` is the normalized projection-minus-full
`gTrial` tail.  `selectedFerrersFiniteCCMResidual` is the finite CCM matrix
Rayleigh residual.  Both are called residuals and live near the same source
trial, but no current theorem identifies them.  Replacing one by the other is
an instance of same coordinates with two laws.  `[ABSTRACT][LEAN]` **[C04]**

The repaired H2A.4 sequence therefore starts with the variance/Riesz object
lock.  It turns the residual into one exact nonnegative scalar and exposes the
literal finite-form defect that the next analytic rate theorem must estimate.
It does not create a new premise and does not claim an ambient compression.
`[FINITE_CELL][LEAN]`

## FINAL PROPOSAL

Ratify H2A.3 exactly at its declared scope.  Execute only
`H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN` next.  Do not attempt a
cofinal residual theorem until the exact second-moment/Riesz target is public
and semantically reviewed.  `[COFINAL_FAMILY][CONDITIONAL]`

Registered outcome for the next test:

```text
The finite variance and Riesz identities will compile with no new mathematics.
The actual H2A.4 rate will remain a source-action theorem, not a corollary of
odd-mass decay.
```

## STRONGEST ATTACK

The strongest counterexample is not approximate.  An exactly even unit row can
have zero odd mass and a large Rayleigh residual under a reflection-commuting
Hermitian matrix.  This kills every proof plan of the form

```text
oddMass -> 0
therefore residual -> 0.
```

The weakest repaired statement is the exact variance identity plus finite Riesz
crosswalk.  Any stronger rate requires a source theorem controlling the action
of the literal CCM finite Riesz operator on the selected trial.
`[ABSTRACT][LEAN]` **[C10]**

## CODEX DIRECTIVE

Execute exactly the authorized H2A.4.0 transaction described in the YAML
header.  One Lean file, one source record, one commit.  Do not add the actual
cofinal rate theorem, sector floors, a ground constructor or a Theorem-5.10
consumer.

## META CLOSEOUT

**What became smaller?**

The exact selected odd mass now has a theorem-facing rate and tends to zero.
The residual front is reduced from an overloaded word to one exact variance
and one finite Riesz defect.  `[COFINAL_FAMILY][LEAN]`

**What was killed?**

- odd-mass decay as a proof of residual decay;
- exact parity as a proof that the selected row is an eigenvector;
- substitution of the Galerkin projection tail for the CCM Rayleigh residual;
- an ambient-compression claim not present in the source.

**What must not be tried again?**

Do not use two objects merely because both are named residual.  Do not infer
operator action from physical parity.  Do not hide a missing source theorem in
a rate hypothesis.

**Current smallest named gap:**

```text
H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
```

**Next cheapest decisive test:**

Prove the exact variance/Riesz identities and then test whether L73 controls
that exact defect.  A zero-consistent physical error without a finite-form
continuity theorem remains inconclusive; the discriminator is the literal
Riesz-defect norm.

**Prior prediction fate:** all three H2A.3 predictions confirmed; no
retroactive repair.

```yaml
iteration:
  target: H2A.3 odd-mass decay and H2A.4 selection
  status: PROGRESS
  failed_strategy: derive_finite_CCM_residual_rate_from_odd_mass_or_L73_name_similarity
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN
  invariant_learned: parity_error_and_operator_Rayleigh_residual_are_different_functionals
  forbidden_future_move: substitute_projection_tail_or_odd_mass_for_the_literal_CCM_residual
  next_decisive_test: exact_selected_variance_and_finite_Riesz_crosswalk
  progress_class: PROOF_PROGRESS
  route_score: 5
```
