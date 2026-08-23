# STATUS: PROVED — H2A.4.0 SEMANTICALLY ADMITTED; DIRECT L73-TO-RIESZ RATE KILLED; EXACT SOURCE-ACTION SPLIT AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_4_0_SELECTED_FERRERS_RESIDUAL_VARIANCE_LOCK_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: c1bf4d3e244f23ace7d3ea3760da4cfcf4d05022
  SOURCE_COMMIT: c1bf4d3e244f23ace7d3ea3760da4cfcf4d05022
  ACTUAL_PARENT: bba4c35eaee0b91f345d354116460f8c7c166bbf
  CLAIMED_PARENT: bba4c35eaee0b91f345d354116460f8c7c166bbf
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
  LEAN_GIT_BLOB: 90003d95866658ae9cb7c103324951665bcff6fc
  LEAN_SHA256_REPORTED: 052fdda44d2be65e9e7f76e6a9651d5903dac5dd3ed9485a108562422df35597
  LEAN_LINES_REPORTED: 537
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_0_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 5f0e9d476892dd577ed50bf293a15254c989bc7b
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7926_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS_FOR_ALL_5_PUBLIC_THEOREMS_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SELECTED_FINITE_RESIDUAL_VARIANCE_AND_RIESZ_LOCK
  CONDITIONAL_PORT: selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
  FINAL_SHELL: selectedFerrersCofinalSourceData
  FINITE_ROW: selectedFerrersFiniteCCMRow
  MATRIX: sourceCCMFiniteMatrix_at_the_same_selected_index
  RAYLEIGH_SHIFT: selectedFerrersFiniteCCMRayleigh
  RESIDUAL: selectedFerrersFiniteCCMResidual
  RESIDUAL_ENERGY: selectedFerrersFiniteCCMResidualEnergy
  SECOND_MOMENT: selectedFerrersFiniteCCMSecondMoment
  VARIANCE_IDENTITY: "rho_k^2 = M2_k - a_k^2"
  FINITE_RIESZ_OPERATOR: sourceCCMFiniteRieszOperator
  FINITE_RIESZ_DEFECT: "R_i(x_k) - a_k*x_k on E_m_N"
  AMBIENT_OPERATOR_CLAIMED: false
  COMPRESSION_CLAIMED: false
  SELECTED_ROW_REALIFIED: false
  RAYLEIGH_SHIFT_REPLACED_OR_FITTED: false
  C04_OBJECT_AUDIT: PASS
  C10_FUNCTIONAL_AUDIT: PASS

PLANT_AUDIT:
  EXACT_EVEN_UNIT_ROW_WITH_NONZERO_RAYLEIGH_RESIDUAL:
    STATUS: PASS
    CARRIER: Fin_3
    REFLECTION: swap_0_and_2
    MATRIX: "[[0,1,0],[1,0,1],[0,1,0]]"
    ROW: "(0,1,0)"
    ODD_MASS: 0
    RAYLEIGH: 0
    RESIDUAL: "(1,0,1)"
    RESIDUAL_ENERGY: 2
    CONCLUSION: odd_mass_or_exact_evenness_does_not_control_operator_residual

H2A_BOUNDARY_AFTER_ADMISSION:
  SELECTED_ODD_MASS_DECAY: CLOSED
  SELECTED_FINITE_CCM_RESIDUAL_ENERGY_OBJECT_LOCK: CLOSED
  SELECTED_FINITE_CCM_RESIDUAL_VARIANCE_IDENTITY: CLOSED
  SELECTED_FINITE_RIESZ_RESIDUAL_CROSSWALK: CLOSED
  SELECTED_FINITE_CCM_RESIDUAL_DECAY: OPEN
  SELECTED_EVEN_SECTOR_FLOOR: OPEN
  SELECTED_ODD_SECTOR_FLOOR: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

H2A_4_1_ADJUDICATION:
  REQUESTED_ROUTE: L73_PHYSICAL_APPROXIMATION_CONTROLS_EXACT_FINITE_RIESZ_DEFECT
  STATUS: KILLED_AS_UNSUPPORTED_INFERENCE
  MATHEMATICAL_NEGATION_OF_SELECTED_RESIDUAL_DECAY_PROVED: false
  KILL_SCOPE: L73_L2_OR_LOCALLY_UNIFORM_ERROR_ALONE_TO_RIESZ_DEFECT
  REASONS:
    - L73_controls_the_selected_trial_transform_and_a_window_Hilbert_error_not_the_restricted_Weil_form_action
    - the_finite_Riesz_operator_represents_the_restricted_Weil_form_and_is_not_an_L2_continuous_family_supplied_by_L73
    - no_uniform_graph_norm_or_form_dual_continuity_envelope_is_present
    - the_factor_four_target_is_inversion_even_but_is_not_proved_to_be_a_finite_Riesz_eigenvector_or_radical_vector
    - the_ambient_associated_Weil_operator_compression_crosswalk_remains_source_unavailable
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

ABSTRACT_FALSIFIER:
  NAME: VANISHING_HILBERT_ERROR_WITHOUT_UNIFORM_ACTION_DOES_NOT_CONTROL_RESIDUAL
  CARRIER: "Fin 2 for every n"
  OPERATOR: "R_n = diag(0,n+2)"
  TARGET: "y_n = e_0, an exact zero-eigenvector"
  UNIT_ROW: "q_n = sqrt(1-(n+2)^(-2))*e_0 + (n+2)^(-1)*e_1"
  HILBERT_ERROR: "norm(q_n-y_n) -> 0"
  EXACT_RAYLEIGH: "a_n = (n+2)^(-1)"
  RESIDUAL_ENERGY: "norm(R_n*q_n-a_n*q_n)^2 = 1-(n+2)^(-2) -> 1"
  CONCLUSION: L2_tracking_requires_a_uniform_action_or_form_dual_bound
  SCOPE: ABSTRACT
  VERIFIER: PAPER

REPAIRED_SEQUENCE:
  - H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
  - H2A_4_1B_SELECTED_FERRERS_ERROR_AND_TARGET_FINITE_FORM_ACTION_DECAY
  - H2A_4_1C_SELECTED_FERRERS_RESIDUAL_VARIANCE_RATE

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED
  CODE: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1A_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_SOURCE_ACTION_SPLIT_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
    - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
  PRIMARY_ROLE: >-
    Expose the exact factor-four target and scaled physical L73 error as
    window-Hilbert vectors, project both into the same selected E_m_N, and
    prove the exact finite-Riesz residual decomposition. This transaction
    proves no rate. It identifies the two exact source-action terms which a
    real H2A.4.1 proof must estimate: the shifted Riesz action on the physical
    error and the shifted Riesz defect of the projected factor-four target.
  PUBLIC_SURFACE_REQUIRED:
    - selectedFerrersFactorFourTargetVector
    - selectedFerrersScaledPhysicalErrorVector
    - selectedFerrersFactorFourTargetProjection
    - selectedFerrersScaledPhysicalErrorProjection
    - selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target
    - selectedFerrersFiniteRieszDefect_sourceScale_split
    - norm_sourceScale_mul_selectedFerrersFiniteRieszDefect_le_action_budget
  REQUIRED_PRIVATE_PLANTS:
    - vanishing_Hilbert_error_without_uniform_Riesz_action_does_not_control_residual_plant
    - exact_target_match_without_target_action_theorem_does_not_control_residual_plant
  CLOSES:
    - SELECTED_FERRERS_FACTOR_FOUR_TARGET_HILBERT_OBJECT_LOCK
    - SELECTED_FERRERS_SCALED_PHYSICAL_ERROR_PROJECTION_LOCK
    - SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_EXACT_SPLIT
    - SELECTED_FERRERS_RESIDUAL_SOURCE_ACTION_BUDGET
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: H2A_4_1B_SELECTED_FERRERS_ERROR_AND_TARGET_FINITE_FORM_ACTION_DECAY

SOURCE_ACTION_SPLIT_CONTRACT:
  OBJECTS: |-
    i_k := (selectedFerrersCofinalSourceData P).index k
    x_k := the exact selected kTrial in E_m_N(i_k)
    s_k := (selectedFerrersCofinalSourceData P).sourceScale k
    t_k := sTrial_m_N for that exact selected trial
    G_k := the factor-four explicitCCMLimitH E-star target in H_m(i_k)
    e_k := s_k * gTrial_k - G_k in H_m(i_k)
    gE_k := P_m_N(i_k) G_k
    eE_k := P_m_N(i_k) e_k
    R_k := sourceCCMFiniteRieszOperator i_k
    a_k := selectedFerrersFiniteCCMRayleigh P k
  EXACT_VECTOR_IDENTITY: "s_k*x_k = t_k*(eE_k + gE_k)"
  EXACT_ACTION_IDENTITY: >-
    s_k*(R_k*x_k-a_k*x_k)
      = t_k*((R_k*eE_k-a_k*eE_k) + (R_k*gE_k-a_k*gE_k))
  EXACT_NORM_BUDGET: >-
    norm(s_k)*norm(R_k*x_k-a_k*x_k)
      <= t_k*(norm(R_k*eE_k-a_k*eE_k)
              + norm(R_k*gE_k-a_k*gE_k))
  RATE_CONTENT: none

H2A_4_1B_EXACT_FUTURE_TARGET:
  ERROR_ACTION_TERM: "A_k = norm(R_k*eE_k-a_k*eE_k)"
  TARGET_ACTION_TERM: "T_k = norm(R_k*gE_k-a_k*gE_k)"
  REQUIRED_LIMIT: >-
    (t_k / norm(s_k)) * (A_k + T_k) tends to zero
  L73_CURRENTLY_CONTROLS: "norm(e_k), after the existing window integration"
  L73_DOES_NOT_CURRENTLY_CONTROL:
    - A_k
    - T_k
  RATE_EXPONENT_AUTHORIZED_NOW: false

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: FACTOR_FOUR_TARGET_PLUS_PHYSICAL_ERROR_ACTION_SPLIT
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 5
    ADVANTAGE: preserves_the_exact_L73_error_and_exposes_the_missing_target_defect
    DISCRIMINATOR: derive_a_source_upper_envelope_for_A_k_and_T_k_with_the_weighted_sum_tending_to_zero
  R2:
    CODE: DIRECT_FINITE_FORM_DUAL_DEFECT
    ROLE: RUNNER_UP
    KILL_POWER: 9
    COST: 7
    FORMULA: >-
      sup over unit v in E_m_N of
      abs(BW_m_N(v,x_k)-a_k*inner(v,x_k))
    ADVANTAGE: basis_invariant_and_exactly_equal_to_the_finite_Riesz_defect_norm
    DISCRIMINATOR: obtain_a_uniform_source_pairing_bound_without_using_an_operator_norm_or_row_sum_surrogate
  ZERO_CONSISTENT_RESULT: INCONCLUSIVE_UNLESS_ONE_DISCRIMINATOR_IS_PROVED

FORBIDDEN:
  - infer_Riesz_action_decay_from_Hm_or_L2_error_alone
  - infer_target_Riesz_defect_zero_from_inversion_evenness
  - infer_target_Riesz_defect_zero_from_L73_transform_convergence
  - replace_finite_Riesz_action_by_ambient_A_m_action
  - claim_finite_Riesz_is_an_ambient_compression
  - add_an_abstract_source_action_rate_hypothesis_and_call_the_receiver_H2A_4_1
  - use_absolute_row_sums_or_an_unproved_operator_norm_as_the_source_rate
  - replace_the_exact_selected_Rayleigh_shift
  - replace_the_selected_shell_or_selected_row
  - edit_H2A_0_through_H2A_4_0_or_L73_3_through_L73_8
  - bundle_sector_floors_simple_ground_Theorem510_or_real_zeros
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

VALIDATION:
  WORKDIR_Q3:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit
  WORKDIR_REPO_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  EXPECTED_AXIOM_PROFILE_FOR_EVERY_PUBLIC_THEOREM_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound

SUCCESS: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
FAILURE: H2A_4_1A_FACTOR_FOUR_TARGET_HM_OR_ACTION_SPLIT_GAP

NEXT_LOAD_BEARING_GAP: H2A_4_1B_SELECTED_FERRERS_ERROR_AND_TARGET_FINITE_FORM_ACTION_DECAY
NEXT_CHEAPEST_DECISIVE_TEST: >-
  Prove the exact split first. Then attack the two displayed action terms
  separately. A numerical or zero-consistent small H_m error is not a pass.
  The discriminator is an explicit upper envelope for A_k and T_k whose
  normalizer-weighted sum tends to zero.

REGISTERED_PREDICTIONS:
  P_H2A41A_1:
    claim: exact_vector_and_Riesz_action_splits_close_by_linearity_without_new_mathematics
    probability: 0.93
  P_H2A41A_2:
    claim: the_main_Lean_friction_is_publicizing_the_factor_four_target_MemLp_object_previously_private_in_H2A_3
    probability: 0.84
  P_H2A41B_1:
    claim: L73_error_control_alone_does_not_supply_the_error_action_envelope_A_k
    probability: 0.98
  P_H2A41B_2:
    claim: the_projected_factor_four_target_defect_T_k_is_not_definitionally_zero_and_requires_new_source_mathematics
    probability: 0.95
  LIKELIEST_FAILURE: FACTOR_FOUR_TARGET_MEMLP_PUBLIC_OBJECT_OR_UNBOUNDED_FORM_ACTION_GAP

PRIOR_PREDICTION_FATES:
  P_H2A4_0_1:
    probability: 0.97
    fate: CONFIRMED
    result: exact_variance_identity_closed_by_finite_Hermitian_algebra
  P_H2A4_0_2:
    probability: 0.88
    fate: CONFIRMED
    result: selected_Riesz_crosswalk_reused_the_public_selected_synthesis_theorem_without_interface_substitution
  P_H2A4_0_3:
    probability: 0.995
    fate: CONFIRMED
    result: exact_Fin3_even_row_plant_rejected_residual_from_parity
  LIKELIEST_FAILURE:
    prediction: DEPENDENT_E_M_N_SUBTYPE_COERCION_OR_COMPLEX_INNER_NORMAL_FORM
    fate: CONFIRMED
    observed: subtype_coercion_and_complex_normal_form_only_no_new_mathematics
  RETROACTIVE_REPAIR: false

CLOSES:
  - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_ENERGY_OBJECT_LOCK
  - SELECTED_FERRERS_FINITE_CCM_RESIDUAL_VARIANCE_IDENTITY
  - SELECTED_FERRERS_FINITE_RIESZ_RESIDUAL_CROSSWALK
OPENS: []

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_AUTHORIZED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### H2A.4.0 admission

The source commit has the exact authorized parent, one Lean file and its source
record in the same commit.  The two definitions and five public theorems use
the selected Ferrers shell, selected complex row, literal CCM matrix and exact
selected Rayleigh value.  No neighboring source interface is substituted.
`[COFINAL_FAMILY][LEAN]`

The variance identity is the exact finite Hermitian identity

\[
  \|K_kq_k-a_kq_k\|^2
  =\|K_kq_k\|^2-a_k^2.
\]

The proof expands the residual only after unit normalization, Hermitian
Rayleigh reality and exact residual orthogonality are available.  Therefore
there is no fitted shift and no hidden realification. `[FINITE_CELL][LEAN]`

The Riesz theorem transports the same selected row through the public finite
synthesis and identifies the result with the defect of the finite Riesz
operator on the same selected `kTrial`.  It remains entirely inside `E_m_N`;
coercion to `H_m` is only the subtype inclusion.  The theorem does not invoke
the domain-restricted associated operator `A_m` and does not claim an ambient
compression. `[FINITE_CELL][LEAN]`

The local `rfl` bridges through private upstream definitions are brittle and
expensive, but they prove definitional equality to the public objects.  They
are maintenance debt, not a semantic substitution.  Do not reopen this floor
only to refactor those bridges. `[FINITE_CELL][LEAN]`

### The registered L73 discriminator

L73.7/L73.8 proves locally uniform convergence of the scaled selected trial
transform to `centeredXi`; H2A.3 additionally turns its full pointwise physical
error into an `H_m` squared-error bound.  Neither theorem contains
`sourceCCMFiniteRieszOperator`, `BW_m_N`, the selected CCM matrix action, or a
form-dual continuity envelope. `[COFINAL_FAMILY][LEAN]`

The source itself distinguishes the lower-semicontinuous Weil form, its
finite Riesz restriction, and the domain-restricted associated operator.  It
explicitly does not identify the finite Riesz operator with an ambient
restriction or compression. `[ABSTRACT][PAPER]` **[C04]**

The inference

```text
physical H_m error tends to zero
therefore finite Riesz residual tends to zero
```

is false without a uniform action bound.  The displayed two-dimensional
counterexample has unit vectors converging in Hilbert norm to an exact
zero-eigenvector while the Rayleigh residual stays asymptotically unit size.
This kills the inference, not the source-specific residual-decay theorem.
`[ABSTRACT][PAPER]` **[C10]**

There is a second independent term.  Even if the physical error were exactly
zero, the factor-four target must still be shown to have small shifted finite
Riesz defect.  Inversion-evenness controls reflection parity only; H2A.4.0's
plant already proves that exact evenness does not imply an eigenrelation.
`[ABSTRACT][LEAN]` **[C10]**

## FINAL PROPOSAL

Ratify H2A.4.0 exactly at finite-Riesz scope.  Do not authorize a theorem named
`residual_rate_of_modeAndChiRates`: that would hide the missing action theorem
inside the theorem name.

The next bounded transaction is the exact source-action split.  It must expose
both load-bearing terms without estimating either.  Only after that split is
kernel-checked may the project attack H2A.4.1B:

\[
  \frac{t_k}{|s_k|}\bigl(A_k+T_k\bigr)\longrightarrow0.
\]

No exponent is registered yet.  A source-derived envelope decides the rate;
the existing L73 exponent does not automatically survive the Weil-form
action. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The strongest reviewer objection is:

> The trial is close to the explicit target in the window Hilbert norm, but
> the relevant operator family is not uniformly bounded in that norm, and the
> target is not known to be its eigenvector.  Why should the residual shrink?

At the present pin, it should not be claimed.  The exact repair is to split the
residual into the action on the physical error and the target's own shifted
finite-form defect.  A proof must control both.  Controlling only one is not a
weaker proof of H2A.4.1; it is an incomplete sufficient condition.

## CODEX DIRECTIVE

```text
Execute exactly H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN.

Create one Lean file and one source record in one commit.
Use the two direct imports and seven required public names from the YAML.
Prove only the exact vector identity, exact shifted-action split and norm
budget.  Include both plants.

Do not prove or assume any decay rate.
Do not edit H2A.0 through H2A.4.0 or L73.3 through L73.8.
Do not define an ambient Weil operator or claim compression.
Do not submit Aristotle.
```

## META CLOSEOUT

**What became smaller?**

The overloaded residual-rate question is now two explicit finite-form action
terms on one selected source family.  H2A.4.0 supplies their exact consumer
norm. `[COFINAL_FAMILY][CONDITIONAL]`

**What was killed?**

- residual decay from odd-mass decay;
- residual decay from L73 Hilbert error alone;
- target eigenvector status from inversion-evenness;
- ambient compression hidden behind the finite Riesz operator.

**What must not be tried again?**

Do not add a thin receiver whose new premise is already the desired source
action rate.  Do not call Hilbert convergence graph-norm convergence.  Do not
use a matrix norm or row-sum surrogate without a source-derived cofinal
envelope.

**Current smallest named gap:**

```text
H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
```

**Next cheapest decisive test:**

Kernel-check the exact split, then seek a genuine upper envelope for both
`A_k` and `T_k`.  A zero-compatible numerical result is inconclusive unless
it discriminates the two terms separately.

**Fate of prior predictions:**

All three H2A.4.0 predictions are confirmed.  The predicted subtype/coercion
failure fired exactly.  No retroactive repair.

```yaml
iteration:
  target: H2A.4.0 semantic admission and H2A.4.1 discriminator
  status: PROGRESS
  failed_strategy: infer_finite_Riesz_residual_decay_from_L73_Hilbert_error
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN
  invariant_learned: Hilbert_error_and_restricted_Weil_form_action_are_different_topologies_and_the_target_has_its_own_defect
  forbidden_future_move: hide_source_action_decay_inside_a_thin_rate_receiver
  next_decisive_test: exact_error_plus_target_Riesz_action_split
  progress_class: PROOF_PROGRESS
  route_score: 5
```
