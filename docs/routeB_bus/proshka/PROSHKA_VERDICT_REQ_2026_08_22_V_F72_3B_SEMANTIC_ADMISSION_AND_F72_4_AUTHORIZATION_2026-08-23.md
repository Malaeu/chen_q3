# STATUS: PROVED — F72.3B SEMANTICALLY ADMITTED AS A CONDITIONAL FUCHS PORT; F72.4 CENTER-INTEGRAL RATE AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_3B_AND_AUTHORIZE_F72_4_CENTER_INTEGRAL_RATE
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 193e21c6c310c0d096b7482eed2ce49cbe357cfd
  SOURCE_COMMIT: 193e21c6c310c0d096b7482eed2ce49cbe357cfd
  ACTUAL_SOURCE_COMMIT_PARENT: b20998850bdcc89205440022f6ed2f143b596c6f
  CLAIMED_SOURCE_RECORD_BASE_HEAD: b20998850bdcc89205440022f6ed2f143b596c6f
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean
  LEAN_GIT_BLOB: 11cc5ffa7d3154f7641e155b2a85b5f2e39a9463
  LEAN_SHA256_REPORTED: 9e94718d95a63ac9d8575a345856a3defcb44cbf01de5dd784885d6dbfe5a31f
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 23e4cb69a74a8e289b97ba66a69c0d5f224f1c56

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7840_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_PAPER_PORT
  THEOREM: Q3.RouteB.D0Pstar.selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates
  DIRECTION: EXPLICIT_FUCHS_EIGENRELATIONS_AND_CONCENTRATION_DEFECTS_TO_SELECTED_PROJECT_CHI_DEFECT_RATE
  PAPER_EIGENVALUES_ARE_ARGUMENTS: true
  PAPER_EIGENVALUES_DEFINED_FROM_PROJECT_CHI: false
  FULL_FUCHS_EIGENRELATIONS_REQUIRED_ON_PAPER_WINDOW: true
  FULL_RELATIONS_CONSUMED_AT_CENTER: true
  PROJECT_EIGENRELATIONS_FROM_EXACT_SELECTED_PAIR: true
  RESCALED_CENTER_NONZERO: true
  MU_CROSSWALK_DERIVED_BY_CANCELLATION: mu_equals_sqrt_2pi_mul_chi
  MU_CROSSWALK_ASSUMED: false
  PAPER_CONCENTRATION_VALUE: mu_squared_div_2pi
  PROJECT_SCALAR_ZERO: selectedFerrersPreAnchorPair_chi0
  PROJECT_SCALAR_FOUR: selectedFerrersPreAnchorPair_chi2
  DEGREE_MAP:
    paper_degree_0: project_chi0
    paper_degree_4: project_chi2
  PROJECT_CHI2_MISREAD_AS_PAPER_DEGREE_2: false
  POSITIVE_MU_BRANCH_IS_EXPLICIT: true
  POSITIVE_PROJECT_CHI_DERIVED: true
  SQUARE_ONLY_PORT_REFUTED_BY_PLANT: true
  WINDOW_IDENTITY: paperWindowRadius_lambda_squared_eq_2pi_lambda_squared
  PAPER_RATE_UNIT: paperWindowRadius_inverse_squared
  PROJECT_RATE_UNIT: selectedFerrersPaperLambda_inverse_squared
  RATE_TRANSFER_USES_2PI_GE_ONE: true
  COMMON_OUTPUT_CONSTANT: C0_plus_C4
  FITTED_CONSTANT: false
  C04_OBJECT_UNIT_AND_BRANCH_AUDIT: PASS
  C09_PRECOMMIT_AND_NO_FIT_AUDIT: PASS
  C10_EXACT_SELECTED_MODE_AUDIT: PASS

SCOPE_GUARD:
  PROVES_CONDITIONAL_PROJECT_CHI_RATE: true
  PROVES_FUCHS_THEOREM_1: false
  PROVES_EXISTENCE_OF_MU0_MU4: false
  PROVES_FUCHS_EIGENRELATIONS_FOR_SELECTED_MODES: false
  PROVES_POSITIVITY_OF_FUCHS_MU_FROM_FIRST_PRINCIPLES: false
  PROVES_PAPER_DEFECT_RATES: false
  PROVES_F72_4: false
  PROVES_F72_5_OR_L73_2: false
  RAW_PAPER_INPUT_REMAINS_EXPLICIT: true

SOURCE_RECORD_AUDIT:
  SAME_COMMIT_AS_LEAN: true
  BASE_HEAD_CORRECT: true
  BASE_HEAD_PROVENANCE_RECORDED: true
  PREFLIGHT_RECORDED: true
  LEAN_BLOB_AND_SHA256_PRESENT: true
  PUBLIC_SURFACE_COMPLETE: true
  PRIVATE_DECLARATIONS_RECORDED: true
  EXPECTED_AXIOM_PROFILES_FIELD_PLURAL: true
  CLOSES_OPENS_PRESENT: true
  VERIFICATION_HANDOFF_PRESENT: true
  NEXT_LOAD_BEARING_GAP_PRESENT: true
  SELF_BLOB_PLACEHOLDER: ACCEPTED_AS_SELF_REFERENCE_WORKAROUND
  STATUS: CLEAN

PREDICTION_FATE:
  P_F72_3B_1:
    claim: exact_mu_equals_sqrt_2pi_mul_chi_closes_by_comparing_full_eigenrelations_at_zero_and_cancelling_nonzero_rescaled_center
    fate: CONFIRMED
  P_F72_3B_2:
    claim: positive_branch_is_load_bearing_and_negative_branch_plant_refutes_square_only_port
    fate: CONFIRMED
  P_F72_3B_3:
    claim: paper_a_inverse_square_rate_transfers_to_project_lambda_inverse_square_without_fitted_constants
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: COMPLEX_SCALAR_CANCELLATION_OR_PAPERRESCALE_ZERO_NORMAL_FORM
    fate: NOT_OBSERVED
    observed:
      - LOCAL_SELECTED_LAMBDA_POSITIVITY_WAS_MADE_EXPLICIT
      - PI_GT_THREE_WAS_NEEDED_FOR_THE_FINAL_DENOMINATOR_COMPARISON
  RETROACTIVE_REPAIR: false

F72_4_ADJUDICATION:
  STATUS: LEAN_READY_EXACT_ASSEMBLY
  EXTERNAL_PAPER_INPUT: none_new
  INPUT: common_eventual_selected_project_chi_defect_rate
  EXACT_IDENTITIES:
    mode_zero: centerAnchorScalarZero_mul_I0_eq_chi0
    mode_four: centerAnchorScalarFour_mul_I4_eq_three_mul_chi2
  WHY_INTEGRAL: ProlatePair_I0_I4_are_exact_whole_line_integrals
  TARGET_VALUES:
    mode_zero: 1
    mode_four: 3
  COMMON_RATE_CONSTANT: three_mul_Cchi
  EXPANDING_WINDOW_SUP_ERROR_INTEGRATION_USED: false
  F72_1C_DEPENDENCY_REQUIRED: false
  CHARACTER: FREQUENCY_ZERO_IDENTITY_PLUS_CENTER_ANCHOR_ALGEBRA

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1FuchsSelectedEigenvalueDefectRate
  TARGET_THEOREM: selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
  REQUIRED_PRIVATE_PLANT: centerAnchoredIntegral_without_chiRate_plant
  CLOSES:
    - F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY

CLOSES:
  - F72_3B_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_3_SELECTED_PROJECT_FUCHS_EIGENVALUE_CROSSWALK
  - F72_3B_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_EXACT_CENTER_ANCHORED_I0_I4_IDENTITIES_AND_EVENTUAL_RATE

REGISTERED_PREDICTIONS:
  P_F72_4_1:
    claim: exact_frequency_zero_fields_and_center_anchor_locks_reduce_both_integral_rates_to_chi_defects_without_any_new_analysis
    probability: 0.98
  P_F72_4_2:
    claim: one_common_rate_constant_three_mul_Cchi_suffices_for_both_modes
    probability: 0.97
  P_F72_4_3:
    claim: F72_4_does_not_need_F72_1C_or_pointwise_cylinder_rates
    probability: 0.99
  LIKELIEST_FAILURE: COMPLEX_OFREAL_NORM_OR_H0_FOURIER_CENTER_REWRITE_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
ARISTOTLE_AUTHORIZED: false
QUEUE_STATUS_MUTATED: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_FUCHS_PAPER_INPUT
```

## ROUTE MAP

### 1. Semantic admission of F72.3B

The public theorem keeps the paper and project objects distinct.

The paper data are the functions `mu0`, `mu4`, their positivity, their full finite-Fourier eigenrelations for the rescaled exact selected modes, and the concentration-defect estimates for `mu^2/(2*pi)` in the paper window unit. The theorem never defines `mu` from a project scalar. `[COFINAL_FAMILY][LEAN]`

The project data are the literal `selectedFerrersPreAnchorPair` modes and scalars. At `t = 0`, F72.3A identifies the paper transform of `paperRescale h` with `sqrt(2*pi)` times the rescaled project transform. The project eigenrelation and the paper eigenrelation therefore act on the same nonzero vector `paperRescale h 0`. Cancelling it proves

\[
\mu=\sqrt{2\pi}\,\chi.
\]

The nonzero factor is not a convention: it follows from the exact selected center and the nonzero constant `(2*pi)^(-1/4)`. `[ABSTRACT][LEAN]` **[C04] [C10]**

The theorem's full-window Fuchs eigenrelations are stronger than the one center equation consumed in the final cancellation. This is intentional. It preserves source provenance: the caller must supply an actual eigenrelation for the exact rescaled selected mode, not merely the scalar equality that the theorem is supposed to derive. `[COFINAL_FAMILY][LEAN]`

### 2. Positive branch and rate transfer

The concentration value sees only

\[
\Lambda=\frac{\mu^2}{2\pi}=\chi^2.
\]

Without a sign condition, `chi = -1` has zero concentration defect and project defect `|1-chi|=2`. The private plant records exactly this counterexample. The assumptions `mu0(k)>0` and `mu4(k)>0`, together with the exact crosswalk, derive `chi0(k)>0` and `chi2(k)>0`; no positive phase is selected after inspecting the defect. `[ABSTRACT][LEAN]` **[C09]**

For positive `chi`,

\[
|1-\chi|\le |1-\chi^2|
\]

because `|1-chi^2|=|1-chi|\,(1+chi)` and `1+chi>=1`. The exact window identity

\[
\operatorname{paperWindowRadius}(\lambda)^2
=2\pi\lambda^2
\]

then gives

\[
\frac{C}{\operatorname{paperWindowRadius}(\lambda)^2}
\le\frac{C}{\lambda^2}
\]

for `C>=0`. The output common constant `C0+C4` is an a priori algebraic combination, not a fitted quantity. `[COFINAL_FAMILY][LEAN]`

### 3. Exact scope boundary

The admitted theorem proves an implication conditional on explicit Fuchs data. It does not formalize Fuchs Theorem 1, construct `mu0` or `mu4`, prove their positive convention, or establish the concentration-defect rates. Those remain external paper inputs. `[COFINAL_FAMILY][PAPER]`

Accordingly:

```text
F72.3B kernel port:
  SEMANTICALLY_ADMITTED.

Fuchs external rate and phase suppliers:
  EXPLICIT INPUTS, not proved by F72.3B.

F72.4 and later floors:
  NOT CLAIMED by the admitted theorem.
```

## F72.4 EXACT TARGET

Create exactly one Lean source file with exactly one direct import:

```lean
import Q3.Proofs.RouteB.G6N1FuchsSelectedEigenvalueDefectRate
```

The exact public theorem is:

```lean
theorem selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
    (Cχ : ℝ) (hCχ : 0 ≤ Cχ)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ CΙ : ℝ, 0 ≤ CΙ ∧
      ∀ᶠ k in Filter.atTop,
        ‖centerAnchorScalarZero k *
            ((selectedFerrersPreAnchorPair k).I0 : ℂ) - (1 : ℂ)‖ ≤
            CΙ / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
            ((selectedFerrersPreAnchorPair k).I4 : ℂ) - (3 : ℂ)‖ ≤
            CΙ / (selectedFerrersPaperLambda k) ^ 2
```

Use `CΙ = 3 * Cχ`. The Unicode capital iota may be replaced by an ASCII identifier such as `CI`; no mathematical change is permitted.

The terms `I0` and `I4` are the exact whole-line integrals by the fields `ProlatePair.I0_eq_integral` and `ProlatePair.I4_eq_integral`. The proof should consume the stronger exact frequency-zero fields

```lean
ProlatePair.h0_fourier_center
ProlatePair.h4_fourier_center
```

together with

```lean
centerAnchorScalarZero_mul_center
centerAnchorScalarFour_mul_center.
```

They give, exactly,

\[
 a_{0,k}I_{0,k}=\chi_{0,k},
 \qquad
 a_{4,k}I_{4,k}=3\chi_{2,k}.
\]

Therefore

\[
 \|a_{0,k}I_{0,k}-1\|=|1-\chi_{0,k}|,
\]

and

\[
 \|a_{4,k}I_{4,k}-3\|=3|1-\chi_{2,k}|.
\]

No integration of the F72.1C sup-error is allowed. Such an integration over a window of length `2*lambda` would lose one power and recover only an `O(lambda^-1)` estimate. F72.4 exists precisely to avoid that loss.

## REQUIRED PRIVATE PLANT

```lean
private theorem centerAnchoredIntegral_without_chiRate_plant :
    |(-1 : ℝ) - 1| = 2 ∧ |3 * (-1 : ℝ) - 3| = 6 := by
  norm_num
```

It records that center anchoring alone does not force the whole-window integral targets: a negative transform scalar sends the anchored integrals to `-1` and `-3`. The chi-defect input is load-bearing.

## PROOF ROUTE

1. Run the catalog preflight before editing:

```text
./ask.sh "centerAnchorScalarZero I0 h0_fourier_center center integral rate chi defect"
```

2. Obtain the eventual chi bounds from `hχ`.
3. For each `k`, derive the two exact anchored-integral identities from the `ProlatePair` frequency-zero fields and center locks.
4. Rewrite the complex norms of real casts with `Complex.norm_real` and `Real.norm_eq_abs`; use `abs_sub_comm` where necessary.
5. Use the mode-zero defect directly.
6. Multiply the mode-four defect by `3` exactly.
7. Choose `CI = 3*Cχ`; use `hCχ` only for the harmless common-constant enlargement of the mode-zero row.
8. Do not invoke F72.1C, Satz 9, a cylinder target bound, or any new eventual denominator guard.

## FORBIDDEN

```text
integrate the pointwise F72.1C error over the expanding window;
import G6N1SelectedFerrersDirectCylinderRate;
add an integral-rate hypothesis;
add target-integral values as hypotheses;
replace I0/I4 by a neighboring integral object;
change target centers 1 and 3;
identify project chi2 with paper degree 2;
fit CI after inspecting values;
bundle F72.5 or L73.2;
edit F72.3B or center-anchor files;
paper axiom;
sorry;
admit;
typed hole;
theorem weakening.
```

## FILES

```text
Lean:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean

Source record:
  docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_2026-08-23.md
```

The source record must use the exact current parent obtained from `git rev-parse HEAD` immediately before editing, list the public theorem and private plant, and carry the plural field `EXPECTED_AXIOM_PROFILES`.

## VALIDATION

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean

lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersCenterIntegralRate

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean
```

Expected public axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_LEAN

FAILURE:
  F72_4_CENTER_ANCHOR_OR_COMPLEX_COERCION_GAP
```

After separate semantic admission, the next floor is:

```text
F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
```

## STRONGEST ATTACK

The strongest objection is that the source theorem uses full paper eigenrelations but extracts the scalar crosswalk only at the center. This is not a circular weakening. The full relations remain in the public type and force `mu` to be an actual eigenvalue of the paper operator on the exact rescaled selected mode. Evaluation at one nonzero point is then sufficient to identify two scalar eigenvalues of the same nonzero vector. Replacing those full relations by a center-only scalar equation would be circular and remains forbidden. `[COFINAL_FAMILY][LEAN]` **[C10]**

The second objection is the sign branch. The concentration defect controls `chi^2`, not `chi`. The private plant shows the negative branch is perfectly compatible with zero concentration defect. The explicit positive `mu` assumptions are therefore mathematically load-bearing, and the proof correctly derives, rather than assumes, positive project `chi`. `[ABSTRACT][LEAN]` **[C04] [C09]**

## META CLOSEOUT

**What became smaller?**

The Fuchs floor is no longer an open unit/phase crosswalk. Its kernel part is a proved conditional port from explicit paper data to the selected project scalar defect rate.

**What was killed?**

- `a = lambda`;
- `Lambda = chi`;
- project `chi2` as Fuchs degree `2`;
- a square-only rate transfer without positive phase;
- defining `mu` from project `chi`;
- fitted window constants.

**What must not be tried again?**

Do not recover the integral rate by integrating the pointwise cylinder estimate over a window of length `2*lambda`. That loses a power. Use the exact frequency-zero eigenrelation.

**Current smallest named gap:**

```text
F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
```

**Next cheapest decisive test:**

Compile the exact center-anchored `I0/I4` identities and their eventual common rate.

**Prior prediction fate:**

All three registered F72.3B predictions were confirmed. The predicted complex-cancellation failure did not occur; only local positivity and a stronger numerical lower bound for `2*pi` were needed. No prediction was repaired retroactively.

**Memory entry:**

```yaml
iteration:
  target: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
  invariant_learned: full Fuchs eigenrelations and positive phase must remain explicit while the scalar crosswalk is derived at one nonzero center
  forbidden_future_move: integrate a lambda^-2 pointwise rate over an expanding lambda-window
  next_decisive_test: exact center-anchor times stored-integral equals chi identity
```
