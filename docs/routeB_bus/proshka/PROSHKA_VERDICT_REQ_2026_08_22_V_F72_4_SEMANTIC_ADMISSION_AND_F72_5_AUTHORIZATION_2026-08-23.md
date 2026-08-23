# STATUS: PROVED — F72.4 SEMANTICALLY ADMITTED; F72.5 ZERO-MASS CYLINDER PACKET ASSEMBLY AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_4_AND_AUTHORIZE_F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: d4c6fafc8ca70470c9b9ee52f4c697318500af3f
  SOURCE_COMMIT: d4c6fafc8ca70470c9b9ee52f4c697318500af3f
  ACTUAL_SOURCE_COMMIT_PARENT: b0cbbc9ef0e49b8a52e818f417d85540dfcb2161
  CLAIMED_SOURCE_RECORD_BASE_HEAD: b0cbbc9ef0e49b8a52e818f417d85540dfcb2161
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean
  LEAN_GIT_BLOB: 5fbff847fe85311e0face9b8afc532ca1af19f6c
  LEAN_SHA256_REPORTED: c08d502b278fecf715241e80dbe02f246b4ea2064fbcd1cfc903d0ac8473c7e4
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 3b7f7f99dbae4bbd3c1b1636874c96611d099ed2

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7841_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED
  THEOREM: Q3.RouteB.D0Pstar.selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
  DIRECTION: SELECTED_PROJECT_CHI_DEFECT_RATE_TO_CENTER_ANCHORED_WHOLE_LINE_INTEGRAL_RATE
  INPUT_IS_EXACT_SELECTED_PROJECT_CHI_RATE: true
  OUTPUT_USES_LITERAL_PROLATEPAIR_I0_I4: true
  OUTPUT_I0_I4_ARE_WHOLE_LINE_INTEGRALS_BY_STRUCTURE: true
  FREQUENCY_ZERO_FIELDS_USED:
    - ProlatePair.h0_fourier_center
    - ProlatePair.h4_fourier_center
  CENTER_ANCHOR_FIELDS_USED:
    - centerAnchorScalarZero_mul_center
    - centerAnchorScalarFour_mul_center
  EXACT_IDENTITIES:
    mode_zero: centerAnchorScalarZero_mul_I0_eq_chi0
    mode_four: centerAnchorScalarFour_mul_I4_eq_three_mul_chi2
  TARGETS:
    mode_zero: 1
    mode_four: 3
  COMMON_OUTPUT_CONSTANT: three_mul_Cchi
  POINTWISE_CYLINDER_RATE_INTEGRATED_OVER_EXPANDING_WINDOW: false
  F72_1C_IMPORTED: false
  NEW_ANALYTIC_INPUT: false
  FITTED_CONSTANT: false
  C04_OBJECT_AND_DEGREE_AUDIT: PASS
  C09_PRECOMMITTED_ANCHOR_AND_CONSTANT_AUDIT: PASS
  C10_EXACT_SCALAR_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_CENTER_ANCHORED_INTEGRAL_RATE: true
  PROVES_FUCHS_THEOREM_1: false
  PROVES_PROJECT_CHI_DEFECT_RATE: false
  PROVES_SELECTED_MODE_CYLINDER_RATE: false
  PROVES_ZERO_MASS_PACKET_RATE: false
  PROVES_F72_5_OR_F72_6: false
  PROVES_L73_2_OR_RH: false
  CHI_RATE_REMAINS_EXPLICIT_INPUT: true

SOURCE_RECORD_AUDIT:
  SAME_COMMIT_AS_LEAN: true
  BASE_HEAD_CORRECT: true
  BASE_HEAD_PROVENANCE_RECORDED: true
  PREFLIGHT_RECORDED: true
  LEAN_BLOB_AND_SHA256_PRESENT: true
  PUBLIC_SURFACE_COMPLETE: true
  PRIVATE_PLANT_RECORDED: true
  EXPECTED_AXIOM_PROFILES_FIELD_PLURAL: true
  CLOSES_OPENS_PRESENT: true
  VERIFICATION_HANDOFF_PRESENT: true
  NEXT_LOAD_BEARING_GAP_PRESENT: true
  SELF_BLOB_PLACEHOLDER: ACCEPTED_AS_SELF_REFERENCE_WORKAROUND
  STATUS: CLEAN

PREDICTION_FATE:
  P_F72_4_1:
    claim: exact_frequency_zero_fields_and_center_anchor_locks_reduce_both_integral_rates_to_chi_defects_without_new_analysis
    fate: CONFIRMED
  P_F72_4_2:
    claim: one_common_rate_constant_three_mul_Cchi_suffices_for_both_modes
    fate: CONFIRMED
  P_F72_4_3:
    claim: F72_4_does_not_need_F72_1C_or_pointwise_cylinder_rates
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: COMPLEX_OFREAL_NORM_OR_H0_FOURIER_CENTER_REWRITE_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: DIV_LE_DIV_OF_NONNEG_RIGHT_REQUIRED_NONNEGATIVE_DENOMINATOR_PROOF
  RETROACTIVE_REPAIR: false

F72_5_ADJUDICATION:
  STATUS: LEAN_READY_FINITE_ALGEBRA
  CHARACTER: EXACT_SOURCE_SCALE_PLUS_TWO_MODE_AND_TWO_INTEGRAL_RATE_ASSEMBLY
  SOURCE_SCALE_NAME: selectedFerrersLemma72Scale
  SOURCE_SCALE_FORMULA: negative_centerAnchorZero_mul_centerAnchorFour_div_16_mul_normalizingDenominator
  SOURCE_SCALE_PRECOMMITTED_BEFORE_RATE: true
  SOURCE_SCALE_NONZERO_FROM:
    - centerAnchorScalarZero_ne
    - centerAnchorScalarFour_ne
    - selected_pair_I0_positive
    - selected_pair_I4_positive
  EXACT_PACKET_IDENTITY: explicitCCMLimitH_eq_cylinder_combination
  MODE_RATE_INPUTS: exact_selected_center_anchored_h0_h4_rates_to_D0_D4
  INTEGRAL_RATE_SUPPLIER: selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
  TARGET_GLOBAL_BOUNDS_REQUIRED_PRIVATELY:
    D0: 1
    D4: 91
  FACTOR_FOUR_INSERTED_HERE: false
  OUTPUT: SELECTED_ZERO_MASS_PACKET_RATE_TO_EXPLICIT_CCM_LIMIT_H
  NEW_EXTERNAL_INPUT: none

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersDirectCylinderRate
    - Q3.Proofs.RouteB.G6N1SelectedFerrersCenterIntegralRate
  PUBLIC_DEFINITION: selectedFerrersLemma72Scale
  PUBLIC_THEOREMS:
    - selectedFerrersLemma72Scale_ne
    - selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates
  REQUIRED_PRIVATE_PLANT: zeroMassCylinderPacket_wrong_scale_sign_plant
  CLOSES:
    - F72_5_SELECTED_FERRERS_INTERNAL_LEMMA72_SCALE
    - F72_5_ZERO_MASS_CYLINDER_PACKET_RATE
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE

CLOSES:
  - F72_4_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_EXACT_NEGATIVE_SOURCE_SCALE_IDENTITY_AND_LAMBDA_MINUS_TWO_PACKET_RATE

REGISTERED_PREDICTIONS:
  P_F72_5_1:
    claim: the_negative_source_scale_cancels_the_exact_prolateCombination_denominator_and_gives_the_required_D4_over_16_minus_3D0_over_16_orientation
    probability: 0.97
  P_F72_5_2:
    claim: source_scale_nonvanishing_closes_from_positive_I0_I4_and_nonzero_center_anchors_without_new_analysis
    probability: 0.99
  P_F72_5_3:
    claim: F72_1C_mode_rates_plus_F72_4_integral_rates_and_crude_D0_D4_bounds_preserve_lambda_inverse_squared_rate
    probability: 0.93
  LIKELIEST_FAILURE: COMPLEX_DIVISION_CANCELLATION_OR_NORM_PRODUCT_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
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
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_SATZ9_AND_FUCHS_RATE_INPUTS
```

## ROUTE MAP

### 1. Semantic admission of F72.4

The theorem uses the literal selected `ProlatePair`. Its fields `I0` and `I4`
are, by construction, the exact whole-line integrals of `h0` and `h4`; the
stronger stored frequency-zero identities are

\[
 I_{0,k}=\chi_{0,k}f_{0,k}(0),
 \qquad
 I_{4,k}=\chi_{2,k}f_{4,k}(0).
\]

The precommitted center anchors satisfy

\[
 a_{0,k}f_{0,k}(0)=1,
 \qquad
 a_{4,k}f_{4,k}(0)=3.
\]

Therefore the proof derives, exactly,

\[
 a_{0,k}I_{0,k}=\chi_{0,k},
 \qquad
 a_{4,k}I_{4,k}=3\chi_{2,k}.
\]

No integral is estimated through a pointwise majorant. In particular, the
proof does not multiply an `O(lambda^(-2))` sup-error by a window of length
`2*lambda`; the otherwise fatal loss to `O(lambda^(-1))` is absent.
`[COFINAL_FAMILY][LEAN]` **[C10]**

The common output constant is fixed before any values are inspected:

\[
 C_I=3C_\chi.
\]

The mode-zero estimate is enlarged from `C_chi` to `3*C_chi`, and the mode-four
identity contributes the exact factor three. This is a source-side algebraic
choice, not a fitted constant. `[ABSTRACT][LEAN]` **[C09]**

The private plant is a valid falsifier. Center anchoring alone is compatible
with transform scalar `-1`, in which case the two anchored integrals are `-1`
and `-3`, at distances `2` and `6` from the targets. Thus the chi-defect input
is load-bearing.

### 2. Scope boundary

F72.4 is a kernel theorem conditional on the explicit project chi-defect rate.
It does not prove Fuchs Theorem 1, construct the Fuchs eigenvalues, or derive
the chi rate. Those inputs remain upstream in F72.3B. It also proves no
pointwise mode rate and no zero-mass packet rate.

Accordingly:

```text
F72.4 exact algebra:
  SEMANTICALLY_ADMITTED.

Fuchs paper suppliers:
  STILL EXPLICIT INPUTS.

F72.5 / F72.6 / L73.2:
  NOT CLAIMED BY F72.4.
```

### 3. Exact F72.5 source scale

Let

\[
 P_k=\operatorname{selectedFerrersPreAnchorPair}(k),
 \qquad
 D_k=P_k.\operatorname{normalizingDenominator},
\]

and let `a0(k)`, `a4(k)` denote the two center-anchor scalars. Define

\[
\boxed{
 s_k=-\frac{a_{0,k}a_{4,k}}{16}D_k.
}
\]

The sign is load-bearing. Since

\[
 q_k=\frac{I_{4,k}f_{0,k}-I_{0,k}f_{4,k}}{D_k},
\]

exact cancellation gives

\[
\boxed{
 s_kq_k
 =\frac1{16}(a_{0,k}I_{0,k})(a_{4,k}f_{4,k})
  -\frac1{16}(a_{4,k}I_{4,k})(a_{0,k}f_{0,k}).
}
\]

At the limiting values this becomes

\[
 \frac1{16}D_4(\sqrt{4\pi}x)
 -\frac3{16}D_0(\sqrt{4\pi}x)
 =\operatorname{explicitCCMLimitH}(x).
\]

A positive sign would produce the negative target. The private plant must
instantiate an ideal scalar example and distinguish the two signs before the
main proof is accepted. `[ABSTRACT][LEAN]` **[C09] [C10]**

The scale is nonzero because both center anchors are nonzero and
`P_k.I0,P_k.I4` are strictly positive, hence

\[
D_k=\sqrt{I_{0,k}^2+I_{4,k}^2}>0.
\]

No asymptotic input is needed for this fact.

## EXACT LEAN TARGET

Create the public definition

```lean
noncomputable def selectedFerrersLemma72Scale (k : ℕ) : ℂ :=
  -((centerAnchorScalarZero k * centerAnchorScalarFour k) / (16 : ℂ)) *
    (((selectedFerrersPreAnchorPair k).normalizingDenominator : ℝ) : ℂ)
```

Harmless coercion-normal-form changes are allowed; the mathematical formula and
negative sign are fixed.

Prove:

```lean
theorem selectedFerrersLemma72Scale_ne (k : ℕ) :
    selectedFerrersLemma72Scale k ≠ 0
```

and the exact assembly theorem:

```lean
theorem selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖selectedFerrersLemma72Scale k *
              prolateCombination (selectedFerrersPreAnchorPair k) x -
            explicitCCMLimitH x‖ ≤
              C / (selectedFerrersPaperLambda k) ^ 2
```

### 4. Proof route

1. Run the catalog preflight before editing:

```text
./ask.sh "selectedFerrersLemma72Scale zero mass cylinder packet rate"
```

2. Prove `selectedFerrersLemma72Scale_ne` from:

```text
centerAnchorScalarZero_ne;
centerAnchorScalarFour_ne;
(selectedFerrersPreAnchorPair_spec k).I0-positive field;
(selectedFerrersPreAnchorPair_spec k).I4-positive field;
ProlatePair.normalizingDenominator_eq.
```

3. Prove a private exact identity by unfolding only the new scale and
`prolateCombination` and cancelling the nonzero denominator:

\[
 s_kq_k
 =\frac1{16}(a_0I_0)(a_4f_4)
  -\frac1{16}(a_4I_4)(a_0f_0).
\]

4. Invoke

```lean
selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
```

on `hχ`, obtaining `CI >= 0` and the two eventual anchored-integral rates.

5. Intersect that event with `hmode`.

6. Reprove privately, from the exact polynomial-Gaussian formulas, the two
crude global bounds

\[
 |D_0(\sqrt{4\pi}x)|\le1,
 \qquad
 |D_4(\sqrt{4\pi}x)|\le91.
\]

The analogous helpers in F72.1C are private and cannot be referenced across
files. This is source duplication only, not a new analytic premise.

7. Use

\[
 \|a_0I_0\|\le1+CI,
 \qquad
 \|a_4I_4\|\le3+CI,
\]

which follows from the integral rates and
`selectedFerrersPaperLambda_sq(k)=k+2>=1`.

8. Subtract the exact cylinder decomposition and apply the triangle inequality.
One valid explicit output constant is

\[
\boxed{
 C=\frac{(1+CI)C_4+(3+CI)C_0+92CI}{16}.
}

No sharpness is required, but the chosen constant must be fixed algebraically
and proved nonnegative.

## REQUIRED PRIVATE PLANT

Use an exact scalar instance that distinguishes the source-scale sign. For
example, with ideal coefficients `I4=3`, `I0=1`, ideal mode values `d0=0`,
`d4=16`, and denominator `1`, the positive scale gives `-1` while the required
negative scale gives `+1`:

```lean
private theorem zeroMassCylinderPacket_wrong_scale_sign_plant :
    ((1 : ℂ) / 16) * ((3 : ℂ) * 0 - 1 * 16) = -1 ∧
      (-((1 : ℂ) / 16)) * ((3 : ℂ) * 0 - 1 * 16) = 1 := by
  norm_num
```

Equivalent exact arithmetic is allowed, but the plant must fail the wrong sign
and pass the mandated sign.

## FORBIDDEN

```text
positive source-scale sign;
defining the scale from the desired rate or limit;
inserting the later factor 4 in F72.5;
changing prolateCombination orientation or denominator;
replacing literal I0/I4 by neighboring integrals;
integrating the mode sup-error over the expanding window;
adding target bounds as theorem hypotheses;
adding denominator or source-scale nonvanishing as hypotheses;
selecting a different ProlatePair;
identifying project chi2 with paper degree 2;
editing F72.1C, F72.4, center-anchor or exact-cylinder files;
bundling F72.6, L73.3 or the port inhabitant;
paper axiom;
sorry;
admit;
typed hole;
theorem weakening.
```

## VALIDATION

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersZeroMassCylinderPacket

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
```

Expected profiles for both public theorems:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY_LEAN

FAILURE:
  F72_5_SOURCE_SCALE_SIGN_DENOMINATOR_OR_RATE_ALGEBRA_GAP
```

F72.6 is not authorized until this source passes the kernel and receives a
separate semantic admission.

## FINAL PROPOSAL

Admit F72.4 and execute exactly one finite-algebra floor, F72.5. The source
scale is not an existential fit: it is the unique sign/orientation dictated by
the literal `prolateCombination`, the two precommitted center anchors, and the
exact cylinder decomposition. The two analytic rate suppliers remain explicit
upstream inputs; F72.5 only preserves their `lambda^(-2)` budget through the
zero-mass algebra.

## STRONGEST ATTACK

The strongest reviewer objection is that a vanishing or fitted source scale can
make any convergence statement vacuous. That objection is blocked here by an
explicit formula and a separate all-`k` nonvanishing theorem. The negative sign
is independently guarded by the plant. **[C09] [C10]**

A second objection is that pointwise `lambda^(-2)` mode control cannot be
integrated over a window of length `2*lambda` without losing a power. F72.5 does
not do that. F72.4 supplies the integral coefficients through the exact
frequency-zero identities, and F72.5 uses only finite-dimensional algebra.

## META CLOSEOUT

**What became smaller?**

The two analytic cores now feed exact project mode rates and exact anchored
integral rates. The remaining Lemma-7.2 wall is reduced to one explicit source
scale and one two-mode rate assembly.

**What was killed?**

- direct integration of the sup-error;
- positive source-scale orientation;
- fitted or conclusion-defined source scale;
- premature factor four.

**What must not be tried again?**

Do not reopen F72.4, do not rederive the chi rate inside F72.5, and do not alter
the selected pair or anchors.

**Current smallest named gap:**

```text
F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
```

**Next cheapest decisive test:**

Compile the exact scale-cancellation identity and the resulting packet rate.

**Fate of prior registered predictions:**

```text
P_F72_4_1: CONFIRMED
P_F72_4_2: CONFIRMED
P_F72_4_3: CONFIRMED
```

**Memory entry:**

```yaml
iteration:
  target: F72.4 semantic admission and F72.5 slicing
  status: PROGRESS
  failed_strategy: integrating_lambda_minus_two_sup_error_over_expanding_window
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
  invariant_learned: exact frequency-zero identities preserve the coefficient rate without window-length loss
  forbidden_future_move: fit the source scale or insert the factor four before F72.6
  next_decisive_test: exact_negative_scale_denominator_cancellation_and_packet_rate_compile
  progress_class: PROOF_PROGRESS
  route_score: 5
```
