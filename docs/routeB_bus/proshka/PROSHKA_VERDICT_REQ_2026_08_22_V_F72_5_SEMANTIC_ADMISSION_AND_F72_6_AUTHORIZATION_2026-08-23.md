# STATUS: PROVED — F72.5 SEMANTICALLY ADMITTED; F72.6 FACTOR-FOUR PORT RATE AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_5_AND_AUTHORIZE_F72_6_FACTOR_FOUR_PORT_RATE
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 61343c78aba2769de5096d4809c197f43b232e3d
  SOURCE_COMMIT: 61343c78aba2769de5096d4809c197f43b232e3d
  ACTUAL_SOURCE_COMMIT_PARENT: b7e56afd94186386f281124a514640ec29e6c611
  CLAIMED_SOURCE_RECORD_BASE_HEAD: b7e56afd94186386f281124a514640ec29e6c611
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
  LEAN_GIT_BLOB: 1c34fd65feac5f1752df56b0cdbf671571f3ab20
  LEAN_SHA256_REPORTED: a0b25b03d9cf8f5cb685c127a559bb0d1c1df8f6540a6c282f4ad14febf05d45
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 2c170c319ef40577f5c9f0ada2526e917fbdfb42

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7847_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersLemma72Scale_ne:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_FINITE_ASSEMBLY
  PUBLIC_DEFINITION: Q3.RouteB.D0Pstar.selectedFerrersLemma72Scale
  PUBLIC_THEOREMS:
    - Q3.RouteB.D0Pstar.selectedFerrersLemma72Scale_ne
    - Q3.RouteB.D0Pstar.selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates
  DIRECTION: EXPLICIT_SELECTED_MODE_AND_CHI_RATES_TO_INTERNAL_LEMMA72_ZERO_MASS_PACKET_RATE
  SOURCE_OBJECT: selectedFerrersPreAnchorPair
  PACKET_OBJECT: prolateCombination_selectedFerrersPreAnchorPair
  TARGET_OBJECT: explicitCCMLimitH
  INTERNAL_SOURCE_SCALE_FORMULA: negative_centerAnchorZero_mul_centerAnchorFour_div_16_mul_normalizingDenominator
  SCALE_CHOSEN_FROM_DESIRED_LIMIT: false
  SCALE_SIGN_PRECOMMITTED: true
  SCALE_SIGN_PLANT_PRESENT: true
  SCALE_NONZERO_DERIVED: true
  DENOMINATOR_IS_LITERAL_PROLATEPAIR_DENOMINATOR: true
  DENOMINATOR_CANCELLED_EXACTLY: true
  I0_I4_ARE_LITERAL_SELECTED_PAIR_FIELDS: true
  EXACT_SCALED_PACKET_IDENTITY: >-
    s_k*q_k = (1/16)*(a0_k*I0_k)*(a4_k*h4_k)
              - (1/16)*(a4_k*I4_k)*(a0_k*h0_k)
  EXACT_TARGET_IDENTITY: explicitCCMLimitH_eq_cylinder_combination
  MODE_RATES_CONSUMED_AT_SAME_SELECTED_PAIR: true
  INTEGRAL_RATES_CONSUMED_AT_SAME_SELECTED_PAIR: true
  POINTWISE_RATE_INTEGRATED_OVER_EXPANDING_WINDOW: false
  TARGET_BOUNDS:
    D0: 1
    D4: 91
  OUTPUT_CONSTANT: ((1_plus_CI)_mul_C4_plus_(3_plus_CI)_mul_C0_plus_92_mul_CI)_div_16
  OUTPUT_RATE_UNIT: selectedFerrersPaperLambda_inverse_squared
  FACTOR_FOUR_INSERTED_IN_F72_5: false
  FITTED_CONSTANT: false
  C04_OBJECT_UNIT_AND_DEGREE_AUDIT: PASS
  C09_PRECOMMITTED_SCALE_SIGN_AND_CONSTANT_AUDIT: PASS
  C10_EXACT_FUNCTIONAL_AND_SOURCE_OBJECT_AUDIT: PASS

SCOPE_GUARD:
  PROVES_INTERNAL_LEMMA72_SOURCE_SCALE: true
  PROVES_INTERNAL_SCALE_NONVANISHING: true
  PROVES_ZERO_MASS_PACKET_RATE_CONDITIONAL_ON_HMODE_AND_HCHI: true
  PROVES_MEIXNER_SCHAEFKE_SATZ9: false
  PROVES_FUCHS_THEOREM_1: false
  PROVES_THE_EXPLICIT_MODE_RATES: false
  PROVES_THE_PROJECT_CHI_RATE: false
  PROVES_FACTOR_FOUR_PORT_NORMALIZATION: false
  PROVES_L73_3_OR_L73_5_OR_PORT_INHABITANT: false
  PROVES_RH: false
  RAW_PAPER_INPUTS_REMAIN_EXPLICIT_UPSTREAM: true

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
  P_F72_5_1:
    claim: negative_source_scale_cancels_literal_denominator_and_gives_D4_div_16_minus_3D0_div_16_orientation
    fate: CONFIRMED
  P_F72_5_2:
    claim: scale_nonvanishing_closes_from_positive_integrals_and_nonzero_center_anchors_without_new_analysis
    fate: CONFIRMED
  P_F72_5_3:
    claim: mode_rates_plus_integral_rates_plus_crude_D0_D4_bounds_preserve_lambda_inverse_squared_rate
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: COMPLEX_DIVISION_CANCELLATION_OR_NORM_PRODUCT_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: FIRST_GATE_PASS_NO_REPAIR_ROUND
  RETROACTIVE_REPAIR: false

F72_6_ADJUDICATION:
  STATUS: LEAN_READY_EXACT_SCALAR_PORT
  CHARACTER: FIXED_FACTOR_FOUR_SOURCE_NORMALIZATION_AND_RATE_SCALING
  INTERNAL_SCALE: selectedFerrersLemma72Scale
  PORT_SCALE: selectedFerrersLemma73SourceScale
  PORT_SCALE_FORMULA: four_mul_selectedFerrersLemma72Scale
  INTERNAL_TARGET: explicitCCMLimitH
  PORT_TARGET: four_mul_explicitCCMLimitH
  INTERNAL_RATE_CONSTANT: C
  PORT_RATE_CONSTANT: four_mul_C
  FACTOR_FOUR_SOURCE: REQ_E_QUARTER_CENTERED_XI_NORMALIZATION_AUDIT
  FACTOR_FOUR_OCCURS_EXACTLY_ONCE: true
  NEW_EXTERNAL_INPUT: none
  L73_2_ALGEBRAIC_ASSEMBLY_CLOSED_AFTER_F72_6: true
  L73_2_UNCONDITIONAL_PAPER_SUPPLY_CLOSED: false

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersZeroMassCylinderPacket
  PUBLIC_DEFINITION: selectedFerrersLemma73SourceScale
  PUBLIC_THEOREMS:
    - selectedFerrersLemma73SourceScale_ne
    - selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
  REQUIRED_PRIVATE_PLANT: factorFour_occurs_exactly_once_plant
  CLOSES:
    - F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE
    - F72_6_FACTOR_FOUR_PORT_PACKET_RATE
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR

CLOSES:
  - F72_5_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_5_SELECTED_FERRERS_INTERNAL_LEMMA72_SCALE
  - F72_5_ZERO_MASS_CYLINDER_PACKET_RATE
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_EXACT_ONE_TIME_FACTOR_FOUR_SCALE_AND_RATE_TRANSFER

REGISTERED_PREDICTIONS:
  P_F72_6_1:
    claim: factor_four_port_rate_is_pure_scalar_algebra_over_F72_5_with_no_new_analysis
    probability: 0.99
  P_F72_6_2:
    claim: port_scale_nonvanishing_closes_from_four_ne_zero_and_internal_scale_nonvanishing
    probability: 0.999
  P_F72_6_3:
    claim: the_required_plant_distinguishes_missing_once_and_duplicated_factor_four_normalizations
    probability: 0.99
  LIKELIEST_FAILURE: POINTWISE_SCALAR_MULTIPLICATION_OR_COMPLEX_NORM_FOUR_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
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

F72.5 uses the literal selected `ProlatePair`, its literal integral fields, its literal denominator and the exact production `prolateCombination`. The source scale

\[
s_k=-\frac{a_{0,k}a_{4,k}}{16}D_k
\]

is fixed before the rate hypotheses are inspected. Exact cancellation gives

\[
s_kq_k
=\frac1{16}(a_{0,k}I_{0,k})(a_{4,k}f_{4,k})
-\frac1{16}(a_{4,k}I_{4,k})(a_{0,k}f_{0,k}).
\]

At the limiting values this is exactly

\[
\frac1{16}D_4(\sqrt{4\pi}x)
-\frac3{16}D_0(\sqrt{4\pi}x)
=\operatorname{explicitCCMLimitH}(x).
\]

This is an exact source-object identity, not a surrogate comparison. `[COFINAL_FAMILY][LEAN]` **[C09][C10]**

The nonvanishing proof is source-derived. Both anchors are nonzero; `I0>0` already makes

\[
D_k=\sqrt{I_{0,k}^2+I_{4,k}^2}>0.
\]

No asymptotic or numerical assumption is used. `[ABSTRACT][LEAN]`

The rate proof preserves the `lambda^(-2)` unit. It never integrates a pointwise error over an interval of length `2*lambda`. The four error terms are instead bounded by the two mode rates, the two anchored-integral rates and the global cylinder bounds `1` and `91`, giving the exact a-priori constant

\[
\frac{(1+C_I)C_4+(3+C_I)C_0+92C_I}{16}.
\]

`[COFINAL_FAMILY][LEAN]`

The theorem remains conditional on explicit upstream rate contracts. It does not prove Satz 9, Fuchs Theorem 1 or the existence of paper data realizing those contracts. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

F72.6 must introduce the factor four exactly once and only at the port boundary:

\[
\boxed{
\operatorname{selectedFerrersLemma73SourceScale}(k)
=4\operatorname{selectedFerrersLemma72Scale}(k).
}
\]

The target changes simultaneously from `explicitCCMLimitH` to `4 * explicitCCMLimitH`. This is forced by the independent normalization audit

\[
\mathcal M(E_\star\operatorname{explicitCCMLimitH})(-iz)
=\frac14\operatorname{centeredXi}(z).
\]

The factor is not a fitted convention and must not occur in F72.5, in the literal packet definition, or a second time in the Mellin theorem. `[ABSTRACT][PAPER]` **[C04][C09]**

Create exactly one file and prove the following public surface.

```lean
noncomputable def selectedFerrersLemma73SourceScale (k : ℕ) : ℂ :=
  (4 : ℂ) * selectedFerrersLemma72Scale k
```

```lean
theorem selectedFerrersLemma73SourceScale_ne (k : ℕ) :
    selectedFerrersLemma73SourceScale k ≠ 0
```

```lean
theorem selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
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
          ‖selectedFerrersLemma73SourceScale k *
              prolateCombination (selectedFerrersPreAnchorPair k) x -
            (4 : ℂ) * explicitCCMLimitH x‖ ≤
              C / (selectedFerrersPaperLambda k) ^ 2
```

The proof must call `selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates`, choose the output constant `4*C`, and use the exact pointwise identity

\[
4s_kq_k-4h=4(s_kq_k-h).
\]

No new asymptotic input is permitted. `[COFINAL_FAMILY][LEAN]`

## STRONGEST ATTACK

A reviewer may say that multiplying both the source scale and target by four is vacuous. It would be vacuous if the scalar were chosen merely to restate the same rate. Here it has a fixed downstream consumer: the unscaled literal packet has Mellin transform `one quarter * centeredXi`. Multiplication by four is therefore the unique fixed port normalization that targets the production `centeredXi`. `[ABSTRACT][PAPER]` **[C04]**

The opposite attack is more dangerous: the factor may be inserted twice, once here and once in L73.5. The mandatory plant must distinguish all three cases:

```lean
private theorem factorFour_occurs_exactly_once_plant :
    ((1 : ℂ) / 4 ≠ 1) ∧
      (4 : ℂ) * ((1 : ℂ) / 4) = 1 ∧
      (16 : ℂ) * ((1 : ℂ) / 4) ≠ 1 := by
  norm_num
```

This protects both omission and duplication. The literal packet, `centeredXi` and the quarter-Mellin statement remain unchanged. `[ABSTRACT][LEAN]` **[C09]**

## CODEX DIRECTIVE

```text
TASK: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the full Proshka verdict commit returned by this verdict write;
  run git rev-parse HEAD immediately before editing.

CREATE EXACTLY ONE LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersFactorFourPortRate.lean

CREATE SOURCE RECORD IN THE SAME COMMIT:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_2026-08-23.md

DIRECT IMPORTS — EXACTLY ONE:
  import Q3.Proofs.RouteB.G6N1SelectedFerrersZeroMassCylinderPacket

PUBLIC SURFACE:
  selectedFerrersLemma73SourceScale
  selectedFerrersLemma73SourceScale_ne
  selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates

REQUIRED PRIVATE PLANT:
  factorFour_occurs_exactly_once_plant

PROOF ROUTE:
  1. Run ./ask.sh for the exact scale and factor-four rate names.
  2. Define selectedFerrersLemma73SourceScale = 4 * selectedFerrersLemma72Scale.
  3. Prove nonvanishing from 4 ≠ 0 and selectedFerrersLemma72Scale_ne.
  4. Apply F72.5 to hmode and hχ, obtaining C and the internal rate.
  5. Choose Cport = 4*C before inspecting any values.
  6. Rewrite the pointwise port error as 4 times the internal error.
  7. Use norm multiplication and exact field/ring algebra to obtain
       4*(C/lambda^2) = (4*C)/lambda^2.
  8. Print axioms for both public theorems.

FORBIDDEN:
  - changing explicitCCMLimitH;
  - changing centeredXi;
  - inserting factor four into F72.5;
  - inserting factor sixteen here;
  - adding a factor-four hypothesis;
  - choosing the scalar from observed convergence;
  - importing the quarter-Mellin theorem as a proof substitute;
  - bundling L73.3, L73.5 or the port inhabitant;
  - editing F72.5 or any upstream admitted file;
  - paper axiom, sorry, admit, typed hole or theorem weakening.

GATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate

  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean

EXPECTED AXIOMS FOR BOTH PUBLIC THEOREMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_LEAN

FAILURE:
  F72_6_FACTOR_FOUR_DUPLICATION_OR_COMPLEX_SCALAR_NORMAL_FORM_GAP

NEXT AFTER SEPARATE SEMANTIC ADMISSION ONLY:
  L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
```

## META CLOSEOUT

**What became smaller?**

The last nontrivial finite-dimensional assembly before the port normalization is kernel-green and semantically source-locked. The open algebraic gap is now only multiplication by the fixed scalar four. `[COFINAL_FAMILY][LEAN]`

**What was killed?**

- the positive source-scale orientation;
- denominator-zero concerns;
- rate loss from integrating over the growing window;
- fitted zero-mass normalization;
- insertion of the factor four inside F72.5.

**What must not be tried again?**

Do not rederive the zero-mass combination through window integration. Do not redefine the literal packet. Do not hide the factor four in a convention or duplicate it at L73.5. `[ABSTRACT][LEAN]`

**Current smallest named gap:**

```text
F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
```

**Next cheapest decisive test:**

Compile the exact one-time factor-four definition and pointwise rate scaling with the omission/double-factor plant.

**Fate of prior registered predictions:**

All three F72.5 predictions are confirmed. The predicted complex cancellation/norm failure did not occur; the source passed its first gate. No retroactive repair. `[ABSTRACT][LEAN]`

**Memory entry:**

```yaml
iteration:
  target: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
  invariant_learned: factor four belongs exactly once at the port scale and target, never inside the literal packet or internal Lemma-7.2 assembly
  forbidden_future_move: duplicate the factor four in L73.5 or hide it in a convention
  next_decisive_test: compile exact factor-four scale and rate transfer
  progress_class: PROOF_PROGRESS
  route_score: 5
```
