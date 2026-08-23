# STATUS: PROVED — F72.6 SEMANTICALLY ADMITTED AS AN EXACT CONDITIONAL SCALAR PORT; L73.3 E-STAR WINDOW MAIN ERROR AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_6_AND_AUTHORIZE_L73_3_ESTAR_WINDOW_MAIN_ERROR
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 6e8767e6d453bed5672f19a012a028a1b4303390
  SOURCE_COMMIT: ffb615b3fc8ed73cde90a9487245de11ce918a14
  ACTUAL_SOURCE_COMMIT_PARENT: f9623d8b193d32a6c4311d279411f0bb06452401
  CLAIMED_SOURCE_RECORD_BASE_HEAD: f9623d8b193d32a6c4311d279411f0bb06452401
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  POST_SOURCE_HEAD_COMMIT: 6e8767e6d453bed5672f19a012a028a1b4303390
  POST_SOURCE_HEAD_CHANGE: DOCS_ONLY_PROGRESS_LOG
  LEAN_DRIFT_AFTER_SOURCE: false
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
  LEAN_GIT_BLOB: ccc86efd6bb52fb2dace277262e08dbc953600e3
  LEAN_SHA256_REPORTED: 53ce931302f59c8f3ae0ba338f1b7696df29748d1ea2d96a2833d81c08fab18c
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: e941d1a9527b72436479977abf80095284a97ea1

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7848_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersLemma73SourceScale_ne:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_SCALAR_PORT
  PUBLIC_DEFINITION: Q3.RouteB.D0Pstar.selectedFerrersLemma73SourceScale
  PUBLIC_THEOREMS:
    - Q3.RouteB.D0Pstar.selectedFerrersLemma73SourceScale_ne
    - Q3.RouteB.D0Pstar.selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
  DIRECTION: INTERNAL_LEMMA72_PACKET_RATE_TO_FACTOR_FOUR_LEMMA73_PORT_PACKET_RATE
  SOURCE_OBJECT: selectedFerrersPreAnchorPair
  PACKET_OBJECT: prolateCombination_selectedFerrersPreAnchorPair
  INTERNAL_SCALE: selectedFerrersLemma72Scale
  PORT_SCALE: selectedFerrersLemma73SourceScale
  PORT_SCALE_FORMULA: four_mul_selectedFerrersLemma72Scale
  INTERNAL_TARGET: explicitCCMLimitH
  PORT_TARGET: four_mul_explicitCCMLimitH
  INTERNAL_RATE_CONSTANT: C
  PORT_RATE_CONSTANT: four_mul_C
  ONE_LINEAR_PORT_RESCALE_APPLIED_TO_SOURCE_AND_TARGET: true
  FACTOR_FOUR_SOURCE: REQ_E_QUARTER_CENTERED_XI_NORMALIZATION_AUDIT
  FACTOR_FOUR_MISSING_REJECTED_BY_PLANT: true
  FACTOR_FOUR_DUPLICATED_REJECTED_BY_PLANT: true
  PORT_SCALE_NONZERO_DERIVED_FROM_INTERNAL_SCALE: true
  SAME_SELECTED_PAIR_PRESERVED: true
  SAME_MODE_AND_CHI_RATE_WITNESSES_PRESERVED: true
  NEW_ANALYTIC_INPUT: none
  FITTED_SCALAR: false
  C04_UNIT_AND_TARGET_AUDIT: PASS
  C09_FIXED_NORMALIZATION_AUDIT: PASS
  C10_EXACT_SOURCE_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_EXACT_FACTOR_FOUR_SCALE: true
  PROVES_FACTOR_FOUR_SCALE_NONVANISHING: true
  PROVES_FACTOR_FOUR_PACKET_RATE_CONDITIONAL_ON_HMODE_AND_HCHI: true
  PROVES_QUARTER_MELLIN_IDENTITY_IN_LEAN: false
  PROVES_MEIXNER_SCHAEFKE_SATZ9: false
  PROVES_FUCHS_THEOREM_1: false
  PROVES_EXPLICIT_MODE_RATES: false
  PROVES_PROJECT_CHI_RATE: false
  PROVES_FULL_ESTAR_ERROR: false
  PROVES_TARGET_TAIL: false
  PROVES_L73_3_OR_L73_4_OR_L73_5: false
  PROVES_CCM_LEMMA73_PORT_INHABITANT: false
  PROVES_RH: false
  UPSTREAM_PAPER_RATE_INPUTS_REMAIN_EXPLICIT: true
  QUARTER_MELLIN_CROSSWALK_REMAINS_SEPARATE_L73_5_FLOOR: true

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
  P_F72_6_1:
    claim: factor_four_port_rate_is_pure_scalar_algebra_over_F72_5_with_no_new_analysis
    fate: CONFIRMED
  P_F72_6_2:
    claim: port_scale_nonvanishing_closes_from_four_ne_zero_and_internal_scale_nonvanishing
    fate: CONFIRMED
  P_F72_6_3:
    claim: plant_distinguishes_missing_once_and_duplicated_factor_four_normalizations
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: POINTWISE_SCALAR_MULTIPLICATION_OR_COMPLEX_NORM_FOUR_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: FIRST_GATE_PASS_NO_REPAIR_ROUND
  RETROACTIVE_REPAIR: false

EARLIER_L73_PREDICTION_FATE:
  P_L73_1_PAIR_SPEC_NEEDED:
    fate: CONFIRMED
    evidence: selectedFerrersPreAnchorData_pair_spec_was_added_and_is_load_bearing
  P_L73_2_FIXED_NONZERO_REAL_SCALE:
    fate: REFUTED_AS_STATED
    evidence: source_scale_is_explicit_source_derived_but_k_dependent
  P_L73_3_RATE_DOMINATES_FORMAL_COST:
    fate: CONFIRMED_SO_FAR
    evidence: F72_rate_and_object_chain_was_load_bearing; L73_3_is_now_finite_sum_assembly
  P_L73_4_EXPLICIT_TARGET_TAIL_REQUIRED:
    fate: PENDING
  RETROACTIVE_REPAIR: false

L73_3_ADJUDICATION:
  STATUS: LEAN_READY_FINITE_SUM_ASSEMBLY
  CHARACTER: EXACT_DYNAMIC_MAIN_INDEX_SUM_PLUS_SOURCE_RATE_COUNTING
  NEW_EXTERNAL_INPUT: none
  SOURCE_SCALE: selectedFerrersLemma73SourceScale
  SOURCE_PACKET: prolateCombination_selectedFerrersPreAnchorPair
  TARGET_PACKET: four_mul_explicitCCMLimitH
  SOURCE_WINDOW: sourceWindow_selectedFerrersPaperLambda
  MAIN_INDEX_RULE: positive_integer_n_with_n_mul_u_le_lambda
  MAIN_INDEX_IMPLEMENTATION: Finset.range_floor_lambda_div_u_with_index_n_plus_one
  INPUT_RATE: F72_6_factor_four_packet_rate
  EXACT_POINTWISE_BOUND: C_div_lambda_mul_sqrt_u
  FULL_TARGET_ESTAR_TAIL_INCLUDED: false
  TARGET_TAIL_REMAINS_L73_4: true
  MELLIN_INTEGRATION_PERFORMED_HERE: false
  CLOSES:
    - SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR
  OPENS: []

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
    - Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
  PUBLIC_DEFINITIONS:
    - selectedFerrersEStarMainCount
    - selectedFerrersEStarWindowMainError
  PUBLIC_THEOREM: selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
  REQUIRED_PRIVATE_PLANT: eStarMainSum_cardinalityFactor_plant
  CLOSES:
    - SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL

CLOSES:
  - F72_6_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE
  - F72_6_FACTOR_FOUR_PORT_PACKET_RATE
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_DYNAMIC_MAIN_COUNT_AND_C_DIV_LAMBDA_SQRT_U_BOUND

REGISTERED_PREDICTIONS:
  P_L73_3A_1:
    claim: L73_3_closes_by_finite_sum_triangle_inequality_and_floor_count_without_new_analysis
    probability: 0.95
  P_L73_3A_2:
    claim: the_sharp_bound_C_div_lambda_mul_sqrt_u_is_available_from_the_F72_6_lambda_inverse_squared_rate
    probability: 0.93
  P_L73_3A_3:
    claim: no_target_tail_or_Mellin_integration_is_needed_in_this_floor
    probability: 0.99
  LIKELIEST_FAILURE: NAT_FLOOR_CAST_OR_FINSET_RANGE_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
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

### 1. Semantic admission of F72.6

The public theorem does not change the selected source object. It calls F72.5 with the same `hmode` and `hchi` inputs and multiplies the resulting exact packet error by four. The source scale and the target change together:

\[
\operatorname{selectedFerrersLemma73SourceScale}(k)
=4\operatorname{selectedFerrersLemma72Scale}(k),
\]

\[
4s_kq_k-4h=4(s_kq_k-h).
\]

The output constant is fixed as `4*C` before any point or error is inspected. This is exact scalar algebra on the literal selected packet, not a new source family and not a fitted normalization. `[COFINAL_FAMILY][LEAN]` **[C09][C10]**

The factor four has a fixed downstream meaning. The independent normalization audit identifies the Mellin transform of the literal packet with one quarter of production `centeredXi`. Therefore the one-time port rescaling targets the production normalization. The private plant rejects omission and duplication. `[ABSTRACT][PAPER]` **[C04]**

This semantic value must not be overstated. The new Lean file does not prove the quarter-Mellin identity and does not import it as a theorem. F72.6 is therefore admitted as an exact conditional scalar port. L73.5 remains the separate theorem-level Mellin/`centeredXi` crosswalk.

### 2. Exact scope boundary

F72.6 proves an implication conditional on the explicit mode and chi rates. Those rates ultimately depend on explicit Satz-9 and Fuchs paper inputs. The theorem does not create those inputs from the names of source structures, and it does not prove any full `E_star`, Mellin, or locally-uniform convergence statement.

Accordingly:

```text
F72.6 exact port algebra:
  SEMANTICALLY_ADMITTED.

F72.1 / F72.3 external rate data:
  STILL EXPLICIT INPUTS.

L73.3 target main-sum error:
  NEXT.

L73.4 target tail and L73.5 quarter-Mellin identity:
  OPEN AND SEPARATE.
```

### 3. L73.3 computing object

For the selected window

\[
\lambda_k=\operatorname{selectedFerrersPaperLambda}(k)
\]

and `u` in `[lambda_k⁻¹, lambda_k]`, define the exact number of positive main indices

\[
M_k(u)=\left\lfloor\frac{\lambda_k}{u}\right\rfloor.
\]

The positive index represented by `n : Fin M_k(u)` is `n+1`. Define

\[
\mathcal E_k^{\rm main}(u)
=
\sqrt u\sum_{n=0}^{M_k(u)-1}
\left[
 a_kq_k((n+1)u)-4h((n+1)u)
\right],
\]

where

```text
a_k = selectedFerrersLemma73SourceScale k;
q_k = prolateCombination (selectedFerrersPreAnchorPair k);
h   = explicitCCMLimitH.
```

For each included index, `(n+1)u <= lambda_k`; hence the F72.6 pointwise rate applies. Since

\[
M_k(u)\le\frac{\lambda_k}{u},
\]

we obtain

\[
\boxed{
\|\mathcal E_k^{\rm main}(u)\|
\le
\frac{C}{\lambda_k\sqrt u}.
}
\]

This is exactly the CCM Lemma-7.3 main-sum estimate:

\[
\sqrt u\,\delta_k\frac{\lambda_k}{u},
\qquad
\delta_k\le C\lambda_k^{-2}.
\]

No target term with `n*u > lambda_k` belongs here. Those terms form the explicit target tail and remain L73.4.

## FINAL PROPOSAL

Create exactly one Lean file with the following public definitions.

```lean
noncomputable def selectedFerrersEStarMainCount (k : ℕ) (u : ℝ) : ℕ :=
  Nat.floor (selectedFerrersPaperLambda k / u)
```

```lean
noncomputable def selectedFerrersEStarWindowMainError
    (k : ℕ) (u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) *
    ∑ n in Finset.range (selectedFerrersEStarMainCount k u),
      (selectedFerrersLemma73SourceScale k *
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((n + 1 : ℕ) : ℝ) * u)
        - (4 : ℂ) *
          explicitCCMLimitH (((n + 1 : ℕ) : ℝ) * u))
```

Prove the exact source-facing theorem:

```lean
theorem selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
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
        ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
          ‖selectedFerrersEStarWindowMainError k u‖ ≤
            C / (selectedFerrersPaperLambda k * Real.sqrt u)
```

The theorem must call `selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates`; it may not accept a free `E_star` main-error premise.

### Required private plant

```lean
private theorem eStarMainSum_cardinalityFactor_plant :
    ‖∑ _n in Finset.range 4, (1 : ℂ)‖ = 4 ∧
      ¬ ‖∑ _n in Finset.range 4, (1 : ℂ)‖ ≤ 1 := by
  norm_num
```

The plant records that the number of active dilation terms is load-bearing. A one-term source bound cannot be reused as a bound for the entire finite comb without paying the count.

### Proof route

1. Run the required `ask.sh` preflight for the exact target and helper names.
2. Call F72.6 and obtain `C >= 0` plus the eventual pointwise packet rate.
3. Fix `k` in that eventual event and `u` in the exact source window.
4. Derive `0 < lambda_k`, `0 < u`, and
   `Nat.floor (lambda_k/u) <= lambda_k/u` after real coercion.
5. For every `n < Nat.floor (lambda_k/u)`, prove
   `((n+1):R)*u` lies in `Icc (-lambda_k) lambda_k`.
6. Apply the F72.6 pointwise rate term by term.
7. Use `norm_sum_le`, `Finset.card_range`, the floor bound and the exact identity
   `u = (sqrt u)^2` to derive
   `C / (lambda_k * sqrt u)`.
8. Do not unfold or estimate the infinite target `E_star` tail.

## STRONGEST ATTACK

The strongest false shortcut is to sum the F72.6 error over all `n <= k+2`, because the source packet is compactly supported. That ignores the moving condition `n*u <= lambda_k`. Near the upper edge of the multiplicative window it overcounts by a factor of order `lambda_k`, and the resulting bound no longer has the sharp `u^(-1/2)` behavior needed by the Mellin estimate.

The repaired theorem uses the dynamic count `floor(lambda_k/u)`.

A second false shortcut is to claim that this controls the full difference

\[
E_\star(a_kq_k)-E_\star(4h).
\]

It does not. The source term vanishes beyond `lambda_k`, while the Gaussian target does not. The omitted target terms are exactly the L73.4 tail. **[C04][C10]**

## CODEX DIRECTIVE

```text
TASK: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the commit containing this verdict;
  run git rev-parse HEAD immediately before editing.

CREATE_EXACTLY_ONE_LEAN_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersEStarWindowMainError.lean

CREATE_SOURCE_RECORD_SAME_COMMIT:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_2026-08-23.md

DIRECT_IMPORTS:
  import Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
  import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

PUBLIC_SURFACE:
  selectedFerrersEStarMainCount
  selectedFerrersEStarWindowMainError
  selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates

REQUIRED_PRIVATE_PLANT:
  eStarMainSum_cardinalityFactor_plant

CLOSES:
  SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR

OPENS: []

FORBIDDEN:
  - free E_star-error hypothesis
  - full sourcePositiveIndexFinset count in place of floor(lambda/u)
  - claim on the full target E_star tail
  - Mellin integration in this floor
  - target-tail hypothesis
  - changing the selected pair or precommitted schedule
  - dropping the factor four
  - editing F72.1C, F72.4, F72.5 or F72.6
  - bundling L73.4, L73.5, L73.6 or the final port inhabitant
  - paper axiom
  - sorry
  - admit
  - typed hole
  - theorem weakening

GATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersEStarWindowMainError
  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean

EXPECTED_AXIOM_PROFILE:
  selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates:
    [propext, Classical.choice, Quot.sound]

SUCCESS:
  L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_LEAN

FAILURE:
  L73_3_NAT_FLOOR_CARDINALITY_OR_FINITE_SUM_BOUND_GAP

NEXT_AFTER_SEMANTIC_ADMISSION_ONLY:
  L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
```

## META CLOSEOUT

**What became smaller?**

The entire F72 object/rate chain now terminates in one exact factor-four packet rate. The next unknown is no longer the source normalization or zero-mass coefficient stability; it is the elementary dynamic finite-sum lift into the starred comb.

**What was killed?**

- a missing factor four;
- a duplicated factor four;
- a fitted port scalar;
- any claim that F72.6 already proves the quarter-Mellin theorem;
- any claim that the full target `E_star` error is controlled without an explicit target tail.

**What must not be tried again?**

Do not replace the dynamic count `floor(lambda/u)` with the full source carrier. Do not merge L73.3 and L73.4 by silently dropping the Gaussian target tail.

**Current smallest named gap:**

```text
L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
```

**Next cheapest decisive test:**

Compile the exact `Nat.floor` count and the sharp

\[
C/(\lambda\sqrt u)
\]

bound from F72.6.

**Fate of prior registered predictions:**

```text
P_F72_6_1: CONFIRMED
P_F72_6_2: CONFIRMED
P_F72_6_3: CONFIRMED
predicted failure: NOT OBSERVED
retroactive repair: false
```

**Memory entry:**

```yaml
iteration:
  target: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
  invariant_learned: factor_four_is_one_fixed_port_rescale_and_target_tail_is_a_separate_floor
  forbidden_future_move: replace_dynamic_main_count_by_full_carrier_or_hide_target_tail
  next_decisive_test: compile_floor_count_and_C_div_lambda_sqrt_u_bound
  progress_class: PROOF_PROGRESS
  route_score: 5
```

**Route boundary:** `CHALLENGER / NOT_RH`; **Bus 010:** `VOID`; **Goal 055:** `HOLD`; no route promotion and no RH claim.
