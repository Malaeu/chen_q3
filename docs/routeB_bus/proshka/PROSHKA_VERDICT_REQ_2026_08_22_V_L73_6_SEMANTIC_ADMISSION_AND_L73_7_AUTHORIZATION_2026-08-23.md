# STATUS: PROVED — L73.6 SEMANTICALLY ADMITTED; L73.7 CLOSED-SUBSTRIP MELLIN CONVERGENCE AUTHORIZED
```yaml
PRIMARY: ADMIT_L73_6_AND_AUTHORIZE_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: e6402afaf0d05717d58e66ff4d018c0a9206817b
  SOURCE_COMMIT: e6402afaf0d05717d58e66ff4d018c0a9206817b
  ACTUAL_SOURCE_COMMIT_PARENT: 04b95c7e3534d7bc176598d6ea1067a27757b0c7
  CLAIMED_SOURCE_RECORD_BASE_HEAD: 04b95c7e3534d7bc176598d6ea1067a27757b0c7
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean
  LEAN_GIT_BLOB: d2d729e5b5360d7e86167ee07f09b7344ba2d27a
  LEAN_SHA256_REPORTED: db836a402448fcd8f9dd632b672d1ee98e68502361f67a26d75dbdaaca445d72
  LEAN_LINES_REPORTED: 520
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: fce132a3c83fe2e4275f8d3862d33e6764b7c45f
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7838_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_FACTOR_FOUR_TARGET_OUTER_MELLIN_TAIL
  PUBLIC_DEFINITION:
    - Q3.RouteB.D0Pstar.selectedFerrersFactorFourExplicitLimitMellinOuterTail
  PUBLIC_THEOREM:
    - Q3.RouteB.D0Pstar.selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn
  EXACT_TARGET_PACKET: explicitCCMLimitH
  EXACT_TARGET_COMB: E_star_of_four_mul_explicitCCMLimitH
  EXACT_MELLIN_COORDINATE: minus_I_mul_z
  OUTER_TAIL: lowerMellinTail_plus_upperMellinTail
  SCHEDULE: selectedFerrersPaperLambda_k_equals_sqrt_k_plus_2
  FACTOR_FOUR_OCCURS_EXACTLY_ONCE: true
  UNSCALED_SURROGATE_USED: false
  COORDINATE_IDENTITY: real_part_of_minus_I_mul_z_equals_imaginary_part_of_z
  EXPONENT_GUARD:
    upper: z_im_minus_nine_halves_lt_minus_four
    lower: two_lt_z_im_plus_five_halves
  POINTWISE_DECAY:
    explicit_target: norm_h_x_le_33_div_x_pow_four_for_all_positive_x
    factor_four_Estar_at_infinity: norm_le_132_mul_Z4_mul_u_pow_minus_seven_halves
    factor_four_Estar_at_zero: norm_le_132_mul_Z4_mul_u_pow_seven_halves
  UPPER_TAIL_RATE: 44_mul_Z4_div_lambda_cubed
  LOWER_TAIL_RATE: 44_mul_Z4_div_lambda_cubed
  COMBINED_RATE: 88_mul_Z4_div_lambda_cubed
  RATE_PROVED_BEFORE_TOPOLOGY: true
  WHOLE_OPEN_STRIP_UNIFORMITY: true
  CLOSED_SUBSTRIP_CATALOG_REQUIREMENT_CLOSED_BY_STRONGER_THEOREM: true
  FITTED_CONSTANT: false
  NEW_PAPER_INPUT: none
  C04_EXACT_TARGET_AND_UNIT_AUDIT: PASS
  C09_SINGLE_FACTOR_FOUR_PRECOMMIT_AUDIT: PASS
  C10_LITERAL_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

SCOPE_GUARD:
  PROVES_TARGET_OUTER_MELLIN_TAIL_UNIFORMITY: true
  PROVES_STRONGER_WHOLE_OPEN_STRIP_TARGET_TAIL_UNIFORMITY: true
  PROVES_SOURCE_WINDOW_MELLIN_ERROR_CONVERGENCE: false
  PROVES_SELECTED_FERRERS_MELLIN_CONVERGENCE_TO_CENTERED_XI: false
  PROVES_CCM_LEMMA73_PREANCHOR_PORT_INHABITANT: false
  PROVES_MODE_OR_CHI_RATES: false
  PROVES_SATZ9_OR_FUCHS_INPUTS: false
  PROVES_RH: false

SOURCE_RECORD_AUDIT:
  SAME_COMMIT_AS_LEAN: true
  BASE_HEAD_CORRECT: true
  BASE_HEAD_PROVENANCE_RECORDED: true
  PREFLIGHT_RECORDED: true
  LEAN_BLOB_AND_SHA256_PRESENT: true
  DIRECT_IMPORTS_EXACT: true
  PUBLIC_SURFACE_COMPLETE: true
  PRIVATE_DECLARATIONS_RECORDED: true
  EXPECTED_AXIOM_PROFILES_FIELD_PLURAL: true
  CLOSES_OPENS_PRESENT: true
  VERIFICATION_HANDOFF_PRESENT: true
  NEXT_LOAD_BEARING_GAP_PRESENT: true
  SELF_BLOB_PLACEHOLDER: ACCEPTED_AS_SELF_REFERENCE_WORKAROUND
  STATUS: CLEAN

PREDICTION_FATE:
  P_L73_6_1:
    claim: inverse_four_decay_and_exact_inversion_close_a_uniform_lambda_cubed_denominator_bound_on_the_entire_strip
    fate: CONFIRMED
  P_L73_6_2:
    claim: no_new_paper_input_is_required
    fate: CONFIRMED
  P_L73_6_3:
    claim: factor_four_changes_only_the_fixed_scalar
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: MELLIN_INDICATOR_SET_INTEGRAL_AND_RPOW_NORMAL_FORM
    fate: PARTIALLY_OBSERVED
    observed: rpow_and_nat_cast_normal_forms_only_indicator_integral_layer_passed_first_attempt
  FIRST_GATE_WITHOUT_REPAIR: false
  REPAIR_ROUNDS_REPORTED: 4
  RETROACTIVE_REPAIR: false

L73_7_ADJUDICATION:
  STATUS: AUTHORIZED
  CHARACTER: QUANTITATIVE_WINDOW_MELLIN_ASSEMBLY_ON_EACH_FIXED_CLOSED_SUBSTRIP
  EXACT_SOURCE_OBJECT: selectedFerrersPreAnchorPair
  EXACT_SOURCE_SCALE: selectedFerrersLemma73SourceScale
  EXACT_SOURCE_TRANSFORM: preAnchorGwinTransformCoordinate
  EXACT_TARGET: centeredXi
  EXACT_COORDINATE: s_equals_minus_I_mul_z
  DOMAIN: abs_z_im_le_sigma_with_zero_le_sigma_lt_one_half
  WHOLE_OPEN_STRIP_SOURCE_CONVERGENCE_AUTHORIZED: false
  WHY_WHOLE_STRIP_IS_FORBIDDEN: source_window_main_error_loses_decay_at_the_strip_boundary
  C01_LOCALIZATION_KILL_APPLIED: true
  C04_DOMAIN_MISMATCH_KILL_APPLIED: true
  MAIN_INPUTS:
    - selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
    - selectedFerrersFullEStarError_eq_main_sub_targetTail
    - selectedFerrersExplicitTargetTail_bound
    - mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi
    - selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn
    - selectedFerrersPreAnchorPair_lambda_eq
  POINTWISE_FULL_ERROR_UNIT: one_div_lambda_mul_sqrt_u
  WINDOW_MELLIN_RATE: >-
    C * (lambda^(-1/2 + sigma) / (sigma + 1/2)
         + lambda^(-1) / (1/2 - sigma))
  WINDOW_MELLIN_RATE_TENDS_TO_ZERO: true
  TARGET_OUTER_TAIL_TENDS_TO_ZERO: true
  NEW_EXTERNAL_INPUT: none
  MAIN_FORMAL_RISK: GWIN_IOO_VS_WINDOWED_MELLIN_ICC_AND_MELLIN_CONVERGENCE_NORMAL_FORM

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
    - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail
  PUBLIC_THEOREM:
    - selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
  REQUIRED_PRIVATE_PLANT: closedSubstrip_margin_is_loadBearing_plant
  CLOSES:
    - CCM_LEMMA_7_3_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_INHABITANT

CLOSES:
  - L73_6_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
NEXT_CHEAPEST_DECISIVE_TEST: PROVE_THE_EXACT_SOURCE_MINUS_TARGET_MELLIN_SPLIT_BEFORE_ESTIMATING_ANY_POWER_INTEGRAL

REGISTERED_PREDICTIONS:
  P_L73_7_1:
    claim: L73_3_main_error_plus_L73_4_target_tail_gives_the_full_pointwise_error_with_the_same_one_div_lambda_sqrt_u_unit
    probability: 0.94
  P_L73_7_2:
    claim: closed_substrip_power_integration_gives_the_explicit_two_term_rate_and_tends_to_zero
    probability: 0.90
  P_L73_7_3:
    claim: the_main_formal_friction_is_Gwin_Ioo_to_windowedMellin_Icc_and_integrability_not_new_mathematics
    probability: 0.85
  LIKELIEST_FAILURE: GWIN_IOO_ICC_ENDPOINT_OR_MELLIN_INTEGRABLE_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN
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
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_MODE_AND_CHI_RATE_INPUTS
```

## ROUTE MAP

### L73.6 semantic admission

The public tail is the exact downstream target from L73.5:

\[
\mathcal E(4h),
\qquad
h=\operatorname{explicitCCMLimitH},
\qquad
s=-iz.
\]

The factor four is inside the target function exactly once. The file does not prove an unscaled neighboring theorem and then relabel it. This passes the exact-object and functional audit. `[COFINAL_FAMILY][LEAN]` **[C04][C10]**

The coordinate identity

\[
\Re(-iz)=\Im z
\]

is proved before either tail estimate. On the upper tail, for every point of the open centered strip,

\[
\Im z-\frac92<-4,
\]

and on the lower tail,

\[
2<\Im z+\frac52.
\]

These inequalities permit the fixed majorants \(u^{-4}\) on \(u\ge1\) and \(u^2\) on \(0<u\le1\). They remain valid uniformly as \(|\Im z|\) approaches \(1/2\) from below. Therefore whole-open-strip uniformity is genuinely proved for the **target outer tail**; it is not a mislabeled family of closed-substrip statements. `[COFINAL_FAMILY][LEAN]`

The two sides satisfy

\[
\|T_k^{\rm upper}(z)\|
\le \frac{44Z_4}{\lambda_k^3},
\qquad
\|T_k^{\rm lower}(z)\|
\le \frac{44Z_4}{\lambda_k^3},
\]

hence

\[
\boxed{
\|T_k^{\rm outer}(z)\|
\le \frac{88Z_4}{\lambda_k^3}
}
\]

for every \(z\) in the open strip. Since \(\lambda_k^2=k+2\) and \(\lambda_k\ge1\), this tends uniformly to zero. The constants are derived algebraically; no numerical fit or paper estimate occupies the quantifier. `[COFINAL_FAMILY][LEAN]`

The result is stronger than the catalog requirement, but only on the target-tail object. It does not imply whole-strip convergence of the selected Ferrers source family. `[COFINAL_FAMILY][LEAN]`

### Why L73.7 must remain closed-substrip

The source-window error has the pointwise form

\[
\|\operatorname{FullError}_k(u)\|
\le
\frac{C}{\lambda_k\sqrt u}.
\]

At Mellin coordinate \(s=-iz\), its integrand has norm bounded by

\[
\frac{C}{\lambda_k}u^{\Im z-3/2}.
\]

For a fixed closed substrip \(|\Im z|\le\sigma<1/2\), splitting the source window at \(u=1\) gives

\[
\boxed{
\frac{C\lambda_k^{-1/2+\sigma}}{\sigma+1/2}
+
\frac{C\lambda_k^{-1}}{1/2-\sigma}.
}
\]

Both terms tend to zero. At the boundary value \(\Im z=-1/2\), however, the lower-window model becomes

\[
\frac1\lambda\int_{1/\lambda}^{1}u^{-2}\,du
=
1-\frac1\lambda,
\]

which does not tend to zero. Thus upgrading L73.7 to uniform convergence on the entire open strip would discard the distance-to-boundary invariant and is killed by **C01** and **C04**. The weakest correct statement is uniform convergence on each fixed closed substrip. `[COFINAL_FAMILY][PAPER]` **[C01][C04]**

## FINAL PROPOSAL

### Files

```text
Lean:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersClosedSubstripMellinConvergence.lean

Source record:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_2026-08-23.md
```

Use the verdict commit as `BASE_HEAD`, but take a live snapshot immediately before editing:

```bash
git rev-parse HEAD
```

### Exactly two direct imports

```lean
import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail
```

### Exact public theorem

```lean
theorem selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
    (σ C0 C4 Cχ : ℝ)
    (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2)
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
    TendstoUniformlyOn
      (fun k z =>
        selectedFerrersLemma73SourceScale k *
          preAnchorGwinTransformCoordinate
            (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k)) z)
      centeredXi
      Filter.atTop
      {z : ℂ | |z.im| ≤ σ}
```

The theorem must use the exact selected pair, exact precommitted index schedule, exact factor-four source scale, exact `Gwin` coordinate, and the production `centeredXi`.

### Mandatory private plant

```lean
private theorem closedSubstrip_margin_is_loadBearing_plant
    {λ : ℝ} (hλ : 1 < λ) :
    (1 / λ) * (λ - 1) = 1 - 1 / λ ∧
      0 < 1 - 1 / λ := by
  ...
```

The docstring must state that this is the exact algebraic value of the lower-window boundary model

\[
\lambda^{-1}\int_{\lambda^{-1}}^1u^{-2}\,du.
\]

The plant must kill any attempt to replace the closed substrip by the whole open strip.

### Proof route

1. Call `ask.sh` for the exact theorem name, the selected `Gwin` family, and Mellin-window decomposition.
2. Invoke L73.3 and L73.4 to obtain one eventual constant \(C_{\rm full}\ge0\) with
   \[
   \|\operatorname{FullError}_k(u)\|
   \le C_{\rm full}/(\lambda_k\sqrt u)
   \]
   on the entire source window.
3. Prove the exact source-side identity between `preAnchorGwinTransformCoordinate` and the source-window Mellin integral. Reconcile `Ioo` with `sourceWindow = Icc` only through endpoint-null integral equalities.
4. Prove, or locally re-prove, the exact `MellinConvergent` fact needed to invoke `mellin_eq_lower_add_window_add_upper` for the factor-four target at `-I*z`. The private convergence lemmas in L73.5/L73.6 are not importable. Do not add convergence as a hypothesis and do not edit admitted upstream files.
5. Derive the exact pointwise identity
   \[
   a_kGwin(h_k,\lambda_k,-iz)-\Xi(z)
   =
   \operatorname{WindowMellin}(\operatorname{FullError}_k)(-iz)
   -
   \operatorname{OuterTail}_k(z).
   \]
6. Fix `σ`, `z` with `|z.im| ≤ σ`, and split the source-window integral at `u = 1`.
7. On `[lambda⁻¹,1]`, majorize by `u^(-σ-3/2)` and integrate exactly.
8. On `[1,lambda]`, majorize by `u^(σ-3/2)` and integrate exactly.
9. Obtain the two-term rate
   \[
   C\left(
   \frac{\lambda^{-1/2+\sigma}}{\sigma+1/2}
   +
   \frac{\lambda^{-1}}{1/2-\sigma}
   \right).
   \]
10. Combine this uniform window-error convergence with the public L73.6 outer-tail convergence.
11. Print axioms of the public theorem.

### Forbidden

```text
whole-open-strip source convergence;
pointwise-in-z convergence relabeled as uniform;
a free window-Mellin error hypothesis;
a free Mellin-convergence hypothesis;
using an unscaled target;
omitting or duplicating factor four;
changing the selected pair or schedule;
choosing sigma after inspecting k;
integrating the original F72.6 sup error over a physical window of length 2 lambda;
editing L73.3, L73.4, L73.5, or L73.6;
bundling L73.8 or the port inhabitant;
paper axiom;
sorry;
admit;
typed hole;
theorem weakening.
```

### Gate

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean

lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean
```

Expected profile:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN

FAILURE:
  L73_7_GWIN_WINDOWED_MELLIN_CROSSWALK_OR_CLOSED_SUBSTRIP_POWER_INTEGRAL_GAP
```

After a separate semantic admission, the next floor is:

```text
L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_INHABITANT
```

L73.8 is not authorized by this verdict.

## STRONGEST ATTACK

The strongest remaining objection is formal rather than asymptotic:

> L73.6 exports uniform tail convergence, but its integrability and decay helpers are private. Why is the exact full-Mellin decomposition in L73.7 legal?

It is legal only if L73.7 proves the missing integrability locally or proves the source-minus-target split directly with explicit integrable pieces. The public equality from L73.5 gives the Mellin value; it does not by itself certify `MellinConvergent`, and Lean integral linearity cannot be invoked without the corresponding integrability proof. Adding this fact as a hypothesis would merely relocate the floor and is forbidden.

The second objection is the tempting over-strengthening to the whole open strip. The boundary model above is a direct counterexample to the available error budget. Whole-strip target-tail convergence from L73.6 does not transfer to the source-window error. That transfer would compare different functionals and domains and is killed by **C01/C04**.

## CODEX DIRECTIVE

```text
TASK:
  L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersClosedSubstripMellinConvergence.lean

  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_2026-08-23.md

FIRST DECISIVE TEST:
  Prove the exact identity

    sourceScale * preAnchorGwin - centeredXi
      = windowedMellin(fullError) - factorFourOuterTail

  for the exact selected source object and `s = -I*z`.

STOP IMMEDIATELY IF:
  this identity requires a new hypothesis,
  changes the source object,
  or cannot be typed without assuming target Mellin convergence.

THEN:
  derive the fixed-closed-substrip two-term power rate and finish
  TendstoUniformlyOn.

VALIDATE:
  lake env lean target file;
  lake build target module;
  q3_check from repository root;
  print the public theorem's axiom profile.

SUCCESS CODE:
  L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN

FAILURE CODE:
  L73_7_GWIN_WINDOWED_MELLIN_CROSSWALK_OR_CLOSED_SUBSTRIP_POWER_INTEGRAL_GAP
```

## META CLOSEOUT

**What became smaller?**

The target-side analytic floors are now complete through L73.6. The only remaining quantitative floor before the port constructor is the selected-source closed-substrip Mellin assembly.

**What was killed?**

- unscaled target-tail substitution;
- duplicate factor four;
- pointwise tail convergence relabeled as uniform;
- whole-open-strip source convergence from a closed-substrip rate;
- treating a finite Mellin value as an integrability certificate.

**What must not be tried again?**

Do not import L73.6 whole-strip uniformity into the source-window error. The two objects have different boundary behavior.

**Current smallest named gap:**

```text
L73_7_EXACT_SOURCE_MINUS_TARGET_MELLIN_SPLIT
```

**Next cheapest decisive test:**

Prove that exact split before doing any power integral or topology.

**Fate of prior predictions:**

All three L73.6 predictions are confirmed; the predicted normal-form failure is partially observed; no retroactive repair.

```yaml
iteration:
  target: L73.6 semantic admission and L73.7 theorem-shape authorization
  status: PROGRESS
  failed_strategy: whole_open_strip_source_convergence
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_7_EXACT_SOURCE_MINUS_TARGET_MELLIN_SPLIT
  invariant_learned: target_outer_tail_is_uniform_on_the_open_strip_but_source_window_error_requires_fixed_boundary_margin
  forbidden_future_move: use_L73_6_whole_strip_target_bound_as_a_source_window_convergence_theorem
  next_decisive_test: exact_source_minus_target_Mellin_split
  progress_class: PROOF_PROGRESS
  route_score: 5
```
