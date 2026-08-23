# STATUS: PROVED — L73.5 SEMANTICALLY ADMITTED; L73.6 FACTOR-FOUR OUTER-MELLIN TAIL AUTHORIZED
```yaml
PRIMARY: ADMIT_L73_5_AND_AUTHORIZE_L73_6_FACTOR_FOUR_OUTER_MELLIN_TAIL
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 866b783e1bdeebc12220f27df0fd404183492cc6
  SOURCE_COMMIT: 866b783e1bdeebc12220f27df0fd404183492cc6
  ACTUAL_SOURCE_COMMIT_PARENT: 1dc9254650d8a53639b8be42bc37170cbb5f2c6a
  CLAIMED_SOURCE_RECORD_BASE_HEAD: 1dc9254650d8a53639b8be42bc37170cbb5f2c6a
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean
  LEAN_GIT_BLOB: bc9b5eddf38bb8377d118cfec749e4f37b4cd516
  LEAN_SHA256_REPORTED: 0d79d4aba4d54374e17a9ccfdc0018020f5f152ce3b0a4fe9d71e8a563451fc9
  LEAN_LINES_REPORTED: 794
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 9bbfd562d8a00d7a738dfd1e4c999af458da1cab
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7758_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi:
      - propext
      - Classical.choice
      - Quot.sound
    mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_MELLIN_NORMALIZATION_AND_FACTOR_FOUR_CROSSWALK
  PUBLIC_THEOREMS:
    - Q3.RouteB.D0Pstar.mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
    - Q3.RouteB.D0Pstar.mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi
  EXACT_PACKET: Q3.RouteB.D0Pstar.explicitCCMLimitH
  EXACT_STARRED_COMB: Q3.RouteB.D0Pstar.E_star
  EXACT_TARGET: Q3.RouteB.centeredXi
  EXACT_COORDINATE: s_equals_minus_I_mul_z
  ROUTE_DOMAIN: centeredCriticalStrip
  GAUSSIAN_MELLIN_FORMULA: mellin_h_p_equals_p_mul_p_minus_one_div_8_mul_GammaR_p
  ONE_EIGHTH_APPEARS_BEFORE_ZETA_MULTIPLICATION: true
  ESTAR_MELLIN_ABSOLUTE_ASSUMED: false
  ESTAR_MELLIN_ABSOLUTE_PROVED: true
  SEED_DOMAIN: one_half_lt_re_s
  CONNECTED_CONTINUATION_DOMAIN: minus_3_lt_re_s_lt_3
  CONTINUATION_ASSUMED: false
  TWO_SIDED_DECAY:
    at_infinity: O_u_pow_minus_seven_halves
    at_zero: O_u_pow_seven_halves
    zero_side_source: exact_E_star_inversion
  IDENTITY_THEOREM_USED: AnalyticOnNhd_eqOn_of_preconnected_of_eventuallyEq
  RIEMANN_XI_FUNCTIONAL_EQUATION_DERIVED: true
  UNSCALED_RESULT: quarter_mul_centeredXi
  SCALED_RESULT: centeredXi_after_exactly_one_factor_four
  FACTOR_FOUR_FITTED: false
  FACTOR_FOUR_DERIVED_BY_LINEARITY: true
  QUARTER_LOAD_BEARING_PLANT_PRESENT: true
  C04_UNIT_AND_COORDINATE_AUDIT: PASS
  C09_FACTOR_FOUR_PRECOMMIT_AUDIT: PASS
  C10_LITERAL_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_FULL_TARGET_MELLIN_IDENTITY_ON_CENTERED_STRIP: true
  PROVES_FACTOR_FOUR_TARGET_MELLIN_EQUALS_CENTERED_XI: true
  PROVES_GAUSSIAN_MELLIN_COEFFICIENT: true
  PROVES_OUTER_MELLIN_TAIL_DECAY_ALONG_SELECTED_SCHEDULE: false
  PROVES_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE: false
  PROVES_CCM_LEMMA73_PORT_INHABITANT: false
  PROVES_RAW_SATZ9_OR_FUCHS_INPUTS: false
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
  P_L73_5_1:
    claim: Gaussian_Mellin_algebra_closes_with_exact_one_eighth_before_zeta_product
    fate: CONFIRMED
  P_L73_5_2:
    claim: inversion_and_polynomial_decay_supply_one_connected_holomorphy_strip
    fate: CONFIRMED
  P_L73_5_3:
    claim: factor_four_corollary_is_pure_linearity
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: BIGO_NEAR_ZERO_OR_ANALYTIC_IDENTITY_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: coercion_cpow_set_membership_and_elementary_API_friction_only
  RETROACTIVE_REPAIR: false

L73_6_ADJUDICATION:
  STATUS: AUTHORIZED_WITH_STRONGER_WHOLE_CENTERED_STRIP_UNIFORM_TARGET
  CATALOG_NAME_PRESERVED: EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
  EXACT_TARGET_OBJECT: E_star_of_four_mul_explicitCCMLimitH
  UNSCALED_TARGET_FOR_PUBLIC_THEOREM: FORBIDDEN_C04_C10_MISMATCH
  OUTER_TAIL: lowerMellinTail_plus_upperMellinTail
  SCHEDULE: selectedFerrersPaperLambda_k_equals_sqrt_k_plus_2
  CLAIMED_RATE: O_selectedFerrersPaperLambda_k_pow_minus_3
  EXPLICIT_ALLOWED_CONSTANT: 88_mul_tsum_pnat_inverse_four
  UNIFORMITY_DOMAIN: entire_centeredCriticalStrip
  REASON_STRONGER_THAN_OLD_FLOOR:
    upper_integrand_exponent: y_minus_nine_halves_le_minus_four
    lower_integrand_exponent: y_plus_five_halves_ge_two
    y_range: minus_one_half_lt_y_lt_one_half
  NEW_PAPER_INPUT: none
  MAIN_FORMAL_RISK: MELLIN_INDICATOR_SET_INTEGRAL_AND_RPOW_NORMAL_FORM

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization
    - Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
  PUBLIC_DEFINITIONS:
    - selectedFerrersFactorFourExplicitLimitMellinOuterTail
  PUBLIC_THEOREMS:
    - selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn
  REQUIRED_PRIVATE_PLANT: centeredStrip_tail_exponent_guard_plant
  REQUIRED_PRIVATE_RATE: factorFour_outerTail_norm_le_inv_cube
  CLOSES:
    - EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE

CLOSES:
  - L73_5_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI
  - FACTOR_FOUR_EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
NEXT_CHEAPEST_DECISIVE_TEST: DERIVE_THE_COMMON_88_Z4_DIV_LAMBDA_CUBED_BOUND_BEFORE_TOPOLOGY_ASSEMBLY

REGISTERED_PREDICTIONS:
  P_L73_6_1:
    claim: inverse_four_decay_plus_exact_inversion_closes_a_uniform_lambda_minus_three_bound_on_the_entire_centered_strip
    probability: 0.93
  P_L73_6_2:
    claim: no_new_paper_input_is_needed
    probability: 0.995
  P_L73_6_3:
    claim: factor_four_changes_only_the_fixed_scalar_constant
    probability: 0.999
  LIKELIEST_FAILURE: MELLIN_INDICATOR_SET_INTEGRAL_AND_RPOW_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

EXECUTION_AUTHORIZED_NOW: true
CODEX_AUTHORIZED_NOW: true
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
SCOPE: ABSTRACT
VERIFIER: LEAN
```

## ROUTE MAP

### L73.5 is the exact object, not a normalization surrogate

The admitted theorem uses the literal production packet

\[
h(x)=\frac{\pi}{2}x^2(2\pi x^2-3)e^{-\pi x^2},
\]

the literal positive-dilate starred comb `E_star`, the project Mellin transform, and the production `centeredXi`. No definition is changed and no zero-free gauge is inserted. `[ABSTRACT][LEAN]` **[C04][C10]**

The Gaussian calculation is completed before the zeta product:

\[
\mathcal Mh(p)
=
\frac{p(p-1)}8\Gamma_{\mathbb R}(p),
\qquad \Re p>0.
\]

The file then proves, rather than assumes, the absolute sum/integral interchange needed for

\[
\mathcal M(E_\star h)(s)
=
\zeta(s+\tfrac12)\mathcal Mh(s+\tfrac12)
\]

on `1/2 < Re(s)`. Consequently the coefficient `1/4` is forced algebraically before analytic continuation. `[ABSTRACT][LEAN]`

The continuation step is also theorem-bearing. The exact inversion of `E_star h` transports the `O(u^{-7/2})` bound at infinity to `O(u^{7/2})` at zero. Thus the integral-defined Mellin transform is holomorphic on the connected strip

\[
-3<\Re s<3,
\]

which contains both the seed half-plane and the image of the centered critical strip under `s=-iz`. The identity theorem extends the exact quarter identity through that strip. `[ABSTRACT][LEAN]`

Finally,

\[
-iz+\frac12
=
1-\left(\frac12+iz\right),
\]

and the project functional equation `riemannXi(1-s)=riemannXi(s)` converts the right side to the production `centeredXi z`. The factor-four theorem is then pure linearity of `E_star`, `tsum`, and `mellin`; the scalar occurs exactly once. `[ABSTRACT][LEAN]` **[C09]**

### Exact scope

L73.5 closes the Mellin normalization floor. It does not estimate the omitted lower and upper Mellin tails of a finite source window, does not combine source and target errors on closed substrips, and does not construct `CCMLemma73PreAnchorPort`. Those remain L73.6, L73.7 and L73.8 respectively. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

### Stronger L73.6 target

The old floor requested uniform convergence on every closed substrip. The exact target admits a stronger theorem: uniform convergence on the whole open `centeredCriticalStrip`.

Define:

```lean
noncomputable def selectedFerrersFactorFourExplicitLimitMellinOuterTail
    (k : ℕ) (z : ℂ) : ℂ :=
  lowerMellinTail (selectedFerrersPaperLambda k)
      (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (-Complex.I * z) +
    upperMellinTail (selectedFerrersPaperLambda k)
      (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (-Complex.I * z)
```

Prove:

```lean
theorem selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn :
    TendstoUniformlyOn
      selectedFerrersFactorFourExplicitLimitMellinOuterTail
      (fun _ : ℂ => 0)
      Filter.atTop
      centeredCriticalStrip
```

The public object must contain the factor-four target. An unscaled public outer-tail theorem would estimate a different function from the target identified with `centeredXi` by L73.5 and would fail the C04/C10 object audit.

### Exact rate before topology

Let

\[
Z_4:=\sum_{n\ge1}n^{-4}.
\]

The private quantitative lemma must prove

\[
\boxed{
\left\|T_k(z)\right\|
\le
\frac{88Z_4}{\lambda_k^3}
}
\]

for every `z ∈ centeredCriticalStrip`, where `T_k` is the definition above and `lambda_k = selectedFerrersPaperLambda k`.

The constant is source-derived, not fitted. The already used inverse-four estimate gives

\[
\|4E_\star h(u)\|
\le132Z_4u^{-7/2}
\qquad(u\ge1).
\]

For `s=-iz`, write `y=Re(s)=Im(z)`. On the centered strip, `-1/2<y<1/2`. Therefore the upper Mellin integrand is bounded by

\[
132Z_4u^{y-9/2}\le132Z_4u^{-4},
\qquad u\ge\lambda_k\ge1,
\]

and its integral is at most `44*Z4/lambda_k^3`.

Exact inversion gives the lower-side bound

\[
\|4E_\star h(u)\|
\le132Z_4u^{7/2}
\qquad(0<u\le1).
\]

Hence the lower Mellin integrand is bounded by

\[
132Z_4u^{y+5/2}\le132Z_4u^2,
\qquad 0<u\le\lambda_k^{-1},
\]

and contributes the same `44*Z4/lambda_k^3`. Summing gives the boxed constant. Since `lambda_k^2=k+2`, the rate tends to zero uniformly in `z`.

### Required plant

```lean
private theorem centeredStrip_tail_exponent_guard_plant
    {y : ℝ} (hy : |y| < 1 / 2) :
    y - 9 / 2 < -4 ∧ 2 < y + 5 / 2 := by
  have h := abs_lt.mp hy
  constructor <;> linarith
```

This plant protects both ends simultaneously. It prevents a sign error in `s=-iz` from converting one decaying tail into a growing one.

## STRONGEST ATTACK

The strongest attack on L73.5 is that the half-plane product identity might have been merely renamed as a strip identity, or that the missing factor `4` was inserted after seeing the target. Neither happened.

The source separately proves two-sided Mellin holomorphy and uses an identity theorem on one connected domain. The coefficient `1/8` is present in the Gaussian Mellin formula before `riemannZeta` enters, and the central nonvanishing plant distinguishes the quarter identity from the false coefficient-one identity. `[ABSTRACT][LEAN]` **[C04][C09][C10]**

The strongest attack on L73.6 is a coordinate-sign error. If `Re(-iz)` were taken as `-Im(z)`, the two exponent ledgers would be swapped. The mandatory plant and an explicit theorem `(-I*z).re = z.im` must occur before either tail estimate.

## CODEX DIRECTIVE

```text
TASK: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the current [Proshka] verdict commit;
  run `git rev-parse HEAD` immediately before editing;
  record the full actual parent in the source record.

CREATE EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1ExplicitCCMLimitMellinOuterTail.lean

  docs/routeB_bus/
    LINUX_SOURCE_RECORD_REQ_V_L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_2026-08-23.md

DIRECT IMPORTS EXACTLY:
  Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization
  Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary

PUBLIC SURFACE EXACTLY:
  selectedFerrersFactorFourExplicitLimitMellinOuterTail
  selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn

TARGET:
  prove uniform convergence to zero on the entire centeredCriticalStrip;
  this is stronger than the catalog's closed-substrip requirement and closes it.

PROOF ROUTE:
  1. Run `./ask.sh "explicit limit Mellin outer tail lowerMellinTail upperMellinTail inverse four"`.
  2. Define the factor-four target tail exactly as above.
  3. Re-prove privately the inverse-four bound for explicitCCMLimitH; upstream copies are private.
  4. Derive the factor-four E_star bounds at infinity and at zero using exact inversion.
  5. Prove `(-I*z).re = z.im` and run the required exponent plant.
  6. Bound the upper indicator Mellin integral by `44*Z4/lambda^3`.
  7. Bound the lower indicator Mellin integral by `44*Z4/lambda^3`.
  8. Prove the private common rate `88*Z4/lambda^3` before invoking topology.
  9. Use `selectedFerrersPaperLambda_sq` and `lambda_k >= 1` to prove the public TendstoUniformlyOn theorem.
  10. Print axioms of the public theorem.

PINNED MATHLIB SOURCES TO USE AFTER LOCAL RG VERIFICATION:
  Mathlib.Analysis.SpecialFunctions.ImproperIntegrals:
    integral_Ioi_rpow_of_lt
    integrableOn_Ioi_rpow_of_lt
  For the lower finite interval, use the pinned finite-interval rpow integral API found by local `rg`; record its exact theorem and source line in the source record.

FORBIDDEN:
  - unscaled explicitCCMLimitH target in the public definition;
  - omitted or duplicated factor four;
  - adding outer-tail decay as a theorem hypothesis;
  - proving only pointwise convergence;
  - assuming Mellin convergence or target inversion;
  - importing L73.3 or L73.4 to create a fake dependency;
  - editing L73.5 or any prior admitted file;
  - bundling L73.7, L73.8, or the port inhabitant;
  - numerical constants fitted from samples;
  - paper axiom, sorry, admit, typed hole, or theorem weakening.

CLOSES:
  EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS

OPENS:
  none

SUCCESS:
  L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS_LEAN

FAILURE:
  L73_6_MELLIN_INDICATOR_INTEGRAL_OR_RPOW_UNIFORM_BOUND_GAP

VALIDATION:
  WORKDIR: q3.lean.aristotle
    lake env lean \
      Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean

    lake build \
      Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail

  WORKDIR: repository root
    scripts/q3_check.sh \
      Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

NEXT AFTER SEPARATE SEMANTIC ADMISSION ONLY:
  L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
```

## META CLOSEOUT

**What became smaller?**

The exact limiting target is now identified with production `centeredXi` in Lean, including its load-bearing quarter and the one legal factor-four repair. The remaining target-side work is one explicit omitted-window integral estimate.

**What was killed?**

- the false unscaled coefficient-one Mellin identity;
- any claim that analytic continuation was only paper prose;
- an unscaled L73.6 public target;
- treating the whole-strip strengthening as requiring a new analytic input.

**What must not be tried again?**

Do not hide the factor four in a source convention, redo L73.5, or prove pointwise outer-tail convergence and call it a uniform closed-substrip result.

**Current smallest named gap:**

```text
L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
```

**Next cheapest decisive test:**

Prove the explicit common bound

\[
88Z_4/\lambda_k^3
\]

before any `TendstoUniformlyOn` assembly.

**Fate of prior registered predictions:**

```text
P_L73_5_1: CONFIRMED
P_L73_5_2: CONFIRMED
P_L73_5_3: CONFIRMED
LIKELIEST_FAILURE: NOT_OBSERVED
RETROACTIVE_REPAIR: false
```

```yaml
iteration:
  target: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
  status: PROGRESS
  failed_strategy: false_unscaled_coefficient_one_identity_already_killed
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
  invariant_learned: exact_packet_exact_Estar_exact_coordinate_and_factor_four_once
  forbidden_future_move: unscaled_outer_tail_or_pointwise_only_tail_claim
  next_decisive_test: derive_88_Z4_div_lambda_cubed_uniform_bound
```
