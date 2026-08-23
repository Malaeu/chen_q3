# STATUS: PROVED — L73.4 SEMANTICALLY ADMITTED; L73.5 QUARTER-CENTERED-XI MELLIN PORT AUTHORIZED
```yaml
PRIMARY: ADMIT_L73_4_AND_AUTHORIZE_L73_5_QUARTER_CENTERED_XI_MELLIN_PORT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: bba7cf89ce1bc6892e737b2e6766af4ec2046330
  SOURCE_COMMIT: bba7cf89ce1bc6892e737b2e6766af4ec2046330
  ACTUAL_SOURCE_COMMIT_PARENT: 405777bc8e905655141b9abcc6994db2b8970872
  CLAIMED_SOURCE_RECORD_BASE_HEAD: 405777bc8e905655141b9abcc6994db2b8970872
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
  LEAN_GIT_BLOB: 69b1613b19dd76553cacd9112c38f8ea85c1aa7b
  LEAN_SHA256_REPORTED: 751471675dbd8f72f5e4cdf1a257a8519c17e0773d89818276fbcf7cfdbf941e
  LEAN_LINES_REPORTED: 508
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 172d05ff9a350e1dd28ef4b8e48272a9d21f82bb
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7850_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersFullEStarError_eq_main_sub_targetTail:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersExplicitTargetTail_bound:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SUPPORT_REPAIR_AND_TARGET_TAIL_BOUND
  PUBLIC_DEFINITIONS:
    - Q3.RouteB.D0Pstar.selectedFerrersExplicitTargetTail
    - Q3.RouteB.D0Pstar.selectedFerrersFullEStarError
  PUBLIC_THEOREMS:
    - Q3.RouteB.D0Pstar.selectedFerrersFullEStarError_eq_main_sub_targetTail
    - Q3.RouteB.D0Pstar.selectedFerrersExplicitTargetTail_bound
  SOURCE_OBJECT: selectedFerrersPreAnchorPair
  SOURCE_PACKET: prolateCombination_selectedFerrersPreAnchorPair
  SOURCE_SCALE: selectedFerrersLemma73SourceScale
  SOURCE_WINDOW: sourceWindow_selectedFerrersPaperLambda
  TARGET_OBJECT: four_mul_explicitCCMLimitH
  MAIN_COUNT: floor_selectedFerrersPaperLambda_div_u
  MAIN_INDEX_SET: positive_indices_1_through_M
  TAIL_FIRST_INDEX: M_plus_1
  TAIL_INDEX_FORMULA: M_plus_n_plus_1
  FULL_ERROR_SPLIT: full_error_equals_main_error_minus_target_tail
  SOURCE_TRUNCATION_DERIVED_FROM_LITERAL_SUPPORT: true
  TARGET_NONCOMPACTNESS_PRESERVED: true
  PNAT_TO_NAT_REINDEX_PROVED: true
  TSUM_PREFIX_TAIL_SPLIT_PROVED: true
  FACTOR_FOUR_OCCURS_EXACTLY_ONCE: true
  STATIC_K_PLUS_TWO_CUTOFF_USED: false
  TARGET_TAIL_ASSUMED: false
  FULL_ERROR_SPLIT_ASSUMED: false
  POINTWISE_TARGET_DECAY: norm_h_x_le_33_div_x_pow_four_for_all_x_pos
  SERIES_MAJORANT: one_div_n_plus_one_sq
  OUTPUT_CONSTANT: 132_mul_tsum_one_div_n_plus_one_sq
  OUTPUT_UNIT: one_div_lambda_mul_sqrt_u
  NUMERICAL_FIT: false
  NEW_PAPER_INPUT: none
  C04_SUPPORT_CATEGORY_AUDIT: PASS
  C09_DYNAMIC_CUTOFF_AND_FIXED_FACTOR_AUDIT: PASS
  C10_LITERAL_SOURCE_AND_TARGET_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_EXACT_FULL_ESTAR_POINTWISE_ERROR_SPLIT: true
  PROVES_EXPLICIT_TARGET_TAIL_POINTWISE_BOUND: true
  PROVES_BOUND_UNIFORMLY_ON_THE_SOURCE_WINDOW: true
  PROVES_FULL_MELLIN_IDENTITY: false
  PROVES_TARGET_MELLIN_EQUALS_CENTERED_XI: false
  PROVES_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE: false
  PROVES_OUTER_MELLIN_TAIL_DECAY: false
  PROVES_CCM_LEMMA73_PORT_INHABITANT: false
  PROVES_RH: false
  UPSTREAM_MODE_AND_CHI_RATES_REMAIN_EXPLICIT: true

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
  P_L73_4_1:
    claim: exact_full_error_split_closes_after_literal_source_support_and_target_tsum_decomposition
    fate: CONFIRMED
  P_L73_4_2:
    claim: inverse_four_decay_plus_ordinary_inverse_square_summability_gives_the_required_one_div_lambda_sqrt_u_unit
    fate: CONFIRMED
  P_L73_4_3:
    claim: no_new_paper_input_is_needed
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: TSUM_PNAT_NAT_REINDEX_OR_FLOOR_TAIL_SPLIT_NORMAL_FORM
    fate: PARTIALLY_OBSERVED
    observed: pnat_nat_index_alignment_and_tsum_congruence_required_repairs
  RETROACTIVE_REPAIR: false

L73_5_ADJUDICATION:
  STATUS: AUTHORIZED_ROUTE_FACING_STRIP_IDENTITY
  CHARACTER: EXPLICIT_GAUSSIAN_MELLIN_FORMULA_PLUS_ANALYTIC_CONTINUATION
  FALSE_TARGET_ALREADY_KILLED: unscaled_mellin_equals_centeredXi
  EXACT_UNSCALED_TARGET: quarter_mul_centeredXi
  EXACT_SCALED_TARGET: centeredXi_after_one_factor_four
  ROUTE_DOMAIN: centeredCriticalStrip
  GLOBAL_ALL_Z_THEOREM_REQUIRED: false
  REASON_FOR_STRIP_SCOPE: downstream_consumes_only_the_open_centered_critical_strip
  NEW_EXTERNAL_INPUT: none
  MAIN_EXISTING_SUPPLIERS:
    - mellin_E_star_eq_riemannZeta_mul
    - E_star_explicitCCMLimitH_inv
    - mellin_differentiableAt_of_isBigO_rpow
    - Complex.Gamma_eq_integral
    - Complex.Gamma_add_one
    - GammaR_add_two
    - completedRiemannZeta_eq_Gamma_mul_riemannZeta
    - completedRiemannZeta0_one_sub
    - centeredXi_zero_ne_zero
  MAIN_FORMAL_RISK: BIGO_NEAR_ZERO_OR_ANALYTIC_IDENTITY_NORMAL_FORM

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
    - Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
    - Q3.Proofs.RouteB.CenteredXiZeroNonzero
  PUBLIC_THEOREMS:
    - mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
    - mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi
  REQUIRED_PRIVATE_PLANT: quarter_centeredXi_ne_centeredXi_at_zero
  CLOSES:
    - EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI
    - FACTOR_FOUR_EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS

CLOSES:
  - L73_4_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL
  - SELECTED_FERRERS_FULL_ESTAR_POINTWISE_ERROR_DECOMPOSITION
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
NEXT_CHEAPEST_DECISIVE_TEST: PROVE_GAUSSIAN_MELLIN_COEFFICIENT_IN_THE_ABSOLUTE_HALF_PLANE_BEFORE_CONTINUATION

REGISTERED_PREDICTIONS:
  P_L73_5_1:
    claim: explicit_Gaussian_Mellin_algebra_closes_with_exact_coefficient_one_eighth_before_the_zeta_product
    probability: 0.84
  P_L73_5_2:
    claim: inversion_plus_polynomial_decay_gives_a_connected_Mellin_holomorphy_strip_containing_both_the_product_half_plane_and_the_centered_strip
    probability: 0.72
  P_L73_5_3:
    claim: the_scaled_factor_four_corollary_is_pure_linearity_after_the_quarter_identity
    probability: 0.99
  LIKELIEST_FAILURE: BIGO_NEAR_ZERO_OR_ANALYTIC_IDENTITY_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
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

L73.4 closes the support-category defect which the one-line paper estimate hides under the project's literal zero extension. The source packet is compactly supported, while `explicitCCMLimitH` is not. The theorem therefore proves the exact identity

\[
\operatorname{FullError}_k(u)
=
\operatorname{MainError}_k(u)-\operatorname{TargetTail}_k(u)
\]

with

\[
M_k(u)=\left\lfloor\frac{\lambda_k}{u}\right\rfloor,
\qquad
\operatorname{TargetTail}_k(u)
=
\sqrt u\sum_{n\ge0}4h((M_k(u)+n+1)u).
\]

The off-by-one convention is exact. The main sum contains the positive indices `1,...,M`; if `M*u=lambda`, the boundary term remains in the main sum. The first tail index is `M+1`, and `(M+1)u>lambda`. `[COFINAL_FAMILY][LEAN]` **[C04]**

The source truncation is not postulated. It is derived from the support fields of the literal selected Ferrers `ProlatePair`; the target sum is separately reindexed from positive integers to naturals and split by `Summable.sum_add_tsum_nat_add`. The same selected pair, source scale and factor-four target from F72.6 are preserved. `[COFINAL_FAMILY][LEAN]` **[C09][C10]**

The target bound is also source-derived. The local polynomial-Gaussian estimate

\[
\|h(x)\|\le \frac{33}{x^4}\qquad(x>0)
\]

is proved without a large-`x` premise. For `r=(M+n+1)u`, the two inequalities `r>lambda` and `r>=(n+1)u` give

\[
r^4\ge \lambda^2((n+1)u)^2.
\]

After summing against `sum 1/(n+1)^2` and using `lambda*u>=1`, the theorem obtains

\[
\boxed{
\|\operatorname{TargetTail}_k(u)\|
\le \frac{C}{\lambda_k\sqrt u}.
}
\]

No numerical value of the zeta-two sum is fitted or consumed. `[COFINAL_FAMILY][LEAN]`

The result does not perform Mellin integration. It supplies one of the two pointwise pieces that L73.7 will integrate on a closed substrip. The exact Mellin identification of the limiting target remains a separate floor. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

### Exact L73.5 theorem shape

Do not prove an unnecessarily global all-`z` theorem. The downstream port consumes the identity only on `centeredCriticalStrip`. Prove exactly:

```lean
theorem mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
    {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    mellin (E_star explicitCCMLimitH) (-Complex.I * z) =
      (1 / 4 : ℂ) * centeredXi z
```

and the exact factor-four corollary:

```lean
theorem mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi
    {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    mellin
        (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z) =
      centeredXi z
```

The second theorem must derive from the first by exact linearity. It may not hide the scalar in `centeredXi`, in a new packet definition, or in a fitted source scale. `[ABSTRACT][LEAN]` **[C04][C09]**

### Required plant

```lean
private theorem quarter_centeredXi_ne_centeredXi_at_zero :
    (1 / 4 : ℂ) * centeredXi 0 ≠ centeredXi 0 := by
  have h0 := centeredXi_zero_ne_zero
  intro h
  have hmul : ((1 / 4 : ℂ) - 1) * centeredXi 0 = 0 := by
    calc
      ((1 / 4 : ℂ) - 1) * centeredXi 0 =
          (1 / 4 : ℂ) * centeredXi 0 - centeredXi 0 := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact h0 ((mul_eq_zero.mp hmul).resolve_left (by norm_num))
```

This plant kills the already-refuted coefficient-one theorem at the exact nonzero central anchor. `[ABSTRACT][LEAN]` **[C04]**

### Proof route

1. Run `./ask.sh` for the final theorem names and for a reusable Gaussian-Mellin supplier.
2. Prove privately, in an absolute half-plane, the exact packet formula
   \[
   \mathcal M h(p)=\frac{p(p-1)}8\Gamma_{\mathbb R}(p).
   \]
   Use the pinned Mathlib primitives `mellin_comp_rpow`, `mellin_comp_mul_left`, `mellin_cpow_smul`, `Complex.Gamma_eq_integral`, `Complex.Gamma_add_one`, `Gammaℝ_def`, and `Gammaℝ_add_two`. The coefficient `1/8` must appear before any zeta multiplication.
3. Build the `EStarMellinAbsolute` payload for this Gaussian packet on `1 < p.re`. Reuse the scaling argument of `MuntzV3/EStarMellinAbsolutePayload.lean`; do not assume the interchange.
4. Apply `mellin_E_star_eq_riemannZeta_mul` on the nonempty product half-plane. Combine the Gaussian formula with `completedRiemannZeta_eq_Gamma_mul_riemannZeta` and `riemannXi_eq_completedRiemannZeta` to obtain
   \[
   \mathcal M(E_\star h)(s)=\frac14\,\operatorname{riemannXi}(s+1/2)
   \]
   there.
5. Prove a connected Mellin-holomorphy strip containing both the product half-plane and `-1/2 < s.re < 1/2`. A convenient bounded strip is `-3 < s.re < 3`. At infinity, inverse-four decay and `sum n^{-4}` give `E_star h = O(u^{-7/2})`; at zero, use the exact public inversion `E_star_explicitCCMLimitH_inv` to transfer the same decay. Apply the pinned `mellin_differentiableAt_of_isBigO_rpow` theorem.
6. Extend the half-plane equality across the connected strip with the exact project-used API `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. Do not assume analytic continuation as a theorem input.
7. Prove privately the functional equation for the project `riemannXi` directly from `completedRiemannZeta₀_one_sub`, then substitute `s=-I*z`. This converts `riemannXi(1/2-I*z)` to the production `centeredXi z`.
8. Derive the factor-four corollary by the linearity of `E_star`, `tsum`, and `mellin`.
9. Print the axiom profiles of both public theorems.

`[ABSTRACT][CONDITIONAL]`

## STRONGEST ATTACK

The strongest reviewer objection is not the factor `1/4`; that scalar is already independently locked. The real risk is a fake analytic continuation:

> The product formula is proved only where the Dirichlet series is absolutely convergent. Why is the integral-defined Mellin transform itself holomorphic on a connected domain reaching the centered critical strip?

A proof that establishes only

```text
Re(s) > 1/2:
  mellin(E_star h)(s) = quarter * riemannXi(s+1/2)
```

and then rewrites `s=-I*z` does not close L73.5, because the centered strip lies outside that initial half-plane. The two-sided Big-O and identity-theorem layer are load-bearing. `[ABSTRACT][PAPER]` **[C10]**

A second objection is that Poisson inversion might silently supply the missing factor four. It cannot. Inversion changes the argument `u ↔ u⁻¹`; it does not change a global scalar. The source and target must continue to carry the same exact `1/4` established in the absolute half-plane. `[ABSTRACT][PAPER]` **[C04]**

## CODEX DIRECTIVE

```text
TASK: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the commit containing this verdict;
  run git rev-parse HEAD immediately before editing.

CREATE_EXACTLY_ONE_LEAN_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1ExplicitCCMLimitMellinNormalization.lean

CREATE_SOURCE_RECORD_SAME_COMMIT:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_2026-08-23.md

DIRECT_IMPORTS:
  Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
  Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
  Q3.Proofs.RouteB.CenteredXiZeroNonzero

PUBLIC_SURFACE:
  mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
  mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi

REQUIRED_PRIVATE_PLANT:
  quarter_centeredXi_ne_centeredXi_at_zero

CLOSES:
  EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI
  FACTOR_FOUR_EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI

OPENS: []

FORBIDDEN:
  unscaled coefficient-one equality;
  changing centeredXi;
  changing explicitCCMLimitH;
  fitting the factor four numerically;
  assuming EStarMellinAbsolute;
  assuming Mellin analyticity or analytic continuation;
  proving only the absolute-convergence half-plane identity;
  importing F72.6 as a substitute for the Mellin calculation;
  bundling L73.6, L73.7, or the port inhabitant;
  editing upstream files;
  paper axiom;
  sorry;
  admit;
  typed hole;
  theorem weakening.

SUCCESS:
  L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN

FAILURE:
  L73_5_GAUSSIAN_MELLIN_OR_ANALYTIC_CONTINUATION_GAP

NEXT_AFTER_SEMANTIC_ADMISSION_ONLY:
  L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
```

### Validation gate

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean

lake build \
  Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean
```

Expected for both public theorems:

```text
[propext, Classical.choice, Quot.sound]
```

## META CLOSEOUT

**What became smaller?**

The support mismatch is gone. The full pointwise `E_star` defect is now exactly the sum of two named and bounded pieces: the dynamic main error and the noncompact target tail. `[COFINAL_FAMILY][LEAN]`

**What was killed?**

```text
full E-star error = L73.3 main error
```

without a target-tail term. The plant and exact split kill that shortcut. `[ABSTRACT][LEAN]`

**What must not be tried again?**

Do not treat `explicitCCMLimitH` as compactly supported. Do not replace the dynamic cutoff by `k+2`. Do not use the false coefficient-one Mellin identity.

**Current smallest named gap:**

```text
L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
```

**Next cheapest decisive test:**

Prove the Gaussian Mellin coefficient `p*(p-1)/8` in the absolute half-plane before writing the analytic-continuation layer. If the coefficient is not exactly `1/8`, stop immediately; do not compensate downstream.

**Fate of prior registered predictions:**

All three L73.4 predictions were confirmed; the anticipated `PNat/Nat` reindex friction was partially observed. No prediction was repaired retroactively.

**Memory entry:**

```yaml
iteration:
  target: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
  status: PROGRESS
  failed_strategy: FULL_ERROR_EQUALS_DYNAMIC_MAIN_ERROR
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
  invariant_learned: compact_source_and_noncompact_target_require_an_explicit_shifted_target_tail
  forbidden_future_move: omit_tail_or_duplicate_factor_four
  next_decisive_test: exact_Gaussian_Mellin_coefficient_in_absolute_half_plane
```
