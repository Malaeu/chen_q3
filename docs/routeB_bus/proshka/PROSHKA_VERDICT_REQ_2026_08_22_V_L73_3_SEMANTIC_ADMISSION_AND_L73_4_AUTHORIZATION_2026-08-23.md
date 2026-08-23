# STATUS: PROVED — L73.3 SEMANTICALLY ADMITTED; L73.4 EXACT TARGET-TAIL SPLIT AND BOUND AUTHORIZED
```yaml
PRIMARY: ADMIT_L73_3_AND_AUTHORIZE_L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 49e13d6da982cfc45bdb841be9643f5997907c09
  SOURCE_COMMIT: 49e13d6da982cfc45bdb841be9643f5997907c09
  ACTUAL_SOURCE_COMMIT_PARENT: 19ee838c45f936a929f1989b2888ddc4e04b2fb4
  CLAIMED_SOURCE_RECORD_BASE_HEAD: 19ee838c45f936a929f1989b2888ddc4e04b2fb4
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean
  LEAN_GIT_BLOB: f13703ffa04009132e80eeeacde63d3a1f807bc8
  LEAN_SHA256_REPORTED: 75aa19b608f674e74b98ceffd520c379376a5afe1d8398a6924967a4068ca914
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 43f78f6f82530d6421868b40fa07c20dceb8658e
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7849_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_DYNAMIC_MAIN_SUM_ASSEMBLY
  PUBLIC_DEFINITIONS:
    - Q3.RouteB.D0Pstar.selectedFerrersEStarMainCount
    - Q3.RouteB.D0Pstar.selectedFerrersEStarWindowMainError
  PUBLIC_THEOREM: Q3.RouteB.D0Pstar.selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
  DIRECTION: FACTOR_FOUR_PACKET_POINTWISE_RATE_TO_DYNAMIC_ESTAR_MAIN_SUM_BOUND
  SOURCE_OBJECT: prolateCombination_selectedFerrersPreAnchorPair
  SOURCE_SCALE: selectedFerrersLemma73SourceScale
  TARGET_OBJECT: four_mul_explicitCCMLimitH
  SOURCE_WINDOW: sourceWindow_selectedFerrersPaperLambda
  MAIN_COUNT_FORMULA: floor_selectedFerrersPaperLambda_div_u
  DILATION_INDEX_FORMULA: n_plus_one
  INCLUDED_POINT_CERTIFICATE: every_n_lt_mainCount_has_(n_plus_one)_mul_u_in_closed_source_window
  TERM_RATE_SUPPLIER: selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
  CARDINALITY_FACTOR_PAID_EXACTLY: true
  OUTPUT_BOUND: C_div_selectedFerrersPaperLambda_mul_sqrt_u
  STATIC_K_PLUS_TWO_COUNT_USED: false
  FITTED_CONSTANT: false
  FULL_ESTAR_DIFFERENCE_CLAIMED: false
  TARGET_BEYOND_WINDOW_TAIL_INCLUDED: false
  MELLIN_INTEGRATION_PERFORMED: false
  NEW_ANALYTIC_INPUT: none
  C04_SOURCE_SUPPORT_VS_TARGET_SUPPORT_AUDIT: PASS
  C09_DYNAMIC_CUTOFF_PRECOMMITTED_BY_SUPPORT_AUDIT: PASS
  C10_EXACT_SOURCE_AND_TARGET_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_DYNAMIC_FINITE_MAIN_SUM_ERROR_BOUND: true
  PROVES_FULL_SOURCE_ESTAR_MINUS_TARGET_ESTAR_BOUND: false
  PROVES_EXPLICIT_TARGET_TAIL_BOUND: false
  PROVES_MELLIN_ERROR: false
  PROVES_QUARTER_MELLIN_IDENTITY: false
  PROVES_CLOSED_SUBSTRIP_CONVERGENCE: false
  PROVES_CCM_LEMMA73_PORT_INHABITANT: false
  PROVES_MEIXNER_SCHAEFKE_SATZ9: false
  PROVES_FUCHS_THEOREM_1: false
  PROVES_RH: false
  UPSTREAM_HMODE_AND_HCHI_REMAIN_EXPLICIT_INPUTS: true

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
  P_L73_3A_1:
    claim: L73_3_closes_by_finite_sum_triangle_inequality_and_floor_count_without_new_analysis
    fate: CONFIRMED
  P_L73_3A_2:
    claim: sharp_C_div_lambda_mul_sqrt_u_bound_is_available_from_F72_6_lambda_inverse_squared_rate
    fate: CONFIRMED
  P_L73_3A_3:
    claim: no_target_tail_or_Mellin_integration_is_needed_in_L73_3
    fate: CONFIRMED
  P_L73_4_EXPLICIT_TARGET_TAIL_REQUIRED:
    claim: literal_zero_extended_source_requires_an_explicit_noncompact_target_tail_term
    fate: CONFIRMED_AS_REQUIRED_NEXT_TERM_NOT_YET_PROVED
  LIKELIEST_FAILURE:
    predicted: NAT_FLOOR_CAST_OR_FINSET_RANGE_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: DEAD_RING_AFTER_FIELD_SIMP_CLOSED_GOAL
  RETROACTIVE_REPAIR: false

L73_4_ADJUDICATION:
  STATUS: LEAN_READY_SOURCE_SUPPORT_REPAIR
  CHARACTER: EXACT_FULL_ESTAR_ERROR_DECOMPOSITION_PLUS_MOVING_THRESHOLD_TARGET_TAIL_BOUND
  NEW_EXTERNAL_INPUT: none
  EXACT_SOURCE_PACKET: prolateCombination_selectedFerrersPreAnchorPair
  EXACT_TARGET_PACKET: four_mul_explicitCCMLimitH
  EXACT_DYNAMIC_CUTOFF: selectedFerrersEStarMainCount
  REQUIRED_TAIL_INDEX: mainCount_plus_n_plus_one
  REQUIRED_FULL_ERROR_IDENTITY: full_source_Estar_error_eq_main_error_sub_target_tail
  REQUIRED_TAIL_RATE: C_div_selectedFerrersPaperLambda_mul_sqrt_u
  DECAY_MECHANISM: polynomial_gaussian_is_O_of_x_inverse_four
  SERIES_MECHANISM: positive_integer_inverse_square_summability
  EXPONENTIAL_GAUSSIAN_TAIL_ESTIMATE_REQUIRED: false
  EXISTING_PRIVATE_SOURCE_FACT:
    path: Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean
    fact: explicitCCMLimitH_decay
    visibility: private
    permitted_repair: local_source_duplication_or_stronger_local_inverse_four_decay_proof
  TARGET_TAIL_AS_HYPOTHESIS_ALLOWED: false
  FULL_ERROR_AS_HYPOTHESIS_ALLOWED: false
  MELLIN_INTEGRATION_ALLOWED_HERE: false
  CLOSES:
    - EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL
    - SELECTED_FERRERS_FULL_ESTAR_POINTWISE_ERROR_DECOMPOSITION
  OPENS: []

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersEStarWindowMainError
    - Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
  PUBLIC_DEFINITIONS:
    - selectedFerrersExplicitTargetTail
    - selectedFerrersFullEStarError
  PUBLIC_THEOREMS:
    - selectedFerrersFullEStarError_eq_main_sub_targetTail
    - selectedFerrersExplicitTargetTail_bound
  REQUIRED_PRIVATE_PLANT: dynamicMainCount_does_not_cover_noncompact_target_plant
  CLOSES:
    - EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL
    - SELECTED_FERRERS_FULL_ESTAR_POINTWISE_ERROR_DECOMPOSITION
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN

CLOSES:
  - L73_3_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - SELECTED_FERRERS_ESTAR_FINITE_SUM_ERROR
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_EXACT_MAIN_MINUS_TAIL_SPLIT_AND_C_DIV_LAMBDA_SQRT_U_TARGET_TAIL_BOUND

REGISTERED_PREDICTIONS:
  P_L73_4_1:
    claim: exact_full_error_split_closes_from_literal_source_support_and_tsum_prefix_tail_reindexing
    probability: 0.86
  P_L73_4_2:
    claim: inverse_four_polynomial_gaussian_decay_plus_inverse_square_summability_gives_C_div_lambda_sqrt_u_without_exponential_tail_machinery
    probability: 0.94
  P_L73_4_3:
    claim: no_new_paper_input_or_numeric_bound_is_needed
    probability: 0.99
  LIKELIEST_FAILURE: TSUM_PNAT_NAT_REINDEX_OR_FLOOR_TAIL_SPLIT_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
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

### 1. Semantic admission of L73.3

The theorem controls exactly the finite **main** part of the starred sum.  For

\[
\lambda_k=\operatorname{selectedFerrersPaperLambda}(k),
\qquad
u\in[\lambda_k^{-1},\lambda_k],
\]

it uses

\[
M_k(u)=\left\lfloor\frac{\lambda_k}{u}\right\rfloor
\]

and the positive dilation indices `n+1`, `n < M_k(u)`.  Every included point
satisfies

\[
0<(n+1)u\le\lambda_k,
\]

so the exact F72.6 pointwise estimate applies to the literal selected packet and
the literal target `4 * explicitCCMLimitH`.  The finite-sum triangle inequality
then pays the full factor `M_k(u)` and gives

\[
\left\|\mathcal E^{\rm main}_k(u)\right\|
\le
\sqrt u\,M_k(u)\frac{C}{\lambda_k^2}
\le
\frac{C}{\lambda_k\sqrt u}.
\]

No static `k+2` count is substituted.  Near `u=lambda_k`, the dynamic count is
one; a static count would overpay by order `lambda_k^2` and destroy the useful
`u`-dependence. `[COFINAL_FAMILY][LEAN]` **[C09]**

The theorem uses the same selected pair, the same source scale and the same
factor-four target as F72.6.  It does not replace the source packet by a nearby
function or the target by a compactly supported surrogate. `[COFINAL_FAMILY][LEAN]`
**[C10]**

The private plant is a valid cardinality falsifier: four unit summands have norm
four, not one.  Thus the proof cannot silently reuse a one-term error bound for
the whole comb.

### 2. Scope boundary

The selected Ferrers packet is zero outside `[-lambda_k,lambda_k]`.  The target

\[
h(x)=\frac\pi2 x^2(2\pi x^2-3)e^{-\pi x^2}
\]

is a noncompact polynomial-Gaussian.  Therefore the full pointwise difference is
not the L73.3 main error alone.  With

\[
T_k(u)=
\sqrt u\sum_{r=M_k(u)+1}^{\infty}4h(ru),
\]

one must prove the exact identity

\[
\boxed{
 a_kE_\star(q_k)(u)-4E_\star(h)(u)
 =\mathcal E^{\rm main}_k(u)-T_k(u).
}
\]

This is a **C04** support-category distinction.  The source and target are
compared on the same coordinates, but one is compactly supported and the other
is not.  Dropping `T_k` would be a semantic error, not a loose estimate.
`[ABSTRACT][LEAN]` **[C04]**

Accordingly L73.3 is admitted only as the dynamic main-sum theorem.  It proves no
claim about the full `E_star` difference, Mellin transforms or closed-substrip
convergence.

## FINAL PROPOSAL

### Exact L73.4 definitions

Create:

```lean
noncomputable def selectedFerrersExplicitTargetTail
    (k : ℕ) (u : ℝ) : ℂ :=
  ((Real.sqrt u : ℝ) : ℂ) *
    ∑' n : ℕ,
      (4 : ℂ) * explicitCCMLimitH
        ((((selectedFerrersEStarMainCount k u + n + 1 : ℕ) : ℝ) * u))
```

Harmless cast-normal-form changes are allowed.  The index
`mainCount + n + 1`, the factor four and the literal target are fixed.

Also define:

```lean
noncomputable def selectedFerrersFullEStarError
    (k : ℕ) (u : ℝ) : ℂ :=
  selectedFerrersLemma73SourceScale k *
      E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u -
    (4 : ℂ) * E_star explicitCCMLimitH u
```

### Exact split theorem

```lean
theorem selectedFerrersFullEStarError_eq_main_sub_targetTail
    (k : ℕ) {u : ℝ}
    (hu : u ∈ sourceWindow (selectedFerrersPaperLambda k)) :
    selectedFerrersFullEStarError k u =
      selectedFerrersEStarWindowMainError k u -
        selectedFerrersExplicitTargetTail k u
```

The proof must use the literal support theorem for
`prolateCombination (selectedFerrersPreAnchorPair k)`.  For a positive integer
`r > floor(lambda_k/u)`, prove `r*u > lambda_k`, hence the source term is zero.
Then split and reindex the absolutely summable target series.  Do not accept the
identity as a hypothesis.

### Exact tail bound

```lean
theorem selectedFerrersExplicitTargetTail_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
          ‖selectedFerrersExplicitTargetTail k u‖ ≤
            C / (selectedFerrersPaperLambda k * Real.sqrt u)
```

A full Gaussian-tail theorem is unnecessary.  Prove locally that

\[
\|h(x)\|\le A x^{-4}
\]

for all sufficiently large positive `x`.  The upstream file already proves the
same polynomial-Gaussian mechanism privately at inverse-square order; local
duplication at inverse-four order is permitted because the private theorem is
not importable.

For

\[
r=M_k(u)+n+1,
\]

we have

\[
ru>\lambda_k,
\qquad r\ge n+1.
\]

Hence

\[
(ru)^{-4}
\le
\lambda_k^{-2}u^{-2}(n+1)^{-2}.
\]

Let

\[
Z_2=\sum_{n\ge0}(n+1)^{-2}<\infty.
\]

After multiplying by `4 * sqrt u`, obtain

\[
\|T_k(u)\|
\le
\frac{4AZ_2}{\lambda_k^2u^{3/2}}
\le
\frac{4AZ_2}{\lambda_k\sqrt u},
\]

because `u >= lambda_k^{-1}`.  This gives the required unit without numerical
constants or exponential estimates. `[COFINAL_FAMILY][LEAN]`

### Required plant

```lean
private theorem dynamicMainCount_does_not_cover_noncompact_target_plant :
    let t : ℕ → ℂ := fun n => if n = 2 then 1 else 0
    (∑ n in Finset.range 1, t (n + 1)) = 0 ∧
      (∑ n in Finset.range 2, t (n + 1)) = 1 := by
  norm_num
```

Equivalent finite syntax is allowed.  The plant must show that a target term
strictly beyond the dynamic source count is invisible to the main sum.

## STRONGEST ATTACK

A reviewer may claim that the Gaussian target tail is negligible and may be
ignored before Mellin integration.  Negligibility is not equality.  The source
packet is literally zero-extended, while `explicitCCMLimitH` is not compactly
supported.  Even an exponentially tiny omitted term changes the exact full
`E_star` error and invalidates the later decomposition unless it is named and
bounded.  This is exactly the source-support mismatch predicted in the original
floor map. `[ABSTRACT][LEAN]` **[C04][C10]**

A second objection is that an inverse-square pointwise decay should suffice.
It does, but proving the sharp moving-threshold series bound then requires a
quantitative shifted zeta-tail inequality.  Inverse-four decay plus ordinary
inverse-square summability gives the same final `C/(lambda*sqrt u)` unit with a
simpler source contract.  The representation is changed to reduce Lean cost,
not to weaken the conclusion.

## CODEX DIRECTIVE

```text
TASK: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the Proshka verdict commit returned by this write;
  run `git rev-parse HEAD` immediately before editing.

CREATE EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean

  docs/routeB_bus/
    LINUX_SOURCE_RECORD_REQ_V_L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_2026-08-23.md

DIRECT IMPORTS:
  Q3.Proofs.RouteB.G6N1SelectedFerrersEStarWindowMainError
  Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier

PUBLIC SURFACE:
  selectedFerrersExplicitTargetTail
  selectedFerrersFullEStarError
  selectedFerrersFullEStarError_eq_main_sub_targetTail
  selectedFerrersExplicitTargetTail_bound

REQUIRED PLANT:
  dynamicMainCount_does_not_cover_noncompact_target_plant

PROOF ROUTE:
  1. Run `./ask.sh` for all four public names and moving-threshold target tail.
  2. Define the exact shifted target tail with index M+n+1 and factor four.
  3. Prove absolute summability from a local inverse-four polynomial-Gaussian bound.
  4. Prove the exact source dynamic truncation from literal support and lambda equality.
  5. Split/reindex the target tsum and prove the full-error identity.
  6. Bound every tail term using ru>lambda and r>=n+1.
  7. Sum against the ordinary inverse-square series.
  8. Use lambda*u>=1 to obtain C/(lambda*sqrt u).
  9. Print axioms of both public theorems.

FORBIDDEN:
  - treating explicitCCMLimitH as compactly supported;
  - claiming full E_star error equals the L73.3 main error;
  - omitting or duplicating factor four;
  - using a static k+2 target cutoff;
  - adding target-tail decay as a hypothesis;
  - adding the full-error split as a hypothesis;
  - fitting a numerical constant;
  - Mellin integration;
  - bundling L73.5 or L73.6;
  - editing L73.3 or upstream F72 files;
  - paper axiom;
  - sorry;
  - admit;
  - typed hole;
  - theorem weakening.

SUCCESS:
  L73_4_EXPLICIT_TARGET_SUPPORT_TAIL_LEAN

FAILURE:
  L73_4_TSUM_REINDEX_OR_MOVING_THRESHOLD_DECAY_GAP

NEXT AFTER SEPARATE SEMANTIC ADMISSION ONLY:
  L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
```

### Gate

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean

lake build \
  Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
```

Expected for both public theorems:

```text
[propext, Classical.choice, Quot.sound]
```

## META CLOSEOUT

**What became smaller?**

The full Lemma-7.3 pointwise source/target error is now decomposed into exactly
two named terms: the kernel-proved dynamic main error and one explicit target
tail.

**What was killed?**

- static `k+2` counting near the upper source-window edge;
- the one-term-to-whole-sum shortcut;
- the claim that L73.3 already controls the full `E_star` difference;
- the idea that an exponentially small but unnamed target tail may be omitted.

**What must not be tried again?**

Do not hide the support mismatch inside prose or postpone the exact identity
until Mellin integration.  The pointwise full-error split must be kernel-visible.

**Current smallest named gap:**

```text
L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
```

**Next cheapest decisive test:**

Compile the exact `main - tail` identity before optimizing the decay proof.  If
that identity fails, the object decomposition is wrong; no tail estimate can
repair it.

**Fate of prior registered predictions:**

```text
P_L73_3A_1: CONFIRMED
P_L73_3A_2: CONFIRMED
P_L73_3A_3: CONFIRMED
P_L73_4_EXPLICIT_TARGET_TAIL_REQUIRED:
  CONFIRMED AS A REQUIRED OPEN TERM
RETROACTIVE_REPAIR: false
```

**Memory entry:**

```yaml
iteration:
  target: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_4_EXPLICIT_TARGET_SUPPORT_TAIL
  invariant_learned: compactly_supported_source_and_noncompact_Gaussian_target_require_an_exact_named_tail
  forbidden_future_move: identify_dynamic_main_error_with_full_Estar_error
  next_decisive_test: exact_main_minus_tail_tsum_split
  progress_class: PROOF_PROGRESS
  route_score: 5
```

**Route B:** `CHALLENGER / NOT_RH`  
**Bus 010:** `VOID`  
**Goal 055:** `HOLD`  
**Aristotle:** not authorized  
**Route promotion / RH claim:** none.
