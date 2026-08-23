# STATUS: PROVED — L73.7 SEMANTICALLY ADMITTED; CONDITIONAL L73.8 PRE-ANCHOR PORT CONSTRUCTOR AUTHORIZED
```yaml
PRIMARY: ADMIT_L73_7_AND_AUTHORIZE_L73_8_SELECTED_FERRERS_PREANCHOR_PORT_CONSTRUCTOR
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 4ac54e4f78040bc0386dde861bb0075b0589877a
  SOURCE_COMMIT: 4ac54e4f78040bc0386dde861bb0075b0589877a
  ACTUAL_SOURCE_COMMIT_PARENT: 4c8b995ab2fe44a2c6486a4dfdbbf84fdb3451ba
  CLAIMED_SOURCE_RECORD_BASE_HEAD: 4c8b995ab2fe44a2c6486a4dfdbbf84fdb3451ba
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean
  LEAN_GIT_BLOB: 43c2d6a1902b84b4bea5861d2be473fa52d7eb32
  LEAN_SHA256_REPORTED: 8ee76ce62560e19a3f4c3ada79d8d1f16c1f7603c72a7b052de933c0bea89cbd
  LEAN_LINES_REPORTED: 1052
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 4d20c568399dd5859f5020cc5d809e62e2b13421
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7853_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
  PUBLIC_THEOREM:
    - Q3.RouteB.D0Pstar.selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
  EXACT_SOURCE_PAIR: selectedFerrersPreAnchorPair
  EXACT_SOURCE_INDEX: selectedFerrersPreAnchorIndex
  EXACT_SCHEDULE: m_equals_N_equals_k_plus_2
  EXACT_SOURCE_SCALE: selectedFerrersLemma73SourceScale
  EXACT_SOURCE_TRANSFORM: preAnchorGwinTransformCoordinate
  EXACT_TARGET: centeredXi
  EXACT_MELLIN_COORDINATE: minus_I_mul_z
  EXACT_FACTOR_FOUR_TARGET: E_star_of_four_mul_explicitCCMLimitH
  DECISIVE_IDENTITY:
    source_minus_target: sourceScale_mul_Gwin_minus_centeredXi
    equals: window_Mellin_of_literal_full_error_minus_literal_factor_four_outer_tail
    holds_for_every_k_and_every_z_in_open_strip: true
    new_hypothesis_required: false
  SOURCE_WINDOW_INTEGRABILITY:
    proved: true
    mechanism: literal_pair_support_plus_finite_dilate_sum_plus_Bochner_integrability_fields
    static_surrogate_used: false
  TARGET_MELLIN_CONVERGENCE:
    proved_locally: true
    assumed_as_hypothesis: false
  FULL_POINTWISE_ERROR:
    source: L73_3_plus_L73_4_exact_split
    unit: one_div_lambda_mul_sqrt_u
  CLOSED_SUBSTRIP_RATE: >-
    C * (lambda^(-1/2 + sigma) / (sigma + 1/2)
         + lambda^(-1) / (1/2 - sigma))
  RATE_TENDS_TO_ZERO_FOR_FIXED_SIGMA_LT_ONE_HALF: true
  WHOLE_OPEN_STRIP_SOURCE_CONVERGENCE_CLAIMED: false
  BOUNDARY_MARGIN_LOAD_BEARING: true
  FITTED_CONSTANT: false
  NEW_PAPER_INPUT: none
  C01_LOCATION_AND_BOUNDARY_MARGIN_AUDIT: PASS
  C04_EXACT_OBJECT_DOMAIN_AND_UNIT_AUDIT: PASS
  C09_SCHEDULE_AND_SIGMA_PRECOMMIT_AUDIT: PASS
  C10_LITERAL_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

CONDITIONALITY_LOCK:
  MODE_RATE_INPUT_PROVED_HERE: false
  CHI_RATE_INPUT_PROVED_HERE: false
  SATZ9_INPUT_PROVED_HERE: false
  FUCHS_INPUT_PROVED_HERE: false
  CURRENT_RESULT_IS_CONDITIONAL_ON_EXPLICIT_HMODE_AND_HCHI: true
  UNCONDITIONAL_CCMLemma73PreAnchorPort_INHABITANT_CLAIM_AUTHORIZED: false
  CONDITIONAL_PORT_CONSTRUCTOR_FROM_EXISTING_RATE_INPUTS_AUTHORIZED: true
  RATE_INPUTS_MAY_BE_HIDDEN_IN_STRUCTURE_OR_AXIOM: false

SCOPE_GUARD:
  PROVES_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE: true
  PROVES_EXACT_SOURCE_MINUS_TARGET_SPLIT: true
  PROVES_WINDOW_MELLIN_RATE: true
  PROVES_TARGET_OUTER_TAIL_RATE: false
  CONSUMES_TARGET_OUTER_TAIL_RATE_FROM_L73_6: true
  PROVES_MODE_OR_CHI_RATES: false
  PROVES_UNCONDITIONAL_PREANCHOR_PORT: false
  PROVES_SELECTED_COFINAL_SOURCE_SHELL: false
  PROVES_THEOREM510_REAL_ZERO_BRIDGE: false
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
  P_L73_7_1:
    claim: L73_3_plus_L73_4_give_full_pointwise_error_with_same_one_div_lambda_sqrt_u_unit
    fate: CONFIRMED
  P_L73_7_2:
    claim: closed_substrip_power_integration_gives_explicit_two_term_rate_tending_to_zero
    fate: CONFIRMED
  P_L73_7_3:
    claim: main_friction_is_Gwin_window_crosswalk_and_integrability_normal_forms_not_new_mathematics
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: GWIN_IOO_ICC_ENDPOINT_OR_MELLIN_INTEGRABLE_NORMAL_FORM
    fate: PARTIALLY_OBSERVED
    observed: Ioo_Icc_endpoint_layer_passed_directly_integrability_and_rpow_normal_forms_required_repairs
  FIRST_GATE_WITHOUT_REPAIR: false
  REPAIR_ROUNDS_REPORTED: 6
  RETROACTIVE_REPAIR: false

L73_8_ADJUDICATION:
  STATUS: AUTHORIZED_WITH_CONDITIONALITY_REPAIR
  CHARACTER: STRICT_TOPOLOGICAL_AND_STRUCTURE_ASSEMBLY
  UNREPAIRED_UNCONDITIONAL_NAME: selectedFerrersCCMLemma73PreAnchorPort
  UNREPAIRED_UNCONDITIONAL_SHAPE_AUTHORIZED: false
  REPAIRED_PUBLIC_NAME: selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
  REPAIRED_OUTPUT: CCMLemma73PreAnchorPort_selectedFerrersPreAnchorData
  EXISTING_INPUTS_ONLY:
    - explicit_mode_zero_and_mode_four_rates
    - explicit_chi_zero_and_chi_two_rates
  NEW_ANALYTIC_INPUT: none
  SOURCE_SCALE_FIELD: selectedFerrersLemma73SourceScale
  SOURCE_SCALE_NONZERO_FIELD: selectedFerrersLemma73SourceScale_ne
  CONVERGENCE_FIELD:
    source: L73_7_closed_substrip_theorem
    promotion: every_compact_subset_of_open_strip_is_contained_in_one_strict_closed_substrip
    helper: compact_subset_centeredCriticalStrip_contained_in_closed_substrip
  EXACT_DATA_RECORD: selectedFerrersPreAnchorData
  INDEX_AND_PAIR_REWRITES:
    - selectedFerrersPreAnchorData_index
    - selectedFerrersPreAnchorData_pair
  MAY_CALL_SELECTED_PROLATE_COFINAL_SOURCE_DATA_CONSTRUCTOR: not_in_this_floor
  MAY_BUNDLE_LATER_ROOF_OR_H2B: false
  MAIN_FORMAL_RISK: TENDSTO_LOCALLY_UNIFORMLY_ON_COMPACT_RESTRICTION_OR_STRUCTURE_FIELD_REWRITE_NORMAL_FORM

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence
    - Q3.Proofs.RouteB.D0CriticalStripCompactBound
  PUBLIC_SURFACE:
    - selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
  REQUIRED_PRIVATE_PLANT: openStrip_not_contained_in_fixed_closedSubstrip_plant
  CLOSES:
    - CCM_LEMMA_7_3_PREANCHOR_PORT_FROM_MODE_AND_CHI_RATES
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: SELECTED_FERRERS_COFINAL_SOURCE_SHELL_BIND_OR_RETURN_TO_H2A_FRONT

CLOSES:
  - L73_7_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - CCM_LEMMA_7_3_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE
OPENS: []

NEXT_LOAD_BEARING_GAP: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL
NEXT_CHEAPEST_DECISIVE_TEST: PROMOTE_ONE_L73_7_CLOSED_SUBSTRIP_THEOREM_TO_COMPACT_LOCAL_CONVERGENCE_BEFORE_FILLING_THE_STRUCTURE_RECORD

REGISTERED_PREDICTIONS:
  P_L73_8_1:
    claim: compact_closed_substrip_helper_plus_L73_7_closes_local_uniform_convergence_without_new_analysis
    probability: 0.98
  P_L73_8_2:
    claim: selectedFerrersPreAnchorData_index_and_pair_exports_make_the_structure_family_definitionally_match_L73_7
    probability: 0.995
  P_L73_8_3:
    claim: sourceScale_and_nonvanishing_fields_are_direct_existing_suppliers
    probability: 0.999
  LIKELIEST_FAILURE: TENDSTO_LOCALLY_UNIFORMLY_ON_COMPACT_RESTRICTION_OR_STRUCTURE_REWRITE_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL_LEAN
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

### Why L73.7 is semantically sound

The public theorem concerns exactly the selected Ferrers source object and exactly the production target:

\[
F_k(z)=s_k\,Gwin\!\left(
  \operatorname{prolateCombination}(P_k),
  \lambda_k,
  -iz
\right),
\qquad
F_k\to\operatorname{centeredXi}
\]

uniformly on every fixed set \(|\Im z|\le\sigma<1/2\), under the explicit mode and chi rate inputs. The source pair is `selectedFerrersPreAnchorPair`; the schedule is the precommitted `selectedFerrersPreAnchorIndex`; the scale is `selectedFerrersLemma73SourceScale`; no neighboring source family is substituted. `[COFINAL_FAMILY][LEAN]` **[C04][C09][C10]**

The proof establishes the exact identity

\[
F_k(z)-\Xi(z)
=
\int_{\lambda_k^{-1}}^{\lambda_k}
  u^{-iz-1}\operatorname{FullError}_k(u)\,du
-
\operatorname{OuterTail}_k(z)
\]

for every `k` and every `z` in the open strip. The source-window integral is legal because the literal selected packet has compact support and hence only finitely many active dilations on the window; the target Mellin convergence is re-proved from two-sided decay instead of being inserted as a hypothesis. `[COFINAL_FAMILY][LEAN]`

The pointwise error satisfies

\[
\|\operatorname{FullError}_k(u)\|
\le
\frac{C}{\lambda_k\sqrt u}.
\]

Splitting at \(u=1\) and using \(|\Im z|\le\sigma\) yields

\[
\left\|
\int_{\lambda_k^{-1}}^{\lambda_k}
  u^{-iz-1}\operatorname{FullError}_k(u)\,du
\right\|
\le
C\left(
  \frac{\lambda_k^{-1/2+\sigma}}{\sigma+1/2}
  +
  \frac{\lambda_k^{-1}}{1/2-\sigma}
\right).
\]

The public L73.6 tail tends to zero uniformly on the larger open strip, so the sum tends to zero uniformly on the fixed closed substrip. No numerical estimate occupies a cofinal quantifier. `[COFINAL_FAMILY][LEAN]`

The boundary plant is genuinely load-bearing. At \(\Im z=-1/2\), the lower-window model becomes

\[
\lambda^{-1}\int_{\lambda^{-1}}^1u^{-2}\,du
=1-\lambda^{-1},
\]

which does not tend to zero. Thus the result cannot be promoted to one uniform theorem on the whole open strip from the present budget. `[COFINAL_FAMILY][LEAN]` **[C01][C04]**

### Scope correction for L73.8

The current tree proves L73.7 only after receiving explicit `hmode` and `hchi` rate hypotheses. Therefore the unqualified declaration

```lean
selectedFerrersCCMLemma73PreAnchorPort :
  CCMLemma73PreAnchorPort selectedFerrersPreAnchorData
```

would overstate the result unless the external Satz-9 and Fuchs inputs are already discharged elsewhere. A structure field is not a place to hide unresolved analytic hypotheses. `[COFINAL_FAMILY][PAPER]` **[C04][C10]**

The weakest correct next declaration is therefore a constructor:

```lean
selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
```

with the exact existing `hmode` and `hchi` premises. Once those premises are supplied, the result is an actual inhabitant of

```lean
CCMLemma73PreAnchorPort selectedFerrersPreAnchorData.
```

No additional analytic assumption is introduced.

## FINAL PROPOSAL

### Files

```text
Lean:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean

Source record:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_2026-08-23.md
```

Use the verdict commit as `BASE_HEAD`, and take a live snapshot immediately before editing:

```bash
git rev-parse HEAD
```

### Exactly two direct imports

```lean
import Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence
import Q3.Proofs.RouteB.D0CriticalStripCompactBound
```

### Required private plant

```lean
private theorem openStrip_not_contained_in_fixed_closedSubstrip_plant
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    ∃ z : ℂ, z ∈ centeredCriticalStrip ∧ σ < |z.im| := by
  let y : ℝ := (σ + 1 / 2) / 2
  have hσy : σ < y := by
    dsimp [y]
    linarith
  have hyhalf : y < 1 / 2 := by
    dsimp [y]
    linarith
  have hy0 : 0 ≤ y := le_trans hσ0 hσy.le
  refine ⟨(⟨0, y⟩ : ℂ), ?_, ?_⟩
  · change |y| < 1 / 2
    rw [abs_of_nonneg hy0]
    exact hyhalf
  · change σ < |y|
    rw [abs_of_nonneg hy0]
    exact hσy
```

This plant prevents replacing compact-local promotion by one fixed closed substrip for the entire open strip.

### Exact public constructor

```lean
noncomputable def selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
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
            ((parabolicCylinderD 0
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    CCMLemma73PreAnchorPort selectedFerrersPreAnchorData where
  sourceScale := selectedFerrersLemma73SourceScale
  sourceScale_ne := selectedFerrersLemma73SourceScale_ne
  convergence := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
      isOpen_centeredCriticalStrip]
    intro K hKsub hK
    obtain ⟨σ, hσ0, hσ, hKσ⟩ :=
      compact_subset_centeredCriticalStrip_contained_in_closed_substrip
        hK hKsub
    have hclosed :=
      selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
        σ C0 C4 Cχ hσ0 hσ hC0 hC4 hCχ hmode hχ
    have hKconv : TendstoUniformlyOn
        (fun k z =>
          selectedFerrersLemma73SourceScale k *
            preAnchorGwinTransformCoordinate
              (selectedFerrersPreAnchorIndex k)
              (prolateCombination (selectedFerrersPreAnchorPair k)) z)
        centeredXi Filter.atTop K := by
      rw [Metric.tendstoUniformlyOn_iff] at hclosed ⊢
      intro ε hε
      filter_upwards [hclosed ε hε] with k hk
      intro z hz
      exact hk z (hKσ z hz)
    simpa only [selectedFerrersPreAnchorData_index,
      selectedFerrersPreAnchorData_pair] using hKconv
```

If the exact argument order of the compact-local equivalence differs in the pinned import closure, preserve the theorem statement and use the existing pattern from `MontelCenteredCriticalStrip.lean`; do not weaken the target.

### Proof route

1. Run `ask.sh` for the exact port constructor and compact-substrip helper.
2. Execute the private plant before the constructor.
3. Fill `sourceScale` with the existing source-derived factor-four scale.
4. Fill `sourceScale_ne` from the existing nonvanishing theorem.
5. Expand `TendstoLocallyUniformlyOn` through the compact-subset equivalence.
6. For each compact `K`, obtain one strict closed substrip using the existing compactness theorem.
7. Restrict the L73.7 uniform theorem from that closed substrip to `K`.
8. Rewrite only the exact reducibility exports for `selectedFerrersPreAnchorData.index` and `.pair`.
9. Print axioms of the public constructor.

### Forbidden

```text
unconditional port declaration without hmode/hchi;
adding hmode or hchi as fields of CCMLemma73PreAnchorPort;
adding Satz 9 or Fuchs as an axiom;
choosing one sigma for the whole open strip;
changing selectedFerrersPreAnchorData;
changing selectedFerrersLemma73SourceScale;
changing the selected schedule;
constructing SelectedProlateCofinalSourceData in the same file;
bundling Theorem 5.10, H2a, H2b or an RH roof;
editing L73.3--L73.7;
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
  Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean

lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersCCMLemma73PreAnchorPort

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean
```

Expected profile:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL_LEAN

FAILURE:
  L73_8_COMPACT_LOCAL_PROMOTION_OR_STRUCTURE_REWRITE_GAP
```

## STRONGEST ATTACK

The strongest reviewer objection is not a topology issue. It is the word **inhabitant**.

The source tree currently proves the selected convergence only from explicit mode and chi rate inputs. An unqualified global value of

```lean
CCMLemma73PreAnchorPort selectedFerrersPreAnchorData
```

would silently assert that those analytic inputs already exist. They do not arise from the record type, and compilation of a constructor with hidden axioms would be a C04/C10 object-and-functional error. `[COFINAL_FAMILY][PAPER]` **[C04][C10]**

The repaired conditional constructor is the strongest honest statement available now. It creates the exact port when the existing rate contracts are supplied, without changing the source object, normalization, schedule, target or topology.

## CODEX DIRECTIVE

```text
TARGET:
  L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL_LEAN

WRITE EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean

  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_2026-08-23.md

PUBLIC SURFACE:
  selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates

STOP:
  if compact-local promotion needs a new analytic hypothesis;
  if the exact data index/pair cannot rewrite to the L73.7 family;
  if any nonstandard axiom appears.

DO NOT:
  construct an unconditional port;
  bundle the cofinal source shell;
  start H2a/H2b;
  claim route promotion or RH.
```

## META CLOSEOUT

**What became smaller?**

The analytic convergence front is reduced from a paper narrative to one exact, kernel-green closed-substrip theorem on the literal selected Ferrers family. `[COFINAL_FAMILY][LEAN]`

**What was killed?**

- the claim that the source-window error is uniform on the whole open strip;
- free Mellin-convergence assumptions;
- a hidden source/target substitution;
- an unconditional L73.8 port declaration at the current dependency state.

**What must not be tried again?**

Do not hide unresolved Satz-9/Fuchs rate inputs inside a structure value or an unqualified theorem name. Do not replace compact-local convergence by one global closed-substrip bound.

**Current smallest named gap:**

```text
L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL
```

**Next cheapest decisive test:**

Promote L73.7 to compact-local convergence on one arbitrary compact before assembling the record fields.

**Fate of prior predictions:**

All three L73.7 predictions are confirmed. The predicted normal-form failure was partially observed; no mathematical repair was required. No retroactive repair occurred.

**Memory entry:**

```yaml
iteration:
  target: L73.7 selected Ferrers closed-substrip Mellin convergence
  status: PROGRESS
  failed_strategy: whole_open_strip_source_convergence
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL
  invariant_learned: compact_local_promotion_preserves_exact_source_scale_pair_schedule_and_target
  forbidden_future_move: hide_mode_or_chi_rates_inside_unconditional_port
  next_decisive_test: compact_closed_substrip_promotion_then_structure_assembly
  progress_class: PROOF_PROGRESS
  route_score: 5
```
