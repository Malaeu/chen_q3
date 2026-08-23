# STATUS: PROVED — F72.1C SEMANTICALLY ADMITTED; F72.3B EXPLICIT-FUCHS-RATE PORT AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_1C_AND_AUTHORIZE_F72_3B_EXPLICIT_FUCHS_RATE_PORT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: ed3a4a12084008ba5a358040f36c60c5be893892
  SOURCE_COMMIT: ed3a4a12084008ba5a358040f36c60c5be893892
  ACTUAL_SOURCE_COMMIT_PARENT: a3675740207f3e65f6bc67132865125199225825
  CLAIMED_SOURCE_RECORD_BASE_HEAD: a3675740207f3e65f6bc67132865125199225825
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
  LEAN_GIT_BLOB: eee58ca3139abb8b132945ed9e721be6ae61bf29
  LEAN_SHA256_REPORTED: 14f78726cd53c4559eca50d1adcb2d01df021e3e581802a2d0b807a3774f7ee1
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 993fdb501b04f2b0c9cb21e6e41bcee9c4738e36

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7843_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrers_directCylinderRate_of_explicitSatz9RawRates:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_COMPOSITION
  THEOREM: Q3.RouteB.D0Pstar.selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
  DIRECTION: EXPLICIT_RAW_RATES_ON_EXACT_SOURCE_FAMILIES_TO_SELECTED_CENTER_ANCHORED_PROJECT_CYLINDER_RATES
  SOURCE_FAMILIES: [S0, S4]
  SOURCE_FAMILIES_ARE_ARGUMENTS: true
  SOURCE_FAMILIES_CHOSEN_INSIDE_THEOREM: false
  RAW_RATE_AND_BIND_USE_SAME_S0_S4: true
  RAW_RATE_INFERRED_FROM_PAYLOAD_TYPE: false
  PROJECT_MODES_USED_AS_SOURCE_WITNESSES: false
  PROJECT_MODE_DATA_CONSTRUCTED_FROM_EXACT_SELECTED_SOLUTIONS: true
  PROJECT_THETA_ZERO: mode4ClassicalEvenEigenvalue_G_rank0_plus_G
  PROJECT_THETA_FOUR: mode4ClassicalEvenEigenvalue_G_rank2_plus_G
  PROJECT_WINDOW: selectedFerrersPaperLambda
  PROJECT_OUTPUT_MODES: selectedFerrersPreAnchorPair_h0_h4
  PROJECT_OUTPUT_SCALES: [centerAnchorScalarZero, centerAnchorScalarFour]
  SOURCE_PROJECT_BIND: satz9_source_bind_closed
  RAW_TO_NORMALIZED_TRANSFER: centerNormalizedSatz9Rate_of_scaledFixedModeRate
  DENOMINATOR_GUARDS_DERIVED_FROM_SCHEDULE: true
  DENOMINATOR_GUARDS_ADDED_AS_HYPOTHESES: false
  D0_GLOBAL_BOUND: 1
  D4_GLOBAL_BOUND: 91
  OUTPUT_CONSTANT_ZERO: 2_mul_rawC0_div_pi
  OUTPUT_CONSTANT_FOUR: 94_mul_rawC4_div_3pi
  FITTED_CONSTANT: false
  C04_OBJECT_AND_UNIT_AUDIT: PASS
  C09_PRECOMMIT_AUDIT: PASS
  C10_SAME_FUNCTION_AND_FUNCTIONAL_AUDIT: PASS

SCOPE_GUARD:
  PROVES_CONDITIONAL_SELECTED_PROJECT_RATE: true
  PROVES_MEIXNER_SCHAEFKE_SATZ9: false
  PROVES_LITERAL_FIRST_KIND_PS_PROVENANCE: false
  PROVES_RAW_PAPER_RATE: false
  PROVES_EXISTENCE_OF_ONE_COHERENT_SOURCE_FAMILY_WITH_RATE: false
  PROVES_F72_3: false
  PROVES_F72_4: false
  PROVES_L73_2: false
  FORBID_RATE_INFERENCE_FROM_SATZ9_SOURCE_DATA_NAME: true

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
  P_F72_1C_1:
    claim: selected_composition_closes_from_existing_project_mode_fields_generic_source_bind_and_F72_1A0
    fate: CONFIRMED
  P_F72_1C_2:
    claim: selected_schedule_derives_denominator_guards_without_new_hypotheses
    fate: CONFIRMED
  P_F72_1C_3:
    claim: global_D0_D4_target_bounds_close_with_crude_constants_1_and_91
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: PROJECT_MODE_DATA_FLUX_OR_CONTINUOUSON_NORMAL_FORM
    fate: NOT_OBSERVED
    observed: BETA_REDUCTION_OF_TARGET_CENTER_GOAL_ONLY
  RETROACTIVE_REPAIR: false

F72_3B_ADJUDICATION:
  STATUS: LEAN_READY_CONDITIONAL_PAPER_PORT
  PAPER_THEOREM_REPROOF_REQUIRED: false
  RAW_FUCHS_RATE_REMAINS_EXPLICIT: true
  PAPER_OPERATOR: paperFiniteFourierAction
  PROJECT_OPERATOR: finiteFourierAction
  EXACT_INTERTWINING_SUPPLIER: paperFiniteFourierAction_paperRescale_eq_smul_paperRescale_finiteFourierAction
  PAPER_WINDOW: paperWindowRadius_lambda
  PROJECT_WINDOW: selectedFerrersPaperLambda
  WINDOW_IDENTITY: paper_radius_squared_eq_2pi_lambda_squared
  PAPER_EIGENVALUES: [mu_degree_zero, mu_degree_four]
  PAPER_CONCENTRATION_VALUES: [mu0_squared_div_2pi, mu4_squared_div_2pi]
  PROJECT_SCALARS: [selected_pair_chi0, selected_pair_chi2]
  EXACT_SCALAR_MAP: mu_equals_sqrt_2pi_mul_project_chi
  DEGREE_MAP: [paper_degree_0_to_project_chi0, paper_degree_4_to_project_chi2]
  POSITIVE_BRANCH_IS_LOAD_BEARING: true
  PAPER_DEFECT_UNIT: paperWindowRadius_inverse_squared
  PROJECT_OUTPUT_UNIT: selectedFerrersPaperLambda_inverse_squared
  OUTPUT: COMMON_EVENTUAL_PROJECT_CHI_DEFECT_RATE

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
  CHARACTER: EXACT_OPERATOR_EIGENVALUE_CROSSWALK_PLUS_WEAK_RATE_TRANSFER
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1FuchsProjectOperatorIntertwining
    - Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock
  TARGET_THEOREM: selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates
  REQUIRED_PRIVATE_PLANT: fuchs_positive_branch_guard_plant
  CLOSES:
    - F72_3_SELECTED_PROJECT_FUCHS_EIGENVALUE_CROSSWALK
    - F72_3B_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI

CLOSES:
  - F72_1C_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_0B2_SELECTED_CENTER_NORMALIZED_SOURCE_BIND
  - F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_COMPOSITION
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_EXACT_FUCHS_MU_TO_PROJECT_CHI_CROSSWALK_WITH_NEGATIVE_BRANCH_PLANT

REGISTERED_PREDICTIONS:
  P_F72_3B_1:
    claim: exact_mu_equals_sqrt_2pi_mul_chi_closes_by_comparing_the_two_eigenrelations_at_zero_and_cancelling_the_nonzero_rescaled_center
    probability: 0.90
  P_F72_3B_2:
    claim: positive_branch_is_load_bearing_and_the_negative_branch_plant_refutes_any_square_only_port
    probability: 0.99
  P_F72_3B_3:
    claim: paper_a_inverse_square_rate_transfers_to_project_lambda_inverse_square_without_fitted_constants
    probability: 0.95
  LIKELIEST_FAILURE: COMPLEX_SCALAR_CANCELLATION_OR_PAPERRESCALE_ZERO_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
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
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_FUCHS_PAPER_RATE_INPUT
```

## ROUTE MAP

### 1. Why F72.1C is the intended theorem

The theorem keeps all three semantic layers distinct.

The source layer is the pair `S0`, `S4`.  Each family is typed at the exact selected project separation value, but neither is defined from a project Ferrers mode.  The raw hypotheses `hraw0`, `hraw4` concern precisely these source functions. `[COFINAL_FAMILY][LEAN]`

The project layer is the literal selected pair `selectedFerrersPreAnchorPair`.  The private `ProjectModeData` values are built from the exact selected solutions already stored behind that pair: interior derivatives, the physical divergence-form flux equation, evenness, nonzero center and closed-window continuity are all transported from those exact functions.  No neighboring project object is introduced. `[COFINAL_FAMILY][LEAN]`

The bridge layer uses `satz9_source_bind_closed` on the same `S0 k`, `S4 k` that occur in the raw-rate hypotheses.  The resulting center-normalized equality is then rewritten through the already precommitted center anchors.  Therefore the output concerns the exact production modes and exact production scales. `[COFINAL_FAMILY][LEAN]` **[C09] [C10]**

### 2. Exact rates and constants

For mode zero, F72.1A0 has target center `1` and global target bound `1`.  Its exact constant is

\[
\frac{rawC_0(1+1)}{\pi\cdot1}
=\frac{2rawC_0}{\pi}.
\]

For mode four, the target center is `3` and the private global bound is `91`.  Therefore

\[
\frac{rawC_4(3+91)}{\pi\cdot3}
=\frac{94rawC_4}{3\pi}.
\]

The bound `91` is crude but rigorous.  Writing `s=\pi x^2`, the proof bounds

\[
e^{-s}|16s^2-24s+3|
\le16(s^2e^{-s})+24(se^{-s})+3e^{-s}
\le64+24+3.
\]

No sharp special-function estimate is smuggled into the composition. `[ABSTRACT][LEAN]`

The denominator guards are derived from

\[
\gamma_k=2\pi(k+2)\to\infty.
\]

They are not additional analytic inputs. `[COFINAL_FAMILY][LEAN]`

### 3. Scope boundary

`Satz9SourceData` is still a receiver payload, not a provenance certificate.  Therefore F72.1C does not prove that the supplied functions are the literal Meixner--Schäfke first-kind representatives.  Nor does it prove Satz 9.

This is not a defect in the implication proved here.  The raw rate is an explicit hypothesis about the same source family used in the ODE bind.  A caller that chooses the project mode itself as `S0` or `S4` would still have to supply the full raw cylinder estimate for that same function; the theorem does not manufacture it.  The unconditional route must obtain those hypotheses from the independently source-locked paper family. `[COFINAL_FAMILY][PAPER]` **[C10]**

Accordingly, the exact status is:

```text
conditional selected composition: PROVED;
raw paper theorem: EXTERNAL INPUT;
literal source provenance: NOT PROVED HERE;
F72.4 or L73.2: NOT CLAIMED.
```

## F72.3B EXACT TARGET

Create exactly one source file and prove one public theorem.  The repository's Unicode notation and harmless line wrapping are allowed, but the mathematical contract must remain:

```lean
theorem selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates
    (mu0 mu4 : ℕ → ℝ)
    (C0 C4 : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hmu0pos : ∀ k, 0 < mu0 k)
    (hmu4pos : ∀ k, 0 < mu4 k)
    (hFuchsEigen0 :
      ∀ k t, t ∈ Set.Icc
          (-(paperWindowRadius (selectedFerrersPaperLambda k)))
          (paperWindowRadius (selectedFerrersPaperLambda k)) →
        paperFiniteFourierAction
            (paperWindowRadius (selectedFerrersPaperLambda k))
            (paperRescale (selectedFerrersPreAnchorPair k).h0) t =
          (mu0 k : ℂ) *
            paperRescale (selectedFerrersPreAnchorPair k).h0 t)
    (hFuchsEigen4 :
      ∀ k t, t ∈ Set.Icc
          (-(paperWindowRadius (selectedFerrersPaperLambda k)))
          (paperWindowRadius (selectedFerrersPaperLambda k)) →
        paperFiniteFourierAction
            (paperWindowRadius (selectedFerrersPaperLambda k))
            (paperRescale (selectedFerrersPreAnchorPair k).h4) t =
          (mu4 k : ℂ) *
            paperRescale (selectedFerrersPreAnchorPair k).h4 t)
    (hFuchsDefect0 :
      ∀ᶠ k in Filter.atTop,
        |1 - (mu0 k) ^ 2 / (2 * Real.pi)| ≤
          C0 / (paperWindowRadius (selectedFerrersPaperLambda k)) ^ 2)
    (hFuchsDefect4 :
      ∀ᶠ k in Filter.atTop,
        |1 - (mu4 k) ^ 2 / (2 * Real.pi)| ≤
          C4 / (paperWindowRadius (selectedFerrersPaperLambda k)) ^ 2) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2
```

The explicit Fuchs inputs are about the rescaled exact selected project modes.  The theorem may not replace them by a defect hypothesis already written directly on `chi0` or `chi2`.

## REQUIRED PLANT

```lean
private theorem fuchs_positive_branch_guard_plant :
    |1 - ((-1 : ℝ) ^ 2)| = 0 ∧ |1 - (-1 : ℝ)| = 2 := by
  norm_num
```

This plant kills the false square-only implication.  A concentration eigenvalue equal to one is compatible with transform scalar `-1`; the positive Fuchs phase is therefore load-bearing. `[ABSTRACT][LEAN]` **[C04] [C09]**

## PROOF ROUTE

1. Run `./ask.sh` for the exact target, the Fuchs paper eigenrelation, the selected pair center nonvanishing and existing defect-rate suppliers.  Do not invent a duplicate port.

2. At `t=0`, use F72.3A:

\[
\mathcal F_a(Uh)(0)=\sqrt{2\pi}\,U(T_\lambda h)(0).
\]

3. Use the exact selected project finite-Fourier eigenrelations at `x=0` and the external Fuchs eigenrelations at `t=0`.

4. Prove `paperRescale h 0 ≠ 0` from `selectedFerrersCenterZero_ne` / `selectedFerrersCenterFour_ne` and the nonzero rescaling coefficient.  Cancel this exact common value to obtain

\[
\mu_0=\sqrt{2\pi}\,\chi_0,
\qquad
\mu_4=\sqrt{2\pi}\,\chi_2.
\]

5. Use `hmu0pos`, `hmu4pos` and `sqrt(2*pi)>0` to derive the positive project branches.

6. Prove

\[
\frac{\mu_n^2}{2\pi}=\chi_n^2
\]

from the exact square-root identity, not by normalization convention.

7. For `chi>0`, prove

\[
|1-chi|\le|1-chi^2|.
\]

The negative-branch plant explains why this step cannot be omitted.

8. Convert the paper-window rate to the project-window rate using

\[
\operatorname{paperWindowRadius}(\lambda)^2=2\pi\lambda^2
\]

and `2*pi ≥ 1`.  No fitted factor is allowed.

9. Intersect the two eventual events and choose the common constant `Cχ = C0 + C4` or a provably equivalent nonnegative common upper bound.

## FORBIDDEN

```text
define mu_n to be sqrt(2*pi)*chi_n;
replace the full Fuchs eigenrelation by a center-only scalar equation;
assume Lambda_n = chi_n;
assume a = lambda;
identify project chi2 with Fuchs degree 2;
drop hmu0pos or hmu4pos;
feed a defect hypothesis already stated directly on project chi;
fit any constant from numerical agreement;
import F72.1C merely to force a sequential dependency;
bundle F72.4, F72.5 or L73.2;
edit F72.3A, F72.1C or the center-anchor source;
add a paper axiom, sorry, admit, typed hole or theorem weakening.
```

F72.3B is parallel to F72.1C in the mathematical DAG.  Its execution is authorized after this semantic gate, but its source file should import only the two exact suppliers listed in the YAML header.

## VALIDATION

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean

lake build \
  Q3.Proofs.RouteB.G6N1FuchsSelectedEigenvalueDefectRate

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean
```

Expected public axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT_LEAN

FAILURE:
  F72_3B_FUCHS_PROJECT_EIGENVALUE_OR_POSITIVE_BRANCH_GAP
```

## STRONGEST ATTACK

The strongest objection to F72.1C is that the source structure does not enforce paper provenance.  That objection correctly blocks an unconditional Satz-9 claim, but it does not invalidate this conditional composition: the theorem keeps the raw rate as an explicit assumption on the exact same source families used by the uniqueness bind.  No rate is generated from a renamed project function. **[C10]**

The strongest objection to F72.3B is the sign ambiguity.  The concentration value sees `chi^2`; it cannot distinguish `chi` from `-chi`.  Therefore an implementation that proves only the squared crosswalk and then concludes `chi → 1` is wrong.  The explicit positive Fuchs eigenvalue convention and the negative-branch plant are mandatory. **[C04] [C09]**

## META CLOSEOUT

**What became smaller?**

The selected mode-rate front is now reduced to one external source theorem: explicit raw Satz-9 rates on coherent source families.  All project-side normalization, target bounds, denominator control and selected-mode composition are kernel-proved conditionally on that input.

**What was killed?**

- a second denominator hypothesis;
- assumed cylinder target bounds;
- a different source witness for the rate and for the ODE bind;
- fitted center scales;
- the prediction that project flux/continuity construction would be the first failure.

**What must not be tried again?**

Do not infer literal paper provenance from the name `Satz9SourceData`.  Do not infer a positive transform phase from a squared concentration eigenvalue.

**Current smallest named gap?**

```text
F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
```

**Next cheapest decisive test?**

Compile the exact `mu -> chi` crosswalk at `t=0` with the negative-branch plant and explicit paper-window defect inputs.

**Fate of prior registered predictions?**

```text
P_F72_1C_1: CONFIRMED.
P_F72_1C_2: CONFIRMED.
P_F72_1C_3: CONFIRMED.
LIKELIEST_FAILURE: REFUTED; only beta-reduction friction occurred.
No retroactive repair.
```

**Memory entry**

```yaml
iteration:
  target: F72_1C selected Ferrers direct cylinder rate
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
  invariant_learned: raw rate, source-project bind and project output must use the same source family; squared Fuchs concentration data also requires a positive phase lock
  forbidden_future_move: infer paper provenance from payload fields or infer chi-to-plus-one from chi-squared
  next_decisive_test: exact_mu_crosswalk_plus_positive_branch_plant
  progress_class: PROOF_PROGRESS
  route_score: 5
```
