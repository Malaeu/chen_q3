# STATUS: PROVED — F72.1A0 SEMANTICALLY ADMITTED; F72.1C EXPLICIT-PAPER-RATE COMPOSITION AUTHORIZED
```yaml
PRIMARY: ADMIT_F72_1A0_AND_AUTHORIZE_F72_1C_EXPLICIT_PAPER_RATE_INPUT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: b6e4697564bae346f01ac47203302f547bda6525
  SOURCE_COMMIT: b6e4697564bae346f01ac47203302f547bda6525
  ACTUAL_SOURCE_COMMIT_PARENT: a0b787dbfa2d75b526973f05263d501036c7eced
  CLAIMED_SOURCE_RECORD_BASE_HEAD: a0b787dbfa2d75b526973f05263d501036c7eced
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean
  LEAN_GIT_BLOB: 02cb54e4040552445a44134ceaea548adcbaa92c
  LEAN_SHA256_REPORTED: 8614db5e2ee487ce41b70e3899ca83533b88f7668e399418e797e2f25005a184
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1A0_CENTER_NORMALIZED_SATZ9_RATE_TRANSFER_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 762b86d742bd3ca7b1902946200e3ba31784a001

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7842_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    centerNormalizedSatz9Rate_of_scaledFixedModeRate:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED
  THEOREM: Q3.RouteB.D0Pstar.centerNormalizedSatz9Rate_of_scaledFixedModeRate
  DIRECTION: SCALED_SOURCE_UNIFORM_RATE_TO_CENTER_NORMALIZED_PHYSICAL_LAMBDA_MINUS_TWO_RATE
  RAW_RATE_IS_EXPLICIT_HYPOTHESIS: true
  RAW_RATE_WITNESS_IS_EXACT_S: true
  RATE_INFERRED_FROM_SATZ9_SOURCE_DATA_TYPE: false
  SOURCE_PROJECT_MODE_USED_AS_SOURCE_WITNESS: false
  SCALE_IS_EXPLICIT_PRECOMMITTED_INPUT: true
  SCALE_CANCELS_FROM_CENTER_NORMALIZATION: true
  DENOMINATOR_GUARD_IS_EXPLICIT: true
  DENOMINATOR_GUARD_IS_LOAD_BEARING: true
  NUMERATOR_IDENTITY_EXACT: true
  TARGET_BOUND_USED_ON_EXACT_TARGET: true
  GAMMA_IDENTITY: gamma_k_eq_2_pi_lambda_k_squared
  RATE_TRANSFER: gamma_inverse_to_lambda_inverse_squared
  OUTPUT_CONSTANT: rawC_mul_targetCenter_plus_targetBound_div_pi_targetCenter
  FITTED_CONSTANT: false
  C04_UNIT_AUDIT: PASS
  C09_PRECOMMIT_AUDIT: PASS
  C10_SAME_FUNCTION_AUDIT: PASS

SCOPE_GUARD:
  CLOSES_CENTER_NORMALIZATION_DENOMINATOR_LEDGER: true
  CLOSES_GAMMA_TO_LAMBDA_SQUARED_TRANSFER: true
  PROVES_RAW_MEIXNER_SCHAEFKE_SATZ9_RATE: false
  PROVES_LITERAL_FIRST_KIND_PROVENANCE: false
  PROVES_SELECTED_PROJECT_SOURCE_BIND: false
  PROVES_SELECTED_FERRERS_DIRECT_RATE: false
  PROVES_F72_1C: false
  PROVES_F72_4_OR_L73_2: false

SOURCE_RECORD_AUDIT:
  SAME_COMMIT_AS_LEAN: true
  BASE_HEAD_CORRECT: true
  BASE_HEAD_PROVENANCE_RECORDED: true
  LEAN_BLOB_AND_SHA256_PRESENT: true
  PUBLIC_SURFACE_COMPLETE: true
  EXPECTED_AXIOM_PROFILES_FIELD_PLURAL: true
  CLOSES_OPENS_PRESENT: true
  VERIFICATION_HANDOFF_PRESENT: true
  NEXT_LOAD_BEARING_GAP_PRESENT: true
  SELF_BLOB_PLACEHOLDER: ACCEPTED_AS_SELF_REFERENCE_WORKAROUND
  STATUS: CLEAN

PREDICTION_FATE:
  P_F72_1A0_1:
    claim: transfer_is_pure_norm_and_field_algebra_without_new_spectral_analysis
    fate: CONFIRMED
  P_F72_1A0_2:
    claim: denominator_guard_is_load_bearing_and_plant_refutes_guard_free_transfer
    fate: CONFIRMED
  P_F72_1A0_3:
    claim: gamma_eq_2pi_lambda_squared_preserves_lambda_minus_two_rate_without_fit
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: COMPLEX_NORM_DIVISION_OR_FILTER_EVENTUALLY_NORMAL_FORM
    fate: CONFIRMED_AS_API_NORMAL_FORM_FRICTION
    observed:
      - Complex.norm_real_required_Real.norm_eq_abs
      - final_field_simp_closed_goal_without_followup_ring
  RETROACTIVE_REPAIR: false

F72_1C_ADJUDICATION:
  STATUS: LEAN_READY_CONDITIONAL_COMPOSITION
  RAW_PAPER_RATE_REMAINS_EXPLICIT: true
  SOURCE_FAMILIES_MUST_BE_EXACT_PROJECT_THETA_TYPED: true
  RAW_RATE_AND_BIND_MUST_USE_SAME_SOURCE_FAMILIES: true
  SELECTED_PROJECT_MODES: selectedFerrersPreAnchorPair_h0_h4
  PROJECT_CENTER_SCALES:
    mode_zero: centerAnchorScalarZero
    mode_four: centerAnchorScalarFour
  CYLINDER_TARGETS:
    mode_zero: parabolicCylinderD_0_projectCylinderArgument
    mode_four: parabolicCylinderD_4_projectCylinderArgument
  TARGET_CENTERS:
    mode_zero: 1
    mode_four: 3
  REQUIRED_CRUDE_GLOBAL_BOUNDS:
    mode_zero: 1
    mode_four: 91
  DENOMINATOR_GUARDS_AT_SELECTED_SCHEDULE: DERIVE_EVENTUALLY_NOT_NEW_INPUT
  OUTPUT: TWO_SELECTED_PROJECT_UNIFORM_LAMBDA_MINUS_TWO_RATES

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
  CHARACTER: SELECTED_PROJECT_SOURCE_BIND_PLUS_CENTER_ANCHOR_PLUS_RATE_TRANSFER
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1CenterNormalizedSatz9RateTransfer
    - Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock
  TARGET_THEOREM: selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
  CLOSES:
    - F72_0B2_SELECTED_CENTER_NORMALIZED_SOURCE_BIND
    - F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_COMPOSITION
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT

CLOSES:
  - F72_1A0_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - F72_1A_CENTER_NORMALIZATION_DENOMINATOR_LEDGER
  - F72_1A_GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_SELECTED_TWO_MODE_COMPOSITION_WITH_SAME_SOURCE_WITNESS

REGISTERED_PREDICTIONS:
  P_F72_1C_1:
    claim: selected_composition_closes_from_existing_project_mode_fields_generic_source_bind_and_F72_1A0
    probability: 0.84
  P_F72_1C_2:
    claim: selected_schedule_derives_denominator_guards_without_new_hypotheses
    probability: 0.95
  P_F72_1C_3:
    claim: global_D0_D4_target_bounds_close_with_crude_constants_1_and_91
    probability: 0.83
  LIKELIEST_FAILURE: PROJECT_MODE_DATA_FLUX_OR_CONTINUOUSON_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
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
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_PAPER_RATE_INPUT
```

## ROUTE MAP

### 1. Semantic admission of F72.1A0

The theorem keeps the external asymptotic outside the kernel theorem. Its input `hraw` is a uniform bound on the explicitly scaled function `scale k * (S k).p`, and the output concerns the center-normalized view of that exact same `S`. No project Ferrers mode is inserted as the source function, and no rate is inferred merely from the name `Satz9SourceData`. `[COFINAL_FAMILY][LEAN]`

For `q = scale k * (S k).p` and `c = targetCenter`, the proof uses the exact identity

\[
c\frac{q(x)}{q(0)}-t(x)
=
\frac{c(q(x)-t(x))+t(x)(c-q(0))}{q(0)}.
\]

The raw bound at the center and `2 eps <= c` give

\[
|q(0)|\ge c-eps\ge c/2>0.
\]

Hence

\[
\left|c\frac{q(x)}{q(0)}-t(x)\right|
\le
\frac{2(c+B)}{c}\,eps.
\]

With `eps = rawC/gamma`, `gamma = 2*pi*lambda^2`, this is exactly

\[
\frac{rawC(c+B)}{\pi c}\,\lambda^{-2}.
\]

No inequality direction is reversed and no fitted scalar appears. `[ABSTRACT][LEAN]`

The private plant is a valid falsifier: raw error at two points can be at most one while division by a center of `1/100` makes the normalized error exceed ten. Thus the denominator guard cannot be deleted as decorative strengthening. `[ABSTRACT][LEAN]` **[C09]**

### 2. Scope boundary

F72.1A0 is not the book theorem. It proves only the algebraic transfer from an explicit raw fixed-mode rate to a center-normalized physical rate. Meixner--Schäfke Satz 9 remains an external paper supplier, and the statement does not prove that an arbitrary `Satz9SourceData` is the literal first-kind representative. `[COFINAL_FAMILY][PAPER]`

The next theorem must therefore keep two source families `S0` and `S4` explicitly in its type. The raw rates, the center-normalized source/project bind, and the project output must all refer to those same families. Replacing them after the rate is inspected is forbidden. **[C09] [C10]**

### 3. Exact F72.1C target

The new file shall prove the following theorem shape, with line wrapping allowed but no mathematical weakening:

```lean
theorem selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
    (S0 : forall k : Nat,
      Satz9SourceData
        (selectedFerrersPaperLambda k)
        (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2)))
    (S4 : forall k : Nat,
      Satz9SourceData
        (selectedFerrersPaperLambda k)
        (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2)))
    (scale0 scale4 : Nat -> Complex)
    (rawC0 rawC4 : Real)
    (hrawC0 : 0 <= rawC0)
    (hrawC4 : 0 <= rawC4)
    (hscale0 : forall k, scale0 k != 0)
    (hscale4 : forall k, scale4 k != 0)
    (hraw0 :
      forall eventually k in Filter.atTop,
        forall x in Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          norm (scale0 k * (S0 k).p x -
            (parabolicCylinderD 0 (projectCylinderArgument x) : Complex)) <=
              rawC0 / selectedFerrersPaperGamma k)
    (hraw4 :
      forall eventually k in Filter.atTop,
        forall x in Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          norm (scale4 k * (S4 k).p x -
            (parabolicCylinderD 4 (projectCylinderArgument x) : Complex)) <=
              rawC4 / selectedFerrersPaperGamma k) :
    forall eventually k in Filter.atTop,
      forall x in Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        norm (centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          (parabolicCylinderD 0 (projectCylinderArgument x) : Complex)) <=
            (2 * rawC0 / Real.pi) /
              (selectedFerrersPaperLambda k) ^ 2 and
        norm (centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          (parabolicCylinderD 4 (projectCylinderArgument x) : Complex)) <=
            ((94 * rawC4) / (3 * Real.pi)) /
              (selectedFerrersPaperLambda k) ^ 2
```

The implementation may use the repository's standard Unicode notation. The theorem must remain universal in the explicit source families and may not choose a different source witness inside the proof.

## FINAL PROPOSAL

Build exactly one selected composition file. Construct private `ProjectModeData` values for the two exact selected Ferrers modes, using their existing derivative, flux, evenness, nonzero-center and closed-window continuity suppliers. Apply `satz9_source_bind_closed` to the same `S0` and `S4` that occur in `hraw0` and `hraw4`. Then apply F72.1A0 twice and rewrite the project center-normalized views through the precommitted center anchors.

Derive the denominator guards from the selected schedule:

\[
\gamma_k=2\pi\lambda_k^2=2\pi(k+2)\to\infty.
\]

They are not new theorem hypotheses.

Prove private global target bounds

\[
|D_0(\sqrt{4\pi}x)|\le1,
\qquad
|D_4(\sqrt{4\pi}x)|\le91.
\]

For the second bound, write `y = projectCylinderArgument x ^ 2 >= 0`, use

\[
y e^{-y/4}\le4,
\qquad
y^2e^{-y/4}\le64,
\]

and then

\[
e^{-y/4}|y^2-6y+3|\le64+24+3=91.
\]

Do not weaken the theorem by adding target-bound or denominator hypotheses if the Mathlib normal form is inconvenient.

Registered prediction: the mathematics is now composition-only. The most likely first failure is construction of the normalized selected `ProjectModeData`, especially the flux derivative or `ContinuousOn (centerNormalized f)` normal form.

## STRONGEST ATTACK

The strongest objection is that `Satz9SourceData` does not encode literal first-kind provenance. Correct. F72.1C is therefore authorized only with explicit raw paper-rate hypotheses on the exact `S0` and `S4` consumed by the bind. The theorem may not infer Satz 9 from the payload type, may not set `S0.p` or `S4.p` equal to the selected Ferrers modes, and may not silently exchange one source witness for another. **[C10]**

A second objection is that a raw uniform estimate does not survive center normalization when the source center becomes small. F72.1A0 closes exactly this defect by deriving a quantitative denominator floor. In the selected schedule the guard is eventually automatic because the target centers are fixed positive numbers and `gamma_k -> infinity`; carrying it as a new external hypothesis would be unnecessary overstrengthening.

Weakest repaired statement if the selected composition fails at project data construction:

```text
F72.1A0 remains semantically admitted.
The raw-to-center-normalized source rate remains proved conditionally.
F72.1C remains open at the exact selected ProjectModeData constructor.
No selected Ferrers cylinder rate is claimed.
```

## CODEX DIRECTIVE

```text
TASK: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD:
  use the full Proshka verdict commit returned by this write,
  verified by `git rev-parse HEAD` immediately before creating the source.

CREATE EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_2026-08-23.md

DIRECT IMPORTS EXACTLY:
  Q3.Proofs.RouteB.G6N1CenterNormalizedSatz9RateTransfer
  Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock

PUBLIC SURFACE EXACTLY:
  selectedFerrers_directCylinderRate_of_explicitSatz9RawRates

PROOF ROUTE:
  1. Run `./ask.sh` for the exact theorem name and the selected `ProjectModeData` constructor before editing.
  2. Construct private mode-zero and mode-four `ProjectModeData` values for the literal selected pair.
  3. Prove private target bounds `D0 <= 1`, `D4 <= 91`.
  4. Derive both eventual denominator guards from `selectedFerrersPaperGamma_eq`.
  5. Apply `centerNormalizedSatz9Rate_of_scaledFixedModeRate` to `S0` and `S4`.
  6. Apply `satz9_source_bind_closed` using the exact selected project data.
  7. Rewrite with `centerAnchorScalarZero` and `centerAnchorScalarFour`.
  8. Simplify only the final constants to `2*rawC0/pi` and `94*rawC4/(3*pi)`.

FORBIDDEN:
  - infer the raw Satz-9 rate from `Satz9SourceData`;
  - define a source payload from the selected project mode;
  - choose a replacement source witness inside the theorem;
  - use different source witnesses for `hraw` and `satz9_source_bind_closed`;
  - add `hdenom` as a theorem input;
  - add D0/D4 target bounds as theorem inputs;
  - change target centers 1 and 3;
  - identify project ordinal 2 with full degree 2;
  - import or edit the selected transport, V3.2, F72.1A0 or center-anchor files;
  - bundle F72.3, F72.4 or L73.2;
  - add a paper axiom, `sorry`, `admit`, typed hole or theorem weakening.

VERIFICATION HANDOFF:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersDirectCylinderRate
  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean

EXPECTED AXIOM PROFILE:
  [propext, Classical.choice, Quot.sound]

SUCCESS CODE:
  F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_CONDITIONAL_LEAN

FAILURE CODE:
  F72_1C_SELECTED_PROJECT_MODE_DATA_OR_TARGET_BOUND_GAP
```

## META CLOSEOUT

**What became smaller?**

The opaque statement "Satz 9 survives center normalization" is now a kernel theorem with an exact denominator ledger and exact physical constant.

**What was killed?**

- dropping the source-center denominator;
- assigning `O(gamma^-1)` directly to the unscaled raw mode;
- fitting a scale after inspecting the error;
- inferring a paper asymptotic from a receiver payload;
- using a project mode as the source witness.

**What must not be tried again?**

Do not collapse the raw book theorem, source/project bind and selected project rate into one untyped citation. Do not add a denominator guard to the selected theorem when the schedule itself proves it eventually.

**Current smallest named gap:**

```text
F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
```

**Next cheapest decisive test:**

Compile the exact two-mode selected composition with the same source witness in the raw rate and the ODE bind.

**Fate of prior registered predictions:**

```text
P_F72_1A0_1: CONFIRMED.
P_F72_1A0_2: CONFIRMED.
P_F72_1A0_3: CONFIRMED.
Predicted API failure class: CONFIRMED AS NONSEMANTIC FRICTION.
No retroactive repair.
```

**Memory entry:**

```yaml
iteration: REQ-2026-08-22-V/F72.1A0
target: center-normalized Satz-9 rate transfer
status: PROGRESS
failed_strategy: raw rate without denominator ledger
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
invariant_learned: raw rate and source/project bind must consume the same source witness
forbidden_future_move: infer paper provenance or rate from Satz9SourceData alone
next_decisive_test: selected two-mode composition compile gate
```
