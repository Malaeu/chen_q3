# STATUS: PROVED — SELECTED SATZ9 TRANSPORT SEMANTICALLY ADMITTED; F72.1A NORMALIZATION/RATE TRANSFER AUTHORIZED
```yaml
PRIMARY: ADMIT_SELECTED_SATZ9_TRANSPORT_AND_AUTHORIZE_F72_1A_RATE_TRANSFER
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: d624c2e401c861f9e2d350712d617dd165aec109
  SOURCE_COMMIT: d624c2e401c861f9e2d350712d617dd165aec109
  ACTUAL_SOURCE_COMMIT_PARENT: de86b9bc5d2ca6fa52d08d48e67ea060933e7d31
  CLAIMED_SOURCE_RECORD_BASE_HEAD: f91455e70fc008505b7e6fbd776b609dd5fef2f3
  CLAIMED_BASE_HEAD_IS_ACTUAL_PARENT: false
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedSatz9SourcePackageTransport.lean
  LEAN_GIT_BLOB: 18ebe540a40e9316f5ed8ebbeb40eafdb70a8bc0
  LEAN_SHA256_REPORTED: 4fb9a1356b05a8dd54712e8acaaf1cb01039f4b66538f56e16e1babfb73c97ba
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 68ca6de52bfbf787651334e838e9659e4ffb6b6e

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7856_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedSatz9SourceData_at_projectTheta_degree_zero_four:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED
  THEOREM: Q3.RouteB.selectedSatz9SourceData_at_projectTheta_degree_zero_four
  DIRECTION: SOURCE_EVEN_BRANCH_PAYLOADS_TRANSPORTED_TO_SELECTED_PROJECT_THETA_AT_ORDINALS_ZERO_AND_TWO
  SOURCE_PACKAGE: BookRegularEvenSpectrumEven
  SOURCE_PACKAGE_IS_ARGUMENT: true
  SOURCE_PACKAGE_CHOSEN_INSIDE_THEOREM: false
  SOURCE_EIGENFUNCTION_SUPPLIER: P.evenBranch_regular
  PROJECT_MODE_USED_AS_SOURCE_WITNESS: false
  PROJECT_FINITE_LIMIT_CARRIER_USED_ONLY_FOR_EIGENVALUE_EQUALITY: true
  EIGENVALUE_EQUALITY_SUPPLIER: finiteLimit_selected_theta_equality_degree_zero_four_modular
  PHYSICAL_LIFT_SUPPLIER: regularEvenSpheroidalEigenvalue_physicalSatz9SourceData
  EXACT_WINDOW: selectedFerrersPaperLambda
  EXACT_PARAMETER_IDENTITY: selectedFerrersPaperGamma_sq_eq_jacobiG
  PHYSICAL_THETA_SHIFT: project_carrier_plus_mode4JacobiG
  COMMON_SHIFT_DROPPED: false
  PRECOMMITTED_K: 5_mul_k_plus_2
  PROJECT_ORDINALS: [0, 2]
  SOURCE_FULL_DEGREES_BY_DICTIONARY: [0, 4]
  SPLIT_DEGREE_IDENTIFIED_WITH_SOURCE_DEGREE: false
  C04_OBJECT_AND_UNIT_AUDIT: PASS
  C09_PRECOMMIT_AUDIT: PASS
  C10_SOURCE_FUNCTION_SURROGATE_AUDIT: PASS

SCOPE_GUARD:
  PROVES_SOURCE_RECEIVER_PAYLOAD_AT_PROJECT_THETA: true
  PROVES_LITERAL_PS_FIRST_KIND_PROVENANCE: false
  PROVES_SATZ9_ASYMPTOTIC_RATE: false
  PROVES_SELECTED_PROJECT_MODE_EQUALS_SOURCE_MODE: false
  PROVES_F72_1A: false
  PROVES_F72_1C: false
  DEGREE_TAG_STORED_INSIDE_SATZ9_SOURCE_DATA: false
  DEGREE_PROVENANCE_AVAILABLE_FROM_ORDINAL_AND_DICTIONARY: true
  FORBID_RATE_INFERENCE_FROM_PAYLOAD_TYPE_ALONE: true

SOURCE_RECORD_AUDIT:
  SAME_COMMIT_AS_LEAN: true
  LEAN_BLOB_AND_SHA256_PRESENT: true
  PUBLIC_SURFACE_COMPLETE: true
  EXPECTED_AXIOM_PROFILES_FIELD_PLURAL: true
  CLOSES_OPENS_PRESENT: true
  VERIFICATION_HANDOFF_PRESENT: true
  NEXT_LOAD_BEARING_GAP_PRESENT: true
  SELF_BLOB_PLACEHOLDER: ACCEPTED_AS_SELF_REFERENCE_WORKAROUND
  CLAIMED_BASE_HEAD_CORRECT: false
  FALSE_SCHEMA_REPAIR_FLAG: base_head_now_actual_parent
  ACTUAL_PARENT: de86b9bc5d2ca6fa52d08d48e67ea060933e7d31
  LEAN_DRIFT_BETWEEN_CLAIMED_BASE_AND_ACTUAL_PARENT: false
  STATUS: NONBLOCKING_RECEIPT_DEFECT
  REPAIR_POLICY: DO_NOT_MUTATE_PUSHED_RECORD
  NEXT_RECORD_REQUIREMENTS:
    - RUN_git_rev_parse_HEAD_IMMEDIATELY_BEFORE_THE_SOURCE_COMMIT
    - RECORD_THAT_FULL_SHA_AS_BASE_HEAD
    - DO_NOT_COPY_A_STALE_BASE_HEAD_FROM_THE_DIRECTIVE
    - KEEP_EXPECTED_AXIOM_PROFILES_PLURAL

PREDICTION_FATE:
  P_SELECTED_TRANSPORT_1:
    claim: transport_is_direct_composition_of_V3_2_source_regularity_physical_lift_and_parameter_dictionary
    fate: CONFIRMED
  P_SELECTED_TRANSPORT_2:
    claim: no_project_mode_as_source_and_no_internal_Classical_choose
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: NESTED_NONEMPTY_REWRITE_OR_SELECTED_GAMMA_NORMAL_FORM
    fate: CONFIRMED_AT_REWRITE_NORMAL_FORM_CLASS
    observed: dependent_motive_rewrite_through_P_type_repaired_by_generalize
  P_NEXT_RATE:
    claim: after_selected_transport_the_first_substantive_wall_is_F72_1A_rate_not_more_ordering
    fate: CONFIRMED
  RETROACTIVE_REPAIR: false

F72_1A_ADJUDICATION:
  PAPER_SCOPE: CLOSED
  RAW_SATZ9_MODE_REMAINDER: O_gamma_minus_three_quarters
  SCALED_SATZ9_REMAINDER: O_gamma_minus_one
  PHYSICAL_RATE_AFTER_gamma_eq_2pi_lambda_sq: O_lambda_minus_two
  FULL_UNCONDITIONAL_LEAN_PROOF_FROM_CURRENT_REPO: false
  REASON: THE_BOOK_ASYMPTOTIC_IS_A_PAPER_THEOREM_NOT_A_KERNEL_TERM
  NEW_GLOBAL_PROJECT_AXIOM_AUTHORIZED: false
  FULL_REPROOF_OF_SATZ9_AUTHORIZED: false
  NEXT_KERNEL_SUBFLOOR: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
  NEXT_KERNEL_SUBFLOOR_ROLE:
    - EXACT_DENOMINATOR_LOWER_BOUND_LEDGER
    - CENTER_NORMALIZATION_CANCELLATION
    - GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER
  RAW_FIXED_MODE_RATE_REMAINS: EXPLICIT_PAPER_SUPPLIER

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_AFTER_THIS_VERDICT
  CODE: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
  CHARACTER: SOURCE_ONLY_NORM_DIVISION_AND_UNIT_TRANSFER
  BASE_HEAD_POLICY: USE_THE_PROSHKA_VERDICT_COMMIT_RETURNED_BY_THIS_WRITE
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1A0_CENTER_NORMALIZED_SATZ9_RATE_TRANSFER_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1Satz9SourcePackageInterface
  TARGET_THEOREM: centerNormalizedSatz9Rate_of_scaledFixedModeRate
  REQUIRED_PRIVATE_PLANT: centerNormalization_denominator_guard_plant
  CLOSES:
    - F72_1A_CENTER_NORMALIZATION_DENOMINATOR_LEDGER
    - F72_1A_GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT

CLOSES:
  - SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT_KERNEL_GREEN_SEMANTIC_QUARANTINE
  - W13_7E_SELECTED_THETA_PACKAGE_TRANSPORT
  - SELECTED_SOURCE_PHYSICAL_DATA_AT_PROJECT_THETA
OPENS: []

NEXT_LOAD_BEARING_GAP: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_GENERIC_CENTER_NORMALIZATION_RATE_TRANSFER_WITH_DENOMINATOR_PLANT

REGISTERED_PREDICTIONS:
  P_F72_1A0_1:
    claim: center_normalized_rate_transfer_is_pure_norm_and_field_algebra_with_no_new_spectral_analysis
    probability: 0.88
  P_F72_1A0_2:
    claim: denominator_guard_is_load_bearing_and_the_two_point_plant_will_refute_the_guard_free_statement
    probability: 0.97
  P_F72_1A0_3:
    claim: the_exact_gamma_equals_2pi_lambda_squared_rewrite_preserves_the_lambda_minus_two_rate_without_fitted_constants
    probability: 0.96
  LIKELIEST_FAILURE: COMPLEX_NORM_DIVISION_OR_FILTER_EVENTUALLY_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
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

### 1. Semantic admission of the selected transport

The reviewed theorem compares two genuinely different layers and keeps the
comparison explicit.

The source side is an arbitrary `BookRegularEvenSpectrumEven G`.  Its fields
mention only `RegularEvenSpheroidalEigenvalue`; the theorem does not construct
that package from `mode4ClassicalEvenEigenvalue` and does not choose a package
internally.  For ordinals `0` and `2`, `P.evenBranch_regular` supplies genuine
source eigenfunctions. `[ABSTRACT][LEAN]`

The project side enters only through the already ratified V3.2 scalar identity

```text
mode4ClassicalEvenEigenvalue G 0 = P.evenBranch 0;
mode4ClassicalEvenEigenvalue G 2 = P.evenBranch 2.
```

The physical function is then produced by the source-only lift.  No selected
Ferrers function is assigned to the `p` field of `Satz9SourceData`.  The source
function therefore remains independent of the project mode, and C10 does not
fire. `[COFINAL_FAMILY][LEAN]`

The unit chain is exact:

```text
lambda_k = sqrt(k+2);
gamma_k  = 2*pi*lambda_k^2;
gamma_k^2 = mode4JacobiG(k+2);
theta_phys = Lambda_source + gamma_k^2
           = Lambda_project + mode4JacobiG(k+2).
```

The proof invokes V3.2 before replacing the source value by the project value;
it does not infer equality of separation values from a shared parameter.  This
passes the C04 object/unit audit. `[COFINAL_FAMILY][LEAN]`

The schedule `K=5*(k+2)` is the already committed separation schedule.  It is
not selected after inspecting the source eigenvalue, so the C09 precommit audit
passes. `[COFINAL_FAMILY][LEAN]`

### 2. Strongest attack on the selected transport

The strongest attack is the name `Satz9SourceData` itself:

> Does inhabiting this payload prove that the witness is the literal
> Meixner--Schäfke first-kind mode and therefore inherits Satz 9?

No.  The structure is a receiver payload, not a provenance firewall.  Its
fields carry the ODE, parity, centre nonvanishing and closed-window continuity;
they do not carry a paper degree or an asymptotic estimate.  The transport
therefore proves only the existence of an independently sourced regular-even
physical payload at the selected project theta. `[COFINAL_FAMILY][LEAN]`

This does not kill the theorem.  It kills only the illegal downstream move

```text
Nonempty (Satz9SourceData lambda theta)
  -> Satz 9 rate.
```

The degree labels remain available externally: source ordinal `0` means full
degree `0`, and source ordinal `2` means full degree `4`, by the separately
proved dictionary.  Any rate theorem must carry that degree provenance in its
statement or in its explicit paper-rate premise; it may not infer it from the
payload type. **[C04] [C10]**

### 3. Process finding

The source record claims that its `BASE_HEAD` repair is complete.  Git metadata
contradicts that claim.

```text
recorded BASE_HEAD:
  f91455e70fc008505b7e6fbd776b609dd5fef2f3

actual parent of d624c2e4:
  de86b9bc5d2ca6fa52d08d48e67ea060933e7d31
```

The intermediate commit is the Proshka verdict authorizing this transaction and
changes no Lean source.  The reviewed Lean object and all receipts are exact,
so the defect is nonblocking.  The pushed record remains immutable.  The next
executor must derive `BASE_HEAD` from the live repository immediately before
creating the source commit, rather than copying the stale review head from a
directive. `[ABSTRACT][PAPER]`

### 4. Why F72.1A must be split

The book theorem is external mathematics.  Its verified paper statement gives,
for each fixed degree `n in {0,4}`, a normalized uniform error of order
`gamma^(-1)` after the exact quarter-power scale has been applied.  With
`gamma=2*pi*lambda^2`, this is the required `lambda^(-2)` rate.
`[COFINAL_FAMILY][PAPER]`

A citation does not produce a Lean proof term.  Therefore an unconditional Lean
theorem asserting the raw Satz-9 asymptotic cannot be manufactured from the
current repository without either reproving the book or adding a project axiom.
Both moves are forbidden.

The kernel-executable part is the nontrivial denominator transfer.  Let

```text
q_k(x) = scale_k * p_k(x)
```

be the exact paper-scaled source mode and let `d` be the fixed cylinder target,
with `d(0)=d0>0`.  A uniform estimate

```text
||q_k-d|| <= epsilon_k
```

does not by itself control `p_k/p_k(0)` unless `q_k(0)` stays away from zero.
Under the explicit guard `2*epsilon_k <= d0`, one has

```text
|q_k(0)| >= d0-epsilon_k >= d0/2
```

and the exact identity

```text
d0 * p_k(x)/p_k(0) - d(x)
 = [d0*(q_k(x)-d(x)) + d(x)*(d0-q_k(0))] / q_k(0).
```

This yields a uniform bound, and the exact unit identity converts
`epsilon_k=C/gamma_k` into `O(lambda_k^(-2))`.  This is the authorized kernel
subfloor. `[COFINAL_FAMILY][LEAN_READY]`

## FINAL PROPOSAL

### Exact target theorem

Create one source-only theorem.  Its statement must be exactly:

```lean
theorem centerNormalizedSatz9Rate_of_scaledFixedModeRate
    (lambda gamma theta : ℕ → ℝ)
    (S : ∀ k, Satz9SourceData (lambda k) (theta k))
    (scale : ℕ → ℂ)
    (target : ℝ → ℂ)
    (targetCenter targetBound rawC : ℝ)
    (hlambda : ∀ k, 0 < lambda k)
    (hgamma : ∀ k,
      gamma k = 2 * Real.pi * (lambda k) ^ 2)
    (hcenter : target 0 = (targetCenter : ℂ))
    (hcenterPos : 0 < targetCenter)
    (hbound : 0 ≤ targetBound)
    (htarget : ∀ x : ℝ, ‖target x‖ ≤ targetBound)
    (hrawC : 0 ≤ rawC)
    (hscale : ∀ k, scale k ≠ 0)
    (hraw :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(lambda k)) (lambda k),
          ‖scale k * (S k).p x - target x‖ ≤ rawC / gamma k)
    (hdenom :
      ∀ᶠ k in Filter.atTop,
        2 * (rawC / gamma k) ≤ targetCenter) :
    ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(lambda k)) (lambda k),
        ‖(targetCenter : ℂ) * centerNormalized (S k).p x - target x‖ ≤
          (rawC * (targetCenter + targetBound) /
            (Real.pi * targetCenter)) / (lambda k) ^ 2
```

The theorem is generic in the fixed mode.  It will later be applied once with
`targetCenter=1` and the `D_0` target, and once with `targetCenter=3` and the
`D_4` target.  The exact raw paper rate and exact paper scale remain explicit
inputs about the same `S`; they are not inferred from `Satz9SourceData`.

### Required plant

Before proving the theorem, add one private two-point arithmetic plant:

```lean
private theorem centerNormalization_denominator_guard_plant :
    |(1 / 100 : ℝ) - 1| ≤ 1 ∧
      |(1 : ℝ) - 1| ≤ 1 ∧
      |(1 : ℝ) / (1 / 100 : ℝ) - 1| > 10 := by
  norm_num
```

The first two inequalities model a raw approximation with error `1`; the last
shows that centre normalization can amplify it by two orders of magnitude.
Thus the denominator guard is load-bearing, not decorative.

### Proof route

1. Intersect the eventual raw-rate and denominator events.
2. Fix `k` and obtain positivity of `gamma k` from `hgamma` and `hlambda`.
3. Evaluate `hraw` at `x=0` and use `hcenter`.
4. Prove
   ```text
   norm (scale k * (S k).p 0) >= targetCenter - rawC/gamma k
                                  >= targetCenter/2 > 0.
   ```
5. Use `hscale k` and `(S k).center_ne` to rewrite the centre-normalized ratio
   through the scaled function.
6. Apply the displayed exact numerator identity, the triangle inequality,
   `htarget`, and the denominator lower bound.
7. Rewrite `gamma k = 2*pi*(lambda k)^2` and simplify the constant exactly.

No spectral theorem, ODE theorem or paper estimate is proved in this file.

## STRONGEST ATTACK

The strongest objection to the next node is:

> The theorem merely assumes the Satz-9 rate and therefore does not close the
> paper theorem.

Correct.  It closes the project-side normalization and unit-transfer layer, not
the external theorem.  That is why the verifier is
`LEAN_CONDITIONAL_ON_EXPLICIT_PAPER_RATE_INPUT`, and why no unconditional
F72.1A or RH claim is made.

The repaired statement is still load-bearing: previous route maps repeatedly
used the centre-normalized estimate without a denominator ledger.  The plant
shows that omission is mathematically invalid.  Once this theorem exists, the
remaining paper input has one exact type and cannot be weakened to raw
`O(gamma^-3/4)`, Satz 8's `L2` estimate, a fitted scale, or a rate about a
different witness. **[C04] [C09] [C10]**

## CODEX DIRECTIVE

```yaml
TASK: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
EXECUTOR: CODEX_OR_LINUX_BODY
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD_POLICY:
  command: git rev-parse HEAD
  timing: immediately_before_editing
  rule: record_the_returned_full_SHA_in_SOURCE_RECORD_BASE_HEAD
  forbidden: copy_BASE_HEAD_from_an_older_verdict

CREATE_EXACTLY_ONE_LEAN_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean

CREATE_SOURCE_RECORD_SAME_COMMIT:
  docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1A0_CENTER_NORMALIZED_SATZ9_RATE_TRANSFER_2026-08-23.md

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1Satz9SourcePackageInterface

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.centerNormalizedSatz9Rate_of_scaledFixedModeRate

PRIVATE_PLANT:
  - centerNormalization_denominator_guard_plant

CLOSES:
  - F72_1A_CENTER_NORMALIZATION_DENOMINATOR_LEDGER
  - F72_1A_GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER

OPENS: []

FORBIDDEN:
  - assert_or_axiomatize_the_raw_Satz9_asymptotic
  - use_Satz8_L2_rate_for_a_sup_norm_conclusion
  - put_O_gamma_minus_one_on_the_unscaled_raw_ps_mode
  - infer_rate_from_Satz9SourceData_payload_type
  - define_scale_after_inspecting_the_error
  - remove_or_weaken_hdenom
  - use_a_project_Ferrers_mode_as_the_source_function
  - import_selected_transport_or_project_carrier_files
  - bundle_F72_1C
  - add_sorry
  - add_admit
  - add_typed_hole
  - weaken_the_target

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake env lean Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake build Q3.Proofs.RouteB.G6N1CenterNormalizedSatz9RateTransfer
  - WORKDIR: repository_root
    COMMAND: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.centerNormalizedSatz9Rate_of_scaledFixedModeRate:
    - propext
    - Classical.choice
    - Quot.sound

SUCCESS_CODE: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER_LEAN
FAILURE_CODE: F72_1A0_COMPLEX_DIVISION_OR_EVENTUALLY_API_GAP
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
```

## META CLOSEOUT

**What became smaller?**

The selected-source side is now at the exact project theta values.  The next
unknown is no longer branch ordering, source existence, coordinate scaling or
eigenvalue transport.  It is one explicit normalized-rate inequality.

**What was killed?**

- using the payload name as proof of literal first-kind provenance;
- inferring a degree from the payload type;
- dropping the common `+G` shift;
- claiming the stale `BASE_HEAD` repair succeeded;
- treating raw uniform error as stable under centre normalization without a
  denominator lower bound;
- pretending a paper citation is already a Lean proof term.

**What must not be tried again?**

Do not build another ordering theorem.  Do not select a source package from the
project carrier.  Do not add a paper axiom.  Do not state the centre-normalized
rate without the denominator guard.  Do not copy a stale base SHA into the next
source record.

**Current smallest named gap:**

```text
F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
```

**Next cheapest decisive test:**

Compile the generic ratio-transfer theorem together with the denominator
plant.  If it fails, the failure is Lean algebra/API friction; if the theorem
itself is false, the plant or a scalar counterexample will expose it before any
paper-specific assembly.

**Fate of prior predictions:**

```text
P_SELECTED_TRANSPORT_1: CONFIRMED.
P_SELECTED_TRANSPORT_2: CONFIRMED.
P_SELECTED_TRANSPORT_FAILURE_CLASS: CONFIRMED_AT_REWRITE_NORMAL_FORM_CLASS.
P_NEXT_RATE: CONFIRMED.
No retroactive repair.
```

**Memory entry:**

```yaml
iteration: REQ-2026-08-22-V-selected-transport
target: SELECTED_SATZ9_SOURCE_PACKAGE_TRANSPORT
status: PROGRESS
failed_strategy: copy_stale_BASE_HEAD_and_treat_payload_name_as_rate_provenance
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
invariant_learned: paper_rate_degree_scale_and_source_witness_must_remain_explicit_and_same-object
forbidden_future_move: infer_Satz9_rate_from_Satz9SourceData_or_drop_denominator_guard
next_decisive_test: compile_center_normalization_rate_transfer_with_two_point_plant
```
