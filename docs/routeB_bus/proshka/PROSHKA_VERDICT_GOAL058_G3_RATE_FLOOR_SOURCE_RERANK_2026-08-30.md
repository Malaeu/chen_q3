# STATUS: CONDITIONAL — TRY_FORMALIZE_G3_EXPLICIT_SATZ9_FUCHS_RATE_SOURCE
```yaml
PRIMARY: TRY_FORMALIZE_G3_EXPLICIT_SATZ9_FUCHS_RATE_SOURCE
OPERATIVE_CLASS: TRY_FORMALIZE_G3_EXPLICIT_SATZ9_FUCHS_RATE_SOURCE
PRIMARY_COUNT: 1
DOCUMENT_ROLE: GOAL058_G3_RATE_FLOOR_SOURCE_POLICY_ADJUDICATION

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-08-30-G3RATEFLOOR
  BOUNDARY_ID: GOAL058_G3_PROLATE_RATE_FLOOR_SOURCE_RERANK
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_INTRODUCING_COMMIT: 13fab4c521b62fd5b8ca23b097160894f8cd15f0
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_G3_RATE_FLOOR_SOURCE_RERANK_2026-08-30.txt
  REQUEST_GIT_BLOB: b48a7111ed7e048c3eda67d55651fd4230b438d5
  AUTHORITATIVE_ATTACHMENT:
    NAME: PROSHKA_REQUEST_GOAL058_G3_RATE_FLOOR_SOURCE_RERANK_2026-08-30.txt
    BYTES: 6740
    LINES: 159
    SHA256: a2a41613ee4f620397d2f65bc80656a1f49a68bf396eb365e9cb97a714f931e3
    FINAL_LF: true
  SOURCE_BASE_COMMIT: 239a12108baac55f4b53abc908a37e6d9ce7054e
  DELIVERY_RECEIPT_COMMIT: 4a84acaf61d7057ee90b830bd60813f4afb943e8
  LIVING_CHAT: 6a8c3e2a-df50-83eb-b53d-dd4cc46f646f

PHASE_KEY:
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots
  HONESTY_STATE: CHALLENGER_NOT_RH
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

SOURCE_AUDIT:
  EXECUTION_STATE:
    operational_status: GOAL_058_G3_PROLATE_RATE_AND_FLOOR_OPEN
    contract: G3_PROLATE_RATE_CENTRAL_OVERLAP_DENOMINATOR_FLOOR
    status: SOURCE_THEOREM_OPEN
    finding: STALE_RECEIVER_PLUS_SOURCE_MIXED_ADDRESS
  CONDITIONAL_RECEIVERS:
    direct_mode_rate:
      theorem: Q3.RouteB.D0Pstar.selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
      status: KERNEL_GREEN_CONDITIONAL
      missing_input: EXACT_RAW_SATZ9_RATE_ON_THE_SAME_S0_S4
    chi_defect_rate:
      theorem: Q3.RouteB.D0Pstar.selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates
      status: KERNEL_GREEN_CONDITIONAL
      missing_input: EXACT_FUCHS_EIGENRELATIONS_AND_DEFECT_RATES
    projected_floor_and_normalizer:
      theorem: Q3.RouteB.D0Pstar.selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
      status: KERNEL_GREEN_CONSUMER
      finding: NOT_A_RATE_SUPPLIER
    source_payload:
      theorem: Q3.RouteB.selectedSatz9SourceData_at_projectTheta_degree_zero_four
      status: KERNEL_GREEN_OBJECT_SUPPLIER
      finding: EXPLICITLY_PROVES_NO_SATZ9_RATE
    central_limit_floor:
      theorem: Q3.RouteB.D0Pstar.E_star_explicitCCMLimitH_pos
      status: KERNEL_GREEN_LIMIT_TARGET
      finding: POSITIVITY_IS_NOT_CONVERGENCE
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_BUILD: false
  RECEIVER_AXIOM_PROFILE_ACCEPTED_FROM_SOURCE_RECORDS:
    - propext
    - Classical.choice
    - Quot.sound

QUESTION_1_EXACT_PAPER_SUPPLY:
  ANSWER: YES_AT_PAPER_LEVEL_AND_EXACTLY_FORMALIZABLE
  SINGLE_PAPER_SUPPLIES_EVERYTHING: false
  SOURCE_PAIR_REQUIRED:
    - MEIXNER_SCHAEFKE_1954_SATZ_9
    - FUCHS_1964_THEOREM_1
  SAME_SELECTED_DEGREES:
    zero: FULL_DEGREE_0_CYLINDER_ORDER_0
    four: FULL_DEGREE_4_CYLINDER_ORDER_4
    project_chi2: FULL_DEGREE_4_NOT_DEGREE_2
  SAME_SOURCE_FAMILY_REQUIRED: true
  INDEPENDENT_S0_S4_SELECTION: forbidden
  RH_EQUIVALENT_INPUT_USED: false

MEIXNER_SCHAEFKE_PIN:
  BIBLIOGRAPHY: >-
    Josef Meixner and Friedrich Wilhelm Schaefke, Mathieusche Funktionen und
    Sphaeroidfunktionen, Springer Grundlehren LXXI, 1954,
    DOI 10.1007/978-3-662-00941-3.
  PIN: chapter_3_section_3_2_Satz_9_printed_page_243_scan_page_255
  REGIME: gamma_to_positive_infinity_with_fixed_m_and_n
  SPECIALIZATION:
    m: 0
    n:
      - 0
      - 4
    q_formula: q = 2 * (n - m) + 1
    cylinder_order: n - m
  SOURCE_FUNCTIONS:
    zero: ps_0^0(z; gamma^2)
    four: ps_4^0(z; gamma^2)
    representative: regular_first_kind_continuous_at_both_endpoints
  RAW_MODE_FORMULA: >-
    ps_n^m(z;gamma^2) equals
    (-1)^m * (4*gamma/pi)^(1/4) / (n-m)! *
    sqrt((n+m)!/(2*n+1)) * (1-z^2)^(m/2) *
    D_(n-m)(sqrt(2*gamma)*z) plus O(gamma^(-3/4)),
    uniformly for z in [-1,1].
  FIXED_MODE_SCALE_M0: >-
    A_n(gamma) = (4*gamma/pi)^(1/4) /
    sqrt((2*n+1)*n!).
  CENTER_NORMALIZED_RATE: >-
    Dividing by the mode's own leading center scale converts the raw
    O(gamma^(-3/4)) remainder into an O(gamma^(-1)) error for fixed n=0,4.
  UNIFORMITY_RANGE_DIMENSIONLESS: Set.Icc (-1) 1
  CONSTANTS:
    zero: EXISTS_C_MS_0_NONNEGATIVE_INDEPENDENT_OF_k
    four: EXISTS_C_MS_4_NONNEGATIVE_INDEPENDENT_OF_k
    fitted_constants: forbidden

FUCHS_PIN:
  BIBLIOGRAPHY: >-
    W. H. J. Fuchs, On the Eigenvalues of an Integral Equation Arising in the
    Theory of Band-Limited Signals, Journal of Mathematical Analysis and
    Applications 9 (1964), 317-330,
    DOI 10.1016/0022-247X(64)90017-4.
  PIN: Theorem_1_page_319_with_closing_constant_check_near_page_330
  REGIME: a_to_positive_infinity_with_fixed_n
  THEOREM: >-
    1 - Lambda_n is asymptotic to
    4*sqrt(pi)*8^n/(n!)*a^(2*n+1)*exp(-2*a^2).
  COVERED_DEGREES:
    - 0
    - 4
  POSITIVE_TRANSFORM_BRANCH_REQUIRED: true
  WEAK_RATE_OUTPUT: >-
    There exist C_F_0,C_F_4 >= 0 and a threshold such that the two paper
    concentration defects are at most C_F_n/a^2.

EXACT_CROSSWALK:
  selected_lambda: lambda_k = sqrt(k+2)
  project_gamma: gamma_k = 2*pi*lambda_k^2
  book_parameter:
    gamma_MS: gamma_k
    equation_parameter: gamma_k^2
  dimensionless_coordinate: z = x/lambda_k
  cylinder_argument_identity: >-
    sqrt(2*gamma_k)*z = 2*sqrt(pi)*x = projectCylinderArgument(x).
  physical_window: x in [-lambda_k,lambda_k]
  book_window: z in [-1,1]
  paper_fuchs_window:
    a: sqrt(2*pi)*lambda_k
    a_squared: 2*pi*lambda_k^2
  fourier_rescaling: >-
    U_lambda(h)(s) = (2*pi)^(-1/4)*h(s/sqrt(2*pi)) and
    F_a(U_lambda h) = sqrt(2*pi)*U_lambda(T_lambda h).
  transform_eigenvalues:
    mu_0: sqrt(2*pi)*chi0
    mu_4: sqrt(2*pi)*chi2
  concentration_eigenvalues:
    Lambda_0: chi0^2
    Lambda_4: chi2^2
  project_asymptotics:
    chi0: 1-chi0 ~ 2*sqrt(2)*pi*lambda*exp(-4*pi*lambda^2)
    chi2: >-
      1-chi2 ~ (2^14/3)*sqrt(2)*pi^5*lambda^9*
      exp(-4*pi*lambda^2)
  WEAK_PROJECT_OUTPUT: >-
    There exists C_chi >= 0 such that eventually both
    abs(1-chi0) and abs(1-chi2) are at most C_chi/lambda^2.

EXACT_SOURCE_SCALING_FOR_EXISTING_RECEIVER:
  source_view: CENTER_NORMALIZED_SATZ9_SOURCE_DATA
  scale0: scale0(k) = ((S0(k)).p(0))^(-1)
  scale4: scale4(k) = 3 * ((S4(k)).p(0))^(-1)
  justification: >-
    centerNormalized removes the arbitrary source scalar; D_0 has center 1 and
    D_4 has center 3. The book prefactor is consumed inside the proof and is
    never fitted from project data.
  raw_rate_unit: C_MS_n / selectedFerrersPaperGamma(k)
  selected_output_constants:
    zero: 2*C_MS_0/pi
    four: 94*C_MS_4/(3*pi)

QUESTION_2_APPROVED_SOURCE_INTERFACE:
  ANSWER: NO
  LITERATURE_BRIDGE:
    status: STRATEGY_OPERATOR_ONLY
    meaning: >-
      It authorizes and disciplines a source-to-project audit. It does not
      manufacture a Lean proof term for an external theorem.
  SOURCE_RECORD:
    status: EVIDENCE_RECEIPT_ONLY
    may_close_kernel_goal: false
  CONTROL_V9_SEMANTIC_ATTESTATION:
    status: POST_KERNEL_SEMANTIC_BINDING_ONLY
    may_attest_unformalized_paper_theorem: false
  SEMANTIC_ADMISSION:
    status: NOT_A_SUBSTITUTE_FOR_KERNEL_PROOF
  PROJECT_AXIOM:
    status: FORBIDDEN
  NEW_TRUST_CLASS:
    status: NOT_MINTED
  REPAIR_CLASS_SELECTED: false

CLASS_DECISION:
  TRY_FORMALIZE_G3_EXPLICIT_SATZ9_FUCHS_RATE_SOURCE:
    status: SELECTED
    reason: >-
      Both missing analytic inputs are exact primary-source theorems with the
      fixed modes, normalization, uniformity domain and source-to-project units
      now locked. The absence is a Lean formalization gap, not a missing
      mathematical statement.
  REPAIR_G3_RATE_FLOOR_VIA_EXISTING_APPROVED_SOURCE_INTERFACE:
    status: REJECTED_NO_SUCH_PROOF_CARRYING_INTERFACE
  KILL_G3_PROLATE_RATE_FLOOR_CURRENT_FRONT_AND_RERANK:
    status: REJECTED_KILL_PRECONDITION_FALSE
    reason: >-
      The exact formalizable primary-source supply exists. Killing the front
      merely because its proof is expensive would misclassify a proof-cost wall
      as theorem absence.

AUTHORIZED_FIRST_TRANSACTION:
  MODE: ONE_GOAL_ONE_COMMIT
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean
  MODULE: Q3.Proofs.RouteB.G6N1MeixnerSchaefkeSelectedSatz9RateSource
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.SpheroidalSourceMain
    - Q3.Proofs.RouteB.G6N1Satz9SourcePackageInterface
    - Q3.Proofs.RouteB.G6N1ParabolicCylinderD0D4Exact
    - Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
  PUBLIC_THEOREM_COUNT: 1
  PUBLIC_THEOREM: selectedSatz9SourcePair_centerNormalized_uniformRate_zero_four
  NO_OTHER_PUBLIC_DECLARATIONS: true
  SOURCE_RECORD_REQUIRED_SAME_COMMIT: true
  FOREIGN_MODE_FOUR_FILES_EDITED: false

FIRST_PUBLIC_LEAN_THEOREM_HEAD: |-
  theorem selectedSatz9SourcePair_centerNormalized_uniformRate_zero_four
      (P : forall k : Nat,
        BookRegularEvenSpectrumEven (mode4JacobiG (k + 2))) :
      exists
        (S0 : forall k : Nat,
          Satz9SourceData
            (selectedFerrersPaperLambda k)
            (mode4ClassicalEvenEigenvalue
                (mode4JacobiG (k + 2)) 0 +
              mode4JacobiG (k + 2)))
        (S4 : forall k : Nat,
          Satz9SourceData
            (selectedFerrersPaperLambda k)
            (mode4ClassicalEvenEigenvalue
                (mode4JacobiG (k + 2)) 2 +
              mode4JacobiG (k + 2)))
        (C0 C4 : Real),
        0 <= C0 and 0 <= C4 and
        (forall_eventually k in Filter.atTop,
          forall x in Set.Icc
              (-(selectedFerrersPaperLambda k))
              (selectedFerrersPaperLambda k),
            norm (centerNormalized (S0 k).p x -
              ((parabolicCylinderD 0
                (projectCylinderArgument x) : Real) : Complex)) <=
                C0 / selectedFerrersPaperGamma k and
            norm ((3 : Complex) * centerNormalized (S4 k).p x -
              ((parabolicCylinderD 4
                (projectCylinderArgument x) : Real) : Complex)) <=
                C4 / selectedFerrersPaperGamma k)

THEOREM_HEAD_NOTES:
  syntax_note: >-
    The implementation may replace the prose tokens forall/exists/and and
    forall_eventually by their standard Lean symbols. Binder order, objects,
    quantifiers and conclusion are frozen.
  allowed_hypothesis: ONE_SOURCE_PURE_BOOK_SPECTRUM_PACKAGE
  forbidden_hypotheses:
    - raw_Satz9_rate
    - selected_Ferrers_mode_rate
    - projected_denominator_floor
    - bounded_trial_normalizer
    - RH
    - absence_of_off_critical_zeros
  construction_rule: >-
    S0 and S4 must be constructed together from the same P by the source-only
    regular-even first-kind path. They may not be chosen from independent
    packages after inspecting project modes.
  proof_rule: >-
    The proof must formalize the fixed-mode center-normalized consequence of
    Meixner-Schaefke Satz 9. It may use source ODE uniqueness to transport the
    result between normalized regular first-kind representatives. It may not
    call the existing conditional selected-Ferrers rate theorem.

DOWNSTREAM_CONSUMER:
  theorem: Q3.RouteB.D0Pstar.selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
  instantiation:
    S0: theorem_witness_S0
    S4: theorem_witness_S4
    scale0: fun k => ((S0 k).p 0)^(-1)
    scale4: fun k => 3 * ((S4 k).p 0)^(-1)
    rawC0: C0
    rawC4: C4
  effect: CLOSES_F72_LITERAL_CENTER_ANCHORED_MODE_RATE_AFTER_KERNEL_GATE
  does_not_close:
    - FUCHS_SOURCE_RATE
    - THETA_RATE
    - H2A_SIMPLE_EVEN_GROUND
    - ROUTE_B
    - RH

SECOND_SOURCE_NODE_MAPPED_NOT_AUTHORIZED_BY_FIRST_TRANSACTION:
  ID: G3_FUCHS_FIXED_MODE_DEFECT_SOURCE
  TARGET: >-
    Formalize Fuchs Theorem 1 for fixed n=0,4 sufficiently to produce the exact
    positive-branch paper eigenrelations and eventual C/a^2 defect bounds
    consumed by selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates.
  REVIEW_REQUIRED_AFTER_FIRST_GATE: false
  EXECUTION_REQUIRES_FIRST_GATE_CLOSEOUT_AND_SOURCE_RECORD: true

ADVERSARIAL_PLANTS:
  P1_SATZ9_ORDER_TRAP:
    mutation: USE_q_EQUALS_9_AS_CYLINDER_ORDER_FOR_FULL_DEGREE_4
    expected_failure: >-
      D_9 is odd and vanishes at the center, whereas the selected full-degree-4
      source is even and its cylinder target has center 3. The correct order is
      n-m=4, not q=9 and not the project ordinal 2.
    card: C04_SAME_COORDINATES_TWO_LAWS
  P2_FUCHS_SQUARE_ONLY_BRANCH:
    statement: abs(1-(-1)^2)=0_and_abs(1-(-1))=2
    expected_failure: >-
      Concentration data alone cannot distinguish chi from -chi. The positive
      Fuchs transform branch is load-bearing before converting a square defect
      into abs(1-chi).
    existing_reference: fuchs_positive_branch_guard_plant
    card: C10_FUNCTIONAL_NOT_SURROGATE

MANDATORY_ATTACK_RESULTS:
  RATE_HYPOTHESES_RESTATED_AS_INPUT: REJECTED
  FIXED_FINITE_CELL_FIT_AS_COFINAL_THEOREM: REJECTED
  CHANGED_PROLATE_FAMILY: REJECTED
  CHANGED_COORDINATE_OR_FOURIER_NORMALIZATION: REJECTED
  INDEPENDENT_S0_S4_WITNESSES: REJECTED
  FLOOR_USED_TO_PROVE_ITS_OWN_RATE_INPUTS: REJECTED_CIRCULAR
  CITATION_OR_BROWSER_VERDICT_AS_KERNEL_PROOF: REJECTED
  SEMANTIC_ADMISSION_AS_KERNEL_PROOF: REJECTED
  SAME_RATE_GAP_RENAMED_AS_RERANK: REJECTED

STATE_RECONCILIATION_AFTER_VERDICT_MIGRATION:
  PHASE_KEY_CHANGE: false
  OPERATIONAL_STATUS: GOAL_058_G3_EXPLICIT_PAPER_RATE_SOURCE_FORMALIZATION
  CONTRACT: G3_EXPLICIT_SATZ9_FUCHS_RATE_SOURCE
  STATUS: SOURCE_THEOREM_FORMALIZATION_AUTHORIZED
  NEXT_ACTION: >-
    Create only G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean and its same-commit
    SOURCE RECORD, then run the registered kernel gate.
  MAP_CHANGES:
    RECEIVER_AND_DENOMINATOR_FLOOR_LAYER: CONDITIONALLY_CLOSED_PRESERVED
    SATZ9_PRIMARY_SOURCE_RATE: ACTIVE
    FUCHS_PRIMARY_SOURCE_RATE: QUEUED_AFTER_SATZ9
  CURRENT_TASK_POINTER: G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE
  ROUTE_STATUS_CHANGE: false
  QUEUE_STATUS_MUTATED_BY_PROSHKA: false

VALIDATION:
  WORKDIR_Q3_LEAN:
    - lake env lean Q3/Proofs/RouteB/G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean
    - lake build Q3.Proofs.RouteB.G6N1MeixnerSchaefkeSelectedSatz9RateSource
  WORKDIR_REPOSITORY_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean
  EXPECTED_AXIOM_PROFILE:
    - propext
    - Classical.choice
    - Quot.sound
  FORBIDDEN_AXIOMS:
    - sorryAx
    - new_project_axiom
  SOURCE_SCAN:
    - no_selectedFerrers_directCylinderRate_of_explicitSatz9RawRates_in_proof_dependencies
    - no_raw_rate_binder
    - no_project_mode_used_as_source_witness
    - no_fitted_constant

SUCCESS_CODE: G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_KERNEL_GREEN
FAILURE_CODES:
  - G3_SATZ9_SOURCE_THEOREM_STATEMENT_OR_OBJECT_MISMATCH
  - G3_SATZ9_SOURCE_FAMILY_PROVENANCE_VIOLATION
  - G3_SATZ9_PARAMETER_OR_CYLINDER_ORDER_MISMATCH
  - G3_SATZ9_UNIFORM_ASYMPTOTIC_LIBRARY_WALL
  - G3_SATZ9_RATE_RESTATED_AS_HYPOTHESIS
  - G3_SATZ9_SOURCE_AXIOM_OR_SORRY_CONTAMINATION

CLOSES:
  - G3_RATE_FLOOR_SOURCE_POLICY_AMBIGUITY
  - G3_STALE_RECEIVER_AND_SOURCE_MIXED_EXECUTION_ADDRESS
OPENS: []
CARRIES_OPEN:
  - G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_LEAN
  - G3_FUCHS_FIXED_MODE_DEFECT_SOURCE_LEAN
  - SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY
  - SLOT_H2A_SIMPLE_EVEN_GROUND
  - THEOREM510_REAL_ZERO_BRIDGE

REGISTERED_PREDICTIONS:
  P_G3_SOURCE_1:
    probability: 0.87
    prediction: >-
      The frozen theorem head elaborates after only namespace/API repairs; the
      first substantive blocker is the uniform asymptotic proof, not the source
      family, degree, coordinate or normalization crosswalk.
  P_G3_SOURCE_2:
    probability: 0.72
    prediction: >-
      Current Mathlib and Q3 source ODE infrastructure do not already contain a
      theorem strong enough to close the uniform Satz-9 asymptotic; a new
      fixed-mode analytic proof layer will be required.
  P_G3_SOURCE_3:
    probability: 0.96
    prediction: >-
      No approved source interface will legitimately turn the paper citation
      into a kernel theorem without this formalization or a separately approved
      axiom policy.

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
ROUTE_SCORE: 4

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
LEAN_EDIT_PERFORMED: false
JUDGE_KERNEL_RERUN: false
```

## ROUTE MAP

| Question | Verdict | Tags |
|---|---|---|
| Does an exact paper theorem exist? | **Yes.** Meixner–Schäfke Satz 9 supplies the fixed-mode uniform shape rate; Fuchs Theorem 1 supplies the fixed-mode concentration defect. Their exact units and selected degree-zero/four crosswalks are now locked. | `[COFINAL_FAMILY][PAPER]` |
| Do the current Lean files already prove those paper rates? | **No.** They are exact conditional consumers. `Satz9SourceData` supplies source objects, not asymptotics; the normalizer theorem consumes rates and cannot generate them. | `[COFINAL_FAMILY][LEAN]` |
| Is there an approved external-input carrier? | **No proof-carrying one.** `LITERATURE_BRIDGE`, source records, semantic admission and Control-v9 receipts audit or attest already-existing results; none creates a kernel proof term for an unformalized paper theorem. | `[ABSTRACT][PAPER]` |
| Should the current front be killed? | **No.** The mathematical theorem is present and source-faithful. The stale mixed address is repaired into an explicit source-formalization front. | `[COFINAL_FAMILY][PAPER]` |
| Is another receiver authorized? | **No.** The first transaction is the paper-source theorem itself. | `[COFINAL_FAMILY][CONDITIONAL]` |

## FINAL PROPOSAL

Run exactly one source-formalization transaction:

```text
G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE
```

The theorem must construct the two source packages from one source-pure spectrum package and prove the center-normalized uniform rates. It may not assume `hraw0`, `hraw4`, a projected floor, a normalizer bound, or any selected-project rate.

The existing receiver then spends the result with the exact scales

```text
scale0(k) = ((S0 k).p 0)^(-1)
scale4(k) = 3 * ((S4 k).p 0)^(-1).
```

The first source transaction does not close the Fuchs input, theta input, H2a, Route B or RH.

## STRONGEST ATTACK

The strongest objection is cost, not object mismatch:

> Satz 9 is a genuine 1954 uniform special-function asymptotic. The current repository has the source ODE, regular-mode uniqueness and exact unit dictionary, but it does not visibly contain the uniform asymptotic machinery used in the monograph.

Accepted. A source file that merely restates the rate as a hypothesis would be fake progress and must fail with `G3_SATZ9_RATE_RESTATED_AS_HYPOTHESIS`. If the first proof attempt isolates a true special-function library wall, report that exact missing lemma under `G3_SATZ9_UNIFORM_ASYMPTOTIC_LIBRARY_WALL`; do not add another receiver and do not silently switch to numerical fitting.

This objection does not justify a present kill because the source theorem itself is exact, fixed-mode, source-faithful and non-RH-equivalent.

## CODEX DIRECTIVE

```text
TASK_ID:
  G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE

CREATE EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean

  docs/routeB_bus/
  LINUX_SOURCE_RECORD_GOAL058_G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_2026-08-30.md

DO NOT EDIT:
  existing rate receivers;
  trial-normalizer closure;
  foreign mode-four files;
  Route state files in the source commit;
  Q3.Main;
  control files.

PUBLIC SURFACE:
  exactly one theorem:
  selectedSatz9SourcePair_centerNormalized_uniformRate_zero_four

PROOF INPUTS ALLOWED:
  exact source-pure BookRegularEvenSpectrumEven package;
  source spheroidal ODE and uniqueness;
  exact selected parameter dictionary;
  exact D0/D4 parabolic-cylinder formulas;
  formalized fixed-mode argument from Meixner-Schaefke Satz 9.

FORBIDDEN:
  hraw0 or hraw4 as hypotheses;
  existing conditional selected-Ferrers rate theorem in the proof dependency;
  projected denominator floor;
  trial-normalizer boundedness;
  numerical fit;
  independent source packages for modes zero and four;
  new axiom, sorry, admit or theorem weakening.

VALIDATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean
    lake build Q3.Proofs.RouteB.G6N1MeixnerSchaefkeSelectedSatz9RateSource

  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean

SUCCESS:
  G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_KERNEL_GREEN

FAILURE REPORT:
  exact first unproved analytic lemma;
  exact file and line;
  exact Mathlib/Q3 searches;
  exact source theorem fragment it represents;
  one of the frozen failure codes;
  no fallback receiver.
```

## META CLOSEOUT

**What became smaller?**

The old mixed instruction “build the packet, rates, overlap and floor” is replaced by one exact source theorem. The packet, bind, receiver and floor consumer are already present.

**What was killed?**

- another conditional receiver;
- a citation treated as a Lean proof;
- semantic admission treated as theorem construction;
- independent source witnesses for degree zero and four;
- finite-cell fitting as a cofinal rate;
- circular use of the floor to prove its own rate inputs.

**What must not be tried again?**

Do not re-open the denominator-floor wrapper and do not create a `PaperRateAssumption` structure whose only content is the missing conclusion.

**Current smallest named gap?**

```text
G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_LEAN
```

**Next cheapest decisive test?**

Typecheck the frozen theorem head and isolate whether the first true wall is the uniform asymptotic estimate or an earlier source-object/API mismatch.

**Prediction fate?**

The request’s mechanical preflight is confirmed at the Lean level: no unconditional supplier exists. The stronger source audit changes the diagnosis, not the fact: the missing item is an exact paper theorem awaiting formalization.

```yaml
iteration:
  target: GOAL058_G3_PROLATE_RATE_FLOOR_SOURCE_RERANK
  status: PROGRESS
  failed_strategy: conditional_receiver_accumulation
  cognitive_operator_used: LITERATURE_BRIDGE
  new_gap_name: G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE_LEAN
  invariant_learned: same source family, fixed modes 0/4, exact gamma and Fourier units
  forbidden_future_move: paper citation or semantic admission as kernel proof
  next_decisive_test: typecheck exact theorem head and isolate first analytic lemma
  progress_class: REPRESENTATION_PROGRESS
  route_score: 4
```
