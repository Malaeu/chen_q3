# STATUS: TRY_P59_FINITE_PROJECTED_TRIAL_JET_CROSSWALK
```yaml
PRIMARY: TRY_P59_FINITE_PROJECTED_TRIAL_JET_CROSSWALK
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_P59_FINITE_PROJECTED_TRIAL_JET_CROSSWALK

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-TRIALJET
  BOUNDARY_ID: GOAL058_TRIAL_SECOND_JET_EXACT_AND_GROUND_TRIAL_JET_GAP
  REQUEST_COMMIT: 0c371b5f67383759fcf5bd579953e3783cfe974a
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_TRIAL_SECOND_JET_EXACT_AND_GROUND_TRIAL_GAP_2026-09-04.txt
  REQUEST_GIT_BLOB: 22e2c22e79fbcf489c77b746bb6f90405fcf9d23
  REQUEST_SHA256: a4ece72bae1a7227a03cfe3936a9a635ba8a4e7f1fe9058806d199b956008864
  REQUEST_BYTES: 10163
  REQUEST_LINES: 97
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  POST_REQUEST_RESULTS_USED: false
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_TRIAL_SECOND_JET_EXACT_AND_GROUND_TRIAL_JET_GAP_2026-09-04.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  EVIDENCE_REF: 0c371b5f67383759fcf5bd579953e3783cfe974a
  CONVENTION_CARD:
    path: docs/routeB_bus/CONVENTION_CARD_GOAL058.md
    git_blob: 65e7aec23df97ed738ee0e0c5da4cf77ca8fa37b
  P59_TRANSFORM:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean
    git_blob: 6d38df2ff26cc7dc7eadc4757c15605649cbb6d4
  PROJECTED_MELLIN_CROSSWALK:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
    git_blob: 0bb77a54910216e43f5a5a15c7ace0e093595d78
  PROJECT_TRIAL:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean
    git_blob: a139d3f91659d9baf4936008d8a429d6a2e96705
  NUMERIC_TRIAL_BUILDER:
    path: q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/portable_k_channel_v1.py
    git_blob: 29c1b8cacc2e91558920c0f4accf8212d1f0b157
  TRIAL_JET_REPORT:
    path: docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_TRIAL_SECOND_JET_CONSTANT_DERIVATION.md
    git_blob: 9f82deff5740fe8d681d38d6d9146762c25c0ecf
  DUALCERT_REPORT:
    path: docs/routeB_bus/phase5_scripts/out/edge_ledger_dualcert.md
    git_blob: 906cc7b5499708d3efae40b5b2c8f64b7b61b31
  PRIMARY_PAPER:
    title: Zeta Spectral Triples
    arxiv: 2511.22755v1
    sections: [5.5, 7, 8]

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

TOP_LEVEL_ADJUDICATION:
  FINITE_P59_FQ_EQUALS_FULL_KLAMBDA_MELLIN:
    verdict: REFUTED_AS_STATED
    reason: "The project row q is the normalized finite Fourier projection P_N f_lambda; its P59 transform is the Mellin coordinate of that projection, not of the unprojected paper function k_lambda."
    scope: FINITE_CELL
    verifier: LEAN_PLUS_PAPER
  FULL_E_MAP_ZETA_CANCELLATION:
    verdict: EXACT_FOR_THE_UNWINDOWED_MAIN_TERM
    scope: ABSTRACT
    verifier: PAPER
  WINDOWED_AND_FINITE_ZETA_CANCELLATION:
    verdict: FALSE_WITHOUT_TWO_EXPLICIT_REMAINDERS
    remainders:
      - LOWER_MULTIPLICATIVE_WINDOW_TAIL
      - FINITE_FOURIER_PROJECTION_TAIL
    scope: COFINAL_FAMILY
    verifier: PAPER
  LITERAL_PHI_FINITE:
    status: MEROMORPHIC_NOT_ENTIRE
    scope: ABSTRACT
    verifier: PAPER
  ARCHIMEDEAN_MAIN_TERM_PHI:
    status: HOLOMORPHIC_ON_OPEN_CENTERED_STRIP_NOT_PROVED_ENTIRE
    scope: ABSTRACT
    verifier: PAPER
  PROLATE_OPERATOR_SPLIT:
    formula: "PW_lambda = lambda^2*H + d_x(x^2*d_x)"
    status: EXACT_AS_DIFFERENTIAL_EXPRESSIONS
    scope: ABSTRACT
    verifier: PAPER
  SINGLE_H8_FIRST_ORDER:
    status: FORMAL_PERTURBATION_COEFFICIENT_CONFIRMED
    rigorous_remainder: OPEN
    scope: ABSTRACT
    verifier: PAPER
  SECOND_ORDER_CURVATURE_SIGN:
    request_formula: "kappa(q)=kappa_X-1/(16*pi*m)+13/(256*pi^2*m^2)+O(m^-3)"
    repaired_formula: "kappa(q)=kappa_X-1/(16*pi*m)-13/(256*pi^2*m^2)+O(m^-3)"
    reason: "13/(256*pi^2) is the positive second coefficient of [z^2]Phi, and curvature subtracts that coefficient."
    scope: ABSTRACT
    verifier: PAPER
  DELTA_RATE_EQUIVALENCE:
    status: TRUE_AFTER_FINITE_TRIAL_JET_CROSSWALK
    formula: "delta_m=alpha_G,m-alpha_q,m and alpha_q,m=O(1/m)=o(T_m)"
    consequence: "|delta_m|=O(T_m) iff |alpha_G,m|=O(T_m)"
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
  GAPFREE_DELTA_SUPPLIER:
    status: NOT_PROVED
    best_candidate: P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL

Q1_EXACT_OBJECT_AUDIT:
  SCOPE: FINITE_CELL
  VERIFIER: LEAN_PLUS_PAPER
  LOG_COORDINATE:
    L: "2*log(lambda)=log(m)"
    f_lambda: "x |-> k_lambda(exp(x)/lambda) on [0,L]"
    U_n: "L^(-1/2)*exp(2*pi*i*n*x/L)"
    P_N: "orthogonal Fourier projection onto |n|<=N"
  PROJECT_ROW:
    raw_coefficients: "c_n=<U_n,f_lambda>"
    normalized_row: "q_n=c_n/||P_N f_lambda||_2"
  EXACT_FINITE_IDENTITY: >-
    F_{q,N}(z)=||P_N f_lambda||_2^(-1) *
    exp(i*z*L/2) * integral_0^L (P_N f_lambda)(x)*exp(-i*z*x) dx.
  WINDOWED_MELLIN_MAIN:
    H_lambda(z): "integral_[lambda^-1,lambda] k_lambda(u)*u^(-i*z) d*u"
    identity: "H_lambda(z)=exp(i*z*L/2)*integral_0^L f_lambda(x)*exp(-i*z*x) dx"
  PROJECTION_REMAINDER:
    E_lambda_N_z: >-
      exp(i*z*L/2)*integral_0^L ((I-P_N)f_lambda)(x)*exp(-i*z*x) dx
    exact_repair: "F_{q,N}(z)=||P_N f_lambda||_2^(-1)*(H_lambda(z)-E_lambda_N(z))"
  PLANTED_FAILURE:
    f: "U_0 + epsilon*U_{N+1}, epsilon != 0"
    effect: >-
      P_N f=U_0, so the finite P59 transform is independent of epsilon,
      while the full windowed Mellin coordinate has a nonzero epsilon term.
    conclusion: KILL_FINITE_P59_TRIAL_EQUALS_FULL_MELLIN_EXACTLY

Q1_ZETA_CANCELLATION:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  FULL_E_IDENTITY:
    w: "1/2-i*z"
    formula: "M(E(h_lambda))(-i*z)=zeta(w)*M(h_lambda)(w)"
    initial_domain: "a half-plane of absolute convergence"
    continuation: "meromorphic continuation where both sides are defined"
  LIMIT_IDENTITY:
    formula: "zeta(w)*M(h)(w)=xi(w)/4"
  LOWER_WINDOW_TAIL:
    B_lambda_z: "integral_(0,lambda^-1) E(h_lambda)(u)*u^(-i*z) d*u"
    exact_window_formula: "H_lambda(z)=zeta(w)*M_lambda(w)-B_lambda(z)"
    upper_tail: "zero because h_lambda is supported in [-lambda,lambda]"
  ARCHIMEDEAN_MAIN_RATIO:
    X_z: "centeredXi(z)/centeredXi(0)"
    Phi_arch: >-
      [M_lambda(w)/M_lambda(1/2)] *
      [M_0(1/2)/M_0(w)]
    identity: "A_lambda(z)/A_lambda(0)=X(z)*Phi_arch(z), A_lambda(z)=zeta(w)M_lambda(w)"
    domain: "the open centered strip |Im z|<1/2, where 0<Re w<1 and M_0(w) is nonzero"
  NORMALIZED_WINDOW_CORRECTION:
    formula: >-
      H_lambda(z)/H_lambda(0)
      = X(z)*Phi_arch(z)
      + [B_lambda(0)A_lambda(z)-A_lambda(0)B_lambda(z)] /
        [A_lambda(0)(A_lambda(0)-B_lambda(0))].
  NORMALIZED_PROJECTION_CORRECTION:
    formula: >-
      F_{q,N}(z)/F_{q,N}(0)
      = H_lambda(z)/H_lambda(0)
      + [E_lambda_N(0)H_lambda(z)-H_lambda(0)E_lambda_N(z)] /
        [H_lambda(0)(H_lambda(0)-E_lambda_N(0))].
  ENTIRENESS:
    finite_literal_ratio: "F_{q,N}/X is meromorphic and is entire only if every Xi zero is canceled, which is an open identification statement"
    Phi_arch: "holomorphic on the open centered strip; no supplied theorem makes it entire on C"

Q1_PERTURBATION:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  EXACT_DIFFERENTIAL_IDENTITY:
    formula: >-
      -d_x[(lambda^2-x^2)d_x]+(2*pi*lambda*x)^2
      = lambda^2*(-d_x^2+4*pi^2*x^2)+d_x(x^2*d_x)
  EPSILON: "lambda^-2=m^-1"
  LADDER_OPERATOR: "V=d_x(x^2*d_x)=(S^2-1)/4"
  SELECTION_RULE: "V couples Hermite level n only to n and n+-4"
  FIRST_ORDER:
    internal_0_4_rotation: "cancels in the zero-integral h_0/h_4 line"
    surviving_mode: h_8
    coefficient: "sqrt(105)/(16*pi)"
    Phi_z2: "1/(16*pi*m)"
    curvature: "kappa_X-1/(16*pi*m)"
  SECOND_ORDER:
    Phi_z2: "13/(256*pi^2*m^2)"
    Phi_z4: "1/(512*pi^2*m^2)"
    curvature_z2_consequence: "-13/(256*pi^2*m^2)"
  RIGOR_GAP:
    - "analytic perturbation for the prolate eigenfunctions on the expanding/singular-endpoint problem"
    - "uniform Mellin two-jet remainder"
    - "lower-window tail through two z-derivatives"
    - "finite Fourier projection tail through two z-derivatives"

Q2_TRIAL_TWO_JET_THEOREM:
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL
  CONTINUUM_WINDOWED_CANDIDATE:
    assumptions:
      - "source-locked zero-integral h_lambda in span(h_0,lambda,h_4,lambda)"
      - "second-order prolate perturbation with a Mellin-two-jet O(lambda^-6) remainder on each closed substrip"
      - "lower-window correction and its first two z-derivatives are O_K(lambda^-6)"
      - "nonzero anchor"
    conclusion: >-
      kappa(k_lambda)
      = kappa_X - 1/(16*pi*lambda^2)
        - 13/(256*pi^2*lambda^4) + O(lambda^-6).
    weaker_first_order: "kappa(k_lambda)=kappa_X-1/(16*pi*lambda^2)+O(lambda^-4)"
  FINITE_P59_CANDIDATE:
    additional_assumption: >-
      the normalized finite Fourier projection correction E_lambda,N changes
      the second jet by O(lambda^-4) on N=lambda^2
    conclusion: "the same first-order curvature law for the actual project row q_{lambda,N}"
  LEMMA_7_3:
    supplies: "locally uniform convergence on closed substrips"
    rate_in_its_proof: "O(lambda^(-1/2-alpha)) on Re(s)=alpha, plus an unrated target tail"
    supplies_requested_two_jet_rate: false
    repair_status: "requires a new perturbative/tail theorem; it is not a reinterpretation of Lemma 7.3"
  FIXED_Z_AND_COMPACT:
    safe_additive_form: >-
      G_{q,N}(z)-X(z)
      = X(z)*z^2/(16*pi*lambda^2)+O_K(lambda^-4)
        + lower-window correction + finite-projection correction.
    ratio_form_guard: "use only off the zero set of X"
    O_z2_over_m: "conditional on uniform even analytic remainder bounds on a fixed compact; not a global estimate"

Q3_REMAINING_DELTA:
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL
  DEFINITIONS:
    alpha_G_m: "kappa(G_m)-kappa_X"
    alpha_q_m: "kappa(q_m)-kappa_X"
    delta_m: "kappa(G_m)-kappa(q_m)=alpha_G_m-alpha_q_m"
    exact_finite_row_formula: >-
      delta_m=(L_m^2/(2*pi^2))*sum_{k=1}^{N_m}
      (xi_{m,k}/xi_{m,0}-q_{m,k}/q_{m,0})/k^2.
  RATE_RELATION:
    T_m: "(L_m^2/(4*pi^2))*sum_{k>m}1/k^2 asymptotic to L_m^2/(4*pi^2*m)"
    trial_scale: "alpha_q_m=O(1/m)=o(T_m)"
    equivalence: "|delta_m|=O(T_m) iff |alpha_G_m|=O(T_m)"
    first_order_profile: "delta_m/T_m and alpha_G_m/T_m have the same limit if the finite trial crosswalk is proved"
  SUPPLIER_LANDSCAPE:
    changed_representation: true
    reason: >-
      delta is now a same-cell ground-versus-source-trial observable, so it can
      be attacked before comparing either row with Xi.
    solved: false
  GOOD_DIRECTION_DIAGNOSIS:
    finite_evidence: >-
      q and the ground have close low-order P59 shape/jet observables despite a
      useless relative Rayleigh quotient.
    theorem_status: DIAGNOSTIC_ONLY
    noncircular_source_statement_found: false
    forbidden_explanation: "the ground already approximates Xi on the window"
    paper_status: "the paper explicitly names accurate k_lambda-to-ground approximation as a missing step"

RANKED_DELTA_REPRESENTATIONS:
  1:
    code: R1_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE
    selected_after_crosswalk: true
    object: >-
      Bound the cross-multiplied anchored curvature functional on the exact
      source low-Rayleigh set containing the ground and q, without estimating
      their vector distance.
    theorem_id: P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE
    kill_power: 10/10
    preflight_cost: 3/10
    proof_cost_if_survives: 8/10
    discriminator: >-
      A source-specific dual/S-lemma certificate gives both signs of the
      curvature-functional bound before any spectral inverse or complement
      floor is introduced.
    falsifier: >-
      The exact finite low-Rayleigh admissible set contains two anchor-compatible
      rows whose curvature difference is bounded below independently of T_m.
  2:
    code: R2_TRIAL_RELATIVE_ONE_SHAPE
    object: >-
      Expand the source trial q directly in the even eigenbasis and prove that
      one coherent second mode carries the ground-trial compact defect, with a
      lower-order combined remainder.
    theorem_id: P59_TRIAL_RELATIVE_ONE_SHAPE_REMAINDER
    kill_power: 9/10
    preflight_cost: 4/10
    proof_cost_if_survives: 8/10
    discriminator: >-
      The second-mode coefficient and compact profile are source-coherent and
      the higher-mode remainder is o(T_m).
    falsifier: "the exact combined remainder remains a nonzero fraction of the observed defect"
  3:
    code: R3_TRIAL_RESIDUAL_ADJOINT_COBBOUNDARY
    object: >-
      Express the anchored curvature row as a source-explicit coboundary of
      K-lambda_1 before taking any inverse, then pair it with the trial residual.
    theorem_id: P59_TRIAL_CURVATURE_ADJOINT_COBBOUNDARY
    kill_power: 8/10
    preflight_cost: 2/10
    proof_cost_if_survives: 7/10
    discriminator: "the second-even-mode coefficient cancels exactly in the source identity"
    adverse_evidence: "the prior minimal-norm curvature dual certificate had gap_share approximately 1 on every registered cell"
    evidence_scope: FINITE_CELL
    evidence_verifier: CONDITIONAL
    falsifier: "the source coboundary has a nonzero second-mode component, forcing the collapsed gap"
  4:
    code: R4_WEIGHTED_DAVIS_KAHAN
    status: REJECT_AS_GAPFREE_GENERIC_THEOREM
    reason: >-
      Changing the output norm does not remove the need for coercivity in that
      norm; without a source identity it is a weighted complement-gap theorem.
    kill_scope: THEOREM_SHAPE
    repaired_use: "retain only after an independently proved weighted coercivity estimate"

PREDICTION_FATES:
  P_LOG_DERIVATIVE_EXPOSES_SOURCE_TAIL_BEFORE_GAP:
    probability: 0.35
    fate: REFUTED
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_R1_ONLY_RENAMES:
    probability: 0.70
    fate: CONFIRMED
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_TRIAL_JET_WITHIN_T:
    probability: 0.35
    fate: CONFIRMED_ON_REGISTERED_CELLS_ONLY
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_GROUND_TRIAL_JET_GAP_WITHIN_T:
    probability: 0.40
    fate: CONFIRMED_ON_REGISTERED_CELLS_ONLY
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_TRIAL_JET_WORSE_THAN_GROUND:
    probability: 0.65
    fate: REFUTED_ON_REGISTERED_CELLS
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_ZETA_CANCELLATION_CONFIRMED:
    probability: 0.85
    fate: REFUTED_AS_STATED_FOR_THE_FINITE_P59_PROJECT_ROW
    repaired_fate: CONFIRMED_FOR_THE_UNWINDOWED_E_MAP_MAIN_TERM
    scope: FINITE_CELL
    verifier: LEAN_PLUS_PAPER
  P_H8_FIRST_ORDER_CONFIRMED:
    probability: 0.75
    fate: CONFIRMED_AT_FORMAL_PERTURBATION_COEFFICIENT_LEVEL
    qualification: "the rigorous uniform remainder and finite-projection transfer remain open"
    scope: ABSTRACT
    verifier: PAPER
  P_DELTA_HAS_GAPFREE_SUPPLIER:
    probability: 0.30
    fate: UNRESOLVED
    note: "a gap-free candidate representation is named, but no supplier theorem is proved"
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
  P_DELTA_ATOM_IS_RENAMING:
    probability: 0.35
    fate: CONFIRMED_AT_RATE_EQUIVALENCE_WITH_REPRESENTATION_REPAIR
    note: "the asymptotic obligation is equivalent, but the source-facing object is better"
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL

SCOPED_KILLS:
  FINITE_P59_EQUALS_FULL_MELLIN:
    CODE: KILL_FINITE_P59_TRIAL_EQUALS_FULL_MELLIN_EXACTLY
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_FOURIER_PROJECTION_PLANT
    EVIDENCE_REF: D0PstarProjectedMellinCoordinate.lean@0c371b5f
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  PURE_ARCHIMEDEAN_FINITE_PHI:
    CODE: KILL_FINITE_PHI_AS_PURE_ARCHIMEDEAN_ENTIRE_FACTOR
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: TWO_EXACT_OMITTED_REMAINDERS_PLUS_TARGET_ZERO_DENOMINATOR
    EVIDENCE_REF: REQUEST_AND_PROJECTED_MELLIN_CROSSWALK
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  SECOND_ORDER_PLUS_SIGN:
    CODE: KILL_POSITIVE_SECOND_ORDER_TERM_IN_TRIAL_CURVATURE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_PRODUCT_SECOND_DERIVATIVE_SIGN
    EVIDENCE_REF: TRIAL_JET_REPORT_SECTION_4
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  GENERIC_GAPFREE_WEIGHTED_DAVIS_KAHAN:
    CODE: KILL_WEIGHTED_DAVIS_KAHAN_AS_GAPFREE_GENERIC_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: TWO_BY_TWO_COLLAPSED_OPERATOR_PLANT_AND_DUALCERT
    EVIDENCE_REF: edge_ledger_dualcert.md@0c371b5f
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_GENERIC_STATEMENT

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  PURPOSE: >-
    Turn the already-Lean-proved projected Mellin identity into an exact
    window-tail plus Fourier-projection-tail second-jet ledger on N=lambda^2.
  REGISTERED_PREDICTION:
    name: P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER
    probability: 0.55
  REQUIRED_OUTPUTS:
    - "the exact functions B_lambda and E_lambda,N with all normalization constants"
    - "their values and second derivatives at zero"
    - "an explicit bound on the induced curvature correction"
    - "the first nonzero endpoint/jump term in the Fourier tail"
    - "a proof target at O(lambda^-4), or a certified reason that this rate is false"
  SUCCESS: P59_FINITE_PROJECTED_TRIAL_JET_RATE_CROSSWALK
  FAILURE: P59_FINITE_PROJECTION_SECOND_JET_TAIL_NOT_LOWER_ORDER
  FALSIFIER: >-
    On the production law N=lambda^2, the projection or lower-window correction
    has a nonzero lambda^-2 coefficient, changes 1/(16*pi), or is not uniformly
    O(lambda^-4) through the second jet.

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same anchor-normalized finite ground transforms have only real zeros and
    converge locally uniformly to centeredXi on one cofinal family.
  ORIGINAL_REQUESTED_OBJECT: >-
    Exact trial second-jet asymptotic and an O(T_m) ground-trial curvature gap.
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "bounded ground curvature plus an independent moving-node identifying set"
    - "direct locally uniform ground convergence"
    - "a trial-relative one-shape compact expansion with vanishing amplitude and remainder"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: >-
    Separate the exact finite Fourier projection and multiplicative-window
    corrections before using the archimedean prolate jet.

LEAN_READY:
  ALREADY_LEAN:
    - Q3.RouteB.D0Pstar.selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
    - Q3.RouteB.proposition59RawTransform_secondDerivative_zero
    - Q3.RouteB.proposition59RawTransform_at_zero_eq_sqrt
  NEW_LOCAL_BOOKKEEPING:
    - P59_GROUND_TRIAL_SECOND_JET_DIFFERENCE
    - NORMALIZED_SECOND_JET_SUBTRACTION_IDENTITY
  DOES_NOT_CLOSE_COFINAL_RATE: true

NEW_ANALYTIC:
  - P59_LOWER_WINDOW_MELLIN_TWO_JET_TAIL
  - P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL
  - PROLATE_ZERO_MASS_LINE_SECOND_ORDER_PERTURBATION_WITH_REMAINDER
  - P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE
  - P59_TRIAL_RELATIVE_ONE_SHAPE_REMAINDER

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_ADJUDICATION_ONLY
  FUTURE_TASK_ID: GOAL058_P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY
  TARGET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
  TARGET: >-
    For real even full coefficient rows v and q with nonzero central
    coefficients, prove the exact P59 identity
    kappa(v)-kappa(q)
    = L^2/(2*pi^2) * sum_{k=1}^N (v_k/v_0-q_k/q_0)/k^2.
  INPUTS:
    - proposition59RawTransform_secondDerivative_zero
    - proposition59RawTransform_at_zero_eq_sqrt
  FORBIDDEN:
    - "real-zero hypotheses"
    - "spectral gap or eigenvector hypotheses"
    - "the paper k_lambda substituted for the finite projection"
    - "any cofinal rate claim"
    - "sorry, admit, exact?, new axiom"
  VALIDATION:
    workdir_q3:
      - "lake env lean Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean"
      - "lake build Q3.Proofs.RouteB.Proposition59GroundTrialSecondJetDifference"
    workdir_repo:
      - "scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean"
    expected_axioms: [propext, Classical.choice, Quot.sound]
  SUCCESS: P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY_KERNEL_GREEN
  FAILURE: P59_GROUND_TRIAL_SECOND_JET_NORMALIZATION_MISMATCH

CLOSES:
  - FALSE_FINITE_P59_EQUALS_UNPROJECTED_MELLIN_EXACTNESS
  - FALSE_FINITE_PHI_PURE_ARCHIMEDEAN_ENTIRENESS
  - SECOND_ORDER_TRIAL_CURVATURE_SIGN_AMBIGUITY
  - GENERIC_WEIGHTED_DAVIS_KAHAN_AS_GAPFREE_SUPPLIER
OPENS: []

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5
CURRENT_SMALLEST_GAP: P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL
```

## ROUTE MAP

| Object / route | Verdict | Decisive test | Main risk | Tags |
|---|---|---|---|---|
| Exact finite projected Mellin coordinate | **Already proved, but it is the projection object** | Reuse `selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate` | Silently replacing \(P_Nf_\lambda\) by \(f_\lambda\) | `[FINITE_CELL][LEAN]` |
| Pure archimedean continuum trial jet | **Formal coefficient survives** | Rigorous prolate perturbation plus Mellin two-jet remainder | Expanding-domain/singular-endpoint remainder is not controlled | `[COFINAL_FAMILY][CONDITIONAL]` |
| Finite P59 trial jet | **Primary open crosswalk** | Projection and lower-window corrections are \(O(\lambda^{-4})\) through two jets | Either correction changes the \(1/(16\pi)\) coefficient | `[COFINAL_FAMILY][CONDITIONAL]` |
| Ground–trial curvature sublevel envelope | **Best gap-free candidate after the crosswalk** | Two-sided source certificate controls the scalar observable on the low-Rayleigh set | The low-energy cone may have macroscopic curvature diameter | `[COFINAL_FAMILY][CONDITIONAL]` |
| Trial-relative one-shape theorem | **Runner-up** | One coherent second mode plus lower-order compact remainder | It recreates the same unproved profile convergence | `[COFINAL_FAMILY][CONDITIONAL]` |
| Weighted Davis–Kahan without coercivity | **Killed as a generic gap-free theorem** | — | The weighted inverse is still a complement gap in disguise | `[ABSTRACT][PAPER]` |

## 1. Source lock and byte verification

The controlling request was fetched from GitHub at commit
`0c371b5f67383759fcf5bd579953e3783cfe974a`. Its Git blob is
`22e2c22e79fbcf489c77b746bb6f90405fcf9d23`. Independent decoding gives
exactly `10163` bytes, `97` LF-terminated lines, and SHA-256

```text
a4ece72bae1a7227a03cfe3936a9a635ba8a4e7f1fe9058806d199b956008864
```

The six-field phase key is unchanged. `[ABSTRACT][PAPER]`

No post-request result is used. In particular, later branch diagnostics are
outside this adjudication's evidence lock. `[FINITE_CELL][PAPER]`

## 2. Q1 — exact derivation audit

### 2.1 The first claimed equality uses the wrong object

The project does not define the trial coefficient row as the complete Fourier
series of the paper function \(k_\lambda\). It defines the normalized finite
Galerkin projection.

Put

\[
L=2\log\lambda,\qquad
f_\lambda(x)=k_\lambda(e^x/\lambda),\qquad 0\le x\le L,
\]

and let

\[
U_n(x)=L^{-1/2}e^{2\pi i n x/L}.
\]

Let \(P_N\) be the orthogonal projection onto
\(\operatorname{span}\{U_n:|n|\le N\}\). If

\[
c_n=\langle U_n,f_\lambda\rangle,
\qquad
q_n=\frac{c_n}{\|P_Nf_\lambda\|_2},
\]

then the exact P59 identity is

\[
\boxed{
F_{q,N}(z)
=
\frac{e^{izL/2}}{\|P_Nf_\lambda\|_2}
\int_0^L
(P_Nf_\lambda)(x)e^{-izx}\,dx.
}
\tag{2.1}
\]

This is precisely the object distinction already enforced by
`D0PstarProjectedMellinCoordinate.lean`: the Mellin coordinate belongs to the
literal normalized projection. `[FINITE_CELL][LEAN]`

After the change \(x=\log(\lambda u)\), define

\[
H_\lambda(z)
=
\int_{\lambda^{-1}}^\lambda
k_\lambda(u)u^{-iz}\,d^*u.
\]

The phase cancels because \(L/2=\log\lambda\). Therefore

\[
H_\lambda(z)
=
e^{izL/2}\int_0^L f_\lambda(x)e^{-izx}\,dx.
\]

The exact finite correction is

\[
E_{\lambda,N}(z)
=
e^{izL/2}
\int_0^L((I-P_N)f_\lambda)(x)e^{-izx}\,dx,
\]

and

\[
\boxed{
F_{q,N}(z)
=
\|P_Nf_\lambda\|_2^{-1}
\left(H_\lambda(z)-E_{\lambda,N}(z)\right).
}
\tag{2.2}
\]

`[FINITE_CELL][PAPER]`

The equality \(F_q=\mathcal M(k_\lambda)(-iz)\) is therefore false for the
actual finite project row unless \(E_{\lambda,N}\equiv0\), which is not true
for a generic non-bandlimited \(k_\lambda\).

A decisive plant is

\[
f=U_0+\varepsilon U_{N+1},\qquad \varepsilon\ne0.
\]

Then \(P_Nf=U_0\), so the finite P59 transform ignores \(\varepsilon\), while
the full windowed transform contains a nonzero \(U_{N+1}\) term. This kills the
exact theorem shape, not merely the current proof attempt. `[ABSTRACT][PAPER]`

### 2.2 What the zeta cancellation actually cancels

For the unwindowed summation map

\[
\mathcal E(h)(u)=u^{1/2}\sum_{n\ge1}h(nu),
\]

one has, initially in a half-plane of absolute convergence and then by
continuation,

\[
\boxed{
\mathcal M(\mathcal E(h_\lambda))(-iz)
=
\zeta(w)M_\lambda(w),
\qquad
w=\frac12-iz.
}
\tag{2.3}
\]

For the limiting Hermite combination \(h\),

\[
\zeta(w)M_0(w)=\frac{\xi(w)}4.
\tag{2.4}
\]

This is the exact zeta cancellation mechanism. It concerns the full
\(\mathcal E(h_\lambda)\) main term. `[ABSTRACT][PAPER]`

The paper trial is restricted to
\([\lambda^{-1},\lambda]\). Since \(h_\lambda\) is supported in
\([-\lambda,\lambda]\), the upper tail is zero, but the lower tail is not
identically zero. Define

\[
B_\lambda(z)
=
\int_0^{\lambda^{-1}}
\mathcal E(h_\lambda)(u)u^{-iz}\,d^*u.
\]

Then

\[
\boxed{
H_\lambda(z)
=
\zeta(w)M_\lambda(w)-B_\lambda(z).
}
\tag{2.5}
\]

No estimate may erase \(B_\lambda\) before its value and two-jet are bounded.

Let

\[
X(z)=\frac{\operatorname{centeredXi}(z)}
           {\operatorname{centeredXi}(0)}
\]

and

\[
\Phi_\lambda^{\rm arch}(z)
=
\frac{M_\lambda(w)}{M_\lambda(1/2)}
\frac{M_0(1/2)}{M_0(w)}.
\]

For the unwindowed main term \(A_\lambda(z)=\zeta(w)M_\lambda(w)\),

\[
\frac{A_\lambda(z)}{A_\lambda(0)}
=
X(z)\Phi_\lambda^{\rm arch}(z).
\tag{2.6}
\]

For the actual windowed object,

\[
\boxed{
\frac{H_\lambda(z)}{H_\lambda(0)}
=
X(z)\Phi_\lambda^{\rm arch}(z)
+
\frac{
B_\lambda(0)A_\lambda(z)-A_\lambda(0)B_\lambda(z)
}{
A_\lambda(0)\bigl(A_\lambda(0)-B_\lambda(0)\bigr)
}.
}
\tag{2.7}
\]

For the finite projected object, a second exact correction is

\[
\boxed{
\frac{F_{q,N}(z)}{F_{q,N}(0)}
=
\frac{H_\lambda(z)}{H_\lambda(0)}
+
\frac{
E_{\lambda,N}(0)H_\lambda(z)
-
H_\lambda(0)E_{\lambda,N}(z)
}{
H_\lambda(0)\bigl(H_\lambda(0)-E_{\lambda,N}(0)\bigr)
}.
}
\tag{2.8}
\]

These two terms are the missing ledger. Calling the finite quotient “purely
archimedean” deletes both. `[COFINAL_FAMILY][PAPER]`

The literal quotient

\[
\frac{F_{q,N}(z)/F_{q,N}(0)}{X(z)}
\]

is meromorphic. It is entire only if every zero of \(X\) is canceled by
\(F_{q,N}\), which is an identification result, not an input.

The main factor \(\Phi_\lambda^{\rm arch}\) is holomorphic in the open centered
strip. Indeed, there \(0<\Re w<1\), while

\[
M_0(w)=\frac18\pi^{-w/2}\Gamma(w/2)w(w-1)
\]

is nonzero. The supplied derivation does not prove that this factor is entire
on \(\mathbb C\). `[ABSTRACT][PAPER]`

### 2.3 The prolate perturbation algebra

The differential-expression identity is exact:

\[
\boxed{
PW_\lambda
=
\lambda^2\left(-\partial_x^2+4\pi^2x^2\right)
+
\partial_x(x^2\partial_x).
}
\tag{2.9}
\]

Thus \(\varepsilon=\lambda^{-2}=m^{-1}\) is the natural formal perturbation
parameter. In the Hermite ladder basis,

\[
V=\partial_x(x^2\partial_x)=\frac{S^2-1}{4}
\]

couples only levels \(n\) and \(n\pm4\). The first-order \(h_0\leftrightarrow
h_4\) rotation cancels inside the zero-integral line, and one \(h_8\)
admixture remains with coefficient \(\sqrt{105}/(16\pi)\). This algebra gives

\[
[z^2]\Phi_\lambda^{\rm arch}
=
\frac1{16\pi m}+O(m^{-2}).
\]

The formal second-order calculation gives

\[
\Phi_\lambda^{\rm arch}(z)
=
1+
\frac{z^2}{16\pi m}
+
\frac1{m^2}
\left(
\frac{13z^2}{256\pi^2}
+
\frac{z^4}{512\pi^2}
\right)
+
O(m^{-3}).
\tag{2.10}
\]

`[ABSTRACT][PAPER]`

The curvature sign must now be applied. For anchored even functions,

\[
\kappa(X\Phi)=\kappa(X)-[z^2]\Phi.
\]

Therefore the repaired formal law is

\[
\boxed{
\kappa(k_\lambda)
=
\kappa_X
-
\frac1{16\pi m}
-
\frac{13}{256\pi^2m^2}
+
O(m^{-3}).
}
\tag{2.11}
\]

The plus sign on the second-order curvature term in the request is wrong. The
number \(13/(256\pi^2)\) is positive as a coefficient in
\([z^2]\Phi\), and negative after conversion to curvature.

The ladder coefficients are not yet a rigorous cofinal theorem. A proof still
needs analytic perturbation with a uniform remainder for the expanding
prolate problem, plus the two corrections in (2.7) and (2.8). The agent report
itself classifies its series as asymptotic rather than convergent.
`[COFINAL_FAMILY][CONDITIONAL]`

## 3. Q2 — the exact theorem that can honestly be targeted

There are two different theorems.

### 3.1 Continuum/windowed trial theorem

A rigorous source theorem may state:

> Let \(h_\lambda\) be the source-normalized zero-integral combination of
> \(h_{0,\lambda}\) and \(h_{4,\lambda}\). Assume a second-order prolate
> perturbation expansion in a norm controlling the Mellin transform and its
> first two \(z\)-derivatives on each closed substrip. Assume also that the
> lower-window correction \(B_\lambda\) has the corresponding
> \(O_K(\lambda^{-6})\) two-jet bound. Then
> \[
> \kappa(k_\lambda)
> =
> \kappa_X-\frac1{16\pi\lambda^2}
> -\frac{13}{256\pi^2\lambda^4}
> +O(\lambda^{-6}).
> \]

The weaker first-order target is

\[
\boxed{
\kappa(k_\lambda)
=
\kappa_X-\frac1{16\pi\lambda^2}
+O(\lambda^{-4}).
}
\tag{3.1}
\]

`[COFINAL_FAMILY][CONDITIONAL]`

### 3.2 Actual finite P59 trial theorem

For the project row \(q_{\lambda,N}\), theorem (3.1) additionally requires

\[
\boxed{
\kappa(F_{q_{\lambda,N}})
-
\kappa(H_\lambda)
=
O(\lambda^{-4})
\quad\text{on }N=\lambda^2.
}
\tag{3.2}
\]

By (2.2), this is a weighted Fourier-projection-tail theorem. It is not
supplied by the continuum perturbation calculation.

The exact quotient algebra is already available: if \(F=H-E\), then

\[
\boxed{
\kappa(F)-\kappa(H)
=
\frac{
H(0)E''(0)-H''(0)E(0)
}{
2H(0)(H(0)-E(0))
}.
}
\tag{3.3}
\]

Thus the minimal missing input is a bound on \(E_{\lambda,N}(0)\) and
\(E_{\lambda,N}''(0)\), with the exact project normalization.

This is the current smallest gap:

```text
P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL
```

`[COFINAL_FAMILY][CONDITIONAL]`

### 3.3 Relation to Lemma 7.3

Lemma 7.3 proves locally uniform convergence on closed substrips. Its displayed
estimate is only

\[
O(\lambda^{-1/2-\alpha})
\]

on the line \(\Re s=\alpha\), and its final target-tail step is unrated. It does
not prove the requested two-jet asymptotic. A two-jet rate can be obtained from
a new locally uniform rate by Cauchy estimates, but that rate must first be
proved. `[COFINAL_FAMILY][PAPER]`

Under the stronger perturbative and tail hypotheses, one can target on each
fixed compact \(K\) in the open strip the additive expansion

\[
\boxed{
G_{\lambda,N}(z)-X(z)
=
X(z)\frac{z^2}{16\pi\lambda^2}
+
O_K(\lambda^{-4}),
}
\tag{3.4}
\]

with the two correction ledgers included. This additive form remains typed at
zeros of \(X\). A ratio statement is legal only away from those zeros.

The stronger phrase

\[
\Phi_\lambda(z)=1+O(|z|^2/\lambda^2)
\]

is valid only on a fixed compact after one proves a uniform even analytic
remainder. It is not a global estimate. `[COFINAL_FAMILY][CONDITIONAL]`

## 4. Q3 — what remains after the trial jet is separated

### 4.1 Is \(\delta_m\) merely \(\alpha_m\) renamed?

Algebraically,

\[
\delta_m
=
\kappa(G_m)-\kappa(q_m)
=
\alpha_{G,m}-\alpha_{q,m}.
\]

The exact finite P59 second jet gives

\[
\boxed{
\delta_m
=
\frac{L_m^2}{2\pi^2}
\sum_{k=1}^{N_m}
\frac{
\xi_{m,k}/\xi_{m,0}
-
q_{m,k}/q_{m,0}
}{k^2}.
}
\tag{4.1}
\]

On the production schedule,

\[
T_m\sim\frac{L_m^2}{4\pi^2m},
\qquad
\alpha_{q,m}=O(1/m)=o(T_m).
\]

Hence, after the finite trial-jet crosswalk is proved,

\[
\boxed{
|\delta_m|=O(T_m)
\quad\Longleftrightarrow\quad
|\alpha_{G,m}|=O(T_m).
}
\tag{4.2}
\]

So the asymptotic wall is equivalent. The representation is nevertheless
better: \(\delta_m\) compares two source rows in the same finite carrier and
can be attacked without introducing the target zero divisor. This is
representation progress, not proof progress. `[COFINAL_FAMILY][CONDITIONAL]`

### 4.2 Why can \(q_m\) point in the right direction while its relative Ritz
quotient is useless?

No source theorem currently answers this.

The finite evidence is compatible with a large, extremely flat low-energy
geometry in which the full Rayleigh quotient is a poor coordinate for the
particular low-order P59 observable. The prolate construction can select the
correct transform shape while retaining tiny components in directions that
are cheap in Euclidean angle but enormous relative to the astronomically
small ground eigenvalue.

That is a diagnosis, not a theorem. The forbidden circular explanation is:

```text
both ground and trial approximate Xi on the window.
```

The trial-to-\(\Xi\) half is paper-proved. The ground-to-trial or ground-to-\(\Xi\)
half is exactly the missing step. The source paper explicitly labels accurate
\(k_\lambda\)-to-ground approximation as a remaining obstacle.
`[COFINAL_FAMILY][PAPER]`

### 4.3 Ranked noncircular suppliers

#### Rank 1 — source low-Rayleigh curvature envelope

Fix the source trial \(q_m\). Cross-multiply the anchored curvature observable:

\[
J_{q,m}(v)
=
q_{m,0}\sum_{k=1}^{N_m}\frac{v_k}{k^2}
-
v_0\sum_{k=1}^{N_m}\frac{q_{m,k}}{k^2}.
\]

Then

\[
\delta_m
=
\frac{L_m^2}{2\pi^2\,\xi_{m,0}q_{m,0}}
J_{q,m}(\xi_m).
\tag{4.3}
\]

The candidate theorem is a two-sided bound for \(J_{q,m}\) on an exact
source-defined normalized low-Rayleigh set that contains the ground state and
the trial, with a separate central-anchor lower bound. A dual quadratic or
S-lemma certificate could prove this without estimating
\(\|\xi_m-q_m\|\).

This route survives only if the observable diameter is small before any
spectral inverse appears. One exact finite witness in the admissible set with
macroscopic \(J_{q,m}\) kills it. `[COFINAL_FAMILY][CONDITIONAL]`

#### Rank 2 — trial-relative one-shape theorem

Expand \(q_m\) directly in a coherent even eigenbasis and prove

\[
G_m-Q_m=a_m\psi_{2,m}+R_m,
\]

where \(Q_m\) is the normalized P59 transform of the source trial,
\(a_m=O(T_m)\), \(\psi_{2,m}\) is compact-bounded, and
\(R_m=o(T_m)\) locally uniformly.

This avoids the target \(\Xi\) in the ground-trial step. It remains expensive:
coherent mode selection and the compact remainder are new analytic inputs.
`[COFINAL_FAMILY][CONDITIONAL]`

#### Rank 3 — source adjoint coboundary

Seek a source-explicit vector \(w_m\) such that the anchored curvature row is

\[
\ell_m=(K_m-\lambda_{1,m}I)w_m+\text{anchor term}
\]

before any inverse is taken. Pairing with the trial residual would then compute
\(\delta_m\).

The prior dual-certificate diagnostic is adverse: essentially all of the
minimal-norm curvature dual lies on the second eigenpair. Therefore this route
must exhibit an exact cancellation of that component. If it does not, it is
the dead absolute-gap route again. `[FINITE_CELL][CONDITIONAL]`

#### Rank 4 — weighted Davis–Kahan

A generic weighted Davis–Kahan theorem is not gap-free. It replaces the usual
gap by coercivity in the weighted geometry. Without an independent
source-specific weighted floor, it has only renamed the inverse.

Retain it only after such a floor is proved. Do not use it as the supplier.
`[ABSTRACT][PAPER]`

## 5. Prediction closeout

Probabilities are unchanged.

| Prediction | Probability | Fate | Tags |
|---|---:|---|---|
| `P_LOG_DERIVATIVE_EXPOSES_SOURCE_TAIL_BEFORE_GAP` | `0.35` | **REFUTED** | `[COFINAL_FAMILY][PAPER]` |
| `P_R1_ONLY_RENAMES` | `0.70` | **CONFIRMED** | `[COFINAL_FAMILY][PAPER]` |
| `P_TRIAL_JET_WITHIN_T` | `0.35` | **CONFIRMED on registered cells only** | `[FINITE_CELL][CONDITIONAL]` |
| `P_GROUND_TRIAL_JET_GAP_WITHIN_T` | `0.40` | **CONFIRMED on registered cells only** | `[FINITE_CELL][CONDITIONAL]` |
| `P_TRIAL_JET_WORSE_THAN_GROUND` | `0.65` | **REFUTED on registered cells** | `[FINITE_CELL][CONDITIONAL]` |
| `P_ZETA_CANCELLATION_CONFIRMED` | `0.85` | **REFUTED as stated for the finite P59 row; confirmed for the unwindowed main term** | `[FINITE_CELL][LEAN]` + `[ABSTRACT][PAPER]` |
| `P_H8_FIRST_ORDER_CONFIRMED` | `0.75` | **CONFIRMED at formal perturbation-coefficient scope** | `[ABSTRACT][PAPER]` |
| `P_DELTA_HAS_GAPFREE_SUPPLIER` | `0.30` | **UNRESOLVED** | `[COFINAL_FAMILY][CONDITIONAL]` |
| `P_DELTA_ATOM_IS_RENAMING` | `0.35` | **CONFIRMED at rate-equivalence scope, with a genuine representation repair** | `[COFINAL_FAMILY][CONDITIONAL]` |

No probability is edited after the evidence.

## 6. Lean-ready bookkeeping versus new mathematics

### Already Lean-proved

- the exact finite P59 transform and its second derivative;
- the exact central value;
- the exact identification of the selected projected Mellin coordinate with
  the raw transform of the projected coefficient row.

`[FINITE_CELL][LEAN]`

### Lean-ready local bookkeeping

- the exact ground-trial curvature-difference formula (4.1);
- the normalized second-jet subtraction identity (3.3).

These introduce no spectral assumption and no cofinal rate.
`[FINITE_CELL][PAPER]`

### New analytic mathematics

- a two-jet estimate for the lower multiplicative-window tail \(B_\lambda\);
- a two-jet estimate for the finite Fourier projection tail
  \(E_{\lambda,N}\) on \(N=\lambda^2\);
- a rigorous second-order prolate perturbation theorem for the zero-integral
  line;
- a gap-free source envelope for the ground-trial curvature observable, or a
  trial-relative one-shape theorem.

`[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Do not subtract the formal continuum trial jet from the finite ground jet yet.

First prove the exact corrected ledger

\[
\boxed{
G_{q,N}
=
X\Phi_\lambda^{\rm arch}
+
\mathcal B_\lambda
+
\mathcal P_{\lambda,N},
}
\]

where \(\mathcal B_\lambda\) is the normalized lower-window correction and
\(\mathcal P_{\lambda,N}\) is the normalized finite-projection correction.

The first decisive target is

\[
\boxed{
\kappa(\mathcal B_\lambda+\mathcal P_{\lambda,\lambda^2})
=
O(\lambda^{-4})
}
\]

in the exact quotient algebra, equivalently explicit
\(O(\lambda^{-4})\) bounds for the values and second derivatives entering
(2.7) and (2.8).

Registered prediction:

```yaml
P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER:
  probability: 0.55
```

If a \(\lambda^{-2}\) term survives, the claimed constant \(1/(16\pi)\) does
not belong to the actual finite P59 row and the current subtraction route is
killed. If the correction is \(O(\lambda^{-4})\), the trial jet becomes a
rigorous source input and the next route is the curvature sublevel envelope.

## STRONGEST ATTACK

The strongest objection is an object substitution:

> The continuum Mellin calculation is exact for \(k_\lambda\), so it is exact
> for the finite P59 coefficient row \(q_{\lambda,N}\).

It is not.

The project itself proves that the finite P59 row is the normalized projection
\(P_Nf_\lambda\). Formula (2.2) shows the missing term exactly. A high Fourier
mode plant changes the full Mellin transform while leaving the finite row
unchanged.

This defect is load-bearing because the target effect is only
\(1/(16\pi\lambda^2)\). A projection correction of the same order changes the
constant, and a correction of order \(T_m\) destroys the proposed separation
entirely.

The repaired statement is:

```text
The zeta factor cancels in the unwindowed E-map main term.
The actual finite trial equals that main term only after
lower-window and finite-projection corrections are carried and bounded.
```

No gap, no RH assumption, and no numerical fit can replace those two bounds.

## CODEX DIRECTIVE

No execution is authorized by this paper-only adjudication.

A later bounded transaction may formalize the finite identity:

```text
TASK_ID:
  GOAL058_P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  Proposition59GroundTrialSecondJetDifference.lean

PROVE:
  For real even full coefficient rows v and q with v_0 != 0 and q_0 != 0,

    kappa(F_v) - kappa(F_q)
      = L^2/(2*pi^2)
        * sum_{k=1}^N (v_k/v_0 - q_k/q_0)/k^2.

USE:
  proposition59RawTransform_secondDerivative_zero
  proposition59RawTransform_at_zero_eq_sqrt

FORBIDDEN:
  real-zero assumptions;
  eigenvector or gap assumptions;
  replacing the finite projection by paper k_lambda;
  any cofinal rate;
  sorry, admit, exact?, new axiom.

VALIDATE:

WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
  lake build Q3.Proofs.RouteB.Proposition59GroundTrialSecondJetDifference

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY_KERNEL_GREEN

FAILURE:
  P59_GROUND_TRIAL_SECOND_JET_NORMALIZATION_MISMATCH
```

## META CLOSEOUT

- **What became smaller?** The “exact trial jet” split into one pure
  archimedean main term and exactly two named corrections.
- **What was killed?** Exact equality between the finite P59 row and the full
  \(k_\lambda\) Mellin transform; entire pure-archimedean finite \(\Phi_m\);
  the positive sign of the second-order curvature coefficient; generic
  gap-free weighted Davis–Kahan.
- **What must not be tried again?** Dropping \(P_N\), erasing the lower window,
  dividing by \(\Xi\) at its zeros, or treating a formal perturbation series as
  a cofinal theorem.
- **Current smallest named gap:**
  `P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL`.
- **Next cheapest decisive test:** exact two-jet ledger for
  \(B_\lambda\) and \(E_{\lambda,\lambda^2}\), before any new eigensolve.
- **Fate of prior predictions:** all nine are scored without probability
  edits.
- **Memory entry:** the continuum \(h_8\) coefficient is useful only after the
  finite Fourier projection and lower-window corrections are proved lower
  order; \(\delta_m\) is rate-equivalent to the old curvature wall but is a
  better source-facing observable.

No Lean source was edited. No numerical run was started. No route promotion or
RH claim was made.
