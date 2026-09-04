# STATUS: RUN_P59_LADDER_FESHBACH_D2_REMAINDER_DISCRIMINATOR
```yaml
OPERATIVE_CLASS: RUN_P59_LADDER_FESHBACH_D2_REMAINDER_DISCRIMINATOR
PRIMARY: REPLACE_RAYLEIGH_SUBLEVEL_WIDTH_BY_EXACT_LADDER_FESHBACH_Y_COMPONENT
PRIMARY_COUNT: 1

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-D2SUPPLY
  BOUNDARY_ID: GOAL058_SECOND_MODE_OVERLAP_SUPPLIER_AFTER_TRIAL_CROSSWALK
  REQUEST_COMMIT: 1f41e4cbe20a672ed0b4c0b0c46da1c4e43aca3c
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SECOND_MODE_OVERLAP_SUPPLIER_AFTER_CROSSWALK_2026-09-04.txt
  REQUEST_GIT_BLOB: d0f6875cc15998a1504e825032f8406b250e31d0
  REQUEST_SHA256: 38da3012f2a5578af69adbe37a3ee7ad77f77e68bd64bcd8ecbb9c967db0fd2a
  REQUEST_BYTES: 11695
  REQUEST_LINES: 109
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_SUPPLIER_AFTER_TRIAL_CROSSWALK_2026-09-04.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  EVIDENCE_CUTOFF: 1f41e4cbe20a672ed0b4c0b0c46da1c4e43aca3c
  WRITE_BASE_HEAD: b9bb3f0273c33bfd4f166f598f25ccbf33b24597
  WRITE_BASE_HEAD_USED_AS_EVIDENCE: false
  POST_REQUEST_RESULTS_USED: false
  PARENT_TRIALJET: 33d863fa29e8686f1a372bfa2093a2407cc24f8e
  PARENT_RATE: 5aaa3d935ec51856b35e6dd5a2414a27ac5cbfcd
  PARENT_OVERLAP: af1d9ead928333a607fa15549c0623f9d4323b29
  PARENT_ONESHAPE: 2b11781f9df42ee6c257c4b3473df06e8c3de2c9
  TRIAL_JET_REPORT: docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT.md
  LEAN_SECOND_JET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean
  CONVENTION_CARD: docs/routeB_bus/CONVENTION_CARD_GOAL058.md

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

TOP_LEVEL_ADJUDICATION:
  R1_CURVATURE_RAYLEIGH_SUBLEVEL_ENVELOPE: KILLED_AS_GAP_FREE_SUPPLIER
  SOURCE_DEFINED_NON_RAYLEIGH_O_T_WIDTH_SET_FOUND: false
  R1_ROUTE_FAMILY_KILLED: false
  D2_THREE_BY_THREE_COMPRESSION_SOURCE_COMPUTABLE: true
  RAW_THREE_BY_THREE_COMPRESSION_DETERMINES_D2: false
  EXACT_MISSING_TERM: LADDER_FESHBACH_Y_COMPONENT
  KNOWN_LITERATURE_SECOND_EIGENVECTOR_ASYMPTOTIC: NOT_FOUND_IN_CITED_SOURCES
  QUADRATIC_COEFFICIENT_EXACT_IDENTITY: EXISTS_WITH_REMAINDER
  TRIAL_PROJECTION_ERROR_EQUALS_OVERLAP_TRANSFER_REMAINDER: false
  NEXT_ACTION: RUN_EXACT_LADDER_COMPRESSION_AND_FESHBACH_Y_COMPONENT_LEDGER

Q1_R1:
  VERDICT: KILL_P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE_AS_GAPFREE_D2_SUPPLIER
  EXACT_FINITE_IDENTITY:
    anchor: "e0^T v = 1"
    centre: "v_c = K^(-1)e0 / (e0^T K^(-1)e0)"
    minimum_energy: "epsilon_min = 1 / (e0^T K^(-1)e0)"
    width: "W(epsilon) = sqrt((epsilon-epsilon_min) * g)"
    dual_factor: "g = l_perp^T (P K P)^+ l_perp"
  CONSEQUENCE: >-
    A Rayleigh sublevel gives an O(T_m) curvature width only after the energy
    excess is itself controlled at the collapsed complementary scale. It does
    not remove that scale; it places it inside epsilon-epsilon_min.
  ABSTRACT_KILL_PLANT:
    matrix: "K = diag(mu1,mu2), mu1>0, mu2>0"
    anchor: "v0=1"
    functional: "l(v)=v1"
    sublevel: "v^T K v <= mu1 + mu2 R^2"
    witnesses: ["(1,R)", "(1,-R)"]
    width: "2R"
    conclusion: "the width can be arbitrarily large relative to any prescribed T"
  SOURCE_DEFINED_SET_AUDIT:
    exact_ground_eigenspace:
      ground_membership: true
      O_T_width: true
      admissibility: CIRCULAR_DEFINES_THE_GROUND
    real_zero_cone:
      ground_membership: true_under_simple_even
      O_T_width: false
      reason: "the source-specific real-zero predicate was already shown nonselective"
    trial_sampling_tube:
      source_defined: true
      ground_membership: OPEN_GROUND_TO_TRIAL_WALL
    one_shape_ladder_tube:
      source_defined: true
      ground_membership_and_width: EXACTLY_THE_D2_AND_REMAINDER_TARGET
    extra_affine_curvature_constraint:
      O_T_width: true
      admissibility: CIRCULAR_RESTATES_THE_CONCLUSION
  SOURCE_DEFINED_ADMISSIBLE_SET_NAMED: NONE_WITH_INDEPENDENT_GROUND_MEMBERSHIP_AND_O_T_WIDTH
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: EXACT_ELLIPSOID_WIDTH_IDENTITY_AND_TWO_DIMENSIONAL_COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_A_RAYLEIGH_ONLY_GAPFREE_SUPPLIER
  REOPEN_TRIGGER: >-
    A source-defined invariant set with an independently proved inclusion of
    the actual ground row and a proved curvature width O(T_m), using neither a
    Rayleigh excess at the collapsed gap scale nor the desired curvature bound.
  SCOPE: ABSTRACT
  VERIFIER: PAPER

Q2_A_LADDER_COMPRESSION:
  VERDICT: SOURCE_COMPUTABLE_WITH_EXACT_FESHBACH_REMAINDER
  LADDER:
    basis:
      - "b0 = y_m"
      - "b1 = normalized projection of x^2*y_m orthogonal to b0"
      - "b2 = normalized projection of x^4*y_m orthogonal to span{b0,b1}"
    synthesis: "B_m : C^3 -> H_m, B_m^* B_m = I"
    projections: "P_m=B_m B_m^*, Q_m=I-P_m"
  BLOCKS:
    A_m: "B_m^* K_m B_m"
    C_m: "B_m^* K_m Q_m"
    D_m: "Q_m K_m Q_m"
  SOURCE_COMPUTABILITY:
    entry_formula: >-
      (A_m)_{ab} = sum_{r,s} conjugate((B_m)_{r,a})
      * tau_entry_m(r,s) * (B_m)_{s,b}.
    finite: true
    exact_Xi_samples: true
    required_guards:
      - "the three ladder rows are linearly independent"
      - "the second eigenvalue of A_m is simple, or use its spectral projection"
      - "the compressed second vector is oriented coherently"
  COMPRESSED_OBJECT:
    second_pair: "A_m z_{2,m}^{(3)} = mu_{2,m}^{(3)} z_{2,m}^{(3)}"
    lifted_vector: "u_{2,m}^{(3)} = B_m z_{2,m}^{(3)}"
    compressed_overlap: "d_{2,m}^{(3)} = <y_m,u_{2,m}^{(3)}> = (z_{2,m}^{(3)})_0"
  ACTUAL_EIGENPAIR:
    equation: "K_m u_{2,m} = lambda_{2,m} u_{2,m}"
    coordinates: "p_m=B_m^*u_{2,m}, r_m=Q_m u_{2,m}"
    block_equations:
      - "(A_m-lambda_{2,m} I)p_m + C_m r_m = 0"
      - "C_m^*p_m + (D_m-lambda_{2,m} I)r_m = 0"
  EXACT_REMAINDER:
    raw: >-
      d_{2,m}-d_{2,m}^{(3)}
      = <e0,p_m-z_{2,m}^{(3)}>.
    normalized: >-
      If s_m=||p_m|| and pHat_m=p_m/s_m, then
      d_{2,m}-d_{2,m}^{(3)}
      = (s_m-1)d_{2,m}^{(3)}
        + s_m<e0,pHat_m-z_{2,m}^{(3)}>.
    bound: >-
      abs(d2-d2_3) <= abs(1-s)*abs(d2_3)
      + s*||pHat-z2_3||.
  FESHBACH_FORM:
    guard: "D_m-lambda_{2,m} I is invertible on Q_m H_m"
    tail: "r_m=-(D_m-lambda_{2,m} I)^(-1) C_m^* p_m"
    effective_equation: >-
      [A_m-C_m(D_m-lambda_{2,m} I)^(-1)C_m^*]p_m
      = lambda_{2,m}p_m.
    interpretation: >-
      The actual in-ladder component is an eigenvector of the Feshbach-corrected
      matrix, not of the raw compression A_m.
  FIRST_FAILURE: >-
    Prove an O(T_m) bound for the e0-coordinate change caused by the Feshbach
    self-energy, together with coherent selection of the compressed second mode.
  DIRECTIONAL_ACCURACY_PLANT:
    family: "u(theta)=sqrt(1-theta^2)b1+theta*y"
    observation: "<u(theta),b1> tends to 1 while <y,u(theta)>=theta"
    conclusion: >-
      99.5 percent directional accuracy toward the quadratic ladder direction
      does not give relative control of d2, because d2 lives in the small
      orthogonal correction.
  SCOPE: FINITE_CELL
  VERIFIER: PAPER

Q2_B_LITERATURE_OBJECT:
  VERDICT: NO_PROVEN_SECOND_EIGENVECTOR_ASYMPTOTIC_FOUND
  CORRECT_NAME: >-
    Finite Ritz compression, or after elimination of the complement, the
    Feshbach effective matrix of the localized CCM Weil form on the
    Xi-polynomial sampling subspace.
  NOT_ESTABLISHED_AS:
    - "an unconditional Xi^2 Hankel moment matrix"
    - "the Connes-Consani prolate/Sonin operator"
    - "Suzuki's screw-function operator"
  WHY_NOT_HANKEL_UNCONDITIONALLY: >-
    The matrix contains the windowed Weil form applied to sampled and
    band-limited Xi-polynomial rows. The zero-side representation is indefinite
    off RH, and the nonzero energy is carried by interpolation and band-limit
    corrections rather than by a bare Xi^2 moment functional.
  CITED_SOURCE_AUDIT:
    CCM_2511_22755: "trial-to-Xi and finite Weil machinery; no second-Ritz-vector asymptotic for this ladder compression"
    CONNES_CONSANI_MOSCOVICI_2310_18423: "prolate/Sonin spaces and semilocal operators; different object"
    SUZUKI_2606_09096: "screw-function operator realization; large-window spectral picture does not supply this compressed second-vector theorem"
  UNIVERSAL_LITERATURE_NONEXISTENCE_CLAIM: false
  FAILURE_TYPE: NO_SOURCE
  EPISTEMIC_STATUS: RESEARCH_DEBT
  REOPEN_TRIGGER: "a theorem with an exact object crosswalk to A_m or its Feshbach correction and a proved second-eigenvector asymptotic"
  SCOPE: ABSTRACT
  VERIFIER: PAPER

Q2_C_EXACT_D2_THEOREM:
  TARGET: P59_SECOND_MODE_OVERLAP_O_L_MINUS_2
  EXACT_STATEMENT: >-
    There exist C and m0 such that for every production cell m>=m0,
    abs(<y_m,u_{2,m}>) <= C*T_m,
    where u_{2,m} is the coherently selected unit second even eigenvector.
  MULTIPLICITY_SAFE_STATEMENT: >-
    Replace the chosen u_{2,m} by the spectral projection onto the isolated
    second even spectral cluster and bound the y_m-component of that projection.
  LADDER_SUFFICIENT_INTERFACE:
    - "abs(d_{2,m}^{(3)}) <= C0*T_m"
    - "abs(<e0,p_m-z_{2,m}^{(3)}>) <= C1*T_m"
  STRONGER_ASYMPTOTIC_INTERFACE:
    - "d_{2,m}^{(3)}/T_m -> D0"
    - "<e0,p_m-z_{2,m}^{(3)}>/T_m -> D1"
    - "then d_{2,m}/T_m -> D0+D1"
  FIRST_FAILURE_POINT: P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M
  SECOND_FAILURE_POINT: P59_COMPRESSED_SECOND_RITZ_VECTOR_ASYMPTOTIC
  RAW_COMPRESSION_ALONE_SUFFICIENT: false
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL

Q3_FUNCTIONAL_RANKING:
  - rank: 1
    code: P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY
    identity: >-
      2*pi*d2_m = ell1_m * [alpha_m*M_m-E_m],
      M_m=Tr_m(z^2*X*F2_m),
      E_m=Tr_m(B_m*F2_m),
      B_m=G_m-X+alpha_m*z^2*X.
    status: EXACT_PAPER_IDENTITY
    advantage: "no absolute spectral gap"
    first_uncontrolled_term: "the ground-side remainder E_m"
    object_guard: >-
      E_m here is not the finite projection tail E_{lambda,N} from the trial
      jet crosswalk. They are different objects.
    trial_split: >-
      B_m = [Q_m-X+alpha_q,m*z^2*X]
            + [(G_m-Q_m)+(alpha_m-alpha_q,m)z^2*X].
      The trial crosswalk controls the first bracket's own jet and projection
      corrections; the second bracket is the ground-to-trial wall.
    falsifier: >-
      M_m tends to zero or changes sign without a source mechanism, or
      E_m/(alpha_m*M_m) remains a nonvanishing fraction.
  - rank: 2
    code: P59_XI_LADDER_FESHBACH_Y_COMPONENT
    identity: "d2-d2_3=<e0,p-z2_3>, with p governed by the corrected 3x3 effective matrix"
    status: EXACT_FINITE_ALGEBRA
    advantage: "all finite entries are source-defined"
    first_uncontrolled_term: "the scalar e0-component of the Feshbach correction"
    falsifier: >-
      A precision- and N-stable remainder comparable to or larger than T_m, or
      instability of d2_n/T_m under the nested ladder V2,V3,V4.
  - rank: 3
    code: DIRECT_Y_BLOCK_SCHUR_OVERLAP
    identity: >-
      With u2=d2*y+r, r perpendicular to y, b=QKy and D=QKQ,
      r=-d2*(D-lambda2 I)^(-1)b and
      abs(d2)^(-2)=1+||(D-lambda2 I)^(-1)b||^2.
    status: EXACT_UNDER_INVERTIBILITY
    advantage: "directly targets d2"
    defect: >-
      An O(T_m) upper bound for d2 needs a matching lower bound on the resolvent
      response, which is inverse spectral geometry and may reopen the collapsed gap.
    falsifier: "the inverse estimate can only be proved through 1/dist(lambda2,spectrum(D))"
  - rank: 4
    code: PHYSICAL_SECOND_MOMENT_OF_THE_GROUND
    status: CONDITIONAL_PROFILE_EXTRACTOR_NOT_AN_EXACT_SELECTOR
    defect: >-
      One second-moment functional cannot separate u2 from higher modes without
      the one-shape remainder theorem; vectors can share the same moment and
      have different y-overlap.
    falsifier: "construct a higher-mode perturbation in the kernel of the moment functional with nonzero y-overlap"
  - rank: 5
    code: FUCHS_WINDOW_DERIVATIVE_OF_LAMBDA1
    status: KILLED_AS_DIRECT_GAPFREE_D2_SUPPLIER
    reason: >-
      Hellmann-Feynman determines <u1,K' u1>, not <y,u2>. Eigenvector derivative
      formulas introduce 1/(lambda2-lambda1).
    rotation_plant: >-
      K(L)=U(L)diag(lambda1(L),lambda2(L))U(L)^* has the same eigenvalue curves
      and lambda1 derivative for arbitrary rotations U(L), while the overlap
      of a fixed y with u2 can vary arbitrarily.
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: ISOSPECTRAL_ROTATION_COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_A_DIRECT_OVERLAP_IDENTITY
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

RANKED_NEXT_ACTIONS:
  - rank: 1
    code: RUN_P59_LADDER_FESHBACH_D2_REMAINDER_PREFLIGHT
    kill_power: 10/10
    cost: 1/10
    execution_in_this_verdict: false
    inputs: "existing certified cells and exact tau_entry/Xi-sample rows"
    outputs:
      - "orthonormal V2,V3,V4 ladder bases"
      - "exact compressed matrices A_m^(n)"
      - "coherently oriented second Ritz vectors and d2_m^(n)"
      - "exact actual scalar remainder d2_m-d2_m^(n)"
      - "lifted residual and Feshbach self-energy diagnostics"
      - "ratios d2_m^(n)/T_m and (d2_m-d2_m^(n))/T_m"
    pass: >-
      rigorous upper envelopes show both the compressed overlap and the exact
      scalar remainder are O(T_m), with stable nested-ladder selection.
    fail: >-
      the raw compression is not a supplier if the exact scalar remainder is
      not lower order or the nested compressed second vector is not coherent.
  - rank: 2
    code: TRY_SOURCE_BOUND_FOR_CURVATURE_TRANSFER_REMAINDER
    kill_power: 9/10
    cost: 5/10
    target: "E_m=Tr_m(B_m F2_m)=O(T_m) or o(T_m) after the exact trial/ground split"
  - rank: 3
    code: TRY_SCALAR_FESHBACH_SELF_ENERGY_ASYMPTOTIC
    kill_power: 8/10
    cost: 7/10
    target: "the y-coordinate of the effective second vector, without an operator-norm bound on the whole inverse"

DISCRIMINATOR:
  NAME: P59_LADDER_FESHBACH_Y_COMPONENT_RATIO
  FORMULAS:
    compressed: "D_m^(n)=d2_m^(n)/T_m"
    remainder: "R_m^(n)=(d2_m-d2_m^(n))/T_m"
  PASS_CONDITION: >-
    On one precommitted nested ladder, prove uniform upper bounds for D_m^(n)
    and R_m^(n), or a stronger convergent asymptotic ledger, with coherent mode
    selection and exact source entries.
  FAILURE_CONDITION_FOR_RAW_V3_SUPPLIER: >-
    A source-certified lower bound or exact asymptotic showing that the scalar
    Feshbach remainder is not O(T_m), or failure of coherent second-mode
    selection for A_m^(3).
  FINITE_DIAGNOSTIC_FAILURE_SCOPE: "kills the frozen V3 candidate, not the whole cofinal theorem"
  ZERO_CONSISTENT_RESULT: INCONCLUSIVE
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL

SCOPED_KILLS:
  R1_RAYLEIGH_SUBLEVEL:
    CODE: KILL_P59_CURVATURE_RAYLEIGH_SUBLEVEL_AS_GAPFREE_D2_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_S_LEMMA_WIDTH_AND_TWO_DIMENSIONAL_PLANT
    PINNED_EVIDENCE: "REQUEST_COMMIT item 5 plus Q1 abstract plant"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_STATED
    CARD: C10_FUNCTIONAL_NOT_SURROGATE
  RAW_LADDER_COMPRESSION:
    CODE: KILL_RAW_V3_COMPRESSION_AS_COMPLETE_D2_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_BLOCK_EIGEN_EQUATIONS
    PINNED_EVIDENCE: "Q2_A_LADDER_COMPRESSION"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_WITHOUT_FESHBACH_REMAINDER
    CARD: C04_SAME_COORDINATES_TWO_LAWS
  TRIAL_E_SUBSTITUTION:
    CODE: KILL_TRIAL_PROJECTION_E_AS_GROUND_TRANSFER_REMAINDER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_OBJECT_DECOMPOSITION
    PINNED_EVIDENCE: "Q3 rank 1 object guard"
    EPISTEMIC_STATUS: WRONG_OBJECT
    CARD: C04_SAME_COORDINATES_TWO_LAWS
  WINDOW_DERIVATIVE:
    CODE: KILL_LAMBDA1_WINDOW_DERIVATIVE_AS_DIRECT_D2_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: ISOSPECTRAL_ROTATION_COUNTEREXAMPLE
    PINNED_EVIDENCE: "Q3 rank 5 rotation plant"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_STATED

PREDICTION_FATES:
  P_ENVELOPE_WIDTH_AT_TRIAL_LEVEL_GG_T:
    probability: 0.90
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_WIDTH_AT_LAMBDA2_LEVEL_GG_T:
    probability: 0.70
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_CENTRE_CURVATURE_NEAR_GROUND:
    probability: 0.80
    fate: CONFIRMED_EXACTLY
    scope: FINITE_CELL
    verifier: PAPER_PLUS_ARB_INTERVAL
  P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER:
    probability: 0.55
    fate: ON_TRACK_NOT_COFINALLY_SCORED
    note: >-
      The exact tail formula and the clean m=83 diagnostic support it, but the
      requested source asymptotic remains unproved.
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
  P_R1_KILLED_AS_STATED:
    probability: 0.80
    fate: CONFIRMED_WITH_THEOREM_SHAPE_SCOPE
    scope: ABSTRACT
    verifier: PAPER
  P_LADDER_COMPRESSION_COMPUTABLE:
    probability: 0.60
    fate: CONFIRMED_WITH_SIMPLE_MODE_AND_FESHBACH_REMAINDER_GUARDS
    scope: FINITE_CELL
    verifier: PAPER
  P_LADDER_IS_KNOWN_OBJECT:
    probability: 0.35
    fate: REFUTED_AS_A_CITED_PROVEN_SECOND_EIGENVECTOR_ASYMPTOTIC
    note: "the compression has a standard Ritz/Feshbach description, but no cited source supplies the requested asymptotic"
    scope: ABSTRACT
    verifier: PAPER
  P_QUADRATIC_COEFFICIENT_HAS_SOURCE_IDENTITY:
    probability: 0.30
    fate: CONFIRMED_WITH_REMAINDER_AND_OBJECT_GUARDS
    note: >-
      Exact curvature-transfer and block-Schur identities exist; neither by
      itself proves d2=O(T_m), and the trial projection remainder is not the
      ground transfer remainder.
    scope: FINITE_CELL
    verifier: PAPER

LEAN_READY:
  ALREADY_LEAN_GREEN:
    - P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY
  LOCAL_TARGETS:
    - P59_FINITE_TRIAL_SAMPLING_IDENTITY
    - P59_FINITE_PROJECTION_TAIL_VALUE_AND_SECOND_JET
    - P59_S_LEMMA_CENTRE_AND_WIDTH_IDENTITY
    - P59_XI_LADDER_COMPRESSION_BLOCK_EQUATIONS
    - P59_XI_LADDER_D2_EXACT_REMAINDER
    - P59_DIRECT_Y_BLOCK_SCHUR_OVERLAP_IDENTITY
    - P59_TWO_DIMENSIONAL_RAYLEIGH_SUBLEVEL_WIDTH_PLANT

NEW_ANALYTIC:
  - P59_SECOND_MODE_SELECTION_COHERENCE
  - P59_COMPRESSED_SECOND_RITZ_VECTOR_ASYMPTOTIC
  - P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M
  - P59_SECOND_MODE_OVERLAP_O_L_MINUS_2
  - P59_CURVATURE_TRANSFER_GROUND_REMAINDER_O_T_M
  - P59_SOURCE_SPECIFIC_NON_RAYLEIGH_ADMISSIBLE_TUBE

CODEX_DIRECTIVE:
  PRESENT_BECAUSE_LEAN_READY_ITEM_EXISTS: true
  EXECUTION_AUTHORIZED_BY_THIS_VERDICT: false
  TASK_ID: P59_XI_LADDER_FESHBACH_EXACT_REMAINDER
  TARGET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean
  CLOSES:
    - P59_XI_LADDER_COMPRESSION_BLOCK_EQUATIONS
    - P59_XI_LADDER_D2_EXACT_REMAINDER
  OPENS: []
  REQUIRED:
    - "define an orthonormal Fin 3 ladder synthesis B and P=B B*, Q=I-P"
    - "define A=B* K B, C=B* K Q, D=Q K Q"
    - "prove the two projected eigen-equations for an exact Hermitian eigenpair"
    - "prove d2=<e0,B*u> and d2-d2_3=<e0,p-z2_3>"
    - "under invertibility, prove the exact Feshbach effective equation"
    - "include the u(theta) directional-accuracy plant"
  FORBIDDEN:
    - "assume the scalar remainder is small"
    - "identify the raw compression eigenvector with the full eigenvector"
    - "introduce a complement-floor or desired O(T_m) premise"
    - "use post-request numerical results as proof"
  VALIDATION:
    - "lake env lean Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean"
    - "lake build Q3.Proofs.RouteB.P59XiLadderFeshbachRemainder"
    - "scripts/q3_check.sh Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean"
  EXPECTED_AXIOMS: [propext, Classical.choice, Quot.sound]
  SUCCESS_CODE: P59_XI_LADDER_FESHBACH_EXACT_REMAINDER_LEAN
  FAILURE_CODE: P59_XI_LADDER_FESHBACH_EXACT_REMAINDER_TYPE_MISMATCH

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized finite-ground entire family has only real zeros and
    converges locally uniformly to centeredXi on one production cofinal path.
  ORIGINAL_REQUESTED_OBJECT: P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "d2_m=O(T_m), compact boundedness of the second profile, and a vanishing combined remainder imply ground convergence"
    - "the exact curvature-transfer identity plus source bounds on alpha_m, M_m and E_m implies d2_m=O(T_m)"
    - "direct local-uniform ground-to-trial convergence bypasses d2"
  FAILURE_TYPE: COUNTEREXAMPLE_FOR_R1_AND_NO_DERIVATION_FOR_D2_RATE
  EPISTEMIC_STATUS:
    R1_RAYLEIGH_ONLY: MATHEMATICALLY_DEAD_AS_STATED
    D2_RATE: RESEARCH_DEBT
    WHOLE_ROUTE: UNRESOLVED
  NOVELTY_AXIS: >-
    Source-specific asymptotics of the Xi-polynomial ladder Feshbach
    y-component inside the collapsed finite Weil spectrum.
  REOPEN_TRIGGERS:
    R1: "an independently source-certified O(T_m)-width admissible set containing the ground"
    D2: "a source theorem bounding the compressed overlap and exact scalar Feshbach remainder by T_m"

CANDIDATE_REREPRESENTATIONS:
  - code: R1_LADDER_FESHBACH_SCALAR_COMPONENT
    rank: PRIMARY
    kill_power: 10/10
    cost: 4/10
  - code: R2_CURVATURE_TRANSFER_WITH_EXACT_TRIAL_GROUND_SPLIT
    rank: RUNNER_UP
    kill_power: 9/10
    cost: 6/10
  - code: R3_DIRECT_Y_BLOCK_SCHUR_RESPONSE
    rank: DIAGNOSTIC
    kill_power: 8/10
    cost: 5/10
    gap_reopening_risk: HIGH

CLOSES:
  - P59_CURVATURE_RAYLEIGH_SUBLEVEL_AS_GAPFREE_SUPPLIER_ADJUDICATION
  - P59_LADDER_COMPRESSION_SOURCE_COMPUTABILITY_ADJUDICATION
  - P59_QUADRATIC_COEFFICIENT_IDENTITY_ADJUDICATION
OPENS: []

NEXT_LOAD_BEARING_GAP: P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M
PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## ROUTE MAP

The request lock is clean. The committed bytes reproduce the stated Git blob,
11,695-byte size, 109 LF-terminated lines, and SHA-256 exactly. The six-field
phase key and the production object family are unchanged. No result committed
after the request lock was used in this adjudication. `[ABSTRACT][PAPER]`

The route has now compressed to one scalar, but not to a free scalar. The
finite projected-trial jet is no longer the issue: its exact projection and
lower-window corrections are lower order at the level tested by the request,
and the project has a kernel-green coefficient-row formula for second-jet
differences. The surviving unknown is

\[
d_{2,m}=\langle y_m,u_{2,m}\rangle,
\]

plus the compact higher-mode remainder required by the parent one-shape
identity. `[COFINAL_FAMILY][CONDITIONAL]`

### Q1 — R1 is dead as stated

The S-lemma computation is decisive. For an anchored positive quadratic form,
the curvature range on a Rayleigh sublevel has width

\[
W(\varepsilon)=\sqrt{(\varepsilon-\varepsilon_{\min})g}.
\]

This is an exact ellipsoid-support formula. The two-dimensional diagonal plant
shows that no bound of order \(T_m\) follows from a Rayleigh level alone: choose
the level to contain \((1,\pm R)\), and the functional width is \(2R\).

Therefore `P59_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE` is killed as a
**gap-free supplier theorem shape**. It is not evidence that no future
source-specific invariant set can work. It says that a set described only by
anchor plus Rayleigh excess cannot do the job without paying the collapsed
complementary geometry. `[ABSTRACT][PAPER]`

No current alternative set survives the noncircularity audit. The exact ground
eigenspace is circular. The real-zero cone is not selective. A trial tube has
no proved ground-membership theorem. A ladder tube requires the very
\(d_2\)-and-remainder estimate under review. Thus there is no presently named
source-defined set with both independent ground membership and proved
\(O(T_m)\) curvature width.

### Q2(a) — the 3x3 object is computable; its missing scalar is exact

Let \(B_m\) have the orthonormal ladder columns \(y_m\), the centered quadratic
row and the centered quartic row. Then

\[
A_m=B_m^*K_mB_m
\]

is a literal 3x3 matrix. Each entry is a finite double sum of `tau_entry`
against exact Xi-sample rows, so it is source-defined and finite-cell
computable. Selecting a single second Ritz vector additionally requires a
simple compressed second eigenvalue and an orientation; otherwise the correct
object is its spectral projection.

The raw compression is not the actual effective operator. If
\(u_{2,m}=B_mp_m+r_m\), with \(r_m\perp V_3\), then

\[
(A_m-\lambda_{2,m}I)p_m+C_mr_m=0,
\qquad
C_m^*p_m+(D_m-\lambda_{2,m}I)r_m=0.
\]

When the complement inverse exists,

\[
\left[A_m-C_m(D_m-\lambda_{2,m}I)^{-1}C_m^*\right]p_m
=\lambda_{2,m}p_m.
\]

Hence the exact missing scalar is

\[
d_{2,m}-d_{2,m}^{(3)}
=\langle e_0,p_m-z_{2,m}^{(3)}\rangle.
\]

This is the **ladder Feshbach y-component**. It is not controlled by the fact
that the full vector is visually close to the quadratic ladder direction.
The plant

\[
u(\theta)=\sqrt{1-\theta^2}\,b_1+\theta y
\]

has cosine tending to one with \(b_1\), while its overlap with \(y\) is exactly
\(\theta\). Since \(d_2\) lives in the small correction, a 99.5% shape match can
still have order-one relative error in the target scalar.

### Q2(b) — standard finite object, no cited asymptotic theorem

The honest name is a **Ritz compression** of the localized Weil form, or after
eliminating the complement, a **Feshbach effective matrix** on the
Xi-polynomial sampling subspace. It is not presently crosswalked to a standard
Xi-weighted Hankel moment matrix. The cited Connes/Sonin and Suzuki operator
families are adjacent spectral constructions, not this m-dependent compressed
matrix, and no cited theorem supplies the requested second-eigenvector
asymptotic.

This is a `NO_SOURCE` result, not a universal nonexistence theorem. A future
paper theorem reopens the question only if it identifies the exact compression
or its self-energy-corrected form, with the same window, normalization and
production schedule. `[ABSTRACT][PAPER]`

### Q2(c) — exact theorem and first failure

The consumer-spendable statement is

\[
\exists C,m_0\ \forall m\ge m_0:\quad
|\langle y_m,u_{2,m}\rangle|\le C T_m.
\]

A valid ladder proof may split this into

\[
|d_{2,m}^{(3)}|\le C_0T_m,
\qquad
|d_{2,m}-d_{2,m}^{(3)}|\le C_1T_m.
\]

The first failure is not construction of the 3x3 matrix. It is the bound on the
**y-coordinate of the Feshbach correction**. The next failure is the asymptotic
selection of the second Ritz vector itself. A norm or principal-angle estimate
that is merely \(o(1)\) is insufficient; the scalar target is already of order
\(T_m\).

### Q3 — functional identities ranked

The best exact identity remains

\[
2\pi d_{2,m}=\ell_{1,m}(\alpha_mM_m-E_m).
\]

It pays no absolute gap. But `E_m` in this identity is the ground-side pairing
of the two-jet remainder. It is **not** the finite trial projection tail
`E_{lambda,N}` whose second derivative was made explicit by the trial crosswalk.
Substituting one for the other is a wrong-object error. Splitting through the
trial leaves a second bracket containing \(G_m-Q_m\), which is the original
same-family wall.

The ladder/Feshbach scalar is ranked second and is the cheapest new
discriminator because it exposes exactly the component missed by the raw
polynomial picture. The direct one-block Schur formula targets \(d_2\) even
more directly, but a rate from it is likely to require inverse spectral
geometry. A physical second moment is only a profile extractor until the
higher-mode remainder is controlled. A Fuchs/Hellmann-Feynman derivative of
\(\lambda_1\) does not identify \(d_2\): isospectral rotations preserve the
eigenvalue derivative while changing the eigenvectors, and differentiating an
eigenvector reintroduces \((\lambda_2-\lambda_1)^{-1}\).

## FINAL PROPOSAL

Run one bounded, source-locked discriminator on the existing data and no new
mathematical assumption:

```text
RUN_P59_LADDER_FESHBACH_D2_REMAINDER_PREFLIGHT
```

Build the nested ladder compressions \(V_2,V_3,V_4\), compute the coherent
second Ritz vectors, and report both the compressed overlap and the exact
scalar remainder in units of \(T_m\). The decisive quantity is not the norm of
the omitted vector; it is its contribution to the \(y\)-coordinate.

This verdict does not execute that test. It also does not use any result created
after the request lock.

## STRONGEST ATTACK

The strongest objection is that the observed 99.7% containment in
\(\operatorname{span}\{y,yx^2,yx^4\}\) should already make the 3x3 compression
sufficient. That conclusion is false without an energy-invariance statement.
A subspace can approximate an eigenvector in Euclidean norm while the Ritz
vector of the compressed operator points elsewhere, because a tiny omitted
component can carry a huge Rayleigh penalty. Even if the lifted Ritz vector is
close in norm, \(d_2\) can live entirely in the small correction, as the
\(u(\theta)\) plant shows.

The repaired statement is therefore not “the ladder fails.” It is:

> the raw ladder compression is only the head; the source supplier must control
> the scalar y-component of its Feshbach tail correction at the \(T_m\) scale.

## CODEX DIRECTIVE

A Lean-ready exact structural target exists, so one directive is recorded but
not authorized for execution by this paper-only verdict:

```text
TASK_ID: P59_XI_LADDER_FESHBACH_EXACT_REMAINDER
TARGET: prove the exact block equations, Feshbach equation and
        d2-d2^(3) y-coordinate identity for a Fin 3 orthonormal ladder.
DO NOT: assume the remainder is small, introduce a complement floor, or identify
        the raw compressed vector with the full second eigenvector.
GATE: lake env lean + lake build + scripts/q3_check.sh;
      every printed theorem must have [propext, Classical.choice, Quot.sound].
```

## META CLOSEOUT

**What became smaller?** The curvature route and the ladder route now meet at
one explicit scalar:

```text
P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M.
```

**What was killed?** Rayleigh-sublevel curvature width as a gap-free supplier;
raw 3x3 compression as a complete supplier; substitution of the trial
projection tail for the ground transfer remainder; and the window derivative
of \(\lambda_1\) as a direct overlap identity.

**What must not be tried again?** Do not infer a small target coordinate from a
high cosine, do not call the raw Ritz compression the effective operator, and
do not rename a collapsed-gap Rayleigh tolerance as an S-lemma envelope.

**Current smallest named gap:** `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M`.

**Next cheapest decisive test:** the exact nested-ladder/Feshbach scalar ledger
with the frozen source rows and no post-hoc subspace selection.

**Prediction fates:** all probabilities are preserved in the YAML ledger. The
R1 kill and compression computability predictions are confirmed; the claimed
available literature asymptotic is refuted; the existence of an exact
quadratic-coefficient identity is confirmed with a remainder and object guard.

```yaml
iteration:
  target: REQ-2026-09-04-D2SUPPLY
  status: PROGRESS
  failed_strategy: Rayleigh_sublevel_width_as_gap_free_curvature_supplier
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M
  invariant_learned: the small d2 coordinate lives in the correction, so scalar control is stricter than shape control
  forbidden_future_move: identify raw ladder compression or trial projection error with the full effective ground correction
  next_decisive_test: RUN_P59_LADDER_FESHBACH_D2_REMAINDER_PREFLIGHT
  progress_class: FALSIFICATION_AND_REPRESENTATION_PROGRESS
  route_score: 5
```
