# STATUS: RUN_P59_ANCHORED_ONE_SHAPE_FUNCTIONAL_DISCRIMINATOR
```yaml
OPERATIVE_CLASS: RUN_P59_ANCHORED_ONE_SHAPE_FUNCTIONAL_DISCRIMINATOR
PRIMARY: ADJUDICATE_ONE_SHAPE_BY_EXACT_ANCHORED_EIGENBASIS_IDENTITY
PRIMARY_COUNT: 1

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-ONESHAPE
  BOUNDARY_ID: GOAL058_ONE_SHAPE_DEVIATION_AND_XI_POLYNOMIAL_LADDER
  REQUEST_COMMIT: 202080c29cfc85d6623935c8dafec0c8b3499040
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ONE_SHAPE_DEVIATION_2026-09-04.txt
  REQUEST_GIT_BLOB: 4b9285303d992a256f33c0c57e92d2e2a9209bda
  REQUEST_SHA256: d4439898e03c8ec44d75a1e842fab51ce35efc8fb5e7c7cb53c3ca2e5c84f355
  REQUEST_BYTES: 7610
  REQUEST_LINES: 82
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ONE_SHAPE_DEVIATION_AND_XI_POLYNOMIAL_LADDER_2026-09-04.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: 9821f627
  PARENT_VERDICT_WINDLOCK: 7a78088f
  PARENT_VERDICT_LEAKAGE: 9a202947a0de5ac3c139ac81ce8d4bd3e2034cc9
  PARENT_VERDICT_ZEROPIN: 1529837d895f531330acfa4d81d96c83779a75d7
  PARENT_VERDICT_QUASIEIGEN: 9b8226246adda225c10bca322d75782c8c98dd5e
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
  ONE_SHAPE_PICTURE: SURVIVES_AS_ANCHORED_TWO_MODE_EXPANSION_CANDIDATE
  TWO_LEVEL_DEGENERATE_PERTURBATION_LABEL: NOT_JUSTIFIED
  EXACT_ANCHORED_EIGENBASIS_IDENTITY: PAPER_PROVED
  A_M_O_L_MINUS_2: DIAGNOSTICALLY_SUPPORTED_NOT_PROVED
  RAW_U2_COORDINATE_DECAY_REQUIRED: false
  ANCHOR_RATIO_IS_RATE_CARRIER: true
  HIGHER_MODE_REMAINDER_IS_LOAD_BEARING: true
  XI_POLYNOMIAL_LADDER_AS_RAW_TRIAL: REJECT_CURRENT_ATTEMPT
  XI_POLYNOMIAL_LADDER_AS_PICTURE: RETAIN
  DEGREE_ORDERING_FROM_WINDOW_TRUNCATION_ALONE: KILLED_THEOREM_SHAPE
  PROLATE_EQUALS_FESHBACH_CORRECTION: OPEN_SAME_FAMILY_WALL

Q1:
  VERDICT: REPAIR_TO_EXACT_ANCHORED_EIGENBASIS_DECOMPOSITION
  NOTATION:
    transform: "T_m(v) = F_{m,v}"
    anchor: "ell_m(v) = F_{m,v}(0)"
    target: "X = Xi / Xi(0)"
    ground: "G_m = T_m(u_{1,m}) / ell_m(u_{1,m})"
    xi_sample_row: "y_m, normalized by ell_m(y_m)=1"
    xi_sample_interpolation_error: "e_m = T_m(y_m) - X"
    eigen_expansion: "y_m = sum_j d_{j,m} u_{j,m}"
    anchored_mode_shape: "psi_{j,m} = T_m(u_{j,m}) - ell_m(u_{j,m}) X"
  EXACT_IDENTITY: >-
    d_{1,m} ell_{1,m} (G_m-X)
    = e_m - sum_{j>=2} d_{j,m} psi_{j,m}.
  TWO_MODE_FORM:
    scalar: "a_m = -d_{2,m}/(d_{1,m} ell_{1,m})"
    remainder: >-
      R_m = (e_m - sum_{j>=3} d_{j,m} psi_{j,m})
            /(d_{1,m} ell_{1,m})
    conclusion: "G_m-X = a_m psi_{2,m} + R_m"
  REQUIRED_NONDEGENERACY:
    - "d_{1,m} != 0"
    - "ell_m(u_{1,m}) != 0"
  CORRECTION_TO_QUESTION_I:
    reject: "prove the anchored u_1 transform converges to X as an input"
    reason: "that is the desired ground-to-X conclusion"
    sufficient_structural_input:
      - "psi_{2,m} tends locally uniformly to one fixed psi, or is uniformly compact-bounded"
      - "the Xi-sample interpolation error e_m is controlled"
  LOAD_BEARING_RATE_INPUTS:
    - "a_m = O(L_m^-2)"
    - "R_m = o(1) on each fixed compact; for a first-order profile theorem require R_m=o(L_m^-2)"
  WHICH_IS_LOAD_BEARING: >-
    The scalar ratio in (ii) carries the observed L^-2 rate, but it is not the
    only load-bearing input. A compact higher-mode/interpolation remainder
    bound is independent and mandatory. Item (i) is structural only after it
    is repaired to psi_{2,m}->psi; u_1->X may not be assumed.
  WHY_RAW_L2_COORDINATE_CAN_BE_FLAT: >-
    d_{2,m} may stay O(1) while the anchored coefficient a_m decays because the
    denominator d_{1,m} ell_{1,m} grows like L_m^2. This exactly matches the
    observation that the decay lives in anchor normalization rather than in
    the unit-vector l2 coordinate.
  RELATIVE_RITZ_OPTION:
    unit_row: "q_m=y_m/||y_m|| with coefficients tilde_d_{j,m}"
    formula: >-
      p_m=sum_{j>=2}|tilde_d_{j,m}|^2
      <= epsilon_m/(lambda_{2,m}/lambda_{1,m}-1);
      if p_m<1, then |d_{2,m}/d_{1,m}|^2 <= p_m/(1-p_m).
    hypotheses:
      - "lambda_{1,m}>0"
      - "ordered positive Hermitian spectrum"
      - "q_m is unit-normalized in the relevant Hilbert norm"
    role: OPTIONAL_UPPER_BOUND_ON_RAW_COMPONENT_RATIO
    does_not_explain_observed_rate: true
    warning: >-
      Avoiding an absolute gap is real, but the numerator must then be proved
      small relative to lambda_1. The collapsed scale has not disappeared;
      it has moved into epsilon_m.
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

Q2:
  VERDICT: EXACT_CORRECTION_STATEMENT_YES_SMALL_CORRECTION_AND_DEGREE_ORDER_NO
  EXACT_LADDER_OBJECT:
    sample_operator: "S_m(p) = the finite P59/Nyquist row sampled from X(z)p(z)"
    interpolation_correction: "r_{m,p} = T_m(S_m(p)) - X p"
    identity: "T_m(S_m(p)) = X p + r_{m,p}"
    at_target_zero: "X(rho)=0 implies T_m(S_m(p))(rho)=r_{m,p}(rho)"
  ZERO_SUM_CONSEQUENCE:
    unconditional_real_even: "<S_m(p),K_even S_m(p)> = sum_rho r_{m,p}(rho)^2"
    under_RH: "the same expression becomes a positive squared-sampling energy"
    guard: "off RH the cutoff-free zero-side sum is real but indefinite"
  EIGENVECTOR_LADDER_STATEMENT:
    exact_but_tautological: >-
      For the ladder subspace V_{m,d}=S_m({even p: deg p<=2(d-1)}), every
      eigenvector has an orthogonal decomposition u=P_{V_{m,d}}u+(I-P)u.
    nontrivial_missing_statement: >-
      The principal angle between the first d eigenspace and V_{m,d} tends to
      zero with a quantitative K-energy bound on the correction.
    derivable_from_K_equals_sum_EEt_alone: false
  DEGREE_ORDERING:
    from_window_truncation_alone: false
    exact_plant: >-
      In a two-dimensional ladder basis (1,x^2), let evaluation vectors be
      E_1=(sqrt(2),0), E_2=(0,1). Then K=sum E_r E_r^T=diag(2,1), so the x^2
      direction leaks less than the constant direction. A Gram representation
      alone therefore permits the reverse order.
    actual_CCM_possibility: OPEN_SOURCE_SPECIFIC
    required_extra_structure:
      - "a commuting prolate/Sturm operator"
      - "total positivity or an exact variation-diminishing theorem"
      - "a source-specific monotonic concentration theorem"
  SCOPE: ABSTRACT
  VERIFIER: PAPER

Q3:
  VERDICT: PICTURE_NORM_AND_RAYLEIGH_NORM_ARE_DIFFERENT
  EXACT_SPECTRAL_LEDGER: >-
    For a unit candidate q=alpha u_1+sum_{j>=2} r_j u_j,
    Rayleigh(q)-lambda_1=sum_{j>=2}(lambda_j-lambda_1)|r_j|^2.
  FIT_WARNING: >-
    The reported 1.8e-4 is a relative fit error on one compact in function
    values. It is not an l2 coefficient error and not a K-energy error.
  QUANTITATIVE_INTERPRETATION: >-
    Even if 1.8e-4 were an l2 error, its square is about 3.24e-8. Multiplication
    by lambda_typ/lambda_1 can make the Rayleigh penalty enormous. The measured
    mu_1/lambda_1 values 1.7e6, 1.0e16 and 3.4e36 are the direct evidence that
    the visually tiny correction lives in spectrally expensive directions.
  FESHBACH_CORRECTION:
    block_formula: >-
      With ladder projection P and Q=I-P, an exact eigenvector at eigenvalue
      lambda has complement r=-(QKQ-lambda I)^(-1)QKP p whenever the inverse
      exists.
    interpretation: >-
      This is the band-limited Rayleigh/Feshbach correction omitted by the raw
      polynomial ladder.
    leakage_minimizing_wording: >-
      It is a positive leakage minimizer only when the zero-side form is a
      positive Gram form. Unconditionally it is the Hermitian Rayleigh/Feshbach
      correction.
  PROLATE_TRIAL:
    numerical_evidence: STRONGLY_FAVORS_CAPTURE
    theorem_status: OPEN
    exact_equality_claim: REJECT
    reason: >-
      The prolate packet minimizes a time-frequency concentration defect, not
      definitionally the CCM Weil Feshbach correction. Proving that the former
      approximates the latter is exactly the surviving ground-to-trial
      same-family wall.
  HONEST_TRIAL_DESCRIPTION: >-
    Use a source-defined prolate packet and then prove that its transform admits
    an X*p plus band-limit-correction representation. Defining the correction
    as the K-minimizer would define the ground state itself and be circular.
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

Q4:
  VERDICT: RUN_EXACT_ANCHORED_COEFFICIENT_AND_MULTI_FUNCTIONAL_CHECK
  NO_ABSOLUTE_GAP_REQUIRED: true
  EXACT_SCALAR:
    formula: "a_spec(m) = -d_{2,m}/(d_{1,m} ell_{1,m})"
  INDEPENDENT_EXTRACTORS:
    endpoint: "a_7(m)=Delta_m(7)/psi_{2,m}(7)"
    second_jet: >-
      a_kappa(m) =
      (kappa(G_m)-kappa(X))/kappa(psi_{2,m}),
      where kappa(f)=-f''(0)/2 and kappa(psi_{2,m})!=0
    fixed_grid_least_squares: "a_LS on the precommitted x-set {3,5,7,10,12}"
  EXACT_SECOND_JET_LEDGER: >-
    If Delta_m=a_m psi_{2,m}+R_m, then
    kappa(G_m)-kappa(X)=a_m kappa(psi_{2,m})+kappa(R_m).
  REQUIRED_OUTPUTS_ON_EXISTING_CELLS:
    cells: [83, 163]
    outputs:
      - "a_spec L_m^2, a_7 L_m^2, a_kappa L_m^2 and a_LS L_m^2"
      - "the exact all-mode remainder R_m from the eigenbasis identity"
      - "the two-mode share of the compact norm and second jet"
      - "precision stability and the already-required N-geometry checks"
  FALSIFIER:
    exact_identity_failure: >-
      Any mismatch in the finite all-mode identity above conventions/roundoff
      kills the implementation or basis lock immediately.
    one_shape_failure: >-
      After precision and N stability, a stable nonzero lower bound for
      L_m^2 ||R_m||_K, or a stable separation among a_spec, a_7, a_kappa and
      a_LS after the exact higher-mode correction, refutes the claimed
      first-order one-shape asymptotic.
    source_ratio_failure: >-
      If a_spec L_m^2 is not bounded/stabilizing while Delta_m L_m^2 is, then
      the second mode is not the source of the observed rate.
  ENERGY_RATIO_FORMULAS:
    rank: SECONDARY_DIAGNOSTIC_ONLY
    reason: >-
      The raw Xi-polynomial Rayleigh-Ritz family has already failed at the
      lambda_1 scale, so energy ratios of Xi and Xi*x^2 rows are not the first
      discriminator.
  SCOPE: FINITE_CELL
  VERIFIER: CONDITIONAL

RANKED_NEXT_ACTIONS:
  - rank: 1
    code: RUN_EXACT_ANCHORED_EIGENBASIS_DECOMPOSITION
    kill_power: 10/10
    cost: 1/10
    output: "a_spec plus exact all-mode remainder on the already computed cells"
  - rank: 2
    code: TRY_ANCHOR_GROWTH_AND_HIGHER_MODE_TAIL
    kill_power: 10/10
    cost: 7/10
    target: >-
      d_{1,m}ell_{1,m} grows at least cL_m^2, d_{2,m}=O(1),
      psi_{2,m}->psi locally uniformly, and the normalized interpolation plus
      higher-mode remainder is o(L_m^-2).
  - rank: 3
    code: TRY_SOURCE_DEFINED_PROLATE_FESHBACH_CROSSWALK
    kill_power: 10/10
    cost: 9/10
    target: >-
      Identify the source prolate correction with the CCM low-energy Feshbach
      correction without defining it from the ground state.

SCOPED_KILLS:
  RAW_XI_POLYNOMIAL_LADDER:
    CODE: KILL_RAW_XI_POLYNOMIAL_LADDER_AS_CURRENT_TRIAL
    KILL_SCOPE: ATTEMPT
    KILL_EVIDENCE_KIND: PRECOMMITTED_FINITE_RAYLEIGH_RITZ_REFUTATION
    PINNED_EVIDENCE: >-
      request blob 4b9285303d992a256f33c0c57e92d2e2a9209bda, INTAKE item 4
    EPISTEMIC_STATUS: RESEARCH_DEBT_FOR_CORRECTED_LADDER
    REOPEN_TRIGGER: >-
      a source-defined band-limit correction with a cofinal K-energy estimate,
      not additional uncorrected Xi-polynomial degrees
  DEGREE_ORDERING_FROM_TRUNCATION:
    CODE: KILL_LEAKAGE_DEGREE_ORDER_FROM_WINDOW_TRUNCATION_ALONE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_TWO_DIMENSIONAL_GRAM_COUNTEREXAMPLE
    PINNED_EVIDENCE: "this verdict, Q2 exact plant"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_GENERIC_STATEMENT
    REOPEN_TRIGGER: >-
      an additional source-specific commuting, total-positive, Sturm or
      concentration-order theorem

PREDICTION_FATES:
  P_DEVIATION_IS_SECOND_EIGENVECTOR_SHAPE:
    probability: 0.65
    fate: REFUTED_AS_UNANCHORED_STATEMENT
    repaired_successor: SUPPORTED_ON_REPORTED_CELLS_NOT_PROVED
  P_DEVIATION_L2_LAW:
    probability: 0.70
    fate: CONFIRMED_ON_REPORTED_FIXED_X_CELLS
    theorem_status: NOT_PROVED
  P_LADDER4_CAPTURES_LAMBDA1:
    probability: 0.55
    fate: REFUTED
  P_LADDER4_DEFECT_SMALL:
    probability: 0.60
    fate: REFUTED
  P_LADDER_ADMIXTURE_L2_LAW:
    probability: 0.60
    fate: REFUTED

  P_ONE_SHAPE_IS_TWO_LEVEL_PERTURBATION:
    probability: 0.60
    fate: PARTIALLY_REFUTED
    note: >-
      An exact anchored two-mode expansion exists, but no degenerate-operator
      perturbation theorem or negligible higher-mode remainder has been proved.
  P_SECOND_JET_EQUALS_A_TIMES_KAPPA_PSI:
    probability: 0.55
    fate: CONFIRMED_AS_EXACT_LINEAR_CONSEQUENCE_WITH_REMAINDER
    note: "it identifies a only when kappa(R_m) is controlled"
  P_LADDER_STATEMENT_DERIVABLE:
    probability: 0.45
    fate: CONFIRMED_ONLY_IN_EXACT_CORRECTION_TERM_FORM
    note: "smallness of the correction is new analytic work"
  P_LEAKAGE_ORDERING_PROVABLE_FROM_TRUNCATION:
    probability: 0.35
    fate: REFUTED_AS_GENERIC_THEOREM_SHAPE

LEAN_READY:
  - "finite anchored eigenbasis decomposition and formula for a_spec"
  - "finite all-mode remainder identity"
  - "second-jet extractor identity with explicit remainder"
  - "abstract relative-Ritz upper bound under positive-spectrum hypotheses"
  - "finite Feshbach block identity"
  - "two-dimensional counterexample to degree ordering from Gram form alone"

NEW_ANALYTIC:
  - "P59 Xi-sample interpolation error on fixed compacts"
  - "anchor growth d_{1,m}ell_{1,m} asymptotics"
  - "local-uniform convergence of psi_{2,m} to a fixed shape"
  - "higher-mode anchored tail o(L_m^-2)"
  - "source-defined prolate-to-Weil-Feshbach correction crosswalk"
  - "any source-specific ladder degree ordering"

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same anchor-normalized finite ground transforms converge locally
    uniformly to Xi/Xi(0) on one cofinal family.
  ORIGINAL_REQUESTED_OBJECT: >-
    a fixed second-eigenvector deviation shape with O(L^-2) coefficient and an
    Xi-times-even-polynomial eigenvector ladder
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "direct fixed-compact bound ||G_m-X||_K -> 0"
    - "exact anchored mode expansion plus one scalar ratio and a vanishing tail"
    - "bounded curvature plus a source-locked identifying set, as in the existing Vitali branch"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: ANCHORED_LOW_MODE_ASYMPTOTICS_AND_SOURCE_DEFINED_BANDLIMIT_CORRECTION
  REOPEN_TRIGGER: >-
    a proof of the anchor-ratio asymptotic and higher-mode compact tail, or a
    source-defined prolate/Feshbach intertwiner

REGISTERED_PREDICTIONS:
  P_ANCHOR_RATIO_EXPLAINS_L2:
    statement: "a_spec(m)L_m^2 stabilizes and agrees with a_7 and a_kappa"
    probability: 0.72
    fate: PENDING
  P_TWO_MODE_REMAINDER_IS_LOWER_ORDER:
    statement: "L_m^2 ||R_m||_K tends to zero on each fixed compact"
    probability: 0.42
    fate: PENDING
  P_PROLATE_CAPTURES_FESHBACH_CORRECTION:
    statement: "the source prolate correction approximates the CCM Feshbach correction cofinally"
    probability: 0.58
    fate: PENDING

CLOSES:
  - RAW_XI_POLYNOMIAL_LADDER_AS_CURRENT_TRIAL_ATTEMPT
  - LEAKAGE_DEGREE_ORDER_FROM_WINDOW_TRUNCATION_ALONE
OPENS: []

BOUNDARY:
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_RUN_PERFORMED: false
  JUDGE_KERNEL_RERUN: false
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  RH_CLAIM: false
  HONESTY_STATE: CHALLENGER_NOT_RH
  BUS_010: VOID

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
NEXT_LOAD_BEARING_GAP: P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL
```

## ROUTE MAP

The **one-shape observation survives**, but not under the name “two-level
degenerate perturbation theorem.” No operator family of the form
\(K_m=K_\infty+\varepsilon_m V+o(\varepsilon_m)\), no isolated limiting
two-dimensional cluster and no effective perturbation matrix have been
source-locked. The correct object is an exact **anchored eigenbasis
decomposition**. `[COFINAL_FAMILY][PAPER]`

The raw polynomial ladder is now quarantined as a trial. Its visual fit is
useful for choosing coordinates, but its finite Rayleigh ratios show that it
does not live at the ground-energy scale. Adding further uncorrected powers is
not an authorized response. `[FINITE_CELL][CONDITIONAL]`

The current cheapest route is therefore:

```text
exact anchored coefficient identity
→ independent second-jet / fixed-node discriminator
→ anchor-ratio asymptotic + higher-mode tail
→ fixed-compact ground-to-Xi convergence.
```

This avoids a uniform absolute gap. It does not claim that the collapsed
spectral scale disappears from every possible proof: a relative-Ritz proof
would still have to control its numerator relative to \(\lambda_1\).

## Q1 — exact repaired theorem shape

Let \(T_m\) be the linear Proposition-59 transform and
\(\ell_m(v)=T_m(v)(0)\). Let \(u_{j,m}\) be the unit even eigenbasis, let

\[
G_m=\frac{T_m(u_{1,m})}{\ell_m(u_{1,m})},
\qquad
X=\frac{\Xi}{\Xi(0)},
\]

and let \(y_m\) be the Xi-sample row normalized by \(\ell_m(y_m)=1\). Write

\[
y_m=\sum_j d_{j,m}u_{j,m},
\qquad
e_m=T_m(y_m)-X,
\]

and define the anchored mode shapes

\[
\psi_{j,m}=T_m(u_{j,m})-\ell_m(u_{j,m})X.
\]

Then direct linear algebra gives

\[
\boxed{
d_{1,m}\ell_{1,m}(G_m-X)
=
e_m-\sum_{j\ge2}d_{j,m}\psi_{j,m}.
}
\]

Hence

\[
\boxed{
G_m-X=a_m\psi_{2,m}+R_m,
\qquad
a_m=-\frac{d_{2,m}}{d_{1,m}\ell_{1,m}},
}
\]

with

\[
R_m=
\frac{e_m-\sum_{j\ge3}d_{j,m}\psi_{j,m}}
     {d_{1,m}\ell_{1,m}}.
\]

This identity explains the observer’s central fact: the raw \(u_2\)-coordinate
may remain near \(0.04\), while the function-level coefficient is
\(O(L_m^{-2})\), because the rate can sit entirely in the anchor denominator.

The corrected supplier list is therefore:

1. \(d_{1,m}\ell_{1,m}\neq0\);
2. \(\psi_{2,m}\to\psi\) locally uniformly, or at least compact-uniform
   boundedness;
3. \(a_m=O(L_m^{-2})\);
4. \(R_m=o(L_m^{-2})\) for a genuine first-order shape theorem, or \(R_m=o(1)\)
   merely for convergence.

Assuming \(u_{1,m}\) itself converges to \(X\) is circular: that is the desired
conclusion. The observer’s item (ii) carries the rate only after the
higher-mode and Xi-interpolation remainder is controlled.

A relative-Ritz inequality is available in principle. For the unit row
\(q_m=y_m/\|y_m\|\), write
\(p_m=1-|\langle q_m,u_{1,m}\rangle|^2\). Under a positive ordered spectrum,

\[
p_m
\le
\frac{\varepsilon_m}{\lambda_{2,m}/\lambda_{1,m}-1}.
\]

If \(p_m<1\), this also bounds the scale-free ratio
\(|d_{2,m}/d_{1,m}|^2\le p_m/(1-p_m)\). It is optional here. The exact
anchor ratio already avoids the absolute gap, and the data indicate that the
denominator \(d_1\ell_1\), not decay of \(d_2\), is the dominant mechanism.

## Q2 — the exact ladder and the missing theorem

For an even polynomial \(p\), let \(S_m(p)\) be its Xi-sample row and define

\[
r_{m,p}=T_m(S_m(p))-Xp.
\]

Then the exact statement is simply

\[
\boxed{
T_m(S_m(p))=Xp+r_{m,p}.
}
\]

At any target zero \(\rho\) of \(X\),

\[
T_m(S_m(p))(\rho)=r_{m,p}(\rho).
\]

Combined with the cutoff-free Weil identity, this turns the Rayleigh value of
the sampled ladder row into the zero-side energy of the interpolation
correction. Off RH this is an indefinite square sum; under RH it is a positive
sampling norm.

What does **not** follow from \(K=\sum E E^\mathsf T\) is that \(r_{m,p}\) is
small, that the first eigenspace lies close to the polynomial ladder, or that
leakage is ordered by polynomial degree. Every positive semidefinite matrix is
a sum of rank-one Gram terms. In the two-dimensional ladder basis
\((1,x^2)\), the exact plant

\[
K=
\begin{pmatrix}
2&0\\0&1
\end{pmatrix}
=
(\sqrt2,0)(\sqrt2,0)^\mathsf T
+
(0,1)(0,1)^\mathsf T
\]

makes the \(x^2\) direction leak less than the constant direction. Therefore
window truncation plus Gram form alone cannot select \(X\cdot1\).

A nontrivial ladder theorem would have to prove a vanishing principal angle
between the first \(d\) eigenspace and the sampled \(X\)-polynomial subspace.
That requires extra source structure such as a commuting prolate/Sturm
operator, total positivity or a concentration-order theorem. None is supplied
by the parent identities.

## Q3 — why a 0.02% picture can be a catastrophic trial

A compact relative fit and a Rayleigh fit use different norms. For a unit
candidate

\[
q=\alpha u_1+\sum_{j\ge2}r_j u_j,
\]

the exact spectral ledger is

\[
\operatorname{Rayleigh}(q)-\lambda_1
=
\sum_{j\ge2}(\lambda_j-\lambda_1)|r_j|^2.
\]

The reported \(1.8\times10^{-4}\) is a function-value fit on one compact. It is
not a coefficient norm and not a \(K\)-energy norm. Even pretending it were an
\(l^2\) error gives a squared error of about \(3.24\times10^{-8}\); multiplication
by a huge \(\lambda_{\rm typ}/\lambda_1\) destroys the ground scale. The actual
Rayleigh ratios \(1.7\times10^6,10^{16},3.4\times10^{36}\) are the decisive
measurement.

There is an exact meaning to “band-limited correction.” If \(P\) projects onto
the raw polynomial ladder and \(Q=I-P\), an eigenvector at eigenvalue \(\lambda\)
satisfies, when the inverse exists,

\[
r=-(QKQ-\lambda I)^{-1}QKP\,p.
\]

This is the Feshbach correction. In a positive zero-side Gram regime it is the
energy-minimizing correction; unconditionally it is only the Hermitian
Rayleigh/Feshbach correction.

The prolate trial is numerically far closer to the ground than the raw ladder,
so the mechanism is plausible. But the prolate packet minimizes a
time-frequency concentration defect, not definitionally the Weil Feshbach
functional. Proving that both corrections agree asymptotically is exactly the
ground-to-trial same-family wall. Defining the correction as “whatever
minimizes \(K\)” would merely rename the ground state and become circular.

## Q4 — cheapest decisive test

Do not begin with an energy ratio of raw \(X\), \(Xx^2\) rows. That family has
already failed at the \(\lambda_1\) scale.

On the already computed cells \(m=83,163\), evaluate the exact quantity

\[
a_{\rm spec}(m)
=
-\frac{d_{2,m}}{d_{1,m}\ell_{1,m}}
\]

and the exact all-mode remainder from Q1. Compare it with three independent
linear extractors:

\[
a_7=\frac{\Delta_m(7)}{\psi_{2,m}(7)},
\]

\[
a_\kappa
=
\frac{\kappa(G_m)-\kappa(X)}
     {\kappa(\psi_{2,m})},
\qquad
\kappa(f)=-\frac{f''(0)}2,
\]

and a least-squares coefficient on the precommitted nodes
\(\{3,5,7,10,12\}\).

The second-jet relation is exact with its remainder:

\[
\kappa(G_m)-\kappa(X)
=
a_m\kappa(\psi_{2,m})+\kappa(R_m).
\]

The falsifier is not “the numbers look noisy.” It is one of:

1. the finite all-mode identity fails above precision/convention error;
2. the independent coefficients remain separated by a stable fraction after
   exact higher-mode correction;
3. \(L_m^2\|R_m\|_K\) has a precision-stable positive lower envelope instead of
   tending to zero;
4. \(a_{\rm spec}(m)L_m^2\) fails to remain bounded while
   \(\Delta_mL_m^2\) remains bounded.

A zero-consistent result is still **inconclusive**. Passing two cells only
licenses the analytic target; it does not prove a cofinal rate.

## FINAL PROPOSAL

Run exactly one existing-data preflight:
`RUN_EXACT_ANCHORED_EIGENBASIS_DECOMPOSITION`.

Registered expectation:

```text
P_ANCHOR_RATIO_EXPLAINS_L2 = 0.72
P_TWO_MODE_REMAINDER_IS_LOWER_ORDER = 0.42
```

If the exact scalar and the second-jet/fixed-node extractors agree, freeze the
next theorem target as:

```text
P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL
```

If the scaled remainder is not lower order, kill the one-shape theorem shape
and return to the weaker consumer-spendable target:

```text
P59_GROUND_FIXED_COMPACT_ERROR_TENDS_TO_ZERO.
```

## STRONGEST ATTACK

The strongest objection is that the observed fixed profile may be a
normalization artefact created by using \(X\) itself in
\(\psi_{2,m}=T_m(u_{2,m})-\ell_{2,m}X\). The exact identity above answers the
objection: it exposes the anchor denominator and all higher modes explicitly.
It also shows why a good profile plot is not yet a theorem. Unless
\(R_m=o(L_m^{-2})\), the same plots can be generated by several stable modes
whose coefficients cancel at the chosen anchor.

## META CLOSEOUT

- **Became smaller:** the vague “two-level perturbation” claim is replaced by
  one exact scalar ratio and one exact compact remainder.
- **Killed:** the uncorrected Xi-polynomial ladder as the current trial; generic
  degree ordering from truncation alone.
- **Must not be tried again:** adding more raw polynomial degrees and reporting
  compact fit RMS as a ground-energy certificate.
- **Smallest named gap:** `P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL`.
- **Cheapest decisive test:** exact eigenbasis/anchor decomposition on existing
  cells, followed by the second-jet and fixed-node consistency check.
- **Prior predictions:** scored in the machine header without altered
  probabilities.
- **Memory entry:**

```yaml
iteration:
  target: GOAL058_ONE_SHAPE_DEVIATION_AND_XI_POLYNOMIAL_LADDER
  status: PROGRESS
  failed_strategy: RAW_XI_POLYNOMIAL_LADDER_AS_TRIAL
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL
  invariant_learned: anchor normalization converts flat vector coordinates into a decaying function coefficient through d1*ell1
  forbidden_future_move: infer Rayleigh quality from compact polynomial fit
  next_decisive_test: RUN_EXACT_ANCHORED_EIGENBASIS_DECOMPOSITION
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
