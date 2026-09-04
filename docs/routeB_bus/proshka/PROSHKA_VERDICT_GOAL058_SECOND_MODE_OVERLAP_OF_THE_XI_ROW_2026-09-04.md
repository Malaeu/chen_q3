# STATUS: OPEN — SECOND-MODE OVERLAP SURVIVES; PURE NYQUIST EULER–MACLAURIN L^-2 MECHANISM IS KILLED
```yaml
PRIMARY: TRY_P59_SECOND_MODE_CURVATURE_ORTHOGONALITY_TRANSFER
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_GAP_FREE_SECOND_MODE_OVERLAP

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-OVERLAP
  BOUNDARY_ID: GOAL058_SECOND_MODE_OVERLAP_OF_THE_XI_ROW
  REQUEST_COMMIT: e359b38f960bf8c0a76d7dd4ad314aefc5416888
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SECOND_MODE_OVERLAP_2026-09-04.txt
  REQUEST_GIT_BLOB: d0a4859699d2ab1b83efc2a2ea32d01dd9291214
  REQUEST_SHA256: e2477429a0e35e87d75f4ca2d98eb10a41380fe21eddf8f4309593c7883e036e
  REQUEST_BYTES: 6777
  REQUEST_LINES: 73
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  POST_REQUEST_RESULTS_USED: false
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_OF_THE_XI_ROW_2026-09-04.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  EVIDENCE_REF: e359b38f960bf8c0a76d7dd4ad314aefc5416888
  CONVENTION_CARD:
    path: docs/routeB_bus/CONVENTION_CARD_GOAL058.md
    git_blob: 65e7aec23df97ed738ee0e0c5da4cf77ca8fa37b
  PARENT_ONESHAPE:
    path: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ONE_SHAPE_DEVIATION_AND_XI_POLYNOMIAL_LADDER_2026-09-04.md
    git_blob: 31e4e55f9a1833562eb241fceef56dfd0f3f540c
  PARENT_WINDLOCK:
    path: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md
    git_blob: f76d4290cf5ea9f2ca164a1950720624b2b087a2
  PARENT_LEAKAGE:
    path: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md
    git_blob: 05668c94c326b08131801d283889c4467e2cfa9c
  PRECOMMIT_ADDENDUM_19:
    path: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md
    git_blob: 3fc81a6f3f37bd20513cac723bdc31b3c4899445
  P59_SOURCE:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean
    git_blob: 6d38df2ff26cc7dc7eadc4757c15605649cbb6d4

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

TOP_LEVEL_ADJUDICATION:
  ONE_SHAPE_ROUTE: PRESERVED_AS_PRIMARY
  RATE_CARRIER: SECOND_EVEN_MODE_OVERLAP_D2
  OLD_ANCHOR_GROWTH_MECHANISM: REFUTED
  ANCHOR_PRODUCT: FINITE_DIAGNOSTICALLY_FLAT_AND_NONZERO
  D2_O_L_MINUS_2: FINITE_DIAGNOSTICALLY_SUPPORTED_NOT_COFINALLY_PROVED
  HIGHER_MODE_TAIL_ALONE_SUFFICIENT: false
  COMBINED_INTERPOLATION_AND_HIGHER_MODE_REMAINDER_REQUIRED: true
  PURE_NYQUIST_STEP_CREATES_L_MINUS_2: KILLED_THEOREM_SHAPE
  GAP_OR_COMPLEMENT_FLOOR_REQUIRED: false
  SECOND_MODE_SELECTION_COHERENCE_REQUIRED: true

Q1_DIRECT_ATOM:
  EXACT_NORMALIZATION:
    xi_sample_anchor: "y_m[0] = u_{1,m}[0]"
    ell_y: "ell_m(y_m) = ell_{1,m}"
    interpolation_error: "e_m = T_m(y_m) - ell_{1,m} X"
  EXACT_IDENTITY: >-
    d_{1,m} ell_{1,m} (G_m-X)
    = e_m - sum_{j>=2} d_{j,m} psi_{j,m}.
  TWO_MODE_FORM:
    a_m: "-d_{2,m}/(d_{1,m} ell_{1,m})"
    H_m: "e_m - sum_{j>=3} d_{j,m} psi_{j,m}"
    R_m: "H_m/(d_{1,m} ell_{1,m})"
    identity: "G_m-X = a_m psi_{2,m} + R_m"
  FIRST_ORDER_SUFFICIENT_THEOREM:
    hypotheses:
      - "d_{1,m} ell_{1,m} -> A with A != 0"
      - "L_m^2 d_{2,m} -> D"
      - "psi_{2,m} -> psi locally uniformly"
      - "L_m^2 H_m -> 0 locally uniformly"
    conclusion: "L_m^2 (G_m-X) -> -(D/A) psi locally uniformly"
  CONVERGENCE_ONLY_WEAKER_THEOREM:
    hypotheses:
      - "abs(d_{1,m} ell_{1,m}) is eventually bounded below"
      - "d_{2,m} = O(L_m^-2)"
      - "psi_{2,m} is locally uniformly bounded"
      - "H_m -> 0 locally uniformly"
    conclusion: "G_m -> X locally uniformly"
  D2_INTERPRETATION:
    exact: "d_{2,m} = inner(y_m,u_{2,m})"
    absolute_orthogonality_wording: true
    angle_orthogonality_wording_requires: "uniform control of norm(y_m)"
    finite_scalar_explicit: true
    cofinal_asymptotic_explicit: false
  REQUIRED_MODE_GUARD:
    preferred: "lambda_{2,m} is simple and u_{2,m}[0] != 0, with u_{2,m}[0] > 0"
    multiplicity_safe_repair: "use the spectral projection onto the second even eigenspace"
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

Q2_GAP_FREE_MECHANISM:
  EXACT_LATTICE_PAIRING:
    h_m: "2*pi/L_m"
    T_m_lattice: >-
      Tr_m(f) = h_m * (f(0) + 2*sum_{n=1}^{N_m} f(2*pi*n/L_m)).
    identity: "Tr_m(F_v F_w) = 2*pi*inner(v,w) for real even rows v,w"
    source: "P59 exact removable lattice sampling"
  EXACT_D2_SOURCE_FORM:
    formula: "2*pi*d_{2,m} = ell_{1,m} * Tr_m(X F_{2,m})"
  EXACT_ORTHOGONALITY:
    formula: "Tr_m(G_m F_{2,m}) = 0"
  QUADRATIC_JET_PARAMETER:
    alpha_m: "kappa(G_m)-kappa(X)"
    kappa: "-f''(0)/2 for the anchored functions G_m and X"
    signed_z2_coefficient_of_G_over_X: "-alpha_m"
    B_m: "G_m-X+alpha_m*z^2*X"
    jets: ["B_m(0)=0", "B_m''(0)=0"]
  EXACT_TRANSFER_IDENTITY: >-
    d_{2,m}
    = ell_{1,m}/(2*pi)
      * (alpha_m * Tr_m(z^2 X F_{2,m}) - Tr_m(B_m F_{2,m})).
  EXACT_SECOND_JET_IDENTITY: >-
    alpha_m
    = a_m*kappa(psi_{2,m}) + kappa(R_m);
    hence, if kappa(psi_{2,m}) != 0,
    d_{2,m}
    = -(d_{1,m}ell_{1,m}/kappa(psi_{2,m}))
      * (alpha_m-kappa(R_m)).
  SAME_PARAMETER_SUFFICIENT_CONDITIONS:
    - "ell_{1,m} -> ell != 0"
    - "Tr_m(z^2 X F_{2,m}) -> M != 0"
    - "Tr_m(B_m F_{2,m}) = o(L_m^-2)"
    - "alpha_m = O(L_m^-2)"
    conclusion: "d_{2,m} = ell*M/(2*pi)*alpha_m + o(L_m^-2)"
  CONTINUUM_Q2:
    leading_integral_zero_is_conditional: true
    required_crosswalk: >-
      Tr_m(X F_{2,m}) -> integral_R X(x)^2 q_2(x) dx,
      with source-defined q_2 and all amplitude, aliasing, and finite-window tails.
    leading_zero_conclusion: >-
      If F_{2,m}->X q_2 and G_m has the controlled two-jet profile above,
      orthogonality forces integral X^2 q_2 = 0 at leading order.
    not_ordinary_Parseval: true
  EULER_MACLAURIN:
    pure_grid_L_minus_2: false
    reason: >-
      For a fixed smooth rapidly decaying whole-line integrand, the polynomial
      Euler-Maclaurin boundary terms vanish; the trapezoidal defect is an
      aliasing/tail term, normally superalgebraic or exponential in L.
    surviving_role: >-
      Prove that sampling and finite-window errors are o(L^-2), thereby
      isolating the m-dependent profile or band-limit correction as the source
      of the observed L^-2 term.
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

Q3_DECISIVE_TEST:
  SELECTED:
    code: RUN_EXACT_SECOND_MODE_CURVATURE_TRANSFER_LEDGER
    duplicate_eigensolve_required: false
    use_existing_cells: [13, 23, 43, 83, 163]
    objects:
      - "alpha_m = kappa(G_m)-kappa(X)"
      - "B_m = G_m-X+alpha_m*z^2*X"
      - "M_m = Tr_m(z^2 X F_{2,m})"
      - "E_m = Tr_m(B_m F_{2,m})"
      - "identity residual for 2*pi*d2/ell1 = alpha_m*M_m-E_m"
      - "E_m/(alpha_m*M_m)"
      - "d2/alpha_m"
    exact_identity_gate: "relative residual <= 1e-30 at working precision"
    same_parameter_support: >-
      M_m stays separated from zero and stable, while
      E_m/(alpha_m*M_m) tends to zero.
    same_parameter_falsifier: >-
      M_m tends to zero, changes sign without a source explanation, or the
      residual term remains a nonvanishing fraction of alpha_m*M_m.
  CONTINUUM_FOLLOWUP:
    code: PAPER_POISSON_TRAPEZOID_CROSSWALK
    purpose: >-
      Replace the finite lattice moments by integrals and prove that fixed-profile
      aliasing and cutoff errors are o(L^-2).
  ONE_SHAPE_DIAGNOSTIC_FAILURE:
    one_cell_outside_0_4_0_8_kills_route: false
    what_one_cell_kills: "the frozen finite trend predictor only"
  ONE_SHAPE_ROUTE_KILL_REQUIRES:
    - >-
      a source-proved or certified cofinal lower bound showing
      L_m^2*norm_K(R_m) does not tend to zero on some fixed compact
    - >-
      stable separation of a_spec, a_7, a_kappa, and a_LS after the exact
      higher-mode correction
    - "failure of compact precompactness or convergence of psi_{2,m}"
    - "a coherent second-mode selection cannot be made"
  SCOPE: FINITE_CELL
  VERIFIER: CONDITIONAL

Q4_SEPARATION:
  LEAN_READY:
    - P59_REAL_EVEN_LATTICE_PAIRING
    - P59_ANCHORED_EIGENBASIS_DECOMPOSITION
    - P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY
    - P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY
    - P59_SECOND_JET_TWO_MODE_LEDGER
  NEW_ANALYTIC:
    - P59_SECOND_MODE_SELECTION_COHERENCE
    - P59_SECOND_MODE_PROFILE_LIMIT
    - P59_SECOND_MODE_OVERLAP_O_L_MINUS_2
    - P59_COMBINED_INTERPOLATION_HIGHER_MODE_TAIL_O_L_MINUS_2
    - P59_POISSON_TRAPEZOID_UNIFORM_CROSSWALK
    - P59_QUADRATIC_PROFILE_REMAINDER_PAIRING_O_L_MINUS_2

PREDICTION_FATES:
  P_ANCHOR_RATIO_EXPLAINS_L2:
    probability: 0.72
    fate: CONFIRMED_WITH_MECHANISM_CORRECTION
    scope: FINITE_CELL
    verifier: CONDITIONAL
    note: >-
      a_spec*L^2 stabilizes and agrees with independent extractors, but the
      denominator d1*ell1 is flat; d2 itself carries the observed decay.
  P_A_SPEC_MATCHES_A7:
    probability: 0.65
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_A_KAPPA_MATCHES_A7:
    probability: 0.50
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_REMAINDER_SMALL:
    probability: 0.55
    fate: CONFIRMED_ON_REGISTERED_CELLS
    scope: FINITE_CELL
    verifier: CONDITIONAL
    note: "This does not score the cofinal prediction L^2*R_m -> 0."
  P_A_SPEC_L2_STABILIZES:
    probability: 0.60
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: CONDITIONAL

  P_D2_IS_SAME_PARAMETER_AS_C2:
    probability: 0.55
    fate: UNRESOLVED_WITH_EXACT_REMAINDER_IDENTITY
    scope: COFINAL_FAMILY
    verifier: PAPER
    note: >-
      The signed quadratic Taylor coefficient alpha_m has an exact transfer
      identity to d2, but the transfer moment and remainder limits are open.
  P_EULER_MACLAURIN_GIVES_L2:
    probability: 0.40
    fate: REFUTED_AS_PURE_NYQUIST_STEP_MECHANISM
    scope: ABSTRACT
    verifier: PAPER
    repaired_statement: >-
      Poisson/Euler-Maclaurin may prove that fixed-profile aliasing and cutoff
      errors are o(L^-2); the L^-2 term must come from an m-dependent profile
      or band-limit correction.
  P_JUDGE_KEEPS_ONE_SHAPE_AS_PRIMARY:
    probability: 0.65
    fate: CONFIRMED_WITH_MECHANISM_REPAIR
    scope: COFINAL_FAMILY
    verifier: PAPER

SCOPED_KILLS:
  HIGHER_MODE_TAIL_WITHOUT_INTERPOLATION:
    CODE: KILL_HIGHER_MODE_TAIL_ALONE_AS_REMAINDER_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_ANCHORED_EIGENBASIS_IDENTITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  PURE_GRID_EULER_MACLAURIN:
    CODE: KILL_PURE_NYQUIST_EULER_MACLAURIN_AS_L2_RATE_SOURCE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: VANISHING_WHOLE_LINE_BOUNDARY_TERMS_AND_POISSON_ALIASING_SCALE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_FIXED_PROFILE
  SINGLE_CELL_ROUTE_DEATH:
    CODE: KILL_ONE_CELL_OUTLIER_AS_COFINAL_ROUTE_FALSIFIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: QUANTIFIER_MISMATCH
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

CANDIDATE_REPRESENTATIONS:
  R1_SECOND_JET_ORTHOGONALITY_TRANSFER:
    selected: true
    kill_power: 10/10
    preflight_cost: 2/10
    proof_cost_if_survives: 7/10
    discriminator: >-
      M_m has a nonzero stable limit and E_m/(alpha_m*M_m) tends to zero.
  R2_DISCRETE_XI_ORTHOGONAL_QUADRATIC:
    selected: false
    kill_power: 9/10
    preflight_cost: 3/10
    proof_cost_if_survives: 8/10
    discriminator: >-
      Define q_{2,m} by exact discrete Gram-Schmidt against the Xi row and
      compare the source u2 projection without fitted coefficients.
  R3_DIRECT_COMPACT_ONE_SHAPE:
    selected: false
    kill_power: 8/10
    preflight_cost: 4/10
    proof_cost_if_survives: 8/10
    discriminator: >-
      Prove G_m-X=a_m*psi_m+R_m directly on compacta, without identifying the
      quadratic source of a_m.

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_SECOND_MODE_CURVATURE_TRANSFER_SOURCE_PREFLIGHT
  MODE: PAPER_AND_EXISTING_DATA_READ_ONLY
  SUCCESS: P59_SECOND_MODE_CURVATURE_TRANSFER_REMAINDER_LOWER_ORDER
  FAILURE: P59_SECOND_MODE_CURVATURE_TRANSFER_ONLY_RENAMES_CANCELLATION
  FALSIFIER: >-
    The exact transfer remainder E_m remains a nonzero fraction of
    alpha_m*M_m, or the transfer moment M_m loses a nonzero stable scale.

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same anchor-normalized finite ground transforms converge locally
    uniformly to Xi/Xi(0) on one cofinal family.
  ORIGINAL_REQUESTED_OBJECT: SECOND_MODE_OVERLAP_D2_O_L_MINUS_2
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "direct compact convergence G_m-X -> 0"
    - "a_m psi_{2,m}+R_m with a_m->0, compact-bounded psi2, and R_m->0"
    - "bounded curvature plus a source-locked identifying set"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: GAP_FREE_ORTHOGONALITY_TRANSFER_FROM_SECOND_JET_TO_SECOND_MODE_OVERLAP

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_ADJUDICATION_ONLY
  NEXT_TRANSACTION: GOAL058_P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES
  TARGET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean
  EXPECTED_AXIOMS: [propext, Classical.choice, Quot.sound]
  FORBIDDEN:
    - cofinal rate claims
    - fitted polynomial definitions
    - resolvent norms or complement floors
    - numerical constants as proof
    - schedule changes

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
CURRENT_SMALLEST_GAP: P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL
```

## ROUTE MAP

| Route | Verdict | Decisive test | Main risk | Tags |
|---|---|---|---|---|
| Exact second-mode/second-jet transfer | **PRIMARY, OPEN** | The exact remainder is lower order and the transfer moment has a nonzero limit | The identity only renames an \(O(L^{-2})-O(L^{-2})\) cancellation | `[COFINAL_FAMILY][CONDITIONAL]` |
| Exact discrete Xi-orthogonal quadratic | **RUNNER-UP** | A source-defined Gram-Schmidt mode converges to the second source eigendirection | It becomes a new trial family with no energy control | `[COFINAL_FAMILY][CONDITIONAL]` |
| Direct compact one-shape theorem | **FALLBACK** | \(a_m\to0\), compact-bounded \(\psi_{2,m}\), and \(R_m\to0\) | Gives convergence but may not explain the \(L^{-2}\) law | `[COFINAL_FAMILY][CONDITIONAL]` |
| Pure Nyquist Euler–Maclaurin coefficient | **KILLED FOR A FIXED PROFILE** | — | Whole-line boundary terms vanish and aliases are much smaller than \(L^{-2}\) | `[ABSTRACT][PAPER]` |

## 1. Source lock and normalization repair

The authoritative payload was fetched from GitHub at the stated commit and
blob. Decoding gives exactly `6777` bytes, `73` newline-terminated lines, and
SHA-256

```text
e2477429a0e35e87d75f4ca2d98eb10a41380fe21eddf8f4309593c7883e036e
```

The six-field phase key is unchanged. `[COFINAL_FAMILY][PAPER]`

The convention card fixes the even orthonormal coordinates. If \(v_0\) is the
central even coordinate, the exact P59 anchor is

\[
\ell_m(v)=F_v(0)=\sqrt{L_m}\,v_0,
\]

while at a positive lattice node \(t_{m,n}=2\pi n/L_m\),

\[
F_v(t_{m,n})=\sqrt{L_m/2}\,(-1)^n v_n.
\]

Since the request normalizes the Xi row by \(y_m[0]=u_{1,m}[0]\), it follows
that \(\ell_m(y_m)=\ell_{1,m}\), not \(1\). Therefore the exact interpolation
error in this verdict is

\[
e_m=T_m(y_m)-\ell_{1,m}X.
\]

This repair is mandatory for every identity below. `[FINITE_CELL][LEAN]`

## 2. Q1 — the exact pure-ℓ2 atom

Let \(u_{j,m}\) be a coherent orthonormal even eigenbasis, with \(u_{1,m}\) the
ground vector. Define

\[
G_m=\frac{T_m(u_{1,m})}{\ell_{1,m}},
\qquad
d_{j,m}=\langle y_m,u_{j,m}\rangle,
\]

\[
\psi_{j,m}=T_m(u_{j,m})-\ell_{j,m}X,
\qquad
\ell_{j,m}=\sqrt{L_m}\,u_{j,m}[0].
\]

Expansion of \(y_m\) in the eigenbasis and linearity of the anchor give the
exact identity

\[
\boxed{
d_{1,m}\ell_{1,m}(G_m-X)
=e_m-\sum_{j\ge2}d_{j,m}\psi_{j,m}.
}
\tag{A}
\]

Thus

\[
\boxed{
G_m-X
=-\frac{d_{2,m}}{d_{1,m}\ell_{1,m}}\psi_{2,m}
+\frac{e_m-\sum_{j\ge3}d_{j,m}\psi_{j,m}}
       {d_{1,m}\ell_{1,m}}.
}
\tag{B}
\]

The request’s correction is accepted. The measured denominator is flat near
\(0.9\); it is not the \(L^2\) carrier. The observed rate sits in

\[
\boxed{d_{2,m}=\langle y_m,u_{2,m}\rangle=O(L_m^{-2}).}
\]

This is literally an absolute near-orthogonality statement between the
explicit Xi-sample row and the second even eigenvector. Calling it an angle
estimate additionally requires uniform control of \(\|y_m\|\).

For a first-order one-shape theorem, the exact sufficient statement is:

\[
d_{1,m}\ell_{1,m}\to A\ne0,
\quad
L_m^2d_{2,m}\to D,
\quad
\psi_{2,m}\to\psi,
\]

and

\[
L_m^2\left(e_m-\sum_{j\ge3}d_{j,m}\psi_{j,m}\right)\to0
\]

locally uniformly. Then

\[
L_m^2(G_m-X)\to-\frac DA\psi.
\]

For mere identification, weaken the last rate to \(o(1)\), retain
\(d_2=O(L^{-2})\), compact boundedness of \(\psi_2\), and a nonzero lower bound
for \(|d_1\ell_1|\).

The higher-mode tail alone is not the remainder: the Xi interpolation error
\(e_m\) is part of the same load-bearing object. Any theorem omitting it is
false by the exact identity (A).

At each finite cell, \(y_m\), \(K_m\), \(u_{2,m}\), and \(d_{2,m}\) are
explicit. The open content is the cofinal asymptotic. That proof must control:

1. a coherent second-mode selection;
2. the source profile of \(F_{2,m}=T_m(u_{2,m})\);
3. the Xi-sample pairing with that profile;
4. the combined interpolation and higher-mode remainder.

If the second eigenvalue is multiple, an individual \(u_2\) is not a
source-invariant object. The multiplicity-safe target is the spectral
projection onto the second even eigenspace.

## 3. Q2 — exact gap-free orthogonality mechanism

For real even rows, define the finite P59 trapezoidal functional

\[
\operatorname{Tr}_m(f)
=
\frac{2\pi}{L_m}
\left(f(0)+2\sum_{n=1}^{N_m}f(2\pi n/L_m)\right).
\]

The exact removable-node sampling formulas imply

\[
\boxed{
\operatorname{Tr}_m(F_vF_w)=2\pi\langle v,w\rangle.
}
\tag{C}
\]

Because \(F_{y_m}\) agrees with \(\ell_{1,m}X\) at every included lattice
node,

\[
\boxed{
2\pi d_{2,m}
=\ell_{1,m}\operatorname{Tr}_m(XF_{2,m}).
}
\tag{D}
\]

Orthogonality of \(u_{1,m}\) and \(u_{2,m}\) gives

\[
\boxed{
\operatorname{Tr}_m(G_mF_{2,m})=0.
}
\tag{E}
\]

Define the exact quadratic-jet parameter

\[
\alpha_m=\kappa(G_m)-\kappa(X),
\qquad
\kappa(f)=-\frac{f''(0)}2,
\]

and

\[
B_m(z)=G_m(z)-X(z)+\alpha_mz^2X(z).
\]

Then \(B_m(0)=B_m''(0)=0\), and

\[
G_m=X-\alpha_mz^2X+B_m.
\]

The signed \(z^2\)-coefficient of \(G_m/X\) is \(-\alpha_m\). In the convention
\(G_m=X-(c_{2,m}/c_{0,m})z^2X+\cdots\), one has

\[
\frac{c_{2,m}}{c_{0,m}}=\alpha_m.
\]

Combining (D) and (E) gives the exact gap-free identity

\[
\boxed{
d_{2,m}
=
\frac{\ell_{1,m}}{2\pi}
\left[
\alpha_m\operatorname{Tr}_m(z^2XF_{2,m})
-
\operatorname{Tr}_m(B_mF_{2,m})
\right].
}
\tag{F}
\]

This is the exact relation requested in Q2. It says that \(d_2\) and the
ground quadratic admixture are the same small parameter only after two
additional statements:

\[
\operatorname{Tr}_m(z^2XF_{2,m})\to M\ne0,
\]

and

\[
\operatorname{Tr}_m(B_mF_{2,m})=o(L_m^{-2}).
\]

Under those statements and \(\ell_{1,m}\to\ell\ne0\),

\[
d_{2,m}
=
\frac{\ell M}{2\pi}\alpha_m+o(L_m^{-2}).
\]

The same relation appears at the second jet. From (B),

\[
\boxed{
\alpha_m
=-\frac{d_{2,m}}{d_{1,m}\ell_{1,m}}
\kappa(\psi_{2,m})+\kappa(R_m).
}
\tag{G}
\]

Thus the agreement of `a_spec` and `a_kappa` is a direct finite diagnostic for
small \(\kappa(R_m)\).

The proposed continuum reading is conditional. If a source theorem proves

\[
F_{2,m}\to Xq_2
\]

with all amplitudes fixed and converts \(\operatorname{Tr}_m\) into a
whole-line integral, then (E) forces

\[
\int_{\mathbb R}X(x)^2q_2(x)\,dx=0
\]

at leading order. The next term is proportional to

\[
\alpha_m\int_{\mathbb R}x^2X(x)^2q_2(x)\,dx
\]

plus the band-limit/profile remainders in (F).

This is not ordinary Parseval. It requires two adapters: exact P59 node
sampling to the finite trapezoid, then a uniform finite-trapezoid to
whole-line-integral theorem.

For a fixed smooth rapidly decaying whole-line profile, pure
Euler–Maclaurin cannot be the source of a nonzero \(L^{-2}\) term: its
polynomial boundary terms vanish at infinity, while Poisson summation puts
the error into nonzero Fourier aliases, which are superalgebraic or
exponential for the present analytic profiles. The production cutoff lies
at \(2\pi N/L\), with \(N=m\), where the Xi tail is also much smaller than
\(L^{-2}\).

Therefore the registered Euler–Maclaurin mechanism is refuted in its pure
Nyquist-step form. Its repaired use is to prove that aliasing and cutoff are
\(o(L^{-2})\), thereby isolating the m-dependent eigenprofile or band-limit
correction as the actual source of the observed rate.

## 4. Q3 — cheapest decisive test and falsifier

Do not begin with a fitted quadratic or a new eigensolve. Use the stored
finite objects and compute

\[
\alpha_m=\kappa(G_m)-\kappa(X),
\quad
B_m=G_m-X+\alpha_mz^2X,
\]

\[
M_m=\operatorname{Tr}_m(z^2XF_{2,m}),
\quad
E_m=\operatorname{Tr}_m(B_mF_{2,m}).
\]

First verify the exact identity

\[
\frac{2\pi d_{2,m}}{\ell_{1,m}}=\alpha_mM_m-E_m
\]

to relative error at most \(10^{-30}\) at working precision. Then record

\[
M_m,
\qquad
\frac{E_m}{\alpha_mM_m},
\qquad
\frac{d_{2,m}}{\alpha_m}.
\]

The same-parameter mechanism survives only if \(M_m\) stays separated from
zero and stable while \(E_m/(\alpha_mM_m)\to0\). It fails if \(M_m\to0\), if
its sign changes without a source explanation, or if the remainder retains a
nonzero fraction of the leading term.

Only after this finite test survives should one define a continuum
\(q_{2,m}\) by exact jets or exact discrete Gram–Schmidt and compare

\[
I_2(m)=\int X^2q_{2,m}.
\]

A least-squares quadratic is not a source object and cannot be a premise.

A single cell for which \(a_{\rm spec}L^2\notin[0.4,0.8]\) refutes the frozen
finite trend predictor. It does not kill a cofinal theorem. The one-shape
route is killed only by a cofinal obstruction: nonvanishing \(L^2R_m\) on a
fixed compact, stable disagreement of the independent extractors after exact
remainder correction, failure of compact convergence of \(\psi_{2,m}\), or
failure of coherent second-mode selection.

## 5. Q4 — Lean-ready versus new analysis

### Lean-ready bookkeeping

1. `P59_REAL_EVEN_LATTICE_PAIRING`, the exact identity (C).
2. `P59_ANCHORED_EIGENBASIS_DECOMPOSITION`, identities (A) and (B).
3. `P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY`, identity (D).
4. `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY`, identity (F).
5. `P59_SECOND_JET_TWO_MODE_LEDGER`, identity (G).

These are finite linear algebra plus existing P59 removable-node sampling.
They do not contain any cofinal rate.

### New analytic mathematics

1. A coherent cofinal second-mode selection.
2. \(d_{2,m}=O(L_m^{-2})\).
3. Local-uniform convergence or compact boundedness of \(\psi_{2,m}\).
4. The combined remainder
   \[
   e_m-\sum_{j\ge3}d_{j,m}\psi_{j,m}
   \]
   is \(o(L_m^{-2})\) for the first-order profile, or \(o(1)\) for mere
   identification.
5. A uniform Poisson/trapezoidal crosswalk.
6. A source estimate
   \[
   \operatorname{Tr}_m(B_mF_{2,m})=o(L_m^{-2}).
   \]

## FINAL PROPOSAL

Keep the one-shape route primary, but replace its mechanism.

The rate does not come from anchor growth. The anchor product is only a
nondegenerate denominator. The measured decay is carried by the explicit
source scalar

\[
d_{2,m}=\langle y_m,u_{2,m}\rangle.
\]

The next source target is not a gap theorem and not a fitted
Euler–Maclaurin coefficient. It is the exact transfer identity (F), followed
by a source proof that its remainder is lower order.

The registered prediction remains unchanged:

```yaml
P_D2_IS_SAME_PARAMETER_AS_C2:
  probability: 0.55
  discriminator: >-
    M_m has a nonzero stable limit and
    E_m/(alpha_m*M_m) tends to zero.
```

If the discriminator fails, retain the exact one-shape decomposition but
drop the claim that the ground quadratic admixture explains the rate. Move
to the direct compact remainder representation.

## STRONGEST ATTACK

Identity (F) may merely rename the desired cancellation. The remainder

\[
E_m=\operatorname{Tr}_m(B_mF_{2,m})
\]

can be the same size as \(\alpha_mM_m\). Then orthogonality says only that two
\(O(L^{-2})\) terms cancel; it does not identify a dominant mechanism.
Likewise, defining \(c_2/c_0\) by a fitted polynomial would make the claimed
relation post hoc.

The repair is fail-closed:

- define \(\alpha_m\) by the exact second jet;
- define \(B_m\) exactly;
- verify (F);
- prove or falsify a lower-order bound for \(E_m\);
- never use a fitted quadratic as a premise.

The pure-grid Euler–Maclaurin explanation is dead as a theorem shape. Its
only surviving role is to prove that discretization errors are too small to
carry the observed rate.

## CODEX DIRECTIVE

No execution is authorized by this paper-only request.

A later bounded transaction may formalize only the finite identities:

```text
TASK_ID:
  GOAL058_P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  Proposition59AnchoredSecondModeOverlap.lean

PROVE:
  P59_REAL_EVEN_LATTICE_PAIRING
  P59_ANCHORED_EIGENBASIS_DECOMPOSITION
  P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY
  P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY
  P59_SECOND_JET_TWO_MODE_LEDGER

USE:
  proposition59RawTransform_at_lattice
  proposition59RawTransform_at_zero_eq_sqrt
  Proposition59AlternatingLatticeCurvature second-jet facts
  the exact even/full coordinate conversion from CONVENTION_CARD_GOAL058

FORBIDDEN:
  cofinal rate claims;
  fitted-polynomial definitions;
  any resolvent norm or complement floor;
  numerical constants as proof;
  schedule changes.

VALIDATE:

WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean
  lake build Q3.Proofs.RouteB.Proposition59AnchoredSecondModeOverlap

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES_KERNEL_GREEN

FAILURE:
  P59_SECOND_MODE_OVERLAP_NORMALIZATION_OR_EVEN_COORDINATE_MISMATCH
```

## META CLOSEOUT

- **What became smaller?** The observed \(L^{-2}\) law is now one explicit
  second-mode overlap and one combined compact remainder. The continuum
  cancellation has an exact finite P59 lattice identity.
- **What was killed?** Anchor growth as the rate carrier; higher-mode tail
  without interpolation error; pure Nyquist Euler–Maclaurin as the source of
  a nonzero \(L^{-2}\) term; one-cell route death.
- **What must not be tried again?** A fitted quadratic as a source object,
  ordinary Parseval without the P59 sampling adapter, or a spectral gap to
  estimate this overlap.
- **Current smallest named gap:**
  `P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL`.
- **Next cheapest decisive test:** evaluate the exact transfer ledger
  \((\alpha_m,M_m,E_m)\) on the stored cells before any new eigensolve.
- **Fate of prior predictions:** all eight requested predictions are scored in
  the machine header without changing their probabilities.
- **Memory entry:** the anchor is flat; \(d_2\) carries the rate. The one-shape
  route remains primary only through an exact gap-free
  orthogonality/second-jet transfer and a lower-order remainder theorem.

No Lean source was edited. No numerical run was started. No route promotion or
RH claim was made.
