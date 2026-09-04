# STATUS: OPEN — EXACT TAIL–DEFICIT IDENTITY CONFIRMED; ONE-SIDED FAR-ZERO COUNT IS WRONG-DIRECTION AND NOT A SOURCE-FREE RATE SUPPLIER
```yaml
PRIMARY: TRY_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_UNCONDITIONAL_SCALAR_CURVATURE_RATE

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-RATE
  BOUNDARY_ID: GOAL058_CURVATURE_RATE_L2_OVER_M_AND_FAR_ZERO_DEFICIT
  REQUEST_COMMIT: a7da5095f66b679c224feca9a032520b7a4b8312
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_CURVATURE_RATE_FAR_ZEROS_2026-09-04.txt
  REQUEST_GIT_BLOB: 20ddd7b41bfba5c53cb1bf40564adb5d04ce0a77
  REQUEST_SHA256: cc1f2f82d3ed52ff12848bc510b67bdd1eaeeaa63f6db8fbcf1e498a14b10ed2
  REQUEST_BYTES: 7710
  REQUEST_LINES: 80
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  POST_REQUEST_RESULTS_USED: false
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RATE_L2_OVER_M_AND_FAR_ZERO_DEFICIT_2026-09-04.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  EVIDENCE_REF: a7da5095f66b679c224feca9a032520b7a4b8312
  CURVATURE_SOURCE:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
    git_blob: f167a26670e13bb2b32c6ed6f8b73c4f636e97fd
  SECOND_MODE_LEAN_REPORT:
    path: docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_P59_ANCHORED_SECOND_MODE_OVERLAP_LEAN.md
    git_blob: 49a7da9241389939613c4bf0c0c044bb364f9593
  CURVATURE_TRANSFER_PREFLIGHT:
    path: docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_SECOND_MODE_CURVATURE_TRANSFER_SOURCE_PREFLIGHT.md
    git_blob: 37afedfafeb9b99b73578d7c88f7f4a44fef23b3
  PARENT_OVERLAP: af1d9ead928333a607fa15549c0623f9d4323b29
  PARENT_ZEROPIN: 1529837d895f531330acfa4d81d96c83779a75d7
  PARENT_LEAKAGE:
    path: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md
    git_blob: 05668c94c326b08131801d283889c4467e2cfa9c

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

TOP_LEVEL_ADJUDICATION:
  ALPHA_EQ_TTAIL_MINUS_DEF: EXACT_AFTER_DEFINITION_LOCK
  L2_OVER_M_RATE: FINITE_FIT_NOT_LAW
  CURVATURE_NORMALITY_ROUTE: PRESERVED
  SECOND_MODE_ONE_SHAPE_ROUTE: PRESERVED_CONDITIONALLY
  REQUESTED_DEF_UPPER_BOUND: WRONG_INEQUALITY_DIRECTION_FOR_AN_ALPHA_UPPER_BOUND
  XI_REAL_ZERO_MOMENT_LEDGER: RH_CONDITIONAL_AS_WRITTEN
  ONE_SIDED_NG_GE_NXI_COUNT: DOES_NOT_SUPPLY_ALPHA_UPPER_BOUND
  REALROOTEDNESS_PLUS_DEGREE_SUPPLIES_COUNT: false
  FORCED_LATTICE_TAIL: EXACT
  DEF_IS_ONLY_INSIDE_WINDOW_MISMATCH: false
  GROWING_RECTANGLE_ROUCHE: VALID_CERTIFICATE_BUT_ASYMPTOTICALLY_KNIFE_EDGE
  ALL_PREVIOUS_L2_LAWS_REREAD_FROM_ALPHA: false

Q1_EXACT_DECOMPOSITION:
  SCOPE: FINITE_CELL
  VERIFIER: PAPER
  SOURCE_DEFINITIONS_VERIFIER: LEAN
  DEFINITIONS:
    S_m: "sum over the positive root multiset of the finite P59 Cauchy numerator of 1/rho^2"
    T_m: "(L_m^2/(4*pi^2))*sum_{k>N_m} 1/k^2"
    kappa_G_m: "S_m + T_m"
    kappa_X: "-X''(0)/2 for X=centeredXi/centeredXi(0)"
    Def_m: "kappa_X - S_m"
    alpha_m: "kappa_G_m - kappa_X"
  EXACT_IDENTITY: "alpha_m = T_m - Def_m"
  PRODUCTION_TAIL:
    schedule: "N_m=m, L_m=log m"
    lower: "L_m^2/(4*pi^2*(m+1)) <= T_m"
    upper: "T_m <= L_m^2/(4*pi^2*m)"
    asymptotic: "T_m ~ L_m^2/(4*pi^2*m)"
  DIRECTION_REPAIR:
    requested: "Def_m <= (1-c)*T_m"
    actual_consequence: "alpha_m >= c*T_m"
    does_not_supply: "an upper bound or convergence of alpha_m"
  RATE_ATOM:
    sufficient: "abs(alpha_m) <= C*T_m"
    equivalent_Def_band: "(1-C)*T_m <= Def_m <= (1+C)*T_m"
  NONNEGATIVE_RATE_ATOM:
    if_alpha_nonnegative_is_independently_proved: "0 <= alpha_m <= C*T_m"
    equivalent_Def_band: "(1-C)*T_m <= Def_m <= T_m"
  FIRST_ORDER_PROFILE:
    target: "Def_m/T_m -> delta"
    consequence: "alpha_m/T_m -> 1-delta"
    observed_candidate: "delta approximately 0.65, hence alpha/T approximately 0.35"
    theorem_status: FIT_NOT_LAW
  COMPACT_IDENTIFICATION:
    alpha_rate_alone_sufficient: false
    additional_inputs:
      - "second-mode transfer moment stays nonzero"
      - "transfer remainder is o(alpha_m)"
      - "coherent second-mode profile or a direct compact remainder theorem"
      - "combined interpolation and higher-mode remainder tends to zero"

Q2_ZERO_LEDGER:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  GROUND_LEDGER:
    formula: "kappa_G_m = sum_{rho in numerator positive-root multiset} 1/rho^2 + T_m"
    exact: true
    ground_realzero_hypothesis_required: true
  XI_LEDGER:
    unconditional_object: "kappa_X = -X''(0)/2"
    canonical_product_object: "complex reciprocal-square zero-divisor sum with symmetry grouping"
    formula_sum_positive_real_gamma_inverse_square: RH_CONDITIONAL
    ordinary_Riemann_von_Mangoldt_count_determines_kappa_X: false
  REQUESTED_COUNT_DIRECTION:
    hypothesis: "N_G(t) >= N_X(t) on every t <= R"
    positive_real_measure_consequence: "ground partial inverse-square moment >= target partial moment"
    consequence_for_Def: "an upper bound on Def"
    consequence_for_alpha: "a lower bound on alpha"
    requested_alpha_upper_bound: NOT_OBTAINED
  CORRECTED_COUNT_DIRECTION_FOR_AN_UPPER_BOUND:
    needed_shape: "an upper cumulative bound on the ground moment/count, plus a bound on all ground roots beyond R"
    source_status: OPEN_AND_NOT_FREE
    target_measure_guard: "must use the exact complex/quartet Xi zero weight, not bare 1/gamma^2 unless RH is assumed"
  SOURCE_CLAIM:
    realrootedness_plus_degree_implies_NG_lower_bound: false
    exact_plant: "an even degree-2N real-rooted polynomial can place all N positive numerator roots beyond R"
    forced_roots_only: "give floor(R*L/(2*pi))-N positive roots for R>x_N"
    at_R_1_5_xN: "approximately N/2 forced roots, while the Xi zero count is approximately 1.5N"
  DEF_SPLIT_AT_R:
    formula: >-
      Def_m =
      [target reciprocal-square moment at <=R - ground numerator moment at <=R]
      + [target reciprocal-square tail at >R - ground numerator tail at >R].
    forced_lattice_tail_location: "outside Def_m; it is the separate T_m term"
    conclusion: "Def_m is not only an inside-window mismatch"
  OBSERVED_POINT_35:
    formula: "alpha_m/T_m = 1 - Def_m/T_m"
    status: FINITE_DIAGNOSTIC
    source_constant: false

Q3_GROWING_RECTANGLE:
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER
  DOMAIN: "D_m=[-R_m,R_m] x [-h,h], R_m approximately 1.5*x_N"
  SUFFICIENT_ROUCHE_CERTIFICATE:
    - "G_m and X holomorphic on a neighborhood of the closed rectangle"
    - "X has no zero on the whole boundary"
    - "for every boundary point z, abs(G_m(z)-X(z)) < abs(X(z))"
    - "all four edges and all four corners are covered"
  CONCLUSION: "equal total zero counts with multiplicity inside D_m"
  DOES_NOT_BY_ITSELF_GIVE:
    - "a pairing of individual zeros"
    - "a reciprocal-square moment bound"
    - "a one-sided real-axis count if target off-axis zeros are not separately handled"
  SCALE_COMPARISON_UNDER_REQUESTED_FITS:
    ground_boundary: "sqrt(lambda1_m) approximately 10^(-0.95*m)"
    Xi_boundary_at_1_5_xN: "poly(R_m)*10^(-3.214736*m/L_m)"
    asymptotic_larger: "Xi boundary magnitude"
    consequence: "G_m/X tends toward zero and the relative Rouche error tends toward 1"
    uniform_positive_margin_expected: false
  DEGREE_ONLY_LOWER_COUNT: false

Q4_RATE_REREAD:
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER
  alpha_and_kappa_difference:
    verdict: REREAD_AS_L2_OVER_M_CANDIDATE
    evidence: "m=313 discriminator; alpha*m/L^2 is flat on the last cells"
    theorem_status: NOT_PROVED
  Delta_fixed_x:
    verdict: REREAD_AS_L2_OVER_M_CANDIDATE
    guard: "requires the one-shape compact remainder to be lower order"
  a_m:
    verdict: REREAD_CONDITIONALLY
    guard: "requires stable nonzero psi_2 extractor and combined remainder control"
  d2:
    verdict: REREAD_CONDITIONALLY
    guard: "requires a source proof of the curvature-to-overlap remainder estimate"
  W_absolute_weighted_error:
    verdict: DO_NOT_REREAD_FROM_ALPHA
    reason: "alpha is a signed alternating functional; W uses absolute values"
  sup_node_error:
    verdict: DO_NOT_REREAD_FROM_ALPHA
    reason: "one scalar moment does not control a supremum"
  reciprocal_mode_energy:
    verdict: DO_NOT_REREAD_FROM_ALPHA
    reason: "a signed first moment does not control a positive quadratic norm"
  PROFILE_CONDITIONAL_SCALES:
    assumptions:
      - "Delta_m(x_n)=alpha_m*phi(x_n)+o(alpha_m) on the relevant growing range"
      - "phi(x)/x^2 and abs(phi(x))^2/x^2 have integrable envelopes"
    consequences:
      W_m: "O(alpha_m/L_m)=O(L_m/m)"
      sup_Delta: "O(alpha_m)=O(L_m^2/m)"
      reciprocal_energy: "O(alpha_m^2/L_m)=O(L_m^3/m^2)"
    status: CONDITIONAL_NOT_SUPPLIED_BY_DEF
  SHELL_CONSEQUENCES:
    curvature_normality: "closed by alpha=O(T_m)"
    first_order_one_shape: "needs alpha/T limit plus compact remainder and profile limit"
    H1_reciprocal_energy_shell: "not closed by Def control alone"
    absolute_W_shell: "not closed by Def control alone"
    sup_lattice_shell: "not closed by Def control alone"

PREDICTION_FATES:
  P_E_OVER_ALPHA_M_DECREASES:
    probability: 0.55
    fate: REFUTED_AS_STATED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: "nonmonotone from 13 to 23; later decrease does not repair the registered statement"
  P_M_STABLE_NONZERO:
    probability: 0.65
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_D2_OVER_ALPHA_STABLE:
    probability: 0.60
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  UNREGISTERED_ALL_NIGHT_L_MINUS_TWO_READING:
    probability: null
    fate: REFUTED_FOR_ALPHA_AND_FIXED_X_DISCRIMINATOR_NOT_SCORED_AS_K6
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_ALPHA_EQ_TTAIL_MINUS_DEF_EXACT:
    probability: 0.85
    fate: CONFIRMED_WITH_DEFINITION_LOCK
    scope: FINITE_CELL
    verifier: PAPER
    source_definitions_verifier: LEAN
  P_DEF_IS_INSIDE_WINDOW_MISMATCH:
    probability: 0.55
    fate: REFUTED
    scope: ABSTRACT
    verifier: PAPER
  P_ONE_SIDED_COUNT_IS_SOURCE:
    probability: 0.35
    fate: REFUTED
    scope: ABSTRACT
    verifier: PAPER
  P_JUDGE_REREADS_ALL_L2_LAWS:
    probability: 0.75
    fate: REFUTED_AS_UNIVERSAL
    scope: COFINAL_FAMILY
    verifier: PAPER

SCOPED_KILLS:
  DEF_UPPER_TO_ALPHA_UPPER:
    CODE: KILL_DEF_LE_ONE_MINUS_C_T_AS_ALPHA_UPPER_SUPPLIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_ALGEBRA_ALPHA_EQUALS_T_MINUS_DEF
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  XI_REAL_ZERO_COUNT_LEDGER:
    CODE: KILL_KAPPA_XI_AS_POSITIVE_REAL_GAMMA_SUM_UNCONDITIONALLY
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: TARGET_ZERO_OBJECT_MISMATCH
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_UNCONDITIONAL_STATEMENT
  REALROOT_DEGREE_TO_WINDOW_COUNT:
    CODE: KILL_REALROOTED_DEGREE_TO_GROWING_WINDOW_LOWER_COUNT
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_EVEN_REALROOTED_ROOT_PLACEMENT_PLANT
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  FAR_DEFICIT_TO_ALL_ERROR_NORMS:
    CODE: KILL_SIGNED_CURVATURE_MOMENT_AS_ABSOLUTE_PROFILE_CONTROLLER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: SIGN_CANCELLATION_AND_DIMENSION
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

CANDIDATE_REPRESENTATIONS:
  R1_IMAGINARY_AXIS_LOG_DERIVATIVE:
    selected: true
    object: >-
      S_f(y)=-f'(i*y)/(2*i*y*f(i*y)); for a real-rooted normalized P59
      transform this is a positive Stieltjes sum over its complete divisor,
      while S_X(y) is defined from centeredXi without assuming RH.
    target: >-
      Choose y_m down to zero and prove
      abs(S_Gm(y_m)-S_X(y_m)) <= C*T_m,
      with the y_m-to-zero regularization error o(T_m).
    kill_power: 9/10
    preflight_cost: 3/10
    proof_cost_if_survives: 7/10
  R2_PHYSICAL_SECOND_MOMENT_TWO_OBSERVABLE:
    selected: false
    object: >-
      Compare the exact ground and CCM trial central value and second jet
      directly, then import the paper-proved trial-to-Xi two-jet limit.
    target: "anchored central error plus anchored second-jet error is O(T_m)"
    kill_power: 8/10
    preflight_cost: 4/10
    proof_cost_if_survives: 8/10

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  REGISTERED_PREDICTION:
    name: P_LOG_DERIVATIVE_EXPOSES_SOURCE_TAIL_BEFORE_GAP
    probability: 0.35
  SUCCESS: P59_LOG_DERIVATIVE_TAIL_MATCH_SOURCE_IDENTITY
  FAILURE: P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE
  FALSIFIER: >-
    Reject the representation if the first quantitative step assumes RH,
    substitutes sum 1/gamma^2 for kappa_X, invokes a full/reduced resolvent
    norm, or assumes abs(alpha_m)<=C*T_m under another name.

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same anchor-normalized finite ground transforms have only real zeros
    and converge locally uniformly to centeredXi on one cofinal family.
  ORIGINAL_REQUESTED_OBJECT: FAR_ZERO_DEFICIT_AND_ONE_SIDED_ZERO_COUNT
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "bounded ground curvature plus an independent identifying set"
    - "direct compact convergence"
    - "one-shape expansion with alpha_m->0 and a vanishing combined remainder"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "unconditional scalar log-derivative comparison instead of a target real-zero count"

LEAN_READY:
  - P59_ALPHA_EQ_TTAIL_SUB_DEF_ABSTRACT
  - P59_TTAIL_INTEGRAL_BOUNDS
  - DEF_INEQUALITY_DIRECTION_LEMMAS
  - REALROOTED_DEGREE_WINDOW_COUNT_KILL_PLANT
  - FINITE_DIVISOR_SPLIT_AT_RADIUS

NEW_ANALYTIC:
  - P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH
  - P59_LOG_DERIVATIVE_TO_CURVATURE_RATE
  - P59_COMBINED_INTERPOLATION_HIGHER_MODE_REMAINDER_AT_TTAIL_SCALE
  - P59_SECOND_MODE_PROFILE_LIMIT_AT_TTAIL_SCALE

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_ADJUDICATION_ONLY
  NEXT_TRANSACTION: GOAL058_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY

CLOSES:
  - PURE_L_MINUS_TWO_RATE_READING_FOR_ALPHA
  - ONE_SIDED_NG_GE_NXI_AS_ALPHA_UPPER_SUPPLIER
  - REALROOTEDNESS_PLUS_DEGREE_AS_WINDOW_COUNT_SUPPLIER
  - SIGNED_ALPHA_AS_CONTROLLER_OF_ALL_PROFILE_NORMS
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
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
CURRENT_SMALLEST_GAP: P59_UNCONDITIONAL_LOG_DERIVATIVE_TAIL_MATCH
```

## ROUTE MAP

| Route / object | Verdict | Decisive test | Main risk | Tags |
|---|---|---|---|---|
| Exact curvature tail–deficit ledger | **CONFIRMED** | Definition lock for \(S_m,T_m,\mathrm{Def}_m\) | Misreading the direction of the deficit inequality | `[FINITE_CELL][PAPER]` |
| \(L_m^2/m\) rate for \(\alpha_m\) | **STRONGLY SUPPORTED, OPEN** | A source theorem gives \(|\alpha_m|\le C T_m\) | The six-cell fit is mistaken for a cofinal law | `[COFINAL_FAMILY][CONDITIONAL]` |
| One-sided ordinary zero count \(N_G\ge N_\Xi\) | **REJECTED AS THE RATE SUPPLIER** | Exact Abel direction and a source root-location theorem | It bounds \(\alpha\) from below, and its target ledger is not unconditional as written | `[ABSTRACT][PAPER]` |
| Growing-window Rouché lock | **VALID BUT BADLY CONDITIONED** | A positive lower envelope for the full boundary margin | The relative margin tends to zero near \(R\asymp x_N\) | `[COFINAL_FAMILY][CONDITIONAL]` |
| Imaginary-axis log derivative | **SELECTED PREFLIGHT** | Difference becomes an explicit source tail before any inverse norm | It may only rename the curvature difference | `[COFINAL_FAMILY][CONDITIONAL]` |
| Two-observable ground-to-trial transfer | **RUNNER-UP** | Central and second-jet errors are \(O(T_m)\) on one family | The gap returns through the current projective supplier | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Source lock and byte verification

The authoritative request was fetched from GitHub at commit
`a7da5095f66b679c224feca9a032520b7a4b8312`. Its Git blob is
`20ddd7b41bfba5c53cb1bf40564adb5d04ce0a77`. Independent reconstruction gives
exactly `7710` bytes, `80` LF-terminated lines, and SHA-256
`cc1f2f82d3ed52ff12848bc510b67bdd1eaeeaa63f6db8fbcf1e498a14b10ed2`.
The six-field phase key is unchanged. `[COFINAL_FAMILY][PAPER]`

No post-request result is used.

## 2. Q1 — exact decomposition and inequality-direction repair

Let \(R_m^+\) be the positive-root multiset of the finite even P59 Cauchy numerator, with multiplicity, and put

\[
S_m=\sum_{\rho\in R_m^+}\rho^{-2},\qquad
T_m=\frac{L_m^2}{4\pi^2}\sum_{k>N_m}k^{-2}.
\]

The kernel-green source defines \(\kappa(G_m)=S_m+T_m\). With

\[
\kappa_X=-X''(0)/2,\quad
\mathrm{Def}_m=\kappa_X-S_m,\quad
\alpha_m=\kappa(G_m)-\kappa_X,
\]

one gets exactly

\[
\boxed{\alpha_m=T_m-\mathrm{Def}_m.}
\]

This is algebra from the Lean-locked definition, not an asymptotic model. `[FINITE_CELL][PAPER]`

On \(N_m=m\),

\[
\frac{L_m^2}{4\pi^2(m+1)}\le T_m\le\frac{L_m^2}{4\pi^2m},
\]

so \(T_m\asymp L_m^2/m\). The six reported cells support \(\alpha_m/T_m\approx0.35\), but that is `FIT_NOT_LAW`. `[FINITE_CELL][ARB_INTERVAL]`

The requested inequality points the wrong way:

\[
\mathrm{Def}_m\le(1-c)T_m
\quad\Longrightarrow\quad
\alpha_m\ge cT_m.
\]

It does not give an upper rate. The clean rate atom is

\[
\boxed{|\alpha_m|\le C T_m,}
\]

equivalently

\[
(1-C)T_m\le\mathrm{Def}_m\le(1+C)T_m.
\]

If \(\alpha_m\ge0\) is proved independently, the one-sided upper-rate form is

\[
(1-C)T_m\le\mathrm{Def}_m\le T_m.
\]

For a first-order profile one needs

\[
\mathrm{Def}_m/T_m\to\delta,
\qquad
\alpha_m/T_m\to1-\delta.
\]

The finite candidate \(\delta\approx0.65\) is not a source constant. `[COFINAL_FAMILY][CONDITIONAL]`

The rate \(\alpha_m=O(L_m^2/m)\) closes curvature normality. It does not alone prove compact identification: the anchored decomposition still needs a lower-order transfer remainder, coherent second-mode profile, and the combined interpolation/higher-mode remainder. `[COFINAL_FAMILY][PAPER]`

## 3. Q2 — exact lattice tail, wrong count supplier

The exact ground ledger is

\[
\boxed{\kappa(G_m)=S_m+T_m.}
\]

The \(\rho\)'s are roots of the finite Cauchy numerator. The term \(T_m\) is exactly the contribution of the forced P59 lattice zeros

\[
x_{m,k}=2\pi k/L_m,\qquad k>N_m.
\]

These are different parts of one full P59 divisor. `[FINITE_CELL][LEAN]`

For the target, the unconditional object is \(\kappa_X=-X''(0)/2\). The formula

\[
\kappa_X=\sum_{\gamma>0}\gamma^{-2}
\]

with \(\gamma\) ranging over positive real centered-\(\Xi\) zeros presupposes that the complete target divisor is real. That is RH. Outside RH, the canonical-product ledger uses the complex centered divisor with symmetry grouping; ordinary Riemann–von Mangoldt counting by height does not determine this weighted curvature. `[ABSTRACT][PAPER]`

Even in a conditional positive-real-zero model, Abel summation gives

\[
N_G(t)\ge N_X(t)
\quad\Longrightarrow\quad
\sum_{\rho\le R}\rho^{-2}\ge\sum_{\gamma\le R}\gamma^{-2}.
\]

Thus it bounds \(\mathrm{Def}_m\) from above and \(\alpha_m\) from below. It does not provide the requested upper bound on \(\alpha_m\). `[ABSTRACT][PAPER]`

Real-rootedness and degree also do not supply the count location. For any \(R>0\),

\[
P_N(z)=\prod_{j=1}^{N}\left(1-\frac{z^2}{(R+j)^2}\right)
\]

is even, degree \(2N\), real-rooted and nonzero at zero, but has no numerator root in \([-R,R]\). This kills the theorem shape. `[ABSTRACT][PAPER]`

At \(R=1.5x_N\), the forced lattice roots contribute only about \(N/2\) positive roots, while the Riemann–von Mangoldt count is about \(1.5N\). The missing numerator roots require a location theorem.

For any cutoff \(R\),

\[
\mathrm{Def}_m=
[\kappa_X^{\le R}-S_m^{\le R}]+[\kappa_X^{>R}-S_m^{>R}].
\]

The forced lattice term \(T_m\) is outside this split. Therefore \(\mathrm{Def}_m\) is not only the mismatch inside \(1.5x_N\); numerator roots beyond the cutoff remain in \(S_m^{>R}\). `[FINITE_CELL][PAPER]`

The observed `0.35` is only

\[
\alpha_m/T_m=1-\mathrm{Def}_m/T_m
\]

on six finite cells.

## 4. Q3 — window-scale winding lock

A sufficient certificate on

\[
D_m=[-R_m,R_m]\times[-h,h]
\]

requires holomorphy near the closed rectangle, target nonvanishing on its entire boundary, and

\[
\boxed{|G_m(z)-X(z)|<|X(z)|\quad(z\in\partial D_m).}
\]

All four edges, corners and junctions must be covered. Rouché then gives equal total zero counts with multiplicity. It does not pair roots or control reciprocal-square moments. `[ABSTRACT][PAPER]`

Under the rate fits in the request,

\[
\sqrt{\lambda_{1,m}}\asymp10^{-0.95m},
\]

while for \(R_m=1.5x_N=3\pi m/L_m\),

\[
|X(R_m)|=\operatorname{poly}(R_m)10^{-3.214736\,m/L_m}.
\]

The target is asymptotically much larger. Under the proposed leakage picture, \(G_m/X\to0\), so the relative Rouché error tends to `1`. The lock is legal but knife-edge, not a uniform-margin supplier. `[COFINAL_FAMILY][CONDITIONAL]`

A lower count is not free: degree permits all numerator roots to lie beyond \(R_m\), and the forced lattice floor is insufficient.

## 5. Q4 — rate reread

The \(m=313\) discriminator changes the reading of \(\alpha_m\). It does not transfer automatically to every norm that looked like \(L^{-2}\).

| Quantity | Honest reread | Tags |
|---|---|---|
| \(\alpha_m=\kappa(G_m)-\kappa_X\) | Candidate \(O(L_m^2/m)\), not proved | `[FINITE_CELL][ARB_INTERVAL]` |
| Fixed-\(x\) \(\Delta_m(x)\) | Candidate \(O(L_m^2/m)\), conditional on the one-shape remainder | `[COFINAL_FAMILY][CONDITIONAL]` |
| \(a_m\) | Candidate \(O(L_m^2/m)\), conditional on a stable extractor/profile | `[COFINAL_FAMILY][CONDITIONAL]` |
| \(d_{2,m}\) | Candidate \(O(L_m^2/m)\), conditional on the transfer remainder | `[COFINAL_FAMILY][CONDITIONAL]` |
| \(W_m=\sum|\Delta_{m,n}|/n^2\) | No rate follows from signed \(\alpha_m\) | `[COFINAL_FAMILY][PAPER]` |
| \(\sup_n|\Delta_{m,n}|\) | No rate follows from one signed moment | `[ABSTRACT][PAPER]` |
| \(\sum|\Delta_{m,n}|^2/n^2\) | No rate follows from one signed linear functional | `[ABSTRACT][PAPER]` |

With the additional profile theorem

\[
\Delta_{m,n}=\alpha_m\phi(2\pi n/L_m)+o(\alpha_m)
\]

and suitable weighted integrable envelopes, Riemann-sum scaling gives

\[
W_m=O(\alpha_m/L_m)=O(L_m/m),
\]

\[
\sup_n|\Delta_{m,n}|=O(\alpha_m)=O(L_m^2/m),
\]

\[
\sum_n\frac{|\Delta_{m,n}|^2}{n^2}
=O(\alpha_m^2/L_m)=O(L_m^3/m^2).
\]

Then all earlier absolute shells close with large margin. But this needs the full profile theorem; it is not supplied by a bound on \(\mathrm{Def}_m\) alone. `[COFINAL_FAMILY][CONDITIONAL]`

## 6. Prediction closeout

Probabilities are unchanged.

- `P_E_OVER_ALPHA_M_DECREASES`, `0.55`: **REFUTED AS STATED**. The registered range includes the 13→23 increase.
- `P_M_STABLE_NONZERO`, `0.65`: **CONFIRMED** on the registered finite cells.
- `P_D2_OVER_ALPHA_STABLE`, `0.60`: **CONFIRMED** on the registered finite cells.
- The unregistered whole-night \(L^{-2}\) reading is not scored as K6. It is refuted for \(\alpha_m\) and the fixed-\(x\) discriminator, not automatically for every absolute norm.
- `P_ALPHA_EQ_TTAIL_MINUS_DEF_EXACT`, `0.85`: **CONFIRMED WITH DEFINITION LOCK**.
- `P_DEF_IS_INSIDE_WINDOW_MISMATCH`, `0.55`: **REFUTED**.
- `P_ONE_SIDED_COUNT_IS_SOURCE`, `0.35`: **REFUTED** by the explicit root-placement plant.
- `P_JUDGE_REREADS_ALL_L2_LAWS`, `0.75`: **REFUTED AS UNIVERSAL**.

Finite scores use `[FINITE_CELL][ARB_INTERVAL]`; exact kills use `[ABSTRACT][PAPER]`.

## 7. Lean-ready versus new analysis

### Lean-ready bookkeeping

1. `P59_ALPHA_EQ_TTAIL_SUB_DEF_ABSTRACT`.
2. Integral-test bounds for `proposition59TailZetaTwo`.
3. Exact `Def`/`alpha` inequality-direction lemmas.
4. The even real-rooted degree-\(2N\) root-placement plant.
5. Finite splitting of the numerator reciprocal-square moment at a radius.

These do not prove a cofinal rate. `[FINITE_CELL][PAPER]`

### New analytic mathematics

1. An unconditional source estimate for \(\alpha_m\) at the \(T_m\) scale.
2. A target-side scalar representation that does not assume a real \(\Xi\)-divisor.
3. The combined interpolation/higher-mode remainder at that scale.
4. Coherent second-mode/profile convergence if the one-shape theorem is retained.
5. Any growing-boundary argument-principle estimate if the expensive count route is reopened.

`[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Preserve

\[
T_m\asymp L_m^2/m,
\qquad
\alpha_m=T_m-\mathrm{Def}_m,
\]

and stop calling the observed curvature law \(L^{-2}\).

Do not promote the proposed count theorem. It fails three independent gates:

1. `Def <= (1-c)T` bounds \(\alpha\) from below.
2. Real-rootedness and degree do not locate numerator roots.
3. `kappa_X=sum 1/gamma^2` is not unconditional as written.

Run one read-only preflight on the imaginary-axis log derivative

\[
\mathcal S_f(y)=-\frac{f'(iy)}{2iyf(iy)}.
\]

For normalized real-rooted P59 transforms this is a positive Stieltjes sum over the complete divisor. For centered \(\Xi\), it is defined directly on a zero-free imaginary segment without assuming RH. Seek an exact source subtraction before any inverse norm.

Registered prediction:

```yaml
P_LOG_DERIVATIVE_EXPOSES_SOURCE_TAIL_BEFORE_GAP:
  probability: 0.35
```

Pass only if the difference becomes an explicit omitted-tail or boundary functional with an \(O(T_m)\) budget. Otherwise return `P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE`.

## STRONGEST ATTACK

A reviewer may try to repair the count route by grouping off-line zero quartets. That can make the reciprocal-square total real and can support absolute tail bounds. It does not turn the weight into \(1/\gamma^2\), and it does not repair the direction:

\[
N_G\ge N_X
\Rightarrow \text{larger ground moment}
\Rightarrow \text{smaller Def}
\Rightarrow \text{larger alpha}.
\]

A viable count route needs opposite cumulative control or a two-sided weighted-moment estimate plus ground-tail control. That is a substantial part of complete-divisor control, not a free consequence of real-rootedness.

## CODEX DIRECTIVE

No execution is authorized by this paper-only adjudication.

A later bounded transaction may be opened as:

```text
TASK_ID:
  GOAL058_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean
  the source determinant / D_log statement used by CCM Theorem 5.10
  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md

RETURN:
  1. exact formula for S_Gm(y);
  2. exact formula for S_X(y) without RH;
  3. a legal y_m-to-zero regularization budget;
  4. the first term remaining after source subtraction;
  5. exactly one code:
       P59_LOG_DERIVATIVE_TAIL_MATCH_SOURCE_IDENTITY
     or
       P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE.

FORBIDDEN:
  Lean edits;
  numerical runs;
  kappa_X = sum over positive real gamma as an unconditional premise;
  full or reduced resolvent norms;
  any complement floor;
  post-hoc schedule changes.
```

## META CLOSEOUT

- **What became smaller?** The observed rate is the exact scalar \(\alpha_m=T_m-\mathrm{Def}_m\), with explicit scale \(T_m\asymp L_m^2/m\).
- **What was killed?** The proposed deficit inequality as an upper-rate supplier; real-rootedness-plus-degree as a growing-window count; the unconditional positive-real-\(\Xi\)-zero ledger; inference from signed curvature to all absolute profile norms.
- **What must not be tried again?** Calling a lower bound on \(\alpha\) an upper bound; using Riemann–von Mangoldt counting as though it fixes the centered reciprocal-square divisor; turning one scalar cancellation into an \(\ell^\infty\) or weighted-\(\ell^2\) estimate.
- **Current smallest named gap:** `P59_UNCONDITIONAL_LOG_DERIVATIVE_TAIL_MATCH`.
- **Next cheapest decisive test:** the read-only imaginary-axis log-derivative subtraction.
- **Fate of prior predictions:** all requested probabilities are preserved and scored above.
- **Memory entry:** \(L^{-2}\) was a finite-range mirage for the curvature scalar. The exact \(L^2/m\) scale is real evidence, but the proposed one-sided zero count points in the wrong direction and the absolute shells remain independent.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
