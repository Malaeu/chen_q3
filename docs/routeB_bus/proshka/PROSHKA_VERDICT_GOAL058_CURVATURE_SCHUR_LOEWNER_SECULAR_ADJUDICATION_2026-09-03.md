# STATUS: TRY_SECULAR_IDENTITY_FOR_CURVATURE
```yaml
OPERATIVE_CLASS: TRY_SECULAR_IDENTITY_FOR_CURVATURE
PRIMARY_COUNT: 1

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-03-SCHURLOEWNER
  BOUNDARY_ID: GOAL058_CURVATURE_SCHUR_LOEWNER_SECULAR_ADJUDICATION
  REQUEST_COMMIT: 445bd0068d5d49d7b0308608d30fb4bf755683fd
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_CURVATURE_SCHUR_LOEWNER_SECULAR_ADJUDICATION_2026-09-03.txt
  REQUEST_GIT_BLOB: 0a6c9f8bb13728dfd5387eda407afa02a82867f4
  REQUEST_SHA256: 26aea53eaf13fe1ca7922ba482359db384a389ce22430ee7374b764e2c15f09d
  REQUEST_BYTES: 7276
  REQUEST_LINES: 109
  FINAL_LF: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: 362e089bf22364f5111946c2144824dce9c5a2d4
  PARENT_VERDICT_COMMIT: 0c0a2b37dadea72fff0e3a9048b05bc36d3a98f3
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_SCHUR_LOEWNER_SECULAR_ADJUDICATION_2026-09-03.md
  OPTIONAL_MYTHOS_R2_NOTE_PRESENT: false

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

PRIMARY_DECISION:
  R2_SCHUR_ROUTE: PRESERVED_WITH_REPRESENTATION_REPAIR
  POLE_TERM_SECULAR_ROOT: EXACT
  POLE_TERM_SECULAR_EVALUATES_CURVATURE_PAIRING: false
  CURVATURE_BORDERED_RANK_TWO_SECULAR_DERIVATIVE: PAPER_PASS
  CURVATURE_SOURCE_BOUND: OPEN
  LOEWNER_OFFDIAGONAL_SOURCE_FAITHFULNESS: LEAN_PROVED
  LOEWNER_OPERATOR_MONOTONE_OR_MIXED_RESIDUE_SIGN: NOT_ESTABLISHED
  INPUT_A_CONSUMER: REPAIR_TO_PROJECTIVE_DEFECT_OR_DIRECT_LATTICE_ERROR
  TWO_INDEPENDENT_PROOF_SCHEDULES: REJECTED
  COMMON_COFINAL_REFINEMENT: REQUIRED

Q1_SECULAR_IDENTITY:
  POLE_SPLIT:
    C_L_n: 4*sqrt(L)*sinh(L/4)*L/(L^2+16*pi^2*n^2)
    S_L_n: 16*pi*sqrt(L)*sinh(L/4)*n/(L^2+16*pi^2*n^2)
    identity: W02 = 2*C_L*C_L^T - 2*S_L*S_L^T
  EVEN_SECTOR:
    base: B_e = (-W_R-Prime)|even
    matrix: K_e = B_e + 2*C_L*C_L^T
    secular_equation: 1 + 2*inner(C_L,(B_e-zI)^-1*C_L) = 0
  ODD_SECTOR:
    base: B_o = (-W_R-Prime)|odd
    matrix: K_o = B_o - 2*S_L*S_L^T
    secular_equation: 1 - 2*inner(S_L,(B_o-zI)^-1*S_L) = 0
  CENTER_SPLIT:
    matrix: K = [[a0,b^T],[b,D]]
    root_equation: a0-z-inner(b,(D-zI)^-1*b) = 0
  TARGET:
    c_n: 1/(2*pi^2*n^2)
    S_curv_z: inner(c,(D-zI)^-1*b)
    mismatch: c is neither the center coupling b nor the pole update vector C_L
  REPAIRED_RANK_TWO_DEFORMATION:
    e0: central basis vector
    w: (1/12,c)
    M_curv: e0*w^T + w*e0^T
    rank_bound: 2
    K_t: K + t*M_curv
    Phi_t_z: det(K_t-zI)/det(D-zI)
    equivalent_schur_form: a0+t/6-z-inner(b+t*c,(D-zI)^-1*(b+t*c))
    exact_identity: 1/12-S_curv(z) = (1/2)*d_dt(Phi(t,z))|t=0
    at_ground: Phi(0,lambda1)=0
    source_bound_needed: abs(d_dt(Phi(t,lambda1))|t=0) <= C/L^2

Q2_LOEWNER:
  EXACT_LEAN_THEOREMS:
    - Q3.RouteB.ccmWeilTau_structured_offdiag
    - Q3.RouteB.ccmWeilMatFinite_structured_offdiag
    - Q3.RouteB.ccmBetaFinite_unique
    - Q3.RouteB.ccmWeilMatFinite_commutator
  OFFDIAGONAL_IDENTITY:
    tau_nm: (beta_n-beta_m)/(n-m)
    prime_sum_included: true
    displacement_equation: X*K-K*X = beta*eta^T-eta*beta^T
    displacement_rank_at_most: 2
  FULL_CONFLUENT_LOEWNER:
    existence_of_one_odd_Hermite_interpolant: PAPER_PASS_FINITE
    canonical_source_function: NOT_FIXED
    operator_monotonicity: NOT_PROVED
  PARITY_REPARAMETRIZATION:
    beta_n: n*h(n^2)
    even_sector_symbol: Phi(x)=x*h(x)
    odd_sector_symbol: h(x)
    status: EXACT_FINITE_ALGEBRA_AFTER_INTERPOLANT_LOCK
  CLASSICAL_THEORY_LIMIT:
    explicit_inverse_from_displacement_rank_alone: false
    Bhatia_Friedland_Jain_power_inertia_applicable_to_arithmetic_h: false
    mixed_residue_sign_from_Loewner_property_alone: false
  EXACT_ONE_SIGN_SUPPLIER:
    sufficient_condition: exists g with c=g(D)b and g(mu)>=0 on spectrum(D)
    consequence: residue_j=g(mu_j)*abs(inner(v_j,b))^2 >= 0
    current_supplier: absent

Q3_INPUT_A:
  MINIMAL_PORT:
    projective_defect: p_k = 1-abs(inner(xi_k,q_k))^2
    direct_lattice_error_is_even_weaker: true
    relative_Ritz_eta_is_only_one_optional_supplier: true
  SUFFICIENT_RATE:
    projective: abs(A_k)^2*L_k*p_k -> 0
    phase_aligned_distance: min_phase_norm_sq <= 2*p_k
  PRODUCTION_M_EQUALS_N:
    relative_excess_supplier: DIAGNOSTICALLY_USELESS
    direct_projective_defect: SMALL_BUT_NO_COFINAL_RATE_PROVED
  SCHEDULE_RULE:
    separate_diagnostic_schedules: allowed
    separate_proof_schedules_to_one_consumer: forbidden
    required_repair: choose one precommitted joint path or prove a transport/uniformity theorem
    normality_must_hold_on_Input_A_path: true

SCOPED_KILLS:
  POLE_SECULAR_DIRECTLY_EVALUATES_MIXED_CURVATURE:
    CODE: KILL_POLE_SECULAR_AS_DIRECT_CURVATURE_EVALUATOR
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE_KIND: EXACT_VECTOR_MISMATCH
    EVIDENCE: c_n=1/(2*pi^2*n^2) differs from both b and C_L
  GENERIC_LOEWNER_STRUCTURE_IMPLIES_CURVATURE_RATE:
    CODE: KILL_GENERIC_LOEWNER_TO_L_MINUS_TWO_RATE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE_KIND: TWO_BY_TWO_SCHUR_PLANT
    EVIDENCE: K_t=[[lambda+b^2/t,b],[b,lambda+t]] has ground lambda and S(lambda)=c*b/t, arbitrary with t>0
  STRICT_MIXED_RESIDUES_ONE_SIGN_ON_PRODUCTION_SCHEDULE:
    CODE: KILL_STRICT_ONE_SIGN_RESIDUE_THEOREM
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE_KIND: ARB_INTERVAL_FINITE_CELL
    EVIDENCE: negative residue mass is certified at m=43 and m=83
  TWO_UNRELATED_SCHEDULES_COMPOSE_TO_ZEROESCAPE:
    CODE: KILL_TWO_SCHEDULE_DIRECT_COMPOSITION
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    EVIDENCE_KIND: CONSUMER_TYPE_AUDIT
    EVIDENCE: normality and identification must concern the same sequence F

PREDICTION_FATES:
  P_CURVATURE_SOURCE_1:
    probability: 0.65
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: frozen Probe-4 schedule is positive and flat within factor 1.071; this is not a cofinal theorem
  P_GROUND_RATIO_GROWS_AT_SIGMA_0_4:
    probability: 0.60
    fate: REFUTED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: frozen Probe-3 verdict is BOUNDED, max/min 1.00253
  P_ABS_GAP_COLLAPSES:
    probability: 0.80
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: frozen Probe-1 verdict is CONFIRMED
  P_DUAL_CERT_PAYS_GAP:
    probability: 0.75
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: gap_share is essentially 1 on every tested cell
  P_SCHUR_RESIDUES_ONE_SIGN:
    probability: 0.35
    fate: UNRESOLVED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
    note: frozen rule gives UNRESOLVED; literal strict one-sign is already false at m=43,83
  P_DIRECT_FUNCTIONAL_BEATS_FULL_TRACKING_1:
    probability: 0.72
    fate: CONFIRMED_AT_REPRESENTATION_SCOPE
    scope: FINITE_CELL
    verifier: PAPER_PLUS_ARB_INTERVAL
    note: direct kappa stabilized while R1 paid the full absolute gap; no cofinal source bound is claimed
  P_JOINT_PROJECTIVE_RATE_1:
    probability: 0.38
    fate: REFUTED_AS_REGISTERED_INTERFACE
    scope: COFINAL_FAMILY
    verifier: PAPER_PLUS_ARB_INTERVAL
    note: the prediction required the current residual/floor representation without a new source theorem; that interface is not executable on m=N
  P_SECULAR_IDENTITY_EXISTS:
    probability: 0.55
    fate: REFUTED_AS_STATED
    scope: FINITE_CELL
    verifier: PAPER
    note: the pole split gives a scalar root equation but does not evaluate the mixed curvature pairing; the bordered rank-two derivative repairs it
  P_LOEWNER_CLAIM_SOURCE_FAITHFUL:
    probability: 0.60
    fate: CONFIRMED_WITH_SCOPE_REPAIR
    scope: FINITE_CELL
    verifier: LEAN_PLUS_PAPER
    note: exact divided differences and displacement rank two are source-faithful, including the prime sum; operator monotonicity and a canonical h are not supplied
  P_TWO_SCHEDULES_ALLOWED:
    probability: 0.70
    fate: REFUTED
    scope: COFINAL_FAMILY
    verifier: PAPER
    note: two reconnaissance schedules are legal, but the final consumer requires one common sequence

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_CURVATURE_BORDERED_SECULAR_SOURCE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  TARGET: P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND
  EXACT_REQUIREMENT: abs(d_dt(Phi_k(t,lambda1_k))|t=0) <= C/L_k^2 on one common cofinal path
  FIRST_CHECKS:
    - derive the rank-two deformation from the exact second-jet row
    - express Phi through the source beta/Loewner data before taking any inverse norm
    - test whether the pole vectors cancel the leading part of w=(1/12,c)
    - keep the production diagonal and prime contribution exact
  FALSIFIER:
    code: R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE
    condition: after the exact Schur/determinant rewrite, every estimate still starts with norm((D-lambda1)^-1) or simply assumes the desired slope bound
  SUCCESS:
    code: P59_CURVATURE_BORDERED_SECULAR_SOURCE_IDENTITY
    condition: an exact source identity or one-sided bound controls L^2*d_dt(Phi) without an absolute-gap denominator

CANDIDATE_REPRESENTATIONS:
  R2A_BORDERED_SECULAR_DERIVATIVE:
    selected: true
    kill_power: 9/10
    cost: 3/10
    object: rank-two curvature deformation and determinant-ratio slope
  R2B_SPECTRAL_CALCULUS_RESIDUE_ALIGNMENT:
    selected: false
    kill_power: 8/10
    cost: 5/10
    object: prove c=g(D)b with g nonnegative on spectrum(D)
  A_DIRECT_PROJECTIVE_OR_LATTICE_ERROR:
    selected: false
    kill_power: 8/10
    cost: 6/10
    object: supply p_k or moving-node coefficient error without relative Rayleigh excess

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: the same normalized entire real-zero family converges locally uniformly to centeredXi
  ORIGINAL_REQUESTED_OBJECT: P59_CURVATURE_CENTER_SCHUR_STIELTJES
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - direct uniform bound on normalized curvature kappa_k
    - bordered secular slope O(L^-2)
    - direct normality or ground moment-ratio bound
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: curvature as a source-specific rank-two secular derivative
  REOPEN_TRIGGERS:
    R2_SOURCE_BOUND: exact formula or inequality for the bordered determinant slope
    LOEWNER_SIGN: source-defined h with a proved operator-monotone/generalized-Nevanlinna class
    INPUT_A: one common cofinal path with a proved projective or lattice-error rate

LEAN_READY_BOOKKEEPING:
  - generic block Schur root identity
  - rank-two curvature deformation and determinant-ratio derivative
  - exact W02 rank-two split
  - finite odd Hermite-interpolant/confluent-Loewner existence
  - parity-sector divided-difference algebra

NEW_ANALYTIC_WORK:
  - uniform O(L^-2) source bound for the bordered secular slope
  - any exact residue-alignment theorem for the mixed pairing
  - a common-path projective/lattice-error rate for Input A
  - Hadamard order-at-most-one factorization bridge absent from pinned Mathlib

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_ADJUDICATION_ONLY
  NEXT_TRANSACTION: GOAL058_CURVATURE_BORDERED_SECULAR_SOURCE_PREFLIGHT
  FORBIDDEN:
    - Lean edits
    - numerical reruns
    - full resolvent norm bounds
    - Bhatia-Friedland-Jain power-law inertia transplanted to an unproved arithmetic h
    - separate schedules fed directly to one ZeroEscape consumer

META_CLOSEOUT:
  PROGRESS_CLASS: REPRESENTATION_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  BECAME_SMALLER: normalized-curvature wall became one rank-two determinant-ratio slope
  KILLED:
    - R1 minimal-norm dual annihilator
    - pole secular equation as a direct mixed-curvature evaluator
    - strict one-sign mixed-residue theorem on the production schedule
    - direct composition of two unrelated schedules
  DO_NOT_RETRY:
    - bounding the full reduced resolvent before applying the curvature row
    - treating finite Loewner interpolation as operator monotonicity
    - using relative Rayleigh excess as the Input-A port
  CURRENT_SMALLEST_GAP: P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND
  NEXT_CHEAPEST_DECISIVE_TEST: source-only derivation of the bordered secular slope and its generic two-by-two plant
  MEMORY_ENTRY: direct curvature stays primary; Input A is projective/direct; all final properties share one cofinal family

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
```

## ROUTE MAP

| Route / object | Verdict | Exact discriminator | Main risk | Tags |
|---|---|---|---|---|
| Curvature → normality → Vitali → ZeroEscape | **Preserved** | A source theorem proves \(\sup_k\kappa_k<\infty\) on the same path used by Input A | The observed flat curvature may be finite-range only | `[COFINAL_FAMILY][CONDITIONAL]` |
| Curvature-specific bordered secular derivative | **Selected** | \(L_k^2\partial_t\Phi_k(0,\lambda_{1,k})\) is uniformly bounded without an absolute-gap denominator | The identity may only rename the desired cancellation | `[COFINAL_FAMILY][CONDITIONAL]` |
| Pole-term rank-one secular equation | **Exact but insufficient** | It evaluates the pole-vector self-pairing, not \(\langle c,(D-\lambda)^{-1}b\rangle\) | Confusing nearby \(1/n^2\)-shaped vectors | `[FINITE_CELL][PAPER]` |
| Loewner/displacement structure | **Source-faithful at finite divided-difference level** | Exact source-defined \(h\) belongs to a sign-controlling class | Finite interpolation is noncanonical and operator monotonicity is absent | `[FINITE_CELL][LEAN]` |
| Relative Ritz on \(m=N\) | **Not the Input-A mainline** | Direct \(p_k\) or moving-node error has a common-path rate | Relative excess explodes while projective error stays small | `[COFINAL_FAMILY][CONDITIONAL]` |
| Two schedules | **Diagnostics only** | One common refinement carries both normality and identification | Empty intersection of the two property sets | `[COFINAL_FAMILY][PAPER]` |

## 1. Source lock and harvested evidence

The attached request is byte-locked by commit `445bd0068d5d49d7b0308608d30fb4bf755683fd`, Git blob `0a6c9f8bb13728dfd5387eda407afa02a82867f4`, and SHA-256 `26aea53eaf13fe1ca7922ba482359db384a389ce22430ee7374b764e2c15f09d`.

The six-field phase key is unchanged. The family remains `PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY`, and the terminal consumer remains `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`.

The completed diagnostic schedule supports, but does not prove, the curvature route:

- Probe 1 confirms collapse of the absolute gap.
- Probe 3 classifies the critical moment ratio as bounded on the tested schedule.
- Probe 4 confirms positive, nearly flat normalized curvature.
- Probe 5 proves diagnostically that the minimal-norm dual annihilator pays the second-eigenvalue denominator.
- Probe 6 does not satisfy the frozen one-sign gate.
- Relative Ritz is sharp on the source-faithful Phase-1 cell but useless as a supplier on the \(m=N\) schedule.

All those statements remain finite diagnostic evidence. They occupy no cofinal quantifier.

## 2. Q1 — the exact secular identities

### 2.1 The pole term has an exact rank-two split

For
\[
d_n=L^2+16\pi^2n^2,
\]
define
\[
C_L(n)=\frac{4\sqrt L\,\sinh(L/4)\,L}{d_n},
\qquad
S_L(n)=\frac{16\pi\sqrt L\,\sinh(L/4)\,n}{d_n}.
\]

Direct algebra gives
\[
W_{0,2}(n,m)=2C_L(n)C_L(m)-2S_L(n)S_L(m).
\]

The vector \(C_L\) is even and \(S_L\) is odd. Thus, with
\[
B=-W_{\mathbb R}-W_{\mathrm{prime}},
\]
the parity restrictions satisfy
\[
K_e=B_e+2C_LC_L^T,
\qquad
K_o=B_o-2S_LS_L^T.
\]

Whenever the displayed base resolvent exists, the determinant lemma gives
\[
1+2\langle C_L,(B_e-zI)^{-1}C_L\rangle=0
\]
at an even eigenvalue not already in \(\operatorname{Spec}(B_e)\), and
\[
1-2\langle S_L,(B_o-zI)^{-1}S_L\rangle=0
\]
on the odd side.

This is the exact Weinstein–Aronszajn/Sherman–Morrison object behind the Silva relay.

### 2.2 The same equation does not evaluate the curvature pairing

The center split of the exact even matrix is
\[
K=\begin{pmatrix}a_0&b^T\\ b&D\end{pmatrix}.
\]
If \(D-zI\) is invertible, then
\[
\Phi_0(z)=a_0-z-\langle b,(D-zI)^{-1}b\rangle
\]
and \(\Phi_0(\lambda_1)=0\).

The curvature pairing is different:
\[
S_{\mathrm{curv}}(z)
=\langle c,(D-zI)^{-1}b\rangle,
\qquad
c_n=\frac1{2\pi^2n^2}.
\]

The pole equation evaluates a \(C_L\)-self-pairing. The center Schur equation evaluates a \(b\)-self-pairing. Neither evaluates the mixed \(c,b\) pairing, because the three vectors are not equal. The original prediction is therefore false as stated.

### 2.3 The repaired scalar identity is a rank-two bordered derivative

Let \(e_0\) denote the central basis vector and put
\[
w=\binom{1/12}{c},
\qquad
M_{\mathrm{curv}}=e_0w^T+we_0^T.
\]
Then \(\operatorname{rank}M_{\mathrm{curv}}\le2\).

Define
\[
K(t)=K+tM_{\mathrm{curv}}.
\]
Its normalized bordered determinant is
\[
\Phi(t,z)
=\frac{\det(K(t)-zI)}{\det(D-zI)}
=a_0+\frac t6-z
-\langle b+tc,(D-zI)^{-1}(b+tc)\rangle.
\]

Therefore
\[
\boxed{
\frac12\,\partial_t\Phi(0,z)
=
\frac1{12}
-\langle c,(D-zI)^{-1}b\rangle.
}
\]

At \(z=\lambda_1\), \(\Phi(0,\lambda_1)=0\). This is an exact scalar secular identity and it takes no norm of the resolvent.

It does **not** yet prove the required rate. The new exact analytic target is
\[
\boxed{
\left|\partial_t\Phi_k(0,\lambda_{1,k})\right|
\le \frac{C}{L_k^2}.
}
\]

That is the one statement which would bound
\[
\kappa_k=\frac{L_k^2}{2}
\left(\frac1{12}-S_{\mathrm{curv}}(\lambda_{1,k})\right).
\]

## 3. Q2 — what the Loewner structure really gives

The source-faithful finite statement is already Lean-proved:
\[
\tau_{nm}
=
\frac{\beta_n-\beta_m}{n-m}
\qquad(n\ne m).
\]
The same source proves uniqueness of the normalized \(\beta\)-row and the exact displacement equation
\[
XK-KX=\beta\eta^T-\eta\beta^T.
\]

This includes the finite prime sum. Thus the production matrix is Cauchy-like with displacement rank at most two.

The stronger words need repair.

Because the node set is finite, the parity data admit an odd Hermite-interpolating polynomial \(\psi\) satisfying
\[
\psi(n)=\beta_n,
\qquad
\psi'(n)=\tau_{nn}.
\]
Then \(\psi(x)=x\,h(x^2)\) for a polynomial \(h\), and the even/odd parity blocks can be rewritten through divided differences of
\[
\Phi(\xi)=\xi h(\xi)
\quad\text{and}\quad
h(\xi).
\]

This proves finite confluent-Loewner representability. It does not select a canonical continuum function, and it does not prove that \(h\) or \(\Phi\) is operator monotone, operator convex, Stieltjes, or totally positive.

The Bhatia–Friedland–Jain inertia theorem is for the special family \(f(t)=t^r\). It does not transfer to this arithmetic interpolant without a new theorem placing the source-defined \(h\) in an appropriate function class.

Likewise, displacement rank two is an algorithmic structure, not a closed inverse formula. Inverting preserves a Cauchy-like representation, but its new generators already contain solves with the original matrix. It does not eliminate the hard resolvent.

Finally, if
\[
Dv_j=\mu_jv_j,
\]
then
\[
S_{\mathrm{curv}}(z)
=
\sum_j
\frac{\langle c,v_j\rangle\langle v_j,b\rangle}
     {\mu_j-z}.
\]
A clean exact one-sign theorem would follow from
\[
c=g(D)b,
\qquad
g(\mu_j)\ge0,
\]
because each residue becomes
\[
g(\mu_j)|\langle v_j,b\rangle|^2\ge0.
\]
No such source theorem is present. The finite cells \(m=43,83\) already rule out literal strict one-sign residues for every production cell.

## 4. Q3 — Input A must consume geometry, not one chosen supplier

The final analytic consumer does not need a Rayleigh excess. It needs the same ground transform to agree with the trial target on moving lattice nodes.

A source-stable intermediate port is
\[
p_k
=
1-|\langle\xi_k,q_k\rangle|^2.
\]
For unit vectors,
\[
\min_{|\omega|=1}\|\xi_k-\omega q_k\|^2
=
2(1-|\langle\xi_k,q_k\rangle|)
\le2p_k.
\]
Hence a sufficient moving-node rate is
\[
\boxed{
|A_k|^2L_kp_k\longrightarrow0.
}
\]

Relative Ritz is one optional supplier for \(p_k\). The data show why it must not define the port: on \(m=N\), \(p_k\) is small while the relative Rayleigh excess is enormous. A direct Schur graph, coefficient recurrence, overlap identity, or lattice-coordinate theorem may supply the same port more efficiently.

Two independent proof schedules cannot be sent to the terminal consumer. A normal family on \(m=N\) and identification on \(N\gg m\) concern two different sequences.

Permitted:
- use separate schedules for reconnaissance;
- prove normality uniformly in \(N\) and then select the Input-A schedule;
- prove a transfer theorem between schedules;
- choose one precommitted common diagonal \(N=N(m)\) and prove both inputs there.

Forbidden:
- infer convergence of one family from normality of another because both are cofinal.

The \(N\)-checks are favorable diagnostics for moving the curvature branch to a larger-\(N\) common schedule, but they are not the required uniform theorem.

## 5. Premise → source → consumer → residual gap

| Premise | Exact source / theorem | Consumer | Residual gap | Tags |
|---|---|---|---|---|
| Exact second jet and \(1/\sqrt{80}\) functional bound | `Proposition59EntireTransform.lean` | normalized curvature formula | cofinal source cancellation | `[FINITE_CELL][LEAN]` |
| Forced-zero tail vanishes on \(m=N\) | `Goal058CurvatureArithmetic.lean` | remove external lattice contribution | no intrinsic-curvature bound | `[COFINAL_FAMILY][LEAN]` |
| Finite relative Ritz | `RelativeRitzFinite.lean` | optional supplier for \(p_k\) | source-faithful common-path excess | `[FINITE_CELL][LEAN]` |
| Pole rank-two split | exact `ccmW02Entry` formula | parity secular root equation | mixed vector \(c\) is not the update vector | `[FINITE_CELL][PAPER]` |
| Source Loewner law | `ccmWeilTau_structured_offdiag`; `ccmWeilMatFinite_commutator` | Cauchy-like/parity representation | no canonical sign-controlling \(h\) | `[FINITE_CELL][LEAN]` |
| Bordered secular derivative | finite block determinant identity above | direct \(\kappa\) supplier | prove \(O(L^{-2})\) from source structure | `[COFINAL_FAMILY][CONDITIONAL]` |
| Projective defect \(p_k\) | exact Hilbert geometry | moving-node Input A | direct supplier and common schedule | `[COFINAL_FAMILY][CONDITIONAL]` |
| Normality + lattice identification | Vitali / identity theorem | `rh_of_real_zero_family_tendsto_centeredXi` | both properties on one family | `[ABSTRACT][PAPER]` |

## 6. Strongest attack

The bordered determinant identity may be mathematically exact and still be useless. Every block matrix has a Schur complement. Without a source law for its \(t\)-derivative, the construction merely renames
\[
\frac1{12}-S_{\mathrm{curv}}(\lambda_1).
\]

The generic two-dimensional plant makes this obstruction exact. For fixed \(b,c\ne0\), \(\lambda\in\mathbb R\), and \(t>0\), let
\[
K_t=
\begin{pmatrix}
\lambda+b^2/t & b\\
b & \lambda+t
\end{pmatrix}.
\]
Then \(\lambda\) is the simple lowest eigenvalue, but
\[
\langle c,(D-\lambda)^{-1}b\rangle=\frac{cb}{t}
\]
can take arbitrary scale as \(t\) varies. The matrix has the generic two-node divided-difference/displacement structure.

Therefore no theorem based only on “Loewner matrix”, “rank-two displacement”, or “scalar secular equation” can imply the \(L^{-2}\) rate. A surviving proof must use the exact arithmetic diagonal, prime term, pole vectors, or a source-specific spectral-calculus identity.

This attack kills the generic class statement. It does not kill the exact CCM family.

## 7. Lean-ready work versus new mathematics

### Lean-ready bookkeeping

- the exact rank-two factorization of `ccmW02Entry`;
- the generic center Schur determinant identity;
- the curvature-specific rank-two deformation;
- the derivative formula for the determinant ratio;
- finite odd Hermite interpolation and parity-block formulas.

None of these closes a cofinal quantifier.

### New analytic work

- an exact source identity or one-sided bound giving
  \[
  \partial_t\Phi_k(0,\lambda_{1,k})=O(L_k^{-2});
  \]
- a source theorem aligning the mixed residues, if that route is retained;
- a direct supplier for \(p_k\) or moving-node coordinate error;
- one common cofinal schedule carrying both normality and Input A;
- the still-missing order-one Hadamard factorization layer for the abstract curvature-to-normality theorem.

## FINAL PROPOSAL

Proceed with `TRY_SECULAR_IDENTITY_FOR_CURVATURE`, but use the repaired curvature-specific rank-two deformation, not the pole update alone.

The exact next target is:

```text
P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND

For the same even CCM ground family and one precommitted cofinal path,
define K_k(t)=K_k+t(e0*w_k^T+w_k*e0^T), w_k=(1/12,c_k).

Prove:
  |∂_t [det(K_k(t)-lambda1_k I) /
         det(D_k-lambda1_k I)] at t=0|
    <= C / L_k^2,

without:
  ||(D_k-lambda1_k I)^-1||;
  a uniform absolute gap;
  the desired curvature bound as an assumption;
  an operator-monotone claim for an interpolant not fixed by source.
```

Run the two-by-two plant before accepting any generic Loewner lemma. If the source rewrite leaves only the original mixed pairing or introduces the absolute reduced-resolvent norm, return:

```text
R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE
```

Then move to `R2B_SPECTRAL_CALCULUS_RESIDUE_ALIGNMENT` or directly to a common-path ground moment bound.

## CODEX DIRECTIVE

No execution is authorized in this adjudication. The next transaction, if opened, is read-only:

```text
TASK_ID:
  GOAL058_CURVATURE_BORDERED_SECULAR_SOURCE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  CCMFiniteWeilSourceCommutator.lean
  CCMFiniteWeilSourceMatrixN1.lean
  Proposition59EntireTransform.lean
  the exact even-block builder and pole vectors

RETURN:
  exact source expression for the bordered determinant slope;
  whether its leading term cancels before any norm;
  the first exact term that remains;
  PASS code P59_CURVATURE_BORDERED_SECULAR_SOURCE_IDENTITY
  or FAIL code R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE.
```

## META CLOSEOUT

- **What became smaller?** The curvature wall is one scalar derivative of a rank-two bordered determinant ratio.
- **What was killed?** R1; the pole secular equation as a direct evaluator of the mixed curvature row; strict one-sign residues; direct composition of two schedules.
- **What must not be tried again?** Full reduced-resolvent norms, power-function Loewner inertia on an unclassified arithmetic interpolant, and relative Rayleigh excess as the Input-A type.
- **Current smallest named gap:** `P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND`.
- **Next cheapest decisive test:** source-only expansion of the bordered slope, armed with the two-by-two plant.
- **Prediction fate:** all ten predictions are scored in the machine block without probability edits.
- **Memory entry:** direct curvature remains the normality mainline; Input A consumes projective/direct lattice geometry; both must live on one cofinal family.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
