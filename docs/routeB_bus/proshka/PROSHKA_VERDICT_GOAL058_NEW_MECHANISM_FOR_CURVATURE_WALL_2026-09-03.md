# STATUS: OPEN — C1 TWO-JET TRANSPORT SURVIVES; C5 RECIPROCAL-MODE ODD-GRAM PREFLIGHT SELECTED
```yaml
PRIMARY: TRY_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-03-NEWMECH
  BOUNDARY_ID: GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL
  REQUEST_COMMIT: e72cf4958626248244cd9dbd641767a101a50f0f
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.txt
  REQUEST_GIT_BLOB: a483fb5504457d9ae539e8b717b55be26fa03f17
  REQUEST_SHA256: 3cff2f5b9648fdc3a7042dc66c61b40ea4ccc8c9d6556bc5cf6bd30adac4720f
  REQUEST_BYTES: 7993
  REQUEST_LINES: 119
  FINAL_LF: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: ca738943406935e03e843858a314a29ff9ba55ed
  PARENT_VERDICT_CURVRITZ: 0c0a2b37dadea72fff0e3a9048b05bc36d3a98f3
  PARENT_VERDICT_SCHURLOEWNER: d7c7df3681d1031df55a3c0622e64dc8a3afbd73
  PARENT_VERDICT_CURVBRIDGE: 926c1865cae55fc4c469f6d10efce83905250057
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.md

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

DECISIONS:
  C1_SECOND_JET_POINTWISE_INPUT_A:
    verdict: DEVELOP
    code: DEVELOP_P59_PROJECTIVE_TWO_JET_TRANSFER
    bridge_status: PAPER_PASS_WITH_ANCHOR_REPAIR
    source_rate_status: OPEN
    scope: COFINAL_FAMILY
    verifier: PAPER
  C2_NOT_RH_DICHOTOMY:
    verdict: KILL
    code: KILL_NOT_RH_DICHOTOMY_AS_CURVATURE_SUPPLIER
    kill_scope: THEOREM_SHAPE
    kill_evidence_kind: LOGICAL_BRANCH_WITHOUT_GROUND_DETECTOR_CROSSWALK
    epistemic_status: MATHEMATICALLY_DEAD_AS_GENERIC_IMPLICATION
  C3_RELATIVE_GAP_ONE_THEOREM:
    verdict: KILL
    code: KILL_RELATIVE_GAP_AS_SINGLE_UNCONDITIONAL_MECHANISM
    kill_scope: THEOREM_SHAPE
    kill_evidence_kind: POSITIVITY_TYPE_PREMISE_PLUS_WRONG_MINMAX_DIRECTION
    repaired_conditional_supplier: RETAIN
    epistemic_status: RESEARCH_DEBT_FOR_SOURCE_SUPPLIERS
  C4_DE_BRANGES_CHAIN:
    verdict: KILL
    code: KILL_DEBRANGES_CHAIN_WITHOUT_COMMON_HB_GENERATOR
    kill_scope: THEOREM_SHAPE
    kill_evidence_kind: RH_CONDITIONAL_AMBIENT_SPACE_AND_NONNESTED_OBJECTS
    epistemic_status: MATHEMATICALLY_DEAD_AS_STATED
  C5_RECIPROCAL_MODE_ODD_GRAM:
    verdict: DEVELOP
    code: DEVELOP_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY
    selected_preflight: true
    exact_finite_identity_status: PAPER_PASS
    cofinal_source_bound_status: OPEN
    scope: FINITE_CELL_TO_COFINAL_FAMILY
    verifier: PAPER_THEN_CONDITIONAL

RANKING:
  1:
    mechanism: C5_RECIPROCAL_MODE_ODD_GRAM
    action: SOURCE_ONLY_PREFLIGHT
    kill_power: 10/10
    preflight_cost: 2/10
    proof_cost_if_survives: 7/10
  2:
    mechanism: C1_PROJECTIVE_TWO_JET
    action: FORMALIZE_BRIDGE_THEN_SEEK_DIRECT_PROJECTIVE_RATE
    kill_power: 9/10
    bridge_cost: 3/10
    source_cost: 8/10
  3:
    mechanism: C3_REPAIRED_RELATIVE_RITZ
    action: CONDITIONAL_SUPPLIER_ONLY
    kill_power: 7/10
    source_cost: 9/10
  4:
    mechanism: C2_NOT_RH_DICHOTOMY
    action: STOP
  5:
    mechanism: C4_DE_BRANGES_CHAIN
    action: STOP

C1_EXACT_INTERFACE:
  ground_anchor: A_k = centeredXi(0) / F_xi_k(0)
  projective_defect: p_k = 1 - abs(inner(xi_k,q_k))^2
  phase_alignment: norm(xi_k - omega_k*q_k)^2 <= 2*p_k
  second_jet_operator_norm: norm(ell_N) <= 1/sqrt(80)
  one_rate: J_k = abs(A_k)*L_k^(5/2)*sqrt(p_k)
  normality_sufficient: J_k = O(1)
  curvature_convergence_sufficient: J_k -> 0
  central_mismatch: O(J_k/L_k^2)
  source_supplier: OPEN_DIRECT_PROJECTIVE_OR_OBSERVABLE_RATE

C5_EXACT_INTERFACE:
  center_split: K = [[a0,b^T],[b,D]]
  noncentral_mode_diagonal: X = diag(n), n != 0
  reciprocal_mode_diagonal: R = X^(-1)
  eta: all_one_vector_on_noncentral_modes
  beta: X*b
  reciprocal_vector: r = R*eta
  source_displacement: X*D - D*X = beta*eta^T - eta*beta^T
  derived_commutator: D*R - R*D = b*r^T - r*b^T
  ground_resolvent_symbol: A = (D-lambda1*I)^(-1)
  parity:
    b: even
    r: odd
    A_preserves_parity: true
    inner_r_A_b: 0
  schur_root: inner_b_A_b = a0 - lambda1
  exact_mixed_pairing:
    "inner(R*r,A*b) = inner(r,A*(R*b)) - (a0-lambda1)*inner(r,A*r)"
  exact_curvature_defect:
    E_k: "0.5*norm(r)^2 - inner(r,A*(R*b)) + (a0-lambda1)*inner(r,A*r) + sum_{n>N} 1/n^2"
    kappa_k: "L_k^2/(4*pi^2) * E_k"
    nonnegative: true
  missing_source_bound: E_k <= C/L_k^2
  no_full_resolvent_norm: true
  no_absolute_gap: true
  dangerous_second_even_eigenpair_removed_by_parity: true

CHEAPEST_NEXT_ACTION:
  task_id: GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT
  mode: PAPER_AND_SOURCE_READ_ONLY
  target: P59_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY
  success_code: P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_IDENTITY
  failure_code: C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
  discriminator: >-
    After deriving the exact reciprocal-mode commutator, the curvature defect must
    reduce to an odd-sector Gram/coboundary expression whose estimate does not
    begin with norm((D-lambda1 I)^(-1)), an absolute gap, or the desired kappa bound.
  first_source_question: >-
    Does the full source vector R*b admit an exact odd-sector decomposition that
    closes the Gram defect before any norm is taken?

PREDICTION_FATES:
  P_C1_TWO_JET_TRANSPORT_IS_NONCIRCULAR:
    probability: 0.60
    fate: CONFIRMED_WITH_NORMALIZATION_REPAIR
    note: >-
      Lemma 7.3 gives locally uniform trial-transform convergence on closed
      substrips; Cauchy differentiation gives the trial 2-jet. Projective
      transport is valid after a common phase and ground-anchor ratio are tracked.
  P_C3_RELATIVE_GAP_IS_THE_REAL_OBSTRUCTION:
    probability: 0.65
    fate: REFUTED
    note: >-
      Before g_k is useful, the theorem needs eventual lambda1_k > 0 and a
      same-cell bound Rayleigh(q_k)/lambda1_k <= C. A second trial gives an upper,
      not a lower, bound for lambda2. The production diagnostic already makes the
      claimed easy Rayleigh ratio false for the current trial.
  P_C4_DE_BRANGES_CHAIN_VIABLE:
    probability: 0.25
    fate: REFUTED_AS_STATED
    note: >-
      No Hermite-Biehler generator or nested common de Branges chain is attached
      to the production F_k. The cited Weil/de Branges completion is constructed
      under RH, and ordering applies inside one fixed de Branges ambient space.
  P_C2_DICHOTOMY_YIELDS_CONSTRAINT:
    probability: 0.30
    fate: REFUTED
    note: >-
      Negativity of a windowed Weil minimum constrains an energy value, not the
      logarithmic second derivative of its minimizing transform. No theorem
      identifies the minimizer with a detector of one selected off-line zero.
  P_JUDGE_PROPOSES_BETTER_C5:
    probability: 0.40
    fate: CONFIRMED_AT_REPRESENTATION_SCOPE
    note: >-
      The reciprocal-mode displacement identity converts the even mixed
      curvature pairing into one odd-sector Gram defect, avoiding the collapsed
      second even eigenpair. The cofinal O(L^-2) estimate remains open.

SCOPED_KILLS:
  C2:
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_ABSTRACT_COUNTERMODEL_PLUS_MISSING_SOURCE_CROSSWALK
    REPAIRED_STATEMENT: >-
      Under not-RH, at least one of same-family identification or bounded
      curvature must fail; this disjunction supplies neither input.
  C3:
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_MINMAX_DIRECTION_AND_TYPE_AUDIT
    REPAIRED_STATEMENT: >-
      On cells with 0 < lambda1 < lambda2 and Rayleigh(q) <= C*lambda1,
      p <= (C-1)/(lambda2/lambda1-1). This remains an optional supplier.
  C4:
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: SOURCE_ASSUMPTION_AND_OBJECT_MISMATCH
    REPAIRED_STATEMENT: >-
      A de Branges route may reopen only after constructing source-defined
      Hermite-Biehler E_k, proving F_k is its A-function, and proving nested
      isometric embeddings along the same cofinal family.

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized entire real-zero ground family is locally uniformly
    bounded and is identified with centeredXi on one cofinal path.
  ORIGINAL_REQUESTED_OBJECT: uniform normalized curvature bound
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_THIS_NORMALIZED_REAL_ZERO_NORMALITY_INTERFACE
  KNOWN_WEAKER_INTERFACES:
    - bounded anchored ground second jet
    - bounded two-observable ground-to-trial defect
    - direct local boundedness on one fixed complex disk
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: reciprocal-mode displacement sends curvature to odd-sector Gram geometry

LEAN_READY:
  - P59_PROJECTIVE_TWO_JET_TRANSFER
  - P59_RECIPROCAL_MODE_COMMUTATOR
  - P59_RECIPROCAL_MODE_ODD_GRAM_IDENTITY
  - C2_NEGATIVE_BOTTOM_DOES_NOT_BOUND_CURVATURE_PLANT
  - C3_RELATIVE_RITZ_CONDITIONAL_SUPPLIER

NEW_ANALYTIC_WORK:
  - P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_BOUND
  - P59_DIRECT_PROJECTIVE_SECOND_JET_RATE
  - SAME_COFINAL_TRIAL_NORMALIZATION_CROSSWALK

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_MATHEMATICS_ONLY_VERDICT
  NEXT_TRANSACTION: GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  FORBIDDEN:
    - Lean edits
    - numerical runs
    - full resolvent norm estimates
    - absolute complement floors
    - pole versus Arch-Prime splitting
    - post-hoc schedule changes

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
CURRENT_SMALLEST_GAP: P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_BOUND
```

## ROUTE MAP

| Candidate | Verdict | Exact surviving object | First failure point | Kill-power / cost | Tags |
|---|---|---|---|---:|---|
| **C1 — second jet through projective defect** | **DEVELOP** | Anchored two-jet transfer with \(J_k=|A_k|L_k^{5/2}\sqrt{p_k}\) | A same-family source bound for \(p_k\) or the two scalar observables | `9/10 · 3/10` for the bridge; source cost `8/10` | `[COFINAL_FAMILY][PAPER]` |
| **C2 — work only under not-RH** | **KILL** | Only the disjunction “identification or curvature must fail” survives | No map from a negative witness to the bottom ground transform of one selected zero | `10/10 · 1/10` | `[COFINAL_FAMILY][PAPER]` |
| **C3 — relative gap as one theorem** | **KILL AS PRIMARY; RETAIN CONDITIONAL LEMMA** | \(p_k\le(C-1)/(g_k-1)\) when \(0<\lambda_1<\lambda_2\) and \(R(q)\le C\lambda_1\) | Eventual positivity and the same-cell Rayleigh ratio come before \(g_k\) | `9/10 · 2/10` | `[COFINAL_FAMILY][PAPER]` |
| **C4 — de Branges chain** | **KILL AS STATED** | A possible future route after an \(E_k/A_k\) and nesting theorem | The production \(F_k\) is not a supplied Hermite–Biehler generator or a proved A-function in one nested chain | `9/10 · 2/10` | `[COFINAL_FAMILY][PAPER]` |
| **C5 — reciprocal-mode odd-Gram identity** | **DEVELOP; SELECTED PREFLIGHT** | Exact displacement identity converting the full curvature sum into one odd-sector Gram defect | Whether \(R b\) has a source decomposition that closes before any inverse norm | `10/10 · 2/10` preflight | `[FINITE_CELL][PAPER]` → `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Source and scope lock

The authoritative request is `REQ-2026-09-03-NEWMECH`, boundary `GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL`, fixed by request commit `e72cf4958626248244cd9dbd641767a101a50f0f`, Git blob `a483fb5504457d9ae539e8b717b55be26fa03f17`, and SHA-256 `3cff2f5b9648fdc3a7042dc66c61b40ea4ccc8c9d6556bc5cf6bd30adac4720f`. The six-field phase key is unchanged. `[COFINAL_FAMILY][PAPER]`

This adjudication accepts the request’s dead-shape ledger. It does not reopen a fixed absolute complement floor, the fixed-\(\beta\) residual quotient, the R1 dual solve, the pole/Arch–Prime split, the bordered secular derivative, the naive Hilbert–Schmidt kernel norm, or a two-schedule composition. `[COFINAL_FAMILY][PAPER]`

## 2. C1 — DEVELOP: projective two-jet transfer

### Exact theorem

For each \(k\), let \(T_k(v)=F_{k,v}\) be the exact P59 transform on the same finite carrier. Its source-locked jets are

\[
T_k(v)(0)=\sqrt{L_k}\,v_0,
\qquad
T_k(v)''(0)=-L_k^{5/2}\ell_k(v),
\qquad
\|\ell_k\|\le \frac1{\sqrt{80}}.
\]

Let \(\xi_k,q_k\) be unit vectors in that same carrier and let

\[
p_k=1-|\langle\xi_k,q_k\rangle|^2.
\]

Choose \(|\omega_k|=1\) so that

\[
\|\xi_k-\omega_kq_k\|^2
=
2\bigl(1-|\langle\xi_k,q_k\rangle|\bigr)
\le2p_k.
\]

Let

\[
A_k=\frac{\operatorname{centeredXi}(0)}{T_k(\xi_k)(0)},
\]

and suppose a trial normalization \(B_k\ne0\) satisfies

\[
B_kT_k(q_k)\longrightarrow \operatorname{centeredXi}
\]

locally uniformly on closed substrips. Assume

\[
J_k:=|A_k|L_k^{5/2}\sqrt{p_k}=O(1).
\]

Then

\[
|A_k|\,
|T_k(\xi_k)(0)-T_k(\omega_kq_k)(0)|
\le
\sqrt2\,\frac{J_k}{L_k^2}
\longrightarrow0.
\]

Since \(A_kT_k(\xi_k)(0)=\operatorname{centeredXi}(0)\ne0\), the central values imply

\[
\frac{A_k\omega_k}{B_k}\longrightarrow1.
\]

Local uniform trial convergence therefore gives convergence of the rescaled trial 2-jet by Cauchy’s integral formula. Meanwhile,

\[
\begin{aligned}
|A_k|\,
|T_k(\xi_k)''(0)-T_k(\omega_kq_k)''(0)|
&\le
|A_k|L_k^{5/2}\|\ell_k\|
  \|\xi_k-\omega_kq_k\| \\
&\le
\sqrt{\frac{2}{80}}\,J_k.
\end{aligned}
\]

Thus the anchored ground second derivatives are uniformly bounded. Their central values are fixed and nonzero, so

\[
\sup_k\left|
-\frac{T_k(\xi_k)''(0)}
       {2T_k(\xi_k)(0)}
\right|<\infty.
\]

The explicit real-zero product then gives local uniform boundedness of the anchored ground family. If \(J_k\to0\), the normalized curvature converges to

\[
-\frac{\operatorname{centeredXi}''(0)}
       {2\operatorname{centeredXi}(0)}.
\]

`[COFINAL_FAMILY][PAPER]`

### Adjudication

CCM Lemma 7.3 gives local uniform convergence of the **trial** transform on closed substrips. Cauchy differentiation therefore gives the trial 2-jet at the origin; no separate derivative theorem is needed. `[COFINAL_FAMILY][PAPER]`

The interface is noncircular. It assumes only a geometric projective error or, more weakly, the central and second-jet observable errors. It does not assume normality, a curvature bound, or an absolute spectral floor. `[COFINAL_FAMILY][PAPER]`

The exact first failure is the supplier:

\[
\boxed{
|A_k|^2L_k^5p_k=O(1).
}
\]

Relative Ritz may supply it only after its own positive-relative hypotheses are proved on the same cells. A direct overlap theorem or direct two-observable theorem is strictly weaker and remains admissible. `[COFINAL_FAMILY][CONDITIONAL]`

## 3. C2 — KILL: the not-RH dichotomy is not a supplier

A negative direction for the windowed Weil form can force an upper bound

\[
\lambda_{1,k}\le -c
\]

after an exact fixed-witness and finite-section crosswalk. It does not force the bottom eigenvector to localize at one selected off-line zero, and it gives no estimate of

\[
-\frac{F_k''(0)}{2F_k(0)}.
\]

`[COFINAL_FAMILY][PAPER]`

The generic implication is false. A Hermitian family may have a fixed negative lowest eigenvalue while its assigned normalized real-rooted ground transforms have zero pairs \(\pm\varepsilon_k\) with \(\varepsilon_k\downarrow0\), hence curvature \(\varepsilon_k^{-2}\to\infty\). This plant kills “negative bottom + real zeros ⇒ bounded curvature” without saying anything about the exact CCM source family. `[ABSTRACT][PAPER]`

Under not-RH, the valid conclusion is only:

\[
\text{same-family identification and bounded curvature cannot both hold.}
\]

That is the contrapositive of the existing roof, not a mechanism selecting which input fails. The first exact source failure is the unsupported sentence “the bottom eigenvector is a detector of the chosen off-line zero.” Weil negativity supplies a witness, not that ground-state localization theorem. `[COFINAL_FAMILY][PAPER]`

## 4. C3 — KILL AS THE PRIMARY MECHANISM

The finite conditional lemma is correct:

\[
0<\lambda_1<\lambda_2,\qquad
R(q)\le C\lambda_1
\]

imply

\[
p
\le
\frac{R(q)-\lambda_1}{\lambda_2-\lambda_1}
\le
\frac{C-1}{\lambda_2/\lambda_1-1}.
\]

Combined with C1, a sufficient rate is

\[
|A_k|^2L_k^5
\frac{C_k-1}{g_k-1}
=O(1).
\]

`[FINITE_CELL][PAPER]`

But this is not one unconditional theorem. It requires three prior source facts:

1. eventual \(\lambda_{1,k}>0\), so the multiplicative quotient is typed;
2. a lower bound for \(\lambda_{2,k}\) relative to \(\lambda_{1,k}\);
3. a same-cell trial with \(R(q_k)/\lambda_{1,k}\le C\).

A second trial vector gives an **upper** bound for \(\lambda_2\) by min–max, not the lower bound C3 requests. The lower bound needs complement coercivity or another exclusion theorem. `[FINITE_CELL][PAPER]`

More importantly, on the production \(m=N\) schedule the supplied trial Rayleigh value and \(\lambda_1\) are not on the same multiplicative scale. Therefore the claim that the Rayleigh ratio is the easy input is already refuted for the current source trial. `[FINITE_CELL][ARB_INTERVAL]`

The conditional relative-Ritz theorem remains useful. The proposal that it is the single main mechanism is killed.

## 5. C4 — KILL: no common de Branges chain exists in the supplied objects

The cited Suzuki construction identifies a Weil-form Hilbert completion with a de Branges space **under RH**. The de Branges ordering theorem orders de Branges subspaces inside one fixed ambient de Branges space. It does not order arbitrary real-rooted characteristic functions from changing finite matrices. `[ABSTRACT][PAPER]`

The production \(F_k\) is a real entire spectral determinant/A-function candidate. No source theorem provides:

- a Hermite–Biehler function \(E_k\);
- its conjugate companion \(B_k\);
- an identity \(F_k=(E_k+E_k^\sharp)/2\);
- isometric embeddings \(\mathcal H(E_k)\hookrightarrow\mathcal H(E_{k+1})\);
- a common canonical Hamiltonian ordered along \(m=N=k+2\).

`[COFINAL_FAMILY][PAPER]`

Self-adjointness of \(D_{\log}^{(\lambda,N)}\) supplies a real spectrum. It does not supply the Hermite–Biehler generator or nesting. Positivity of every finite Weil form would also be an RH-flavoured premise rather than a replacement for the current normality wall. `[COFINAL_FAMILY][PAPER]`

The first exact failure is therefore `COMMON_HERMITE_BIEHLER_GENERATOR_AND_NESTING_MISSING`.

## 6. C5 — DEVELOP: reciprocal-mode displacement sends curvature to the odd sector

This is the new representation selected for the next preflight.

### Step 1 — source algebra

Split the exact real symmetric matrix at the central coordinate:

\[
K=
\begin{pmatrix}
a_0&b^{T}\\
b&D
\end{pmatrix}.
\]

On the noncentral modes \(n\ne0\), define

\[
X=\operatorname{diag}(n),
\qquad
R=X^{-1},
\qquad
\eta=(1,\ldots,1)^T,
\qquad
r=R\eta.
\]

The source definition of the beta row gives

\[
\beta=Xb.
\]

The exact CCM displacement law, including the prime term, restricts to

\[
XD-DX=\beta\eta^T-\eta\beta^T.
\]

Multiplication by \(R\) on both sides gives the new exact identity

\[
\boxed{
DR-RD=br^T-rb^T.
}
\]

`[FINITE_CELL][PAPER]`

### Step 2 — scalar Gram identity

Let \(\lambda=\lambda_1(K)\) be the simple even bottom eigenvalue and assume \(D-\lambda I\) is invertible. Put

\[
A=(D-\lambda I)^{-1}.
\]

No norm of \(A\) is taken.

From the previous commutator,

\[
RA-AR
=
A(br^T-rb^T)A.
\]

Pairing on the left with \(r^T\) and on the right with \(b\) gives

\[
r^TRAb
=
r^TARb
+
(r^TAb)^2
-
(r^TAr)(b^TAb).
\]

Reversal symmetry makes \(b\) even and \(r\) odd; \(A\) preserves parity. Hence

\[
r^TAb=0.
\]

The Schur root equation gives

\[
b^TAb=a_0-\lambda.
\]

Therefore

\[
\boxed{
r^TRAb
=
r^TARb
-
(a_0-\lambda)\,r^TAr.
}
\]

Since the curvature vector is

\[
c=\frac1{2\pi^2}Rr,
\]

this evaluates the **entire mixed curvature pairing at once**:

\[
\boxed{
S_{\mathrm{curv}}(\lambda)
=
\frac1{2\pi^2}
\left[
r^TARb-(a_0-\lambda)r^TAr
\right].
}
\]

`[FINITE_CELL][PAPER]`

### Step 3 — exact curvature defect

On the symmetric noncentral carrier,

\[
\frac1{12}
=
\frac1{2\pi^2}
\left[
\frac12\|r\|^2
+
\sum_{n>N}\frac1{n^2}
\right].
\]

Consequently,

\[
\boxed{
\kappa_k
=
\frac{L_k^2}{4\pi^2}E_k,
}
\]

where

\[
\boxed{
E_k=
\frac12\|r_k\|^2
-r_k^TA_kR_kb_k
+(a_{0,k}-\lambda_{1,k})r_k^TA_kr_k
+\sum_{n>N_k}\frac1{n^2}.
}
\]

The real-zero product gives \(E_k\ge0\). The new source target is the upper envelope

\[
\boxed{
E_k\le \frac{C}{L_k^2}.
}
\]

`[COFINAL_FAMILY][CONDITIONAL]`

### Why this is genuinely new

The dangerous second eigenpair is even. The vectors \(r_k\) and \(R_kb_k\) are odd, so every resolvent pairing in \(E_k\) lives in the odd sector. The representation therefore does not pay the collapsed second-even-eigenvalue denominator found by Probe 5. It also keeps the full source center column \(b_k\); it never separates pole and Arch–Prime terms. `[FINITE_CELL][PAPER]`

This identity alone cannot imply the \(L^{-2}\) rate: a generic finite Loewner/displacement plant can vary the odd Gram defect. The surviving source question is whether the exact arithmetic vector \(R_kb_k\) is an odd coboundary or contraction for \(D_k-\lambda_{1,k}I\).

A particularly strong success form is an explicit odd vector \(s_k\), constructed from source rows without inversion, such that

\[
\frac12(D_k-\lambda_{1,k}I)r_k
-R_kb_k
+(a_{0,k}-\lambda_{1,k})r_k
=
(D_k-\lambda_{1,k}I)s_k
\]

and

\[
|\langle r_k,s_k\rangle|
+
\sum_{n>N_k}\frac1{n^2}
\le \frac{C}{L_k^2}.
\]

Then \(E_k=O(L_k^{-2})\) follows without a resolvent norm or an absolute gap. `[COFINAL_FAMILY][CONDITIONAL]`

### First decisive test and kill condition

Derive the finite identity from the existing exact commutator and parity theorems. Then expand only the full source vector \(R_kb_k\).

Pass only if the remaining odd defect becomes:

- an exact \((D_k-\lambda_{1,k}I)\)-coboundary;
- a one-sided source form;
- or a finite-rank term with an explicit \(L^{-2}\) budget.

If every estimate begins with

\[
\|(D_k-\lambda_{1,k}I)^{-1}\|,
\]

an absolute odd floor, or another uncontrolled mixed resolvent pairing, return

```text
C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
```

and move immediately to C1.

## 7. Strongest attack

The strongest objection to C5 is that it may only move the same mixed pairing from the even block to an odd block. Low displacement rank does not by itself imply a quantitative \(L^{-2}\) estimate. A generic source-free Loewner plant can satisfy the reciprocal commutator while making \(E_k\) arbitrary. `[FINITE_CELL][PAPER]`

That objection is accepted. C5 receives only a **source-only preflight**, not a proof campaign. Its value is that the preflight is cheap and decisive:

- if the full \(R b\) vector has a source coboundary identity, the collapsed even gap disappears from the problem;
- if it does not, the exact failure code closes C5 before any numerical or Lean expansion.

`[COFINAL_FAMILY][CONDITIONAL]`

## 8. Lean-ready versus new analytic work

### Lean-ready bookkeeping

The following statements are finite algebra or abstract complex analysis:

1. `P59ProjectiveTwoJetTransfer`;
2. `ccmReciprocalMode_commutator`;
3. `p59Curvature_eq_oddGramDefect`;
4. the conditional relative-Ritz supplier;
5. the C2 negative-bottom/large-curvature plant.

They do not close a cofinal quantifier. `[FINITE_CELL][PAPER]`

### New analytic mathematics

The load-bearing statements are:

1. `P59ReciprocalModeOddGramSourceBound`:
   \[
   E_k\le C/L_k^2;
   \]
2. or, after C5 failure, `P59DirectProjectiveSecondJetRate`:
   \[
   |A_k|^2L_k^5p_k=O(1);
   \]
3. the exact common normalization between the CCM trial limit and the ground anchor.

`[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Run exactly one paper/source preflight:

```text
GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT
```

Use the exact source commutator and the full center column. Do not split the kernel. Do not bound a resolvent norm. Do not assume any absolute gap.

Registered expected outcome for this new test:

```yaml
P_C5_ODD_COBBOUNDARY_EXISTS:
  probability: 0.45
  pass: exact source coboundary or one-sided odd Gram bound
  fail: C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
```

If it passes, the curvature wall becomes one odd-sector \(L^{-2}\) form estimate. If it fails, C1 is the surviving mainline and the exact source obligation is

\[
|A_k|^2L_k^5p_k=O(1)
\]

or the strictly weaker two-observable version.

## CODEX DIRECTIVE

No execution is authorized by this paper-only adjudication.

The next transaction, if separately opened, is:

```text
TASK_ID:
  GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  Q3/Proofs/RouteB/CCMFiniteWeilParity.lean
  Q3/Proofs/RouteB/Proposition59EntireTransform.lean
  exact center-split definitions used by the Schur probe

RETURN:
  1. exact typed definitions of X, R, eta, beta, b and r;
  2. proof or refutation of D*R-R*D = b*r^T-r*b^T;
  3. parity proof that r^T*A*b = 0;
  4. exact derivation of kappa = L^2/(4*pi^2)*E;
  5. full source expansion of R*b;
  6. either:
       P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_IDENTITY
     or:
       C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE.

FORBIDDEN:
  Lean edits;
  numerical runs;
  full resolvent norms;
  absolute floors;
  pole/Arch-Prime splitting;
  post-hoc schedule changes.
```

## META CLOSEOUT

- **What became smaller?** The direct curvature wall has a new exact candidate representation: one odd-sector Gram defect \(E_k\), while the fallback normality route needs only one anchored projective second-jet rate.
- **What was killed?** The not-RH dichotomy as a curvature supplier; the relative gap as one unconditional theorem; the de Branges chain without a common Hermite–Biehler generator and nesting.
- **What must not be tried again?** A second trial as a lower bound for \(\lambda_2\); eventual positivity hidden inside a relative quotient; RH-conditional de Branges completion used as an unconditional compactness engine; any split of the full center column.
- **Current smallest named gap:** `P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_BOUND`.
- **Next cheapest decisive test:** derive the reciprocal-mode identity and inspect the exact full vector \(R b\) for an odd coboundary before any norm.
- **Fate of prior predictions:** all five are scored in the machine block without probability edits.
- **Memory entry:** C1 is valid after anchor repair; C5 may bypass projective tracking by moving the full curvature observable into odd-sector displacement geometry.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
