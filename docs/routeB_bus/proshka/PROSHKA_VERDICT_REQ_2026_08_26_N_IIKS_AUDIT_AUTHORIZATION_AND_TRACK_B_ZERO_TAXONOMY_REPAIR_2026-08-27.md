# STATUS: OPEN
```yaml
PRIMARY: RUN_EXACT_GRAPH_OPERATOR_DIIKS_RHP_SOURCE_AUDIT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-26-N

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TRACK_B_CORRECTION_3:
    commit: 3f401d0255caa23aa9fe0d329440109e0f5f7da2
    path: docs/routeB_bus/LINUX_CORRECTION_3_TRACK_B_ZERO_DENSITY_DOES_NOT_BEAT_ENVELOPE_GOAL058_2026-08-27.md
  TRACK_A_IIKS_IDENTIFICATION:
    commit: d684424793b69c2848432f16b8f340885e8e6bf7
    path: docs/routeB_bus/LINUX_TRACK_A_INTEGRABLE_KERNEL_IDENTIFICATION_GOAL058_2026-08-27.md
  PRIOR_PROSHKA_REPAIR:
    commit: fc05b467d869d1f71d2284936d90c5575457f2ed
    status: SUPERSEDED_IN_TRACK_B_ZERO_TAXONOMY_AND_M2_CLASSIFICATION

TRACK_B:
  vitali_porter_framework: SURVIVES
  real_axis_no_power_growth: SURVIVES
  inverse_square_sup_x_mechanism: KILLED
  full_lattice_zero_claim: REJECTED
  M2_equals_L_squared_over_24_claim: REJECTED
  centered_M2_identity: PAPER_PASS
  centered_M2_uniform_bound: OPEN_NOT_KILLED
  strip_normality: OPEN
  required_cancellation_location: INSIDE_SINE_TIMES_CAUCHY_RATIONAL_FACTOR

TRACK_A:
  offdiagonal_standard_dIIKS_match: PROVED
  full_matrix_standard_dIIKS_match: NOT_PROVED_DIAGONAL_GUARD_REQUIRED
  graph_operator_standard_dIIKS_match: NOT_PROVED_HIGHER_DISPLACEMENT_GENERATOR_REQUIRED
  resolvent_structure: SOURCE_READY_CONDITIONALLY
  asymptotic_rate: OPEN
  audit_authorized: true

EXACT_NEXT_TASK:
  TASK_ID: GOAL058_SELECTED_FERRERS_GRAPH_OPERATOR_DIIKS_RHP_SOURCE_AUDIT
  MODE: PAPER_AND_PRIMARY_SOURCE_READ_ONLY
  LEAN_EDIT: false
  NUMERICS: false
  ARISTOTLE: false

DISCRIMINATOR:
  PASS: SELECTED_FERRERS_GRAPH_DIIKS_RHP_ASYMPTOTIC_SOURCE_READY
  HOLD: DIIKS_EXACT_REPRESENTATION_WITHOUT_SOURCE_ASYMPTOTIC_CLOSURE
  FAIL: DIIKS_RENAMES_LINEAR_SOLVE_OR_REIMPORTS_PRIME_OSCILLATION_WALL

ARSENAL:
  mandate_accepted: true
  cards_applied:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

CANDIDATE_REPRESENTATIONS:
  R1_DIAGONAL_FACTORED_DISCRETE_IIKS:
    selected: true
    kill_power: 10/10
    cost: 5/10
  R2_DIRECT_CAUCHY_LIKE_DISPLACEMENT_INVERSE:
    selected: runner_up
    kill_power: 9/10
    cost: 4/10
  R3_VITALI_REAL_AXIS_PLUS_EXACT_SINE_RATIONAL_CANCELLATION:
    selected: parallel_hold
    kill_power: 8/10
    cost: 7/10

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Track B: correction 3 правильно убила одну оценку, но переубила весь кандидат

Правильная часть correction 3:

- тождество
  \[
  \frac{|f(x+iy)|^2}{|f(x)|^2}
  =\prod_n\left(1+\frac{y^2}{(a_n-x)^2}\right)
  \]
  не даёт полезной оценки через `exp(y^2 S(x))`;
- `sup_x S(x)` сингулярен в каждом вещественном нуле;
- на вещественной оси strip factor равен единице, поэтому real-axis tracking имеет только логарифмическую цену;
- переход в полосу требует cancellation внутри полного `sin * rational` объекта, а не prime-component estimate.

Но две последующие zero-taxonomy строки correction 3 неверны для exact Proposition-59 transform.

Exact Lean bridge разделяет нули на три ветви:

```text
included removable pole;
exterior zero of the sine numerator;
off-lattice Lagrange-polynomial zero.
```

Включённые решёточные точки `|q| <= N` являются removable poles, а не автоматически нулями. Exterior sine-lattice zeros начинаются только при `|q| > N`. Остальные конечные нули — корни Lagrange numerator после exact coordinate crosswalk; репозиторий доказывает их вещественность, но не утверждает, что они совпадают с решёткой.

Следовательно фразы

```text
all zeros lie on the grid;
M2 = sum_{n>=1} 1/(nh)^2 = L^2/24
```

не source-locked.

Для одних только exterior lattice zeros положительный inverse-square contribution равен

\[
M_{2,k}^{\rm ext}
=
\frac{L_k^2}{4\pi^2}
\sum_{q>N_k}\frac1{q^2}
\le
\frac{L_k^2}{4\pi^2 N_k}.
\]

На выбранном schedule `N_k=m_k=k+2` этот вклад стремится к нулю. Неизвестной остаётся finite interior Lagrange-root contribution.

### 2. Судьба center-curvature repair

Для одной и той же чётной entire ground transform, если `F_k(0) != 0`, order не превосходит one и все нули real, парная Hadamard factorization даёт

\[
F_k(z)=F_k(0)
\prod_{a>0}\left(1-\frac{z^2}{a^2}\right),
\]

и exact identity

\[
M_{2,k}:=\sum_{a>0}\frac1{a^2}
=-\frac{F_k''(0)}{2F_k(0)}.
\]

Это тождество остаётся правильным. Uniform bound на `M2_k` является достаточным условием local normality, но не получен и не следует из lattice factor автоматически.

Поэтому предыдущая классификация `CENTERED_EVEN_INVERSE_SQUARE_ZERO_MOMENT` исправляется:

```text
exact scalar identity:
  PAPER PASS;

automatic uniform bound:
  REJECTED;

candidate source preflight:
  STILL LEGAL;

Track B PASS:
  NOT EARNED.
```

Correction 3 правильно предупреждает, что exact cancellation между sine numerator и finite Cauchy/Lagrange factor может быть необходима. Но она не доказывает невозможность uniform center curvature.

### 3. Track A: exact structural match принят на правильной границе

Kernel-green source theorem доказывает для `i != j`:

\[
M_{ij}
=
\frac{\beta_i-\beta_j}{n_i-n_j}.
\]

Поэтому при

\[
f_i=(\beta_i,1)^T,
\qquad
g_j=(1,-\beta_j)^T
\]

имеем

\[
f_i^Tg_j=\beta_i-\beta_j,
\qquad
f_i^Tg_i=0.
\]

Значит **внедиагональная часть** literal finite CCM Weil matrix является exact standard discrete IIKS kernel. Equivalent displacement identity

\[
[D,M]=\beta\mathbf1^T-\mathbf1\beta^T
\]

уже kernel-green.

Это настоящая representation progress.

### 4. Первая обязательная поправка: full matrix не является standard dIIKS без diagonal adapter

В standard discrete IIKS definition diagonal kernel равен zero. Literal CCM matrix имеет собственную diagonal.

Поэтому корректная запись:

\[
M=A_{\rm diag}+K_0,
\]

где `K0` — zero-diagonal IIKS kernel.

Для shift `a`, если diagonal matrix

\[
H_a:=A_{\rm diag}-aI
\]

обратима, можно factor:

\[
M-aI
=H_a\left(I+H_a^{-1}K_0\right).
\]

`H_a^-1 K0` снова является standard discrete IIKS kernel с rescaled left vector. Если хотя бы один diagonal entry равен `a`, требуется declared block split or a different regularization; этот случай нельзя спрятать.

Следовательно строка отчёта

```text
(K-aI)^-1 is directly the standard IIKS resolvent because K/a is integrable
```

слишком сильна для full matrix.

### 5. Вторая обязательная поправка: exact consumer uses graph operator C, not M-aI

Текущий consumer содержит

\[
C=Q(M-\epsilon I)Q+P,
\qquad
E_k(z)\propto\langle\kappa_k(z),C^{-1}r_k\rangle.
\]

Projection terms change the displacement generator. Since

\[
[D,M]
\]

has rank at most two and

\[
[D,P]
\]

has rank at most two, `[D,C]` remains finite-rank, but it is not the same rank-two generator `(beta,1)`.

The audit must derive an exact generator

\[
[D,C]=UV^T
\]

with the smallest justified rank and the literal vectors built from `beta`, `q`, `Dq`, `(M-epsilon I)q` and their adjoints.

Then

\[
[D,C^{-1}]=-C^{-1}UV^TC^{-1}
\]

shows that `C^-1` is Cauchy-like. This is an exact closure statement, but its generators contain the unknown solves `C^-1 U` and `C^{-T}V`. Calling those vectors “explicit” before solving the discrete RHP or an equivalent structured system is circular.

### 6. Что реально даёт discrete RHP

Classical discrete IIKS/Borodin theory states that the resolvent of a zero-diagonal discrete integrable operator stays integrable and can be reconstructed from a discrete Riemann-Hilbert problem. The 2025 paper `arXiv:2511.05046` reviews this scalar theory and generalizes it to matrix/differential kernels.

Our scalar offdiagonal kernel therefore does not need the 2025 generalization merely for existence of a dRHP: Borodin's discrete theory already supplies that layer. The new paper becomes relevant only if the exact graph operator naturally lands in its generalized kernel class or if its hierarchy supplies an actual asymptotic closure.

A dRHP representation is not yet an estimate. For arbitrary residue data `beta_i`, the dRHP can be exactly equivalent to the original linear solve. Decision-changing progress requires extra source structure:

```text
a closed recurrence/difference law for beta_i;
a finite-dimensional Lax deformation under k;
a tractable limiting jump/residue problem;
or an exact formula for the particular graph functional.
```

Without one of these, IIKS is a correct name for the matrix class but not a cheaper RH route.

## FINAL PROPOSAL

Authorize exactly one bounded read-only audit.

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_GRAPH_OPERATOR_DIIKS_RHP_SOURCE_AUDIT

MODE:
  PAPER_AND_PRIMARY_SOURCE_READ_ONLY

PHASE 0 — exact object lock:
  Distinguish literal M, zero-diagonal K0, diagonal A_diag,
  shifted M-aI, graph C=Q(M-epsilon I)Q+P, residual r,
  P59 kernel kappa(z), and the exact scalar consumer.

PHASE 1 — diagonal adapter:
  Construct the exact factorization of M-aI through a zero-diagonal dIIKS
  operator. Enumerate every diagonal-zero exceptional case.

PHASE 2 — graph displacement:
  Derive [D,C]=UV^T with exact minimal generator and rank.
  Show how C^-1 inherits the generator without calling C^-1 U explicit.

PHASE 3 — discrete RHP:
  Write the exact pole/residue problem for the adapted full operator or graph
  operator. Express E_k(z) as a named matrix element / Cauchy coefficient of
  its solution.

PHASE 4 — arithmetic closure:
  Substitute the literal beta_n = n*tau(n,0). Determine whether beta_n obeys
  a source-locked difference, recurrence, Lax, or asymptotic law strong enough
  to analyze the dRHP unconditionally on the frozen schedule.

PHASE 5 — cost comparison:
  Compare exact unresolved inputs with:
    full signed real-axis residual route;
    direct displacement-generator route;
    prior retained-prime Gamma route.
```

Mandatory plants:

```text
P1_EXACT_EIGENVECTOR:
  q exact eigenvector of full M must make the final consumer zero.

P2_DIAGONAL_ONLY:
  K0=0 but A_diag nonconstant; catches the false claim that a commuting
  diagonal is irrelevant to the inverse.

P3_ARBITRARY_BETA:
  arbitrary beta data has an exact dRHP but no automatic asymptotic;
  catches “integrable = explicitly solvable”.

P4_GRAPH_OBJECT:
  replace M-aI by the actual C; catches reuse of the wrong rank-two generator.
```

Success codes:

```text
PASS:
  SELECTED_FERRERS_GRAPH_DIIKS_RHP_ASYMPTOTIC_SOURCE_READY

HOLD:
  DIIKS_EXACT_REPRESENTATION_WITHOUT_SOURCE_ASYMPTOTIC_CLOSURE

FAIL:
  DIIKS_RENAMES_LINEAR_SOLVE_OR_REIMPORTS_PRIME_OSCILLATION_WALL
```

No Lean, numerics or Aristotle before this discriminator.

## STRONGEST ATTACK

The strongest attack is elementary:

> Every finite Cauchy-like matrix admits a low-displacement description, and its inverse inherits one. The new generators are obtained by applying the inverse itself. Therefore the representation may say nothing cheaper than “solve the matrix”.

The audit earns PASS only if the literal arithmetic `beta` closes the dRHP asymptotically or the exact graph functional collapses to finitely many source-controlled quantities.

The strongest Track B attack is also exact:

> A family of high exponential type can converge on the real axis while being non-normal in the strip. Real-axis logarithmic tracking alone does not pay local boundedness.

Track B remains alive only through a source-specific cancellation theorem for the full `sin * rational` transform or a genuine uniform bound on a non-singular scalar such as center curvature.

## CANDIDATE RE-REPRESENTATIONS

### R1 — diagonal-factored dIIKS / dRHP

```text
kill-power: 10/10
cost: 5/10
```

Selected because it tests whether the newly recognized rank-two structure has a real asymptotic consequence.

### R2 — direct Cauchy-like displacement inverse

```text
kill-power: 9/10
cost: 4/10
```

Avoid the dRHP vocabulary. Derive the exact generator of `C^-1` and test whether the one scalar consumer closes from a finite moment system.

### R3 — Vitali after exact sine-rational cancellation

```text
kill-power: 8/10
cost: 7/10
```

Retain the logarithmic real-axis gain, but seek local boundedness from exact cancellation in the full transform rather than from generic real-zero geometry.

## META CLOSEOUT

```yaml
BECAME_SMALLER:
  - Track A: unknown full-residual estimate -> exact offdiagonal dIIKS plus two named adapters
  - Track B: false full-lattice obstruction -> exterior lattice tail plus unknown finite Lagrange-root moment

KILLED:
  - full CCM matrix is directly a zero-diagonal standard IIKS operator
  - graph C uses the same rank-two generator as M
  - dRHP existence automatically gives asymptotic decay
  - all P59 zeros lie on the full sine lattice
  - M2_k is automatically L_k^2/24

DO_NOT_REPEAT:
  - erase the diagonal because it commutes with D
  - call C^-1 U explicit before solving for it
  - replace off-lattice Lagrange roots by lattice nodes
  - infer strip normality from real-axis convergence alone

SMALLEST_NAMED_GAP:
  SELECTED_FERRERS_GRAPH_DIIKS_ARITHMETIC_ASYMPTOTIC_CLOSURE

NEXT_CHEAPEST_DECISIVE_TEST:
  derive the exact diagonal adapter and [D,C] generator before any asymptotic work

PREDICTION_CLOSEOUT:
  P_LIT_B_1: CONFIRMED_FRAMEWORK_ONLY; claimed zero-density mechanism refuted
  prior center-M2 auto-growth claim: REFUTED_BY_EXACT_ZERO_TAXONOMY

NEW_PREDICTIONS:
  P_IIKS_1:
    probability: 0.95
    prediction: exact offdiagonal dIIKS and finite-rank graph displacement close on paper
  P_IIKS_2:
    probability: 0.72
    prediction: no ready unconditional large-k dRHP asymptotic exists for literal beta data
  P_TRACKB_M2_1:
    probability: 0.60
    prediction: exact center-curvature formula is source-ready, uniform bound remains open

MEMORY_ENTRY:
  invariant: standard discrete IIKS has zero diagonal; diagonal-plus-IIKS and graph projection require explicit adapters
  forbidden_future_move: integrable structure is not asymptotic solvability
```
