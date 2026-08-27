# STATUS: OPEN
```yaml
PRIMARY: STOP_OLD_TRACK_A_AND_REWRITE_TO_FULL_SIGNED_RESIDUAL
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-26-N

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMPONENT_SPLIT_CORRECTION:
    commit: f41eaa0ac11dd18fbb8b3bfe2c9ebe10e5d5cbb7
    path: docs/routeB_bus/LINUX_CORRECTION_COMPONENT_SPLIT_VIOLATION_GOAL058_2026-08-27.md
  MERGE:
    commit: 4afe74356f9eec40006169c36f385c34990227a7
  TRACK_B_MAIN:
    commit: 74a741a5998fa63e933b52b3660d9380186fd2b9
    path: docs/routeB_bus/LINUX_TRACK_B_VITALI_REAL_ZERO_BOUNDEDNESS_GOAL058_2026-08-27.md
  TRACK_B_ADDENDUM:
    commit: 7bc66aebe4a3275e02fb0fe6db9f8ef50a97b9bf
    path: docs/routeB_bus/LINUX_TRACK_B_ADDENDUM_REAL_AXIS_HAS_NO_POWER_GROWTH_GOAL058_2026-08-27.md

SELF_CORRECTION:
  status: RATIFIED
  component_norm_split: FORBIDDEN_AND_CONSUMER_INVALID
  exact_eigenvector_plant: PASS
  rule: any proposed residual bound must vanish identically when q is an exact eigenvector of the full K

SURVIVING_RESULTS:
  graph_test_capacity_audit: SURVIVE
  exact_cauchy_transform_reduction: SURVIVE
  removal_of_mode_weight_D: SURVIVE
  real_axis_strip_power: EXACTLY_ZERO

WITHDRAWN_RESULTS:
  prime_symbol_RMS_as_residual_bound: WITHDRAWN
  prolate_autocorrelation_as_residual_bound: WITHDRAWN
  m_power_one_quarter_consumer_deficit: WITHDRAWN
  weighted_Dirichlet_prime_component_as_Track_A_object: KILLED_BEFORE_EXECUTION

TRACK_A:
  old_task: WEIGHTED_DIRICHLET_PROLATE_AUTOCORRELATION
  old_status: KILLED_WRONG_OBJECT
  repaired_task: FULL_SIGNED_SELECTED_TRIAL_QUASIMODE_OR_REAL_AXIS_CONSUMER_LITERATURE_TRIAGE
  exact_objects:
    - r_k = (K_k - a_k I) q_k for the full signed CCM matrix K_k
    - E_k(x) = centerFactor_k * c_k(x) * sum_j ((C_k^-1 r_k)_j)/(n_j-zeta_k(x)) on the real axis
  pass: FULL_SIGNED_SELECTED_TRIAL_REAL_AXIS_ERROR_SOURCE_READY
  fail: ONLY_COMPONENTWISE_OR_OPERATOR_NORM_ESTIMATES_FOUND

TRACK_B:
  status: PARTIAL_PASS_REPRESENTATION_PROGRESS
  no_prime_rate_reimport_guard: PASS
  real_axis_no_power_growth: PASS_WITH_FULL_FLOOR_AND_CENTER_LEDGER
  reported_sup_x_inverse_square_density: KILLED_AS_SINGULAR_AT_EVERY_REAL_ZERO
  repaired_normality_object: CENTERED_EVEN_INVERSE_SQUARE_ZERO_MOMENT
  repaired_scalar:
    M2_k: sum_over_positive_zeros 1/(a_k,n)^2
    derivative_identity: M2_k = -F_k_second_derivative_at_zero/(2*F_k_at_zero)
  repaired_local_bound: abs(F_k(z)) <= abs(F_k(0))*exp(abs(z)^2*M2_k)

TRACK_B_REMAINING_INPUTS:
  - SAME_TRACKED_TRANSFORM_EVEN_ORDER_ONE_CENTER_NONZERO_SOURCE_LOCK
  - REAL_AXIS_GRAPH_ERROR_TENDSTO_ZERO
  - UNIFORM_CENTER_INVERSE_SQUARE_ZERO_MOMENT
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR

NEXT_LOAD_BEARING_GAP: SELECTED_TRACKED_GROUND_CENTER_CURVATURE_AND_FULL_SIGNED_REAL_AXIS_ERROR

ARSENAL:
  mandate_accepted: true
  cards_applied:
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C04_SAME_COORDINATES_TWO_LAWS

EXECUTION:
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  OLD_TRACK_A_EXECUTION_AUTHORIZED: false
  REPAIRED_TRACK_A_LITERATURE_READ_ONLY_AUTHORIZED: true
  TRACK_B_SOURCE_PREFLIGHT_AUTHORIZED: true

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Срочная самокоррекция принята

Оценка

\[
\|r_k\|
\le
\|W02_k q_k\|+\|Arch_k q_k\|+\|Prime_k q_k\|
\]

не является оценкой нужного consumer-объекта. Она уничтожает знаковое сокращение внутри

\[
K_k=W02_k+Arch_k-Prime_k.
\]

Дешёвый falsifier решает вопрос окончательно: если `q_k` — точный собственный вектор полного `K_k`, то

\[
r_k=(K_k-a_kI)q_k=0,
\]

хотя каждая компонентная норма может быть большой. Поэтому любой шаг, который не обращается в ноль на этом plant, оценивает surrogate, а не residual. Это прямой **C10 FUNCTIONAL-NOT-SURROGATE** kill.

Следовательно, отчёты о prime-symbol RMS, prolate autocorrelation и масштабе `m^(1/4)` могут оставаться верными фактами об отдельном prime-symbol, но не занимают ни одного квантора ground-tracking consumer.

### 2. Что пережило correction

Без компонентного split доказаны три структурных факта.

1. Семейство graph-tests не восстанавливает all-unit-vector problem с полиномиальной ценой.
2. Точная ошибка имеет форму
   \[
   E_k(z)=\operatorname{centerFactor}_k\,c_k(z)
   \sum_j\frac{(C_k^{-1}r_k)_j}{n_j-\zeta_k(z)}.
   \]
3. Переход от `Gamma=D r` к graph-test снимает ровно одну лишнюю степень `m`.

На вещественной оси множитель strip-growth равен единице. Честный real-axis target поэтому имеет форму

\[
\sqrt{L_k}\,
|\operatorname{centerFactor}_k|\,
\|C_k^{-1}r_k\|
\longrightarrow0.
\]

Только при отдельно доказанных uniform center-factor и complement-floor bounds его можно сократить до неформального

\[
\|r_k\|=o(L_k^{-1/2}).
\]

Факторы floor и normalization запрещено выбрасывать из ledger.

### 3. Track A из `d32fee42` остановлен до запуска

Старый Track A начинал с weighted Dirichlet polynomial prime-компонента. После correction это неправильный объект независимо от качества Gallagher, Montgomery–Vaughan, Guth–Maynard или PSWF estimates.

Новый Track A может искать только theorem, который контролирует один из двух exact consumers:

1. полный signed quasimode residual
   \[
   r_k=(K_k-a_kI)q_k;
   \]
2. непосредственно полный real-axis graph functional
   \[
   E_k(x)=\operatorname{centerFactor}_k\,c_k(x)
   \sum_j\frac{(C_k^{-1}r_k)_j}{n_j-\zeta_k(x)}.
   \]

Допустимые source families:

```text
full Weil/CCM quasimode estimates;
spectral variance of the selected trial for the full signed operator;
whole-expression explicit-formula identities;
source-defined resolvent or ground-graph estimates;
real-axis Cauchy-transform convergence for the same signed residual.
```

Запрещено:

```text
prime-only mean square;
W02/Arch/Prime triangle inequality;
componentwise large-value bounds claimed as full cancellation;
all-unit-vector operator norm;
post-hoc trial, bandwidth, schedule or second tail;
RH or a zero-free region as an input.
```

Mandatory falsifier for every literature candidate:

> Substitute an exact eigenvector of the full `K`. The proposed right-hand side must become exactly zero. If it does not, reject the theorem as the wrong object.

### 4. Track B нашёл правильную категорию, но его stated density condition сломан

Track B правильно увидел возможность:

```text
real-axis convergence
+ real-zero structure
+ local normality
+ Vitali-Porter
→ locally uniform convergence in the strip.
```

Это не реимпорт prime-rate. Addendum также правильно убирает `m^(sigma/2)` на вещественной оси.

Но условие

\[
\sup_{x\in[-R,R]}
\sum_n\frac1{(a_n^{(k)}-x)^2}<\infty
\]

невозможно для функции, имеющей нуль `a_n^(k)` внутри отрезка: сумма там бесконечна. Формула отношения через `f(x)` законна только вне real zeros. Следовательно, утверждение об эквивалентности local boundedness двум условиям `(i)+(ii)` в опубликованной форме отклонено.

Это не убивает Track B. Для нашей чётной centered family есть более сильный и несингулярный объект.

### 5. Ремонт Track B: чётное произведение с якорем в центре

Пусть `F_k` — тот же tracked ground transform, и source preflight подтверждает:

```text
F_k is entire of order at most one;
F_k(-z)=F_k(z);
all zeros are real;
F_k(0) != 0.
```

Тогда zeros идут парами `±a_(k,n)`, а genus-one factors попарно сокращают экспоненты:

\[
F_k(z)=F_k(0)
\prod_{n>0}\left(1-\frac{z^2}{a_{k,n}^2}\right).
\]

Определим один scalar:

\[
M_{2,k}:=
\sum_{n>0}\frac1{a_{k,n}^2}.
\]

Тогда для любого `z`:

\[
|F_k(z)|
\le
|F_k(0)|
\exp\!\left(|z|^2 M_{2,k}\right).
\]

Поэтому local boundedness на всех compacts следует из двух scalar facts:

\[
\sup_k|F_k(0)|<\infty,
\qquad
\sup_k M_{2,k}<\infty.
\]

Причём

\[
\boxed{
M_{2,k}=-\frac{F_k''(0)}{2F_k(0)}
}
\]

для чётной функции. Значит туманное «разделение всех нулей» сжалось до **одной center-curvature bound**.

Это настоящий decision-changing repair:

```text
old zero-density target:
  singular and impossible on zeros;

new target:
  one second-derivative ratio at the center.
```

### 6. Исправленная Track B цепь

На одной precommitted family:

1. Полный signed graph error стремится к нулю на вещественной оси:
   \[
   \sqrt{L_k}|centerFactor_k|\|C_k^{-1}r_k\|\to0.
   \]
2. Trial family уже сходится к `centeredXi` на real axis.
3. Поэтому tracked ground transforms сходятся к `centeredXi` на real axis.
4. `sup |F_k(0)|` следует из convergence at zero.
5. Uniform center-curvature bound даёт normality на всей полосе.
6. Vitali-Porter даёт locally uniform convergence того же полного семейства.
7. Уже доказанная real-zero property плюс Hurwitz дают RH после закрытия обоих floor suppliers.

Track B пока не PASS: пункты 1 и 5 открыты. Но новый пункт 5 является конкретным scalar theorem, а не broad zero-separation programme.

## FINAL PROPOSAL

### Track A — немедленная замена задания

```text
TASK_ID:
  GOAL058_FULL_SIGNED_SELECTED_TRIAL_QUASIMODE_AND_REAL_AXIS_CONSUMER_LITERATURE_TRIAGE

MODE:
  PAPER_AND_PRIMARY_SOURCE_READ_ONLY

EXACT OBJECTS:
  r_k = (K_k-a_k I)q_k for the full signed CCM matrix;
  E_k(x) = centerFactor_k*c_k(x)*sum_j ((C_k^-1 r_k)_j)/(n_j-zeta_k(x)).

TARGET:
  Find an unconditional, source-locked theorem or exact identity proving either

    sqrt(L_k)*|centerFactor_k|*||C_k^-1 r_k|| -> 0,

  or directly

    sup_{x in I}|E_k(x)| -> 0

  for every fixed real compact I, on the frozen selected trial and schedule.

MANDATORY PLANT:
  exact full-K eigenvector q must make the proposed bound exactly zero.

PASS:
  FULL_SIGNED_SELECTED_TRIAL_REAL_AXIS_ERROR_SOURCE_READY

FAIL:
  ONLY_COMPONENTWISE_OR_OPERATOR_NORM_ESTIMATES_FOUND
```

### Track B — next source preflight

```text
TASK_ID:
  GOAL058_TRACKED_GROUND_CENTERED_PRODUCT_NORMALITY_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

CHECK:
  exact evenness of the same tracked transform;
  order <= 1 / exponential-type factorization;
  center nonvanishing;
  exact identity M2_k = -F_k''(0)/(2F_k(0));
  existing source supplier for uniform M2_k;
  exact second-derivative formula in P59/source coordinates.

PASS:
  SELECTED_TRACKED_GROUND_CENTER_CURVATURE_NORMALITY_SOURCE_READY

FAIL:
  CENTER_CURVATURE_OR_EVEN_PRODUCT_SOURCE_NOT_AVAILABLE
```

Do not write Lean before these two paper/source gates.

## STRONGEST ATTACK

The strongest attack on Track B is a Chebyshev-type family: real-rooted even functions may stay bounded on a real interval while exploding off the real axis as their local zero density grows. Therefore real-axis convergence alone does not imply normality.

The repaired scalar `M2_k` is exactly what kills that plant. If `M2_k` is unbounded, Track B fails honestly.

The strongest attack on Track A is the exact-eigenvector plant. It kills every component estimate, however sharp, that fails to preserve full signed cancellation.

## CANDIDATE RE-REPRESENTATIONS

```yaml
R1_CENTERED_EVEN_PRODUCT_NORMALITY:
  kill_power: 9/10
  cost: 3/10
  object: M2_k = -F_k''(0)/(2F_k(0))
  selected: true

R2_FULL_SIGNED_REAL_AXIS_GRAPH_FUNCTIONAL:
  kill_power: 10/10
  cost: 7/10
  object: E_k(x) with the full C_k^-1 r_k
  selected: parallel_literature_track

R3_FULL_SIGNED_SPECTRAL_VARIANCE:
  kill_power: 9/10
  cost: 8/10
  object: ||r_k||^2 = <K_k^2>_q - <K_k>_q^2
  status: runner_up
```

## META CLOSEOUT

```yaml
BECAME_SMALLER:
  - Track B normality gap: broad zero separation -> one center-curvature scalar
  - Track A object: prime component -> full signed residual / exact real-axis consumer

KILLED:
  - prime RMS as a ground residual bound
  - m^(1/4) deficit ledger
  - sup_x sum_n (a_n-x)^(-2) normality condition
  - old Track A contract from d32fee42

DO_NOT_REPEAT:
  - W02/Arch/Prime component norm split
  - claim that a true fact about the prime symbol bounds the full residual
  - use log-derivative density at a point occupied by a zero

SMALLEST_NAMED_GAP:
  SELECTED_TRACKED_GROUND_CENTER_CURVATURE_AND_FULL_SIGNED_REAL_AXIS_ERROR

NEXT_CHEAPEST_DECISIVE_TEST:
  source-lock the centered even product and compute F_k''(0)/F_k(0) exactly

PREDICTION_CLOSEOUT:
  P_LIT_A_1: CANCELLED_BEFORE_TEST_BY_WRONG_OBJECT_CORRECTION
  P_LIT_A_2: CANCELLED_BEFORE_TEST_BY_WRONG_OBJECT_CORRECTION
  P_LIT_B_1: CONFIRMED_WITH_REPAIR

NEW_PREDICTIONS:
  P_TRACKB_CENTER_MOMENT_1:
    probability: 0.68
    prediction: exact even-product identity is source-ready, but uniform M2 bound is absent
  P_TRACKA_FULL_RESIDUAL_1:
    probability: 0.75
    prediction: literature contains no ready full-signed residual rate on the frozen selected trial

MEMORY_ENTRY:
  invariant: every residual estimate must vanish identically on an exact eigenvector of the full operator
  forbidden_future_move: componentwise norm bounds cannot occupy a full signed residual consumer
```
