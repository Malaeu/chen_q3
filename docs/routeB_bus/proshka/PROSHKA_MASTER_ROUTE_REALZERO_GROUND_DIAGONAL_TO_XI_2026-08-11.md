# STATUS: OPEN — КАНОНИЧЕСКИЙ МАРШРУТ ЗАФИКСИРОВАН; ГЛАВНАЯ СТЕНА — SAME-FAMILY GROUND-TO-TRIAL TRACKING
```yaml
PRIMARY: REALZERO_FINITE_GROUND_DIAGONAL_TO_XI
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: b124fba1fcf33cd105a078254caa9d62240d59e6
  HEAD_VERIFIED: true

FINAL_CONSUMER:
  name: RouteB_ZeroEscape_Closure
  shape:
    - one cofinal normalized entire family
    - every approximant has only real zeros
    - locally uniform convergence to centered Xi
    - Hurwitz/Rouche
    - RH

SELECTED_FAMILY:
  name: finite_CCM_ground_transform_family
  coefficient_row: actual_simple_even_bottom_eigenvector
  transform: Proposition59_raw_transform_with_exact_sign_scale
  status: NOT_YET_MATERIALIZED_AS_CANONICAL_ROUTE_OBJECT

CURRENT_D0_FAMILY:
  name: centeredPstarFamily_from_kTrial
  coefficient_row: projected_prolate_trial
  status: SOURCE_LOCKED_TRIAL_FAMILY
  exact_ground_identification: OPEN
  may_inherit_ground_real_zeros_without_bridge: false

GATES:
  G0:
    name: EXACT_OBJECT_COORDINATE_NORMALIZATION_LOCK
    status: OPEN_PARTIAL
  G1:
    name: COFINAL_FINITE_SIMPLE_EVEN_GROUND_PACKAGE
    status: OPEN_MAIN_SPECTRAL_FRONT
  G2:
    name: PROPOSITION59_GROUND_LAGRANGE_ZEROSET_BRIDGE
    status: OPEN_CHEAP_LOCAL_FRONT
  G3:
    name: FINITE_GROUND_TRANSFORM_TO_CCM_TRIAL_LOCALLY_UNIFORM
    status: OPEN_MAIN_APPROXIMATION_WALL
  G4:
    name: CCM_LEMMA73_PROJECT_OBJECT_NORMALIZATION_CROSSWALK
    status: PAPER_PROVED_PROJECT_IMPORT_OPEN
  G5:
    name: ZERO_ESCAPE_TO_RH
    status: LOGICAL_CORE_PROVED_ANALYTIC_TRANSFER_AVAILABLE_IN_ROOF

MAIN_WALL:
  name: FINITE_GROUND_TRANSFORM_TO_CCM_TRIAL_LOCALLY_UNIFORM
  exact_shape:
    - residual_or_graph_distance_of_ground_to_projected_trial
    - true_gap_lower_bound
    - transform_evaluation_growth
    - finite_projection_tail
    - common_normalization
    - coverage_compatible_cofinal_schedule

H2A_SUPPLIER_ROUTES:
  - PENALTY_CERTIFICATE
  - PARITY_BLOCK_PLUS_KERNEL_CONTROL
  - GLOWER_YOSHIDA_FESHBACH_ODD_COERCIVITY
  - DIRECT_SCHUR_FESHBACH_GROUND_GRAPH
  - RANK_INERTIA_CERTIFICATE
  - VERIFIED_EXTERNAL_SIMPLE_EVEN_IMPORT

TRACKING_SUPPLIER_ROUTES:
  - RESIDUAL_OVER_TRUE_GAP
  - FESHBACH_GRAPH_TRANSFORM_BOUND
  - PENALTY_OVERLAP_BOUND
  - G04_DEFECT_GRAM_PLUS_COMMUTATOR
  - NORM_RESOLVENT_GALERKIN_CONVERGENCE
  - DIRECT_EXACT_GROUND_EQUALS_TRIAL_ONLY_AS_FALSIFIER

FALLBACK_GLOBAL_ROUTES:
  - PSD_PD_GLOBAL_WEIL_POSITIVITY
  - ORIGINAL_MONTEL_S2_CLUSTER_ROUTE
  - G04_NEAR_RADICAL_HUMP_ROUTE_AS_SUPPLIER
  - SOURCE_SPECIFIC_MUNTZ_TAIL_GAUGE_ROUTE

KILLED_SHORTCUTS:
  - CURRENT_TRIAL_PSTAR_SILENTLY_EQUALS_GROUND_FAMILY
  - SCALAR_ONLY_PSTAR_EQUALS_CN_TIMES_LAGRANGE
  - FIXED_MUNTZ_WINDOW_REPLACES_CANONICAL_SOURCE_FAMILY
  - SMALL_RAYLEIGH_VALUE_IMPLIES_SMALL_RESIDUAL
  - ARBITRARY_COFINAL_PATH_SUFFICES
  - FINITE_CERTIFICATES_IMPLY_GLOBAL_THEOREM
  - EXACT_OR_APPLY_SEARCH_IS_A_COMPARATOR

SCHEDULE_GUARD:
  required: N_j / log(m_j) -> infinity
  reason: exterior_Proposition59_lattice_zeros_must_leave_every_fixed_compact

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

NEXT_LOCAL_TARGET:
  PROPOSITION59_GROUND_LAGRANGE_ZEROSET_BRIDGE

EXECUTION:
  AUTHORIZED_BY_THIS_VERDICT: false
  REPO_WRITE: false
  ROUTE_PROMOTION: false
  RH_CLAIM: false

ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

# 1. Маршрут в одной строке

Нужно построить **одну и ту же** последовательность целых функций \(F_j\), для которой одновременно доказаны:

\[
Z(F_j)\subset\mathbb R
\]

и

\[
F_j\longrightarrow\Xi
\]

локально равномерно в открытой центрированной критической полосе.

Тогда Гурвиц–Руше запрещает у \(\Xi\) невещественные нули. Это даёт RH.

\[
\boxed{
\text{finite simple-even ground}
\to
\text{real-zero finite transform}
\to
\text{same-family tracking to CCM trial}
\to
\text{CCM trial}\to\Xi
\to
\text{ZeroEscape}
\to
RH
}
\]

Логическая часть `ZeroEscape` уже формализована: если нули предела аппроксимируются вещественными нулями аппроксимантов, предел имеет только вещественные нули. fileciteturn41file0L2-L6 `[ABSTRACT][LEAN]`

# 2. Несущий инвариант: нельзя использовать две разные семьи

Это главный итог всех последних проверок.

Текущая production-family `centeredPstarFamily` строится из `kTrial`. А `kTrial` является коэффициентной строкой **projected prolate trial**. Source module специально сообщает, что он не доказывает ground-state identification и не доказывает convergence theorem. fileciteturn15file0L2-L6 `[COFINAL_FAMILY][LEAN]`

Finite real-zero theorem работает с другой строкой:

```lean
xi
heig
hbottom
hsimple
hnormalized
```

то есть с actual bottom eigenvector конечной CCM-матрицы. fileciteturn39file0L2-L6 `[FINITE_CELL][LEAN]`

Поэтому запрещена цепь:

```text
trial transform converges to Xi;
ground transform has real zeros;
therefore RH.
```

Она использует две разные последовательности.

Разрешена только цепь:

```text
one normalized ground-transform sequence has real zeros;
that same ground-transform sequence converges to Xi.
```

Это точное применение **[C04]** и **[C10]**: одинаковый интерфейс целых функций не стирает provenance коэффициентов.

# 3. Выбранная функция

Для выбранной пары

\[
(m_j,N_j)
\]

берём actual finite bottom eigenvector

\[
\xi_j:
\operatorname{CCMModeFinite}(N_j)\to\mathbb R.
\]

Определяем ground transform:

\[
F_j(z)
=
\nu_j\,
\operatorname{proposition59RawTransform}
\left(
L_j,\,
[-N_j,N_j],\,
\xi_j^{\mathbb C},\,
-z
\right),
\qquad
L_j=\log m_j.
\]

Здесь:

- \(\xi_j^{\mathbb C}\) — точная complexification конечной вещественной строки;
- `-z` — production orientation текущего D0;
- \(\nu_j\neq0\) — source-defined normalization;
- carrier map должен буквально связывать `CCMModeFinite N` с integer modes \(-N,\ldots,N\).

Current D0 `rawFplus` использует тот же Proposition-5.9 transform и тот же аргумент `-z`, но с trial coefficients. fileciteturn7file0L2-L6 `[COFINAL_FAMILY][LEAN]`

Новая ground-family не должна молча переопределять текущий D0 `Pstar`. Сначала это отдельный source-faithful route object.

# 4. Полная карта

```text
G0  Exact object / coordinate / normalization lock
 │
 ▼
G1  Cofinal finite simple-even bottom ground package
 │
 ▼
G2  Ground Lagrange real zeros
 │
 ▼
G2b Proposition-5.9 lattice zero-set transfer
 │
 ▼
F_j is entire and all zeros of F_j are real
 │
 ▼
G3  The same F_j tracks projected prolate trial
 │
 ▼
G3c projected trial tracks continuum CCM trial
 │
 ▼
G4  CCM Lemma 7.3: continuum trial transform → Xi
 │
 ▼
F_j → Xi locally uniformly
 │
 ▼
G5  ZeroEscape / Hurwitz / centered Xi interface
 │
 ▼
RH
```

# 5. G0 — exact object, coordinate and normalization lock

## 5.1 Exact coordinates

Надо зафиксировать:

\[
\lambda_j=\sqrt{m_j},
\qquad
L_j=\log m_j=2\log\lambda_j.
\]

Finite Lagrange polynomial использует integer nodes:

\[
k=-N,\ldots,N.
\]

Proposition 5.9 использует poles:

\[
a_k=\frac{2\pi k}{L}.
\]

Поскольку D0 подставляет \(-z\), правильная polynomial coordinate имеет вид:

\[
\boxed{
s=-\frac{Lz}{2\pi}.
}
\]

`sourceLagrangePolynomial` действительно является конечным многочленом на source nodes. fileciteturn20file0L2-L6 Proposition-5.9 transform действительно имеет общий sine numerator и poles \(2\pi k/L\). fileciteturn12file0L2-L6 `[ABSTRACT][LEAN]`

Любая потеря:

```text
-z;
2*pi/L;
integer carrier;
finite removable pole case
```

является semantic failure.

## 5.2 Cofinal schedule

Недостаточно потребовать только:

\[
m_j\to\infty,
\qquad
N_j\to\infty.
\]

У finite Proposition-5.9 transform есть exterior lattice zeros:

\[
-\frac{2\pi q}{L_j},
\qquad
|q|>N_j.
\]

Чтобы они покинули каждый фиксированный compact, необходимо:

\[
\boxed{
\frac{N_j}{L_j}
=
\frac{N_j}{\log m_j}
\longrightarrow\infty.
}
\]

Это вывод из source definitions, а не отдельный уже формализованный theorem. Если взять \(N_j\sim j\), а \(\log m_j\sim j^2\), exterior zeros подходят к нулю. При ненулевой anchor normalization локально равномерная сходимость к \(\Xi\) невозможна. `[COFINAL_FAMILY][PAPER]`

Поэтому schedule должен быть **precommitted** до численных испытаний. Это **[C09]**.

## 5.3 Normalization

Ground theorem использует:

\[
\eta\mathbin{\boldsymbol\cdot}\xi=1.
\]

Но это не гарантирует, что ground transform ненулевой в нуле. Для Proposition-5.9 transform значение в нуле особенно чувствительно к central coefficient.

Поэтому route normalization должна быть связана с tracking theorem. Лучший кандидат:

\[
\langle \xi_{m,N},q_{m,N}\rangle>0,
\]

где \(q_{m,N}\) — source projected trial.

Фиксируем фазу или знак так:

\[
\langle \xi_{m,N},q_{m,N}\rangle>0.
\]

Затем нормируем transform в той же convention, что и CCM trial-to-\(\Xi\).

Альтернатива — anchor \(z_\star\), но тогда надо отдельно доказать:

\[
F_j(z_\star)\neq0,
\qquad
T_j(z_\star)\neq0,
\]

и контролировать anchor quotient.

# 6. G1 — cofinal finite simple-even ground package

Для каждого выбранного \((m_j,N_j)\) требуется exact package:

```lean
epsilon_j
xi_j
heig
hbottom
hsimple
hnormalized
```

Consumer уже записан. Он не требует от нас изобретать перевод. `hbottom` имеет точную матричную форму:

\[
\epsilon (x\boldsymbol\cdot x)
\le
x\boldsymbol\cdot Kx.
\]

`heig` — exact `mulVec` equation. `hsimple` — `finrank eigenspace = 1`. fileciteturn39file0L2-L6 `[FINITE_CELL][LEAN]`

Evenness не надо поставлять отдельно. Существующий wrapper выводит её из eigenvector, simplicity и eta-normalization. fileciteturn10file0L2-L6 `[FINITE_CELL][LEAN]`

## 6.1 Основной supplier A — penalty certificate

Generic theorem уже доказан:

\[
K-\beta G+\tau(Gq)(Gq)^*\succeq0,
\qquad
q^*Gq=1,
\qquad
a=q^*Kq<\beta.
\]

Он выдаёт:

- lowest eigenvalue;
- глобальную минимальность;
- simplicity;
- gap не меньше \(\beta-a\);
- evenness ground state.

fileciteturn37file0L2-L6 `[ABSTRACT][LEAN]`

Для CCM обычно \(G=I\). Открытая работа:

1. source-lock `K`, `J`, `q`;
2. получить exact or interval certificate;
3. не выбирать \(q\) после просмотра spectrum;
4. доказать certificate по одной cofinal schedule, а не только на одной клетке;
5. построить family adapter.

**Плюс:** одновременно даёт simplicity, parity и finite gap.

**Минус:** sufficient certificate может не существовать, даже если ground state simple.

## 6.2 Supplier B — parity block decomposition

Уже доказана эквивалентность:

\[
hsimple
\Longleftrightarrow
\left(
S_{\rm odd}\succ0
\right)
\land
\left(
\dim(\ker S\cap{\rm even})=1
\right)
\]

для shifted PSD matrix. Это режет задачу на два блока половинной размерности. fileciteturn33file0L2-L2 `[FINITE_CELL][LEAN]`

Последний commit добавил:

```lean
eta_dot_eq_zero_of_odd
odd_posDef_of_ker_even
```

и показал:

\[
\ker S\subset{\rm even}
\Longrightarrow
S_{\rm odd}\succ0.
\]

fileciteturn31file0L3-L7 `[FINITE_CELL][LEAN]`

Но это пока **representation shift**, а не решение. При \(S\succeq0\):

\[
\ker S\subset{\rm even}
\]

по существу означает отсутствие odd kernel. Это почти та же содержательная задача, что \(S_{\rm odd}\succ0\).

Польза route:

- можно атаковать odd и even sectors разными механизмами;
- parity structure уже source-proved;
- нормализованный ground vector не может быть odd;
- Schur/Feshbach становится естественнее.

## 6.3 Supplier C — GLOWER / Yoshida / residual Feshbach

Odd sector можно закрывать через continuum coercivity:

\[
Q_{13}^{\rm odd}(f)\ge c_0\|f\|^2.
\]

Тогда после exact compression theorem получаем finite odd positivity.

Предложенная конструкция:

```text
continuum high-mode coercivity
+ finite corrected head
+ residual Feshbach certificate
→ full odd floor.
```

Три theorem locks:

```text
OddSourceWeilCompression13
YoshidaTailCoercivity13Explicit
OddResidualFeshbachLower13
```

Именно эта route avoids extrapolating finite eigenvalues to infinity. Но latest source audit подчёркивает: GLOWER artifact запрещено потреблять, пока не доказано, что finite matrix является exact compression ambient odd operator. fileciteturn31file0L3-L7 `[COFINAL_FAMILY][CONDITIONAL]`

## 6.4 Supplier D — direct Schur/Feshbach graph

Разложить:

\[
\mathcal H
=
\mathbb Cq\oplus q^\perp
\]

или parity-head/tail:

\[
K=
\begin{pmatrix}
A&E^*\\
E&D
\end{pmatrix}.
\]

Доказать:

\[
D-\beta I\succeq dI
\]

и corrected head:

\[
A_c-d^{-1}E^*E>0.
\]

Это может сразу дать:

- existence simple lowest eigenvalue;
- gap;
- quantitative ground-to-trial overlap.

Это лучший общий язык, если penalty certificate слишком жёсткий.

## 6.5 Supplier E — rank/inertia certificate

Уже доказан перевод:

\[
hsimple
\Longleftrightarrow
\operatorname{rank}(K-\epsilon I)=2N.
\]

fileciteturn33file0L2-L2 `[FINITE_CELL][LEAN]`

Это полезно для:

- exact finite-cell certification;
- interval rank/nullity-one checks;
- debugging;
- alternative determinant minors.

Но конечное число клеток не занимает cofinal quantifier.

## 6.6 Supplier F — external simple-even theorem

Внешний prolate simple-even theorem может помочь только после точного statement/source audit.

Он не может автоматически supply simple-even for the CCM Weil operator. Prolate operator и \(QW_\lambda\) — разные objects.

Status:

```text
UNVERIFIED_IMPORT
```

до exact theorem and crosswalk.

# 7. G2 — finite real zeros for exact ground transform

## 7.1 Что уже готово

Из exact ground package проект уже доказывает real zeros complexified source Lagrange polynomial:

\[
P_{m,N,\xi}(s)
=
\sum_k\xi_k
\prod_{j\ne k}(j-s).
\]

Theorem использует exact shifted PSD form, one-dimensional kernel, commutator identity и normalization. fileciteturn8file0L2-L6 `[FINITE_CELL][LEAN]`

Более конкретный consumer `ccmSourceLagrangePolynomial...of_bottomRayleigh_simple` уже связывает это с CCM matrix. fileciteturn39file0L2-L6 `[FINITE_CELL][LEAN]`

Quotient basis можно строить автоматически. Поэтому он не является содержательной стеной.

## 7.2 Недостающий theorem

\[
\boxed{
\texttt{Proposition59GroundLagrangeZeroSetBridge}
}
\]

Нужно доказать:

> Если source Lagrange polynomial строки \(\xi\) имеет только вещественные нули, то exact Proposition-5.9 transform с той же строкой также имеет только вещественные нули.

### Proof route

Для zero \(z\) ground transform:

1. Если \(z\) является included removable pole, то \(z\) вещественный.
2. Вне finite poles раскрыть:
   \[
   rawFplus(z)
   =
   \text{scale}\cdot
   \sin(Lz/2)
   \sum_k\frac{\xi_k}{z+2\pi k/L}.
   \]
3. Если sine factor равен нулю, \(z\) лежит на real lattice.
4. Иначе Cauchy sum равна нулю.
5. Умножить на finite denominator.
6. Получить:
   \[
   P\!\left(-\frac{Lz}{2\pi}\right)=0.
   \]
7. Real-rootedness \(P\) даёт \(\Im z=0\).

Это перенос **zero set**, а не ложное equality:

\[
Pstar=c_NP.
\]

## 7.3 Почему scalar-only equality убита

Full Proposition-5.9 transform имеет бесконечно много exterior sine-lattice zeros.

Ненулевой finite polynomial имеет конечное число zeros.

Поэтому один scalar \(c_N\) не может сделать их равными.

Правильная структура:

\[
Z(F_{m,N})
=
Z(P_{m,N})
\cup
Z(\Lambda_{m,N}),
\]

где \(\Lambda_{m,N}\) — real lattice/complement factor.

## 7.4 Альтернативный H2b route

Можно пройти через weighted self-adjoint quotient and characteristic polynomial:

```text
M1 positive metric → Hermitian similar matrix
M2 quotient by radical
M3 determinant/Lagrange identification
```

M1 generic bridge почти закрыт, но M2/M3 остаются.

Короткий radical/Lagrange consumer уже существует. Поэтому M1–M3 сейчас runner-up.

# 8. G3 — главная стена: same-family tracking

Точный target:

\[
\boxed{
\texttt{FiniteGroundTransformToCCMTrialLocallyUniform}
}
\]

Пусть:

- \(F_{m,N}^{\rm ground}\) — Proposition-5.9 transform actual finite ground vector;
- \(T_{m,N}^{\rm trial}\) — transform projected prolate trial;
- \(T_m^{\rm CCM}\) — continuum CCM trial transform.

Для каждого compact \(K\Subset S\) требуется:

\[
\sup_{z\in K}
|F_{m_j,N_j}^{\rm ground}(z)-T_{m_j}^{\rm CCM}(z)|
\to0.
\]

Разбиваем:

\[
\begin{aligned}
\|F^{\rm ground}-T^{\rm CCM}\|_K
\le&
\|F^{\rm ground}-T^{\rm projected\ trial}\|_K\\
&+
\|T^{\rm projected\ trial}-T^{\rm CCM}\|_K.
\end{aligned}
\]

Первая строка — ground-to-trial.

Вторая — finite projection tail.

## 8.1 Main solution A — residual divided by true gap

Пусть \(q_{m,N}\) — normalized projected trial.

Определить:

\[
a_{m,N}=\langle Kq,q\rangle,
\]

\[
r_{m,N}=(K-a_{m,N}I)q,
\]

\[
\Delta_{m,N}
=
\text{distance from the selected ground eigenvalue to the rest}.
\]

Тогда Davis–Kahan/residual theorem даёт:

\[
d_{\rm proj}(\xi,q)
\le
\frac{\|r\|}{\Delta}.
\]

Но для transform convergence нужен consumer-shaped bound:

\[
\sup_{z\in K}
|F_\xi(z)-F_q(z)|
\le
C_K(m,N)\,
\frac{\|r_{m,N}\|}{\Delta_{m,N}}.
\]

Полный detector:

\[
W_j(K)
=
C_K(m_j,N_j)\,
\frac{\|r_j\|}{\Delta_j}
+
\operatorname{Tail}_j(K)
+
\operatorname{NormalizationError}_j(K).
\]

Нужно:

\[
W_j(K)\to0
\qquad
\forall K\Subset S.
\]

Главный риск: \(C_K(m,N)\) может расти быстрее, чем residual/gap уменьшается.

## 8.2 Solution B — direct Feshbach graph theorem

Вместо общего residual theorem доказать ground state как graph over trial line:

\[
\xi
=
\alpha q+y,
\qquad
y\perp q.
\]

Если complement floor and coupling known:

\[
D-\beta I\succeq dI,
\qquad
\|E\|\ll d,
\]

то:

\[
\|y\|
\lesssim
\frac{\|E\|}{d}.
\]

Преимущество:

- ground selection;
- simplicity;
- gap;
- tracking

получаются одним block theorem.

Это сильный candidate, если penalty certificate nearly passes.

## 8.3 Solution C — penalty overlap theorem

Penalty certificate уже даёт floor на \(q^\perp\).

Дополнительный theorem может оценить overlap ground state with \(q\) через:

- Rayleigh excess;
- residual;
- penalty floor;
- rank-one Schur complement.

То есть penalty route можно расширить:

```text
certificate
→ simple even ground
→ quantitative overlap with q
→ transform tracking.
```

## 8.4 Solution D — G04 defect-Gram / prolate leakage

PSWF theory даёт exponential prolate leakage.

Можно построить small normalized defect matrix \(B_\lambda\) и доказать:

\[
\|B_\lambda\|_{\rm op}\le C\lambda^A.
\]

Это даёт малый Weil trial value.

Но есть обязательная граница:

\[
\langle Kq,q\rangle\text{ small}
\not\Rightarrow
\|(K-a)q\|\text{ small}.
\]

Поэтому `NearRadicalTrialRayleighBound` alone не закрывает G3.

Чтобы route стал supplier G3, нужен ещё exact defect equation or commutator theorem producing residual.

Возможная цепь:

```text
ProjectedProlateDefectEquation
→ low-mode commutator cancellation
→ high-mode gap growth
→ resolvent-smoothed residual
→ ground tracking.
```

## 8.5 Solution E — low/high prolate spectral split

Разложить source defect по prolate eigenmodes.

Для low modes доказать cancellation:

\[
|\langle\Gamma_\lambda,E_{\lambda,j}\rangle|
\text{ small}.
\]

Для high modes использовать prolate spectral gap growth.

Тогда:

\[
\left\|
(D_\lambda-\theta_\lambda)^{-1}_{K_\lambda^\perp}
\Gamma_\lambda
\right\|
\]

мал.

Это source-specific version residual route.

## 8.6 Solution F — norm-resolvent Galerkin convergence

Если доказать:

\[
K_{\lambda,N}\to K_\lambda
\]

в norm-resolvent sense, continuum ground simple/isolate, and projected trial tracks continuum ground, then finite ground vectors converge.

Плюс: стандартная spectral perturbation architecture.

Минус: требует continuum simple-even and true gap. Это может быть не дешевле прямого route.

## 8.7 Killed solution — exact ground equals trial

Current source contract не утверждает:

\[
q_{m,N}=\xi_{m,N}.
\]

Это можно проверить как finite-cell falsifier.

Нельзя строить main route на этом equality без нового theorem.

# 9. Откуда взять true gap

Tracking требует не диагностический sectional gap, а gap exact selected operator.

Варианты:

| Route | Что доказывает | Главный риск |
|---|---|---|
| Penalty certificate | \(\Delta\ge\beta-a\) | certificate слишком сильный |
| Parity floors | odd floor + even complement floor | even complement остаётся |
| Schur/Feshbach | gap from block floors and coupling | exact tail/compression |
| GLOWER/Yoshida | continuum odd coercivity | source-to-finite bridge |
| Interval finite spectrum | exact finite gap | не занимает cofinal quantifier |
| Norm-resolvent transfer | continuum gap from limits | may hide same wall |

Gap theorem запрещено доказывать с помощью:

```text
global Weil positivity;
RH;
absence of off-line zeros;
desired F_j → Xi convergence;
W_j → 0.
```

Иначе argument circular.

# 10. G4 — CCM trial-to-\(\Xi\)

CCM Lemma 7.3 уже доказывает:

\[
\widehat{k_\lambda}\to\Xi
\]

равномерно на замкнутых подполосах открытой критической полосы.

Project ledger правильно классифицирует:

```text
trial-to-Xi:
  PAPER_PROVED.

project Lean import:
  OPEN.
```

fileciteturn24file0L2-L2 `[COFINAL_FAMILY][PAPER]`

Нужно закрыть:

```text
paper h_lambda
↔ project hTrial_m;
scalar and phase;
C = 2*pi*lambda^2;
zero extension;
E_star convention;
midpoint/star convention;
transform coordinate.
```

Paper and project objects уже лежат на одной one-dimensional zero-mass source line, но exact normalized equality пока не доказана. fileciteturn24file0L2-L2 `[ABSTRACT][PAPER]`

## 10.1 Muntz route как формализационный supplier

Muntz v3 shell полезен для exact analytic continuation and tail decomposition.

Уже доказан `hRp` on exact v3 class.

Но:

```text
tail analyticity
≠
tail smallness.
```

И fixed PL2 window не может заменить source-locked prolate family.

Muntz route может:

- supply H1;
- formalize exact source tail identities;
- help project-port Lemma 7.3.

Он не обходит ground-to-trial wall.

# 11. G5 — финальная сборка

После G2–G4 имеется одна cofinal sequence:

\[
F_j
\]

такая, что:

1. \(F_j\) entire;
2. zeros \(F_j\) real;
3. \(F_j\to\Xi\) locally uniformly.

Тогда analytic zero-transfer gives:

\[
Z(\Xi)\subset\mathbb R
\]

в centered coordinate.

Classical centered-Xi interface даёт RH.

Generic canonical roof already formalizes the same logical pattern through real-zero selected family, locally uniform cluster and exact Xi identification. fileciteturn11file0L2-L6 `[ABSTRACT][LEAN]`

Direct convergence route делает generic Montel/S2 необязательным.

# 12. Если direct tracking не проходит

## 12.1 Fallback A — original Montel/S2 roof

Слоты:

```text
H1:
  holomorphy.

H2a:
  simple even ground.

H2b:
  real zeros.

ANCHOR:
  nonzero normalization.

S1:
  local boundedness of post-anchor family.

S2:
  every nonzero cluster equals c*Xi*gamma.
```

Это не удаляет same-family requirement.

Он полезен, если можно доказать compactness and cluster identification, но невозможно получить explicit convergence rate.

## 12.2 Fallback B — PSD-pd global Weil positivity

Независимый route:

```text
Hermitian square
→ Arch - Prime analytic form
→ exact B-spline matrix identification
→ finite PSD certificates
→ DirectedFamily/exhaustion
→ global boundary-null Weil positivity
→ Weil criterion
→ RH.
```

Главные walls:

```text
matrix identification;
correct positive-definite test cone;
prime Carleson/sampling bound;
finite-to-global continuity;
boundary leakage.
```

Продуманные решения:

```text
Gram-corrected matrix representation;
penalty/Schur certificates;
Cohn-Elkies-style dual certificate;
higher-order prime correlation lift;
boundary-null correction;
escaping-packet falsifier;
DirectedFamily + topology + continuity.
```

Этот route обходит ground-to-trial tracking, но заменяет его global positivity wall.

## 12.3 Fallback C — G04/HUMP route

Цель:

\[
|QW_\lambda(E(h_\lambda))|
\le
\operatorname{poly}(\lambda)
\left[
(1-\chi_0)+(1-\chi_2)
\right].
\]

После exact Guinand–Weil dictionary это может дать HUMP bound.

Но малый quadratic value не является ground residual.

Поэтому G04 route:

- либо поставляет отдельный RH detector;
- либо должен быть усилен до residual/commutator theorem;
- либо остаётся сильным companion result.

## 12.4 Fallback D — source-specific Muntz cluster route

Можно доказать direct locally uniform identification source trial with Xi через exact Muntz tails and gauge.

Но finite real-zero family всё равно должна совпадать с этой family.

Fixed-window substitution убита.

# 13. Что мы больше не делаем

```text
Не переносим real zeros с ground family на trial family по близости.

Не пишем Pstar = c_N * Lagrange polynomial.

Не выбираем произвольную fixed Muntz function как canonical Pstar.

Не считаем малый Rayleigh quotient малым residual.

Не используем finite cells вместо cofinal theorem.

Не выбираем N(m) после просмотра данных.

Не считаем η-normalization central transform normalization.

Не называем exact?/apply? comparator.

Не импортируем GLOWER floor без exact compression theorem.

Не считаем tail analyticity tail convergence.
```

# 14. Порядок работы

## Phase A — закрыть finite algebraic H2b shell

1. `Proposition59GroundLagrangeZeroSetBridge`.
2. Ground transform definition with exact carrier/sign/scale.
3. Real-zero wrapper from existing CCM consumer.

Это дешёвая, независимая и reusable работа.

## Phase B — атаковать finite H2a

Параллельный ranking:

1. penalty certificate on exact CCM data;
2. parity split and odd/even block suppliers;
3. Schur/Feshbach formulation;
4. GLOWER/Yoshida compression route;
5. rank/inertia checks as finite controls.

Надо выбрать один cofinal theorem, а не коллекцию клеток.

## Phase C — сделать tracking theorem

Начать с exact finite formula:

\[
\sup_K|F_\xi-F_q|
\le
C_K\|\,\xi-cq\,\|.
\]

Затем supply projective distance:

\[
\|\,\xi-cq\,\|
\le
\frac{\|r\|}{\Delta}.
\]

Отдельно доказать projection tail.

## Phase D — импортировать CCM Lemma 7.3

Это object/normalization/topology task, а не новая convergence mathematics.

## Phase E — one theorem assembly

```text
ground real zeros
+ ground-to-trial tracking
+ trial-to-Xi
→ locally uniform real-zero approximants to Xi
→ RH.
```

# 15. Зарегистрированные прогнозы

```yaml
P-MR1:
  prediction: Proposition59GroundLagrangeZeroSetBridge is true and local
  confidence: 0.95

P-MR2:
  prediction: current production kTrial is not definitionally an exact bottom eigenvector
  confidence: 0.95

P-MR3:
  prediction: finite H2a can be obtained on useful cells through penalty or parity/Feshbach machinery
  confidence: 0.80

P-MR4:
  prediction: the cofinal difficulty is uniform source-defined certification, not finite algebra
  confidence: 0.95

P-MR5:
  prediction: the main global wall remains transform-level ground-to-trial tracking
  confidence: 0.95

P-MR6:
  prediction: CCM Lemma 7.3 project import is mainly normalization and topology work
  confidence: 0.90

P-MR7:
  prediction: a convergence-compatible schedule requires N/log(m) -> infinity
  confidence: 0.99
```

# 16. STRONGEST ATTACK

Главное возражение:

> Вы просто переименовали open CCM approximation step в `FiniteGroundTransformToCCMTrialLocallyUniform`. Где реальное уменьшение?

Частично это верно.

Эта стена остаётся RH-level.

Но она теперь имеет exact internal ledger:

\[
\boxed{
C_K(m,N)\frac{\|r_{m,N}\|}{\Delta_{m,N}}
+
\operatorname{Tail}_{m,N}(K)
+
\operatorname{NormalizationError}_{m,N}(K)
\to0.
}
\]

То есть неизвестное больше не называется «ground похож на trial».

Оно распалось на:

```text
actual residual;
true gap;
evaluation norm;
projection tail;
normalization;
schedule.
```

Каждый объект можно отдельно:

- доказать;
- опровергнуть;
- измерить на finite controls;
- заменить Schur/Feshbach representation.

Второе возражение:

> Direct convergence может быть сложнее Montel/S2.

Да.

Поэтому direct route выбран не потому, что он логически короче, а потому, что CCM Lemma 7.3 уже закрывает последний участок. Если transform-level tracking не удаётся, мы возвращаемся к cluster route, не меняя finite real-zero front.

Третье возражение:

> Uniform H2a along a cofinal schedule может быть такой же трудной стеной, как tracking.

Да.

Поэтому H2a и tracking — два параллельных main fronts. Нельзя ждать завершения одного, чтобы начать exact algebra of the other.

# 17. FINAL PROPOSAL

Фокусируем проект на одной дороге:

\[
\boxed{
\texttt{REALZERO\_FINITE\_GROUND\_DIAGONAL\_TO\_XI}
}
\]

Не переопределяем current D0 trial family.

Создаём explicit ground-family route.

Рабочие fronts:

```text
Front 1:
  finite simple-even ground package.

Front 2:
  Proposition59 real-zero transfer.

Front 3:
  finite ground transform → CCM trial transform.

Front 4:
  CCM trial → Xi project import.

Closure:
  ZeroEscape.
```

Самый дешёвый следующий theorem:

\[
\boxed{
\texttt{Proposition59GroundLagrangeZeroSetBridge}
}
\]

Он закрывает полный finite H2b transport и сразу ставит правильные sign/scale/removable-pole plants.

После него центральная работа переходит к:

\[
\boxed{
\texttt{FiniteGroundTransformToCCMTrialLocallyUniform}.
}
\]

# 18. CODEX DIRECTIVE

```text
NO EXECUTION AUTHORIZED BY THIS STRATEGIC VERDICT.

NEXT ADMISSIBLE TARGET:
  PROPOSITION59_GROUND_LAGRANGE_ZEROSET_BRIDGE

PIN:
  repo = Malaeu/chen_q3
  branch = rh_clean
  HEAD = b124fba1fcf33cd105a078254caa9d62240d59e6

PACKAGE:
  q3.lean.aristotle

PURPOSE:
  Prove that the exact Proposition-5.9 transform built from a finite
  real CCM coefficient vector has only real zeros whenever the exact
  source Lagrange polynomial of that vector has only real zeros.

INPUTS:
  Q3/Proofs/RouteB/Proposition59EntireTransform.lean
  Q3/Proofs/RouteB/RankOneCorrectionLagrangePolynomial.lean
  Q3/Proofs/RouteB/RankOneCorrectionLagrangeRealZeros.lean
  Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean
  Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean

REQUIRED PHASES:

1. CARRIER LOCK
   Define or reuse an exact equivalence:
     CCMModeFinite N
     ↔
     integer modes k with -N ≤ k ≤ N.

2. CAUCHY NUMERATOR IDENTITY
   Prove off the finite poles:
     the finite Cauchy numerator equals
     a nonzero explicit scale times
     sourceLagrangePolynomial evaluated at -L*z/(2*pi).

3. ZERO-SET SPLIT
   Handle separately:
     included removable pole;
     exterior sine-lattice zero;
     off-lattice Lagrange zero.

4. CCM WRAPPER
   Compose with:
     ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized.

MANDATORY PLANTS:

P1:
  remove the minus sign.
  Required:
    P59_LAGRANGE_SIGN_MISMATCH.

P2:
  remove 2*pi/L.
  Required:
    P59_LAGRANGE_SCALE_MISMATCH.

P3:
  treat an included removable pole as an exterior forced zero.
  Required:
    P59_REMOVABLE_POLE_CASE_DROPPED.

P4:
  use arbitrary complex coefficients rather than the exact complexification
  of a real CCM row.
  Required:
    P59_REAL_COEFFICIENT_PROVENANCE_MISSING.

VALIDATION:
  lake env lean <touched-file>
  lake build
  #print axioms <public-theorem>

SUCCESS:
  P59_GROUND_LAGRANGE_ZEROSET_BRIDGE_PROVED

FAILURE:
  P59_CARRIER_EQUIV_GAP
  P59_CAUCHY_NUMERATOR_IDENTITY_GAP
  P59_COMPLEX_SINE_ZERO_API_GAP
  P59_LAGRANGE_SIGN_MISMATCH
  P59_LAGRANGE_SCALE_MISMATCH
  LEAN_BUILD_FAIL

FORBIDDEN:
  no redefinition of current D0 Pstar;
  no claim that kTrial is a ground vector;
  no scalar-only Pstar=Lagrange equality;
  no numerical zero matching;
  no finite-to-global claim;
  no route promotion;
  no RH claim.
```

# 19. META CLOSEOUT

## Что стало меньше?

Все прежние ветви сжаты до пяти gates:

```text
finite ground;
finite real zeros;
same-family tracking;
trial-to-Xi;
ZeroEscape.
```

## Что убито?

- silent trial/ground identification;
- scalar-only Lagrange equality;
- arbitrary fixed-window substitution;
- arbitrary cofinal path;
- Rayleigh-value/residual confusion;
- finite-to-global promotion.

## Что нельзя повторять?

Нельзя доказывать real zeros для одной family и convergence для другой.

## Current smallest local gap

\[
\boxed{
\texttt{Proposition59GroundLagrangeZeroSetBridge}
}
\]

## Current smallest global gap

\[
\boxed{
\texttt{FiniteGroundTransformToCCMTrialLocallyUniform}
}
\]

## Next cheapest decisive test

Exact symbolic Cauchy-numerator identity with sign, scale and removable-pole plants.

## Fate of prior predictions

```text
direct real-zero sequence → Xi → RH:
  CONFIRMED.

current D0 trial Pstar receives finite ground real zeros:
  REFUTED.

scalar-only Pstar = cN*Lagrange:
  REFUTED.

CCM trial → Xi:
  CONFIRMED AT PAPER LEVEL.

one arbitrary cofinal diagonal:
  REFUTED.

coverage-compatible source-locked diagonal:
  ALIVE.
```

```yaml
iteration:
  target: full_route_concentration
  status: PROGRESS
  failed_strategy: mix_trial_realzero_and_ground_realzero_families
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: FiniteGroundTransformToCCMTrialLocallyUniform
  invariant_learned: real-zero property and Xi convergence must belong to one normalized cofinal family
  forbidden_future_move: silently inherit facts across trial and ground coefficient rows
  next_decisive_test: Proposition59GroundLagrangeZeroSetBridge
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
