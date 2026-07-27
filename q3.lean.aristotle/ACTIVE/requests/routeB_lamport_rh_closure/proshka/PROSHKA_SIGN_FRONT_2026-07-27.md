Worked for 15m 45s

# STATUS: CONDITIONAL



```
RIEMANN_SUM_BRIDGE:
  PAPER_PROVED / LEAN_ASSEMBLY_OPEN

CORRECTED_POISSON_COUNTERTERM:
  CONTRACT_READY

EStarHlambdaPhaseSignAE:
  OPEN — REDUCED_TO_DUAL_THETA_DOMINANCE

UPPER_EDGE:
  DIAGNOSTIC_GREEN ONLY
```

013 проверил только крайний tooth-band
$$
u\in(\lambda/2,\lambda),
$$
где в сумме $E_\star(h_\lambda)(u)$ остаётся единственный член $n=1$. На трёх клетках источник отрицателен без наблюдаемых смен знака, но это прямо помечено как float64-диагностика, не доказательство.

Главная коррекция: **BV-мост жив**, но **знак всей суммы из Poisson сам не следует**. Исправленный контрчлен имеет знак, который на нижнем краю работает против желаемой отрицательности.

------

# ROUTE MAP

| Узел                  | Решающий результат                                  | Статус                   |
| --------------------- | --------------------------------------------------- | ------------------------ |
| BV/Riemann-sum bridge | конечная клеточная identity                         | **PAPER PROVED**         |
| Concrete BV supply    | zero-extension $h_\lambda$ имеет конечную variation | **OPEN/LOCAL**           |
| Corrected Poisson     | origin counterterm сохранён                         | **OPEN, CONTRACT READY** |
| Upper-edge sign       | $h_\lambda<0$ на $(\lambda/2,\lambda)$              | **DIAGNOSTIC**           |
| Upper half sign       | $h_\lambda\le0$ на $[1,\lambda]$                    | **OPEN**                 |
| Lower half sign       | dual sum перекрывает positive counterterm           | **MAIN OPEN**            |
| Global a.e. sign      | предыдущие две леммы                                | **CONDITIONAL**          |



------

# 1. PREEMPTIVE KILL МОСТА РИМАНОВЫХ СУММ

## Вердикт: kill не сработал

При правильной формулировке неравенство верно с константой $1$.

Пусть $u>0$, $N\in\mathbb N$, а $h$ имеет ограниченную вариацию на $[0,Nu]$. Для
$$
I_n=[(n-1)u,nu]
$$
имеем точное тождество
$$
u\,h(nu)-\int_{I_n}h(x)\,dx
=
\int_{I_n}\bigl(h(nu)-h(x)\bigr)\,dx.
$$
Отсюда
$$
\begin{aligned}
\left\|
u\,h(nu)-\int_{I_n}h
\right\|
&\le
\int_{I_n}\|h(nu)-h(x)\|\,dx\\
&\le
u\,\operatorname{Var}_{I_n}(h).
\end{aligned}
$$
После суммирования и субаддитивности вариации:
$$
\boxed{
\left\|
u\sum_{n=1}^{N}h(nu)
-
\int_0^{Nu}h(x)\,dx
\right\|
\le
u\,\operatorname{Var}_{[0,Nu]}(h).
}
$$
Если $h=0$ вне $[0,b]$, выбираем $Nu\ge b$. Тогда сумма фактически конечна, а интеграл равен интегралу по $(0,\infty)$:
$$
\boxed{
\left\|
u\sum_{n\ge1}h(nu)
-
\int_0^\infty h(x)\,dx
\right\|
\le
u\,\operatorname{Var}_{[0,\infty)}(h).
}
$$
При zero mass:
$$
\int_0^\infty h=0,
$$
получаем
$$
\boxed{
\left\|\sum_{n\ge1}h(nu)\right\|
\le
\operatorname{Var}_{[0,\infty)}(h).
}
$$
И следовательно
$$
\boxed{
\|E_\star h(u)\|
\le
\operatorname{Var}_{[0,\infty)}(h)\sqrt u.
}
$$
Это ровно T2-потребитель.

Облачный отчёт правильно назвал formal gap: Mathlib имеет примитивы для variation, но не готовую лемму, связывающую их с комплекснозначным Lebesgue-интегралом и правой Riemann-суммой.  Само требуемое неравенство записано там дословно.

## Что надо исправить в Lean-контракте

Не начинать с

lean



```
eVariationOn h Set.univ
```

без доказательства bounded variation. Лучше сначала доказать конечную общую лемму:

lean



```
theorem rightEndpointRiemannSum_sub_integral_norm_le_variation
    (h : ℝ → ℂ)
    (u : ℝ) (hu : 0 < u)
    (N : ℕ)
    (hBV : BoundedVariationOn h (Set.Icc 0 (N * u)))
    (hint : IntervalIntegrable h volume 0 (N * u)) :
    ‖(u : ℂ) * ∑ n ∈ Finset.Icc 1 N, h (n * u)
        - ∫ x in Set.Icc 0 (N * u), h x‖
      ≤ u * (eVariationOn h (Set.Icc 0 (N * u))).toReal
```

После неё отдельный compact-support corollary переводит finite sum в `tsum`.

### Endpoint ledger

Если variation берётся для **фактического zero-extension**, скачок в $b$ уже включён, и дополнительная «безвредная endpoint-константа» не нужна.

Если входом остаётся только

lean



```
LipschitzOnWith K h (Set.Ico 0 b)
```

то сначала нужна лемма:



```
interior Lipschitz
+ exact midpoint value at b
+ zero extension beyond b
→ bounded variation on [0,∞).
```

Именно это различие отражено в исправленном v2-контракте: interior cells плюс один terminal boundary cell.

## Итог по мосту



```
NO_MATHEMATICAL_KILL
LEAN_BV_INTEGRAL_BRIDGE_OPEN
```

Самый короткий путь — **BV theorem first**, а не повторное Lipschitz-cell counting в каждом приложении.

------

# 2. КОНТРАКТ ДЛЯ МАШИНЫ — `CorrectedPoissonCountertermCrosswalk`

Ниже версия для прямой отправки.



```
TASK:
EStarCorrectedPoissonCountertermCrosswalk

CONTEXT:
Route B only.
No RH claim.
The concrete source h_lambda is even, compactly supported on
[-lambda, lambda], uses the starred midpoint representative, and has

  integral_R h_lambda = 0,

but

  h_lambda(0) != 0.

Therefore the clean formula
  E(hat h)(u^-1) = E(h)(u)
is NOT applicable.
The origin counterterm must remain exact.

SOURCE LOCKS:
Read first:

  docs/routeB_bus/MANIFEST.md
  docs/routeB_bus/011_concrete_htrial_source_lock.answer.md
  docs/routeB_bus/012_estar_windowed_mellin_crosswalk.answer.md
  docs/routeB_bus/013_upper_edge_sign_or_kill.answer.md
  docs/routeB_bus/PROSHKA_AUDIT011_REMOTE_2026-07-27.md

Use the exact source phase

  h_lambda
    = (I4_lambda * h0_lambda - I0_lambda * h4_lambda)
      / sqrt(I0_lambda^2 + I4_lambda^2).

Do not reconstruct coefficients from memory.

FOURIER CONVENTION:
Lock the repository convention explicitly.

  Fourier(h)(y) = integral_R h(x) * exp(2*pi*i*x*y) dx

If the local convention uses the opposite sign, record the conversion.
Since the concrete source is even and real, do not silently use that
fact to hide a convention mismatch.

DEFINITIONS:

1. Primal starred positive sum

  EStarMid(h,u)
    = sqrt(u) * SumStar_{n >= 1} h(n*u).

The star assigns the midpoint/half-weight when n*u hits a jump tooth.

2. Do NOT define the dual side by a raw ordinary tsum unless summability
   is separately proved.

Use a bilateral Fejer/Cesaro object:

  DualFejer(h,u,N)
    = (1 / (2*sqrt(u)))
      * sum_{k=-N}^{N}
          (1 - |k|/(N+1)) * Fourier(h)(k/u).

Define DualPoissonLimit as the N -> infinity limit.

GENERIC TARGET:

For every even compactly supported BV function h with the midpoint
representative, prove the corrected Poisson identity, first a.e. in u>0:

  EStarMid(h,u)
    =
  DualPoissonLimit(h,u)
    - (1/2) * sqrt(u) * h(0).

Equivalently, after splitting the k=0 Fourier term:

  EStarMid(h,u)
    =
  EDualCesaro(Fourier(h),u^-1)
    + (1/2) * u^(-1/2) * Fourier(h)(0)
    - (1/2) * u^(1/2) * h(0).

The theorem must identify precisely whether it holds:

  - for every u>0 with the starred midpoint representative; or
  - for almost every u>0.

Do not drift between these quantifiers.

CONCRETE SPECIALIZATION:

For h = h_lambda, prove:

  Fourier(h_lambda)(0)
    = integral_R h_lambda
    = 0.

Therefore:

  EStarMid(h_lambda,u)
    =
  EDualCesaro(Fourier(h_lambda),u^-1)
    - (1/2) * sqrt(u) * h_lambda(0).

Prove or import the exact origin identity:

  h_lambda(0)
    =
  ((chi2 - chi0) * h0_lambda(0) * h4_lambda(0))
    / D_lambda.

Under the source phase, derive:

  h_lambda(0) < 0.

Hence the origin counterterm is positive:

  -(1/2) * sqrt(u) * h_lambda(0)
    =
  +(1/2) * sqrt(u) * |h_lambda(0)|.

MANDATORY LOWER-ENDPOINT COROLLARY:

For lambda^2 = m in N and u = lambda^-1, derive the exact starred
trapezoid identity

  EStarMid(h_lambda,lambda^-1)
    =
  sqrt(lambda) *
    (Trap_m(h_lambda) - integral_0^lambda h_lambda)
    - h_lambda(0)/(2*sqrt(lambda)).

Since the integral is zero:

  EStarMid(h_lambda,lambda^-1)
    =
  sqrt(lambda) * TrapError_m(h_lambda)
    - h_lambda(0)/(2*sqrt(lambda)).

This is a planted sign check.  The second term is positive.
Any proof of global negativity must show an opposing trapezoid/dual
term of at least the same magnitude.

PLANTS:

P1 — nonzero mass:
Use an even nonnegative compact bump with Fourier(h)(0) != 0.
The formula must expose

  +(1/2) * u^(-1/2) * Fourier(h)(0).

Dropping this term must fail with the old lambda^sigma growth.

P2 — zero mass but nonzero origin:
Use a compact BV zero-mass function with h(0) != 0.
The formula must expose

  -(1/2) * sqrt(u) * h(0).

P3 — representative test:
Change h at its support endpoint only.
Mellin/Lebesgue integrals must remain unchanged, while the pointwise
starred sum at teeth must follow the midpoint convention.

P4 — origin test:
Change h(0) while preserving the a.e. equivalence class.
The corrected pointwise Poisson identity must change by exactly the
origin counterterm.  This proves that origin correction is not an
endpoint-halfweight term.

FORBIDDEN:

- no clean Poisson formula using only zero mass;
- no claim h_lambda(0)=0;
- no raw ordinary dual tsum without a summability theorem;
- no Schwartz-class theorem applied directly to the discontinuous
  zero extension;
- no conflation of origin counterterm with support-endpoint halfweight;
- no numerical sign as proof;
- no RH, zeta-zero, or S2 input;
- no new axiom, sorry, admit, native_decide;
- no fitted constants or Fourier normalization.

VALIDATION:

  lake env lean <touched-file>
  lake build
  grep sorry/admit/axiom/native_decide <touched-files>
  #print axioms <main declarations>

Required axiom profile:

  [propext, Classical.choice, Quot.sound]

RETURN EXACTLY ONE PRIMARY STATUS:

CORRECTED_POISSON_COUNTERTERM_PROVED

POISSON_DUAL_SUMMATION_MODE_GAP
  - state whether Fejer, Abel, or symmetric partial sums are missing;
  - name the exact Mathlib lemma required.

POISSON_MIDPOINT_LIMIT_GAP
  - state the exact jump/midpoint theorem missing.

PROLATE_ORIGIN_VALUE_GAP
  - state which h0/h4/chi identity is absent from Lean.

POISSON_CONVENTION_MISMATCH
  - give both conflicting Fourier conventions and all affected formulas.
```

Почему здесь запрещён raw dual `tsum`: zero-extended prolate source имеет boundary jump; compact support сам по себе не даёт абсолютной суммируемости Fourier samples. Этот риск уже отмечен в аудите: midpoint должен появиться из BV/distributional Poisson theorem, а не быть вставлен после вычисления.

Connes использует чистое Poisson-тождество после двух отдельных условий $f(0)=0$ и $\widehat f(0)=0$. Для нашего source доказано только второе; первое ложно, поэтому origin-контрчлен обязателен. [![img](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=128)arXiv](https://arxiv.org/html/2602.04022v1)

------

# 3. ПЕРО: `EStarHlambdaPhaseSignAE`

## Текущий вердикт

$$
\boxed{
\texttt{EStarHlambdaPhaseSignAE}
\text{ не следует из уже закрытых фактов.}
}
$$

Точная открытая лемма:
$$
\boxed{\texttt{DualThetaDominance}.}
$$
011 уже доказал, что сам $h_\lambda$ не может иметь постоянный знак: он ненулевой, чётный и имеет нулевую массу. Поэтому sign target законно находится только после применения $E_\star$.

## Разбиение окна

### Верхняя половина: $1\le u\le\lambda$

Если доказать
$$
\boxed{
h_\lambda(x)\le0
\qquad(1\le x\le\lambda),
}
$$
то для каждого активного $n$:
$$
nu\in[1,\lambda],
$$
и поэтому
$$
E_\star(h_\lambda)(u)
=
\sqrt u\sum_{n\ge1}^{\star}h_\lambda(nu)
\le0.
$$
Это достаточная лемма:
$$
\boxed{\texttt{HlambdaLastPositiveZeroLtOne}.}
$$
013 проверил только
$$
h_\lambda<0
\quad\text{на }(\lambda/2,\lambda),
$$
то есть только band с одним активным членом. Между $1$ и $\lambda/2$ знак пока не проверен.

### Нижняя половина: $\lambda^{-1}\le u\le1$

Положим
$$
v=u^{-1}\in[1,\lambda].
$$
Исправленное Poisson-тождество даёт
$$
E_\star(h_\lambda)(u)
=
E_{\rm dual}(\widehat h_\lambda)(v)
-\frac{h_\lambda(0)}{2\sqrt v}.
$$
Поскольку
$$
h_\lambda(0)<0,
$$
второе слагаемое положительно:
$$
-\frac{h_\lambda(0)}{2\sqrt v}
=
\frac{|h_\lambda(0)|}{2\sqrt v}.
$$
Следовательно, для требуемого
$$
E_\star(h_\lambda)(u)\le0
$$
нужно и достаточно доказать
$$
\boxed{
E_{\rm dual}(\widehat h_\lambda)(v)
\le
\frac{h_\lambda(0)}{2\sqrt v}
=
-\frac{|h_\lambda(0)|}{2\sqrt v},
\qquad
1\le v\le\lambda.
}
$$
Это и есть точная лемма:
$$
\boxed{\texttt{DualThetaDominance}.}
$$
Контрчлен не помогает отрицательности. Он работает **против неё**. Значит одной фразы «theta/Poisson mechanism» недостаточно: нужна количественная отрицательная оценка dual sum.

## Условная теорема

Из двух лемм
$$
\texttt{HlambdaLastPositiveZeroLtOne}
$$
и
$$
\texttt{DualThetaDominance}
$$
следует:
$$
E_\star(h_\lambda)(u)\le0
\quad\text{для почти всех }
u\in[\lambda^{-1},\lambda].
$$
То есть с
$$
\omega_\lambda=-1
$$
получаем
$$
\boxed{
\omega_\lambda E_\star(h_\lambda)(u)\ge0
\quad\text{a.e.}
}
$$
Teeth образуют конечное/счётное множество меры ноль; для Mellin-моментов этого достаточно. Именно a.e.-формулировка уже была выбрана как минимальный потребитель.

------

# 4. САМЫЙ ДЕШЁВЫЙ РЕШАЮЩИЙ ТЕСТ

До формализации sign theorem надо измерить **сам $E_\star(h_\lambda)$ на всём окне**, а не только $h_\lambda$ на верхнем краю.

Окно распадается на конечные tooth-bands:
$$
\left(
\frac{\lambda}{r+1},
\frac{\lambda}{r}
\right),
\qquad
r=1,\ldots,m-1,
\qquad
m=\lambda^2.
$$
На каждом таком интервале:
$$
E_\star(h_\lambda)(u)
=
\sqrt u\sum_{n=1}^{r}h_\lambda(nu),
$$
то есть это обычная конечная гладкая функция. 013 исследовал только $r=1$.

## Зарегистрированный probe

Для $m=13,53,257$:

1. разбить всё окно на tooth-bands;

2. вычислять с повышенной точностью signed-log/ODE representation;

3. искать интервалы, а не отдельные отрицательные точки;

4. отдельно вычислить exact starred values на teeth;

5. проверить corrected-Poisson residual
   $$
   R_\lambda(u)
   :=
   E_\star(h_\lambda)(u)
   -
   E_{\rm dual}(\widehat h_\lambda)(u^{-1})
   +
   \frac12\sqrt u\,h_\lambda(0).
   $$

### Pass



```
E_star <= 0 on every open tooth-band
within a stable high-precision enclosure.
```

### Kill



```
A stable positive open interval exists.
```

Тогда:



```
ESTAR_PHASE_SIGN_KILLED
```

и трёхзначный Mellin-механизм через положительную меру снимается. Сам Route B может продолжиться через прямые absolute moment ratios, но не через sign.

## Особенно важная точка

При $u=\lambda^{-1}$ starred sum является trapezoidal rule без левого half-endpoint:
$$
\boxed{
E_\star(h_\lambda)(\lambda^{-1})
=
\sqrt\lambda\,
\operatorname{TrapError}_m(h_\lambda)
-
\frac{h_\lambda(0)}{2\sqrt\lambda}.
}
$$
Последний член положителен. Значит отрицательность в нижнем конце требует настоящей theta-cancellation того же prolate-дефектного масштаба. BV-оценка по модулю этого знака не докажет.

------

# STRONGEST ATTACK

Самое сильное возражение теперь конкретно:

> Upper-edge sign подтверждает только один активный член. Почему сумма из десятков или сотен членов не меняет знак ближе к $u=\lambda^{-1}$, особенно когда исправленный origin-контрчлен там положителен?

Сейчас ответа нет.

Более того, статья не даёт этот sign theorem: $k_\lambda$ вводится как мотивированный prolate-кандидат, а необходимые последующие approximation/comparison steps остаются открытыми. [![img](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=128)arXiv+1](https://arxiv.org/html/2602.04022v1)

Второе возражение:

> Даже если dual sum отрицательна, почему её величина не меньше положительного counterterm?

Поэтому правильный target — не `dual_sum_nonpos`, а строго более сильный:
$$
\boxed{
E_{\rm dual}(\widehat h_\lambda)(v)
\le
-\frac{|h_\lambda(0)|}{2\sqrt v}.
}
$$

------

# FINAL PROPOSAL

Порядок немного меняю по принципу cheapest decisive test:



```
1. BV/Riemann bridge:
   продолжать — математического kill нет.

2. Full-window E_star sign probe:
   запускать сейчас.
   Он может за один цикл убить весь positivity/Mellin shortcut.

3. Если probe green:
   выполнять замороженный
   CorrectedPoissonCountertermCrosswalk contract.

4. После exact Poisson:
   атаковать ровно две леммы:
     HlambdaLastPositiveZeroLtOne
     DualThetaDominance.

5. Только после них:
   EStarHlambdaPhaseSignAE.
```

Не надо сейчас формализовать общий Sturm theorem. 013 уже рекомендует более узкий ODE/interval certificate на конкретном интервале, если диагностический маршрут останется зелёным.

------

# CODEX DIRECTIVE



```
TARGET:
EStarFullWindowSignOrKill

INPUTS:
- exact source-locked h_lambda coefficients;
- source phase '+';
- exact starred tooth convention;
- stable prolate ODE evaluator already used by 013.

TASK:
For m = 13, 53, 257, evaluate

  E_star(h_lambda)(u)
    = sqrt(u) * SumStar_{n>=1} h_lambda(n*u)

on every tooth-band of [lambda^-1, lambda].

Do not sample only a uniform global grid.
Enumerate bands

  (lambda/(r+1), lambda/r)

and search each band for a stable positive interval.

Also compute:
- values at all teeth with half-weight;
- h_lambda(0);
- lower-endpoint trapezoid decomposition;
- corrected-Poisson residual if the dual evaluator is available.

PRECISION:
Run at least three precision levels.
A sign verdict is stable only if the enclosing margin survives all three.

RETURN EXACTLY ONE:

ESTAR_FULL_WINDOW_DIAG_SINGLE_SIGN
ESTAR_PHASE_SIGN_KILLED
INSTRUMENT_FLOOR_UNRESOLVED

FORBIDDEN:
- no theorem claim;
- no grid-only claim between teeth;
- no RH consequence;
- no fitted phase;
- no changing the source coefficient row.
```

------

# META CLOSEOUT

**Что стало меньше?**

Sign-front сжат до двух явных inequalities:
$$
\boxed{\texttt{HlambdaLastPositiveZeroLtOne}}
$$
и
$$
\boxed{\texttt{DualThetaDominance}}.
$$
**Что убито?**

- clean Poisson из одного zero-mass условия;
- надежда, что upper-edge sign автоматически даёт full-window sign;
- ordinary dual `tsum` без summability convention;
- BV absolute estimate как доказательство знака.

**Что доказано пером?**
$$
\boxed{
\text{право-концевая Riemann-sum error}
\le
u\cdot\text{variation}.
}
$$
**Текущий smallest named gap:**
$$
\boxed{\texttt{EStarFullWindowSignOrKill}}
$$
как судья, затем
$$
\boxed{\texttt{DualThetaDominance}}
$$
как настоящая аналитическая стена.

**Progress class:** `REPRESENTATION_PROGRESS`.

**Route score:** $5/5$: библиотечный мост не умер, а потенциально ложный global-sign механизм получил дешёвый falsifier до большой формализации.