# STATUS: OPEN — 033 FULL-WINDOW BUDGET CHOSEN; MÜNTZ TARGET REPAIRED

```yaml
PRIMARY_STATUS: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
SOURCE_MIRROR: cb0cdb99b551729c9f03b74af3d1e1416ba9376f

REQUEST_1:
  CHOSEN_ROUTE: A_FULL_WINDOW_COUPLED_POSITIVE_PART
  NEXT_TRANSACTION: 033_FULL_WINDOW_COUPLED_POSITIVE_PART_BUDGET
  SCOPE: FINITE_CELL_m257
  VERIFIER: ARB_INTERVAL_PLUS_EXACT_RATIONAL_PLUS_PAPER
  CURRENT_SMALLEST_GAP: RemainingWindowPositivePartOrSignSupplier
  POST_033_GAP_IF_GREEN: CofinalFullWindowPositivePartMomentBound
  ROUTES:
    A:
      kill_power: 5
      cost: 3
      verdict: CHOSEN
    B:
      kill_power: 5
      cost: 5
      verdict: DEFERRED_UNTIL_033_PROFILE
    C:
      kill_power: 1
      cost: 2
      verdict: REJECTED_INPUTS_NOT_THEOREM_COMPLETE
      failure_code: S1_ASSEMBLY_INPUT_INSUFFICIENT

REQUEST_2:
  STATUS: POLE_SUBTRACTED_TARGET_READY
  NEW_TASK: EStarMuntzZeroMassContinuation_Standalone_v3_PoleSubtracted
  REMOVE_TARGET: raw_pointwise_riemannZeta_times_Mellin_at_w_eq_1
  REPLACEMENT:
    zeta_factor: analytic_extension_of_(w_minus_1)_times_zeta
    mellin_factor: dslope_of_Mellin_at_1
    regularized_product: zeta_factor_times_mellin_factor
  POLE_VALUE: deriv_Mellin_h_at_1
  RAW_PRODUCT_COROLLARY_DOMAIN: w_ne_1_only

FORBIDDEN:
  - use_022_grid_as_continuum_proof
  - finite_cell_to_cofinal_promotion
  - new_K_or_precision_ladder
  - independent_r_times_epsilon_tail_as_decisive_bound
  - raw_zeta_Mellin_value_at_the_pole
  - pointwise_DualTheta_claim_from_Lebesgue_budget
```

031 принят полностью: band-zero identity убита, Jacobi divided-difference и Green ledger доказаны, точный (S\leftrightarrow E_\star) crosswalk получен, а positive-part budget закрыт на двух priority bands в единственной клетке (m=257).

032 также принят: `RiemannBoundaryCellBridge` пересобран с нуля, T0–T3 совпали с контрактом, `#print axioms` содержит только `propext`, `Classical.choice`, `Quot.sound`.

## 1. Выбор маршрута 033

| Маршрут                                                | Kill-power / cost | Решение                   |
| ------------------------------------------------------ | ----------------- | ------------------------- |
| **(a) Полный coupled-budget одним прогоном**           | **5 / 3**         | **Выбран**                |
| **(b) Знаковая факторизация (D_r) из Jacobi identity** | **5 / 5**         | Отложена до профиля 033   |
| **(c) Немедленная сборка S1 из двух полос и 022**      | **1 / 2**         | Убита как преждевременная |

### Почему не (c)

022 прямо классифицирован как high-precision grid diagnostic, а не theorem о знаке между точками. Там 19 локальных отрицательных кандидатов, но 51 запись остаётся на error floor; полного покрытия окна нет.

Поэтому:

```text
031 two-band theorem
+
022 diagnostic series
≠
S1 supplier on the whole window.
```

Использовать 022 как доказательный вход означало бы занять универсальный квантор диагностикой.

### Почему пока не (b)

031 доказал точное представление

# [ L_{\Theta_4}\delta

\frac{\Theta_4-\Theta_0}{2},b_0
]

и конечный Green ledger с живым terminal boundary term. Но знака forcing pairing, adjoint solution или boundary ledger ещё нет.

Поэтому (D_r)-факторизация — потенциально сильный **cofinal mechanism**, но не дешёвый следующий шаг. Сначала нужен полный профиль (\varepsilon_r): тогда Jacobi-машина атакует только доминирующий класс полос, а не все 239 вслепую.

------

# 2. Директива 033

## PRIMARY TARGET

```text
033_FullWindowCoupledPositivePartBudget
```

## SCOPE

```text
CHALLENGER / NOT_RH
FINITE CELL m=257 ONLY
No cofinal-family claim.
No pointwise sign claim from an integral budget.
```

## Полное окно

При (\lambda=\sqrt{257}):

[
z\in
\left[\frac1{257},\frac1{\sqrt{257}}\right].
]

Оно разбивается на:

```text
partial band:
  r = 16
  J_16 = [1/17, 1/sqrt(257)]

full bands:
  r = 17,...,256
  J_r = [1/(r+1), 1/r]
```

Всего — 241 band portions:

- две (r=255,256) уже закрыты 031;
- остаётся 239;
- в 033 обе закрытые полосы надо **пересчитать как regression controls**.

Точки-зубья окна:

```text
r = 17,...,257
z = 1/r
```

Всего 241 tooth:

- (r=255,256,257) уже покрыты;
- остаётся 238.

## Exact object

# [ S_r(z)

# \sum_{q\ge0}\delta_q A_{r,q}(z), \qquad A_{r,q}(z)

\sum_{n=1}^{r}P_{2q}(nz),
]

# [ \delta_q

\frac{b_{4,q}-b_{0,q}}2,
\qquad
\delta_0=0
]

до interval arithmetic.

Заморозить параметры 030:

```text
core_q = 440
tail_q = 700
tau_response = 2^-512
terminal cone = [0,1/2]
canonical phase = '+'
```

Новой глубины и новой precision ladder нет.

## Coupled backend

Для каждой полосы построить один whole-response polynomial, содержащий все центры до (q=700). Наружу добавить только:

- coefficient-box response uncertainty;
- infinite response remainder beyond (q=700).

Получить:

[
L_r\le S_r(z)\le U_r
\qquad (z\in J_r),
]

и определить

[
\boxed{
\varepsilon_r:=\max(0,-L_r).
}
]

Старый финальный хвост

[
r\left(\varepsilon_0/J_0+\varepsilon_4/J_4\right)
]

запрещён.

## Guard для (r=16)

[
\frac1{\sqrt{257}}
]

не рационально. Нельзя передавать его в exact rational Bernstein backend как decimal masquerading as exact.

Разрешены два варианта:

1. algebraic endpoint с relation
   [
   257z^2=1;
   ]
2. rational outer endpoint (z_{16}^{+}) с exact integer-square proofs
   [
   \frac1{\sqrt{257}}
   \le z_{16}^{+}
   <
   \frac1{16}.
   ]

Во втором случае envelope сертифицируется на большем интервале

[
[1/17,z_{16}^{+}],
]

но интегрируется только истинный участок до (1/\sqrt{257}).

Failure code:

```text
FULL_WINDOW_PARTIAL_ENDPOINT_GAP
```

## Exact positive-part theorem

031 дал:

# [ E_\star(h_\lambda,\lambda z)

-\frac{I_0I_4}{D}
\sqrt{\frac z\lambda},
S_\lambda(z),
\qquad
\frac{du}{u}=\frac{dz}{z}.
]

Положим

[
C_\lambda=\frac{I_0I_4}{D}>0.
]

Для каждого

[
0\le\sigma<\frac12
]

доказать:

[
\Delta_{257,\sigma}^{+}
:=
\int_{1/\lambda}^{1}
\max(E_\star(h_\lambda,u),0)
u^{-\sigma}\frac{du}{u}
]

и

## [ \boxed{ \begin{aligned} \Delta_{257,\sigma}^{+} \le {}& C_\lambda\lambda^{-\sigma-\frac12} \frac{1}{\frac12-\sigma} \Bigg[ \varepsilon_{16} \left( \lambda^{\sigma-\frac12}

## 17^{\sigma-\frac12} \right)\ &+ \sum_{r=17}^{256} \varepsilon_r \left( r^{\sigma-\frac12}

(r+1)^{\sigma-\frac12}
\right)
\Bigg].
\end{aligned}
}
]

Выводить отдельно:

```text
Delta_full_over_C_lambda(sigma)
Delta_full(sigma) with outward C_lambda interval
```

Сохранённый decimal (C_\lambda) точным входом не считать.

Верхняя половина (u\in[1,\lambda]) не вносит positive part благодаря 027; G5 при этом всё ещё остаётся compiler-open и требует уже cofinal supplier, а не одну клетку.

## Teeth ledger

Для каждого (r=17,\dots,257):

# [ S_r^\star

\sum_{q\ge0}\delta_q
\left(
\sum_{n=1}^{r-1}P_{2q}(n/r)
+
\frac12P_{2q}(1)
\right).
]

Зубья имеют Lebesgue measure zero и в (\Delta^+) не входят.

Secondary flag — ровно один:

```text
ALL_WINDOW_TEETH_NONNEGATIVE_PROVED
```

только если все lower envelopes неотрицательны;

```text
POINTWISE_DUALTHETA_KILLED_AT_TOOTH
```

только если хотя бы один upper envelope строго отрицателен;

```text
TOOTH_SIGN_INCONCLUSIVE
```

во всех остальных случаях.

Если на заранее фиксированной rational band-subcell получается (U<0), разрешён secondary:

```text
POINTWISE_DUALTHETA_KILLED_ON_BAND_SUBCELL
```

Это finite-cell kill pointwise sign theorem, но не kill positive-part/S1 route.

------

## K1-планты 033

### P1 — priority regression

(r=255,256) должны дословно воспроизвести exact envelopes и (\varepsilon_r) из 031.

### P2 — missing band

Удаление одной полосы или subcell обязано ломать coverage-completeness.

### P3 — junction mutation

Положительный gap или overlap между соседними band covers должен обнаруживаться.

### P4 — irrational endpoint

Замена (1/\sqrt{257}) на (1/16) или uncertified decimal должна стрелять.

### P5 — independent-tail regression

Подмена coupled tail на (r\varepsilon_\Psi) должна вернуть существенно более широкую 029-style enclosure. Диагностика не входит в verdict.

### P6 — terminal ratio zero

Замена live terminal cone на terminal zero должна менять enclosure.

### P7 — phase

Flip mode-4 phase должен ломать (\delta_0)-lock или priority regression.

### P8 — Jacobian

Для control (S=-1) удаление (du/u=dz/z) или множителя
(\lambda^{-\sigma-1/2}) должно менять closed form.

### P9 — diagnostic is not proof

Попытка заполнить отсутствующий exact envelope строкой из 022 должна быть отвергнута checker’ом.

### P10 — tooth mutation

Изменение конечного числа tooth values не меняет Lebesgue budget, но меняет tooth ledger.

### P11 — coefficient centers as exact

Удаление coefficient-box uncertainty должно ломать сертификат.

------

## Verdict codes 033

Ровно один primary:

```text
FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED
```

если все 241 band portions покрыты и all-(\sigma) формула доказана;

```text
FULL_WINDOW_COUPLED_RESPONSE_BACKEND_GAP
```

если frozen backend не закрывает хотя бы одну полосу;

```text
FULL_WINDOW_COVERAGE_GAP
```

если есть пропуск в полосах или junction ledger;

```text
FULL_WINDOW_PARTIAL_ENDPOINT_GAP
```

если не закрыт (r=16);

```text
FULL_WINDOW_SOURCE_LOCK_MISMATCH
```

если regression 030/031 не совпадает.

Артефакты:

```text
033_full_window_positive_part.answer.md
FULL_WINDOW_POSITIVE_PART_CERT.json
full_window_positive_part_certificate.py
check_full_window_positive_part_certificate.py
FULL_WINDOW_BAND_PROFILE.csv
FULL_WINDOW_TOOTH_LEDGER.csv
```

Независимый checker не импортирует generator, Arb или flint.

## Registered predictions

```text
P033-1:
  frozen q=700 backend closes every band.

P033-2:
  total positive-part budget is dominated by interior bands,
  not r=255,256.

P033-3:
  at least one remaining tooth is negative or zero-compatible;
  this does not affect the Lebesgue budget.

P033-4:
  the result reveals a band-profile law but gives no cofinal theorem.
```

033 — **последняя разрешённая полная finite-cell enumeration**. После неё запрещена новая cell ladder. Следующий theorem обязан быть parametric/cofinal либо маршрут переходит к Jacobi representation.

------

# 3. Ремонт Aristotle: pole-subtracted Müntz target

Текущий v2 уже пытался заменить raw product на `ZetaMellinReg`, но всё ещё формулировал цель через точечное `if w = 1 then deriv ... else ζ·M`.

Ремонт: не доказывать аналитичность сырого произведения с вручную назначенным значением. Факторизовать устранимую особенность на две аналитические части.

Mathlib определяет `dslope f a` как обычную divided difference вне (a) и как `deriv f a` в самой точке; для аналитической функции имеется power-series theorem для `dslope`. ([Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DSlope.html?utm_source=chatgpt.com))

Mathlib также прямо отмечает, что `riemannZeta` получает некоторое служебное значение при (s=1), остаётся differentiable только вне (1), а theorem `riemannZeta_residue_one` контролирует предел ((s-1)\zeta(s)\to1). ([Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html?utm_source=chatgpt.com))

## Новый task

```text
EStarMuntzZeroMassContinuation_Standalone_v3_PoleSubtracted
```

T1–T3 и 032 не переписывать.

## Mellin quotient

Пусть

[
M_h(w)=\operatorname{Mellin}(h)(w).
]

Определить:

```lean
noncomputable def MellinDivOne (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  dslope (Mellin h) 1 w
```

Доказать:

[
\operatorname{MellinDivOne}(1)=M_h'(1),
]

а при (w\ne1):

# [ \operatorname{MellinDivOne}(w)

\frac{M_h(w)-M_h(1)}{w-1}.
]

Из zero mass (M_h(1)=0):

# [ \operatorname{MellinDivOne}(w)

\frac{M_h(w)}{w-1}.
]

Главный target:

```text
MellinDivOne analytic on {w | 0 < re w}.
```

## Residue-removed zeta factor

Определить не raw (\zeta), а extension:

```lean
noncomputable def ZetaResidueFactor (w : ℂ) : ℂ :=
  Function.update
    (fun z => (z - 1) * riemannZeta z)
    1
    1
```

Доказать:

[
Z_1(1)=1,
]

[
w\ne1
\Longrightarrow
Z_1(w)=(w-1)\zeta(w),
]

и аналитичность (Z_1) на (\Re w>0).

В точке (1):

1. `riemannZeta_residue_one` даёт continuity updated factor;
2. вне (1) используется differentiability zeta;
3. затем removable-singularity theorem.

Разрешён existential witness вместо `Function.update`, если он несёт поля:

```text
analyticOn
value_one = 1
eq_raw_factor for w != 1
```

## Pole-subtracted product

```lean
noncomputable def ZetaMellinPoleSub
    (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  ZetaResidueFactor w * MellinDivOne h w
```

Доказать:

[
\operatorname{ZetaMellinPoleSub}
]

аналитична на (\Re w>0);

при (w\ne1):

# [ \operatorname{ZetaMellinPoleSub}(w)

\zeta(w)M_h(w);
]

в точке (w=1):

# [ \boxed{ \operatorname{ZetaMellinPoleSub}(1)

M_h'(1).
}
]

Никакого равенства с raw Mathlib expression

```lean
riemannZeta 1 * Mellin h 1
```

не формулировать.

------

## Исправленный T5

Из absolute-region identity при (\Re s>1/2) вывести для всех

[
\Re s>-\frac12:
]

# [ \boxed{ G_{\rm win}(s)

## \operatorname{ZetaMellinPoleSub} \left(s+\frac12\right)

R^-(s)-R^+(s).
}
]

Затем два разных corollary.

### Punctured raw-product corollary

Только при

[
s\ne\frac12:
]

# [ G_{\rm win}(s)

## \zeta(s+\tfrac12)M_h(s+\tfrac12)

R^-(s)-R^+(s).
]

### Pole-value corollary

В точке

[
s=\frac12:
]

# [ \boxed{ G_{\rm win}(\tfrac12)

## M_h'(1)

## R^-(\tfrac12)

R^+(\tfrac12).
}
]

Это и есть честная replacement theorem.

------

## Plants для v3

### PL1 — positive mass

Старый positive-mass triangular plant сохраняется и должен показывать (\lambda^\sigma)-рост.

### PL2 — raw-value mismatch

Для zero-mass difference of triangular bumps с

[
M_h'(1)<0
]

доказать:

# [ \operatorname{ZetaMellinPoleSub}(1)

M_h'(1)\ne0.
]

Любая попытка присвоить continuation value (0) должна падать.

### PL3 — factor cancellation

Удаление:

- ((w-1)) из zeta factor; или
- деления на ((w-1)) из Mellin quotient

обязано ломать off-pole equality.

## Новые коды

Ровно один:

```text
ESTAR_MUNTZ_POLE_SUBTRACTED_CONTINUATION_PROVED
MELLIN_DSLOPE_ANALYTICITY_GAP
ZETA_RESIDUE_FACTOR_EXTENSION_GAP
IDENTITY_THEOREM_GLUE_GAP
RIEMANN_SUM_BOUNDARY_CELL_GAP
```

Вагонный код `ZETA_POLE_API_GAP` больше не использовать: он смешивает два независимых фронта.

## Imports/API

```text
Mathlib.Analysis.Calculus.DSlope
Mathlib.Analysis.Analytic.IsolatedZeros
Mathlib.Analysis.Complex.RemovableSingularity
Mathlib.NumberTheory.LSeries.RiemannZeta
```

Validation:

```text
lake env lean <touched-file>
lake build
grep sorry/admit/axiom/native_decide <touched-files>
#print axioms <all new T4/T5 declarations>
```

Требуемый профиль:

```text
[propext, Classical.choice, Quot.sound]
```

------

## META CLOSEOUT

- **Стало меньше:** 239 полос сведены к одному (\varepsilon_r)-ledger; zeta-pole разложен на два аналитических фактора.
- **Убито:** немедленное S1 из 031+022; raw `ζ·Mellin` в полюсе; новая depth/precision ladder.
- **Не повторять:** 022 как continuum proof, (r\varepsilon_\Psi), назначение removable value декларацией.
- **Smallest gaps:** `033_FullWindowCoupledPositivePartBudget`; `ZetaResidueFactorExtension`.
- **Fate predictions:** R1, R2, R3 подтверждены; R4 подтверждён scope-ом.
- **Progress class:** `PROOF_PROGRESS + REPRESENTATION_PROGRESS`.
- **Route score:** `5/5`.

[Полный единый markdown-контракт для шины](sandbox:/mnt/data/PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md)