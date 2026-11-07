# STATUS: TRY_C_LONG_ODD_FOLD_AND_STRIP_O

```yaml
OPERATIVE_CLASS: TRY_C_LONG_ODD_FOLD_AND_STRIP_O
DATE: 2026-11-07
AUTHORITY: OWNER_PROVE_C_LONG_LE_X_TO_ONE_HALF_PLUS_ETA
INPUT_COMMIT: 45afff3806bd7671919f5330830b246b1229c75c
INPUT_BLOB: 27168a1a764b5254b53d87e5772673017b7f5d37
INPUT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
OBSERVED_EXISTING_FREEZE: 5393c758e76d78a1668d3a0b787aede3cf66f0d9
EXISTING_FREEZE_NOT_OVERWRITTEN: true
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_C_LONG_ODD_FOLD_2026-11-07_O.md
TARGET_BOUND_PROVED: false
FIRST_SOURCE_POWER_GAIN: NOT_OBTAINED
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
FULL_RH_ACCEPTANCE: NOT_COMPLETE
PROVED_STEPS:
  - {id: C_LONG_POWER_EXPONENT_EQUIVALENT_TO_FIXED_ZERO_FREE_HALF_PLANE, scope: COFINAL_FAMILY, verifier: PAPER, note: EQUIVALENCE_NOT_ITS_UNPROVED_PREMISE}
  - {id: BACKWARD_DYADIC_LOG_BUDGET_LE_12_LOG_FOURTH, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_ODD_DIVISOR_FOLD_WITH_ALL_TWO_POWERS, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: FOLDED_ACTIVE_BLOCK_POSITIVE_LOWER_ENVELOPE, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: NONZERO_MELLIN_RESIDUE_SURVIVES_THE_EXACT_FOLD, scope: ABSTRACT, verifier: PAPER}
  - {id: EXPLICIT_SUBEXPONENTIAL_FULL_C_LONG_UPPER_ENVELOPE, scope: COFINAL_FAMILY, verifier: PAPER, import: JOHNSTON_YANG_THEOREM_1_4}
RH_GAP: NO_SOURCE_SPECIFIC_COFINAL_POWER_BOUND_FOR_THE_FULL_SIGNED_FORM
REQUESTED_GAP: FOR_EVERY_ETA_POSITIVE_C_LONG_X_LE_C_ETA_X_TO_ONE_HALF_PLUS_ETA_ON_ALL_LATE_DYADIC_X
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: EXACT_FOLD_LOCAL_LOWER_ENVELOPE_AND_TRANSFER_THEOREMS_ONLY
RH_SIGN_PROGRESS: NONE
TARGET_EXPONENT_PROGRESS: NONE
KILLS: []
CLOSES: [ODD_FOLD_SOURCE_RETURN, FOLDED_ACTIVE_BLOCK_SIGN, EXACT_STRENGTH_OF_REQUESTED_EXPONENT]
OPENS: []
COGNITIVE_OPERATOR: EXACT_EULER_FACTOR_FOLD_AND_POLE_DISCRIMINATOR
ROUTE_SCORE: 1
DISCRIMINATOR: NONZERO_MELLIN_RESIDUE_NOT_FINITE_NUMERICAL_SMALLNESS
EXACT_TESTS: {formal_source_cells: 982, kernel_pairs: 2334, signed_quadratic_forms: 100}
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **Запрошенную оценку я не доказал.** Выполнена новая арифметическая попытка: точное объединение делителей `d` и `2d`, до модулей и с настоящей μ. Оно полностью оплачивает вклад степеней двойки, но оставляет явно положительный подписанный блок. Независимой верхней оценки полной формы из этой операции не получилось.

Ниже — доказательства того, что действительно получено. В частности, точная сила поставленной цели установлена в обе стороны:

\[
\boxed{\begin{gathered}
\forall\eta>0:\quad C_{\rm long}(X)\ll_\eta X^{1/2+\eta}
\quad\text{на всех поздних диадических }X\\
\Longleftrightarrow\quad
\zeta(s)\ne0\quad(\Re s>3/4).
\end{gathered}}                                                     \tag{O1}
\]

Это **доказанная эквивалентность, а не доказательство любой из двух её сторон**. Получение самой оценки было бы первым настоящим степенным выигрышем. Для RH затем нужен дополнительный шаг, продолжающий улучшать показатель. Более сильный feedback из M(23) и слабее сформулированная нынешняя цель не смешиваются.

## 1. Источник, импорты и область

[FINITE_CELL | PAPER для source-lock; импорты ниже — THEOREM, не новые результаты.]

M прочитан через GitHub по указанному коммиту; connector вернул именно blob `27168a1a764b5254b53d87e5772673017b7f5d37`. Из M наследуются только его определения и доказанные (14)–(16), не открытая оценка (23). Проверен также K, commit `06238eb5dd6d06887d9b088aca089fdb3c05b9cc`, файл `PROSHKA_VERDICT_CRITICAL_DYADIC_FLUX_2026-11-07_K.md`, blob `cd777de92a512c2bb1f5cbb1aedbc38fa83d8757`: критическое телескопирование уже было известно; оно не заявляется новым механизмом.

Протокол и Pappus skill получены заново. Просмотрены конструктор `docs/routeB_bus/mythos/ROUTE_B_CONSTRUCTOR_PROVEN_2026-11-06.md` и свежие inbox-коммиты. Обнаружен существующий freeze N: `PROSHKA_FREEZE_LOW_FREQUENCY_FEEDBACK_2026-11-07_N.md`, commit `5393c758…`, blob `256a47d2d08064771712c62718e98072b41e3395`. Его Fourier-проекция здесь не дублируется и файл не изменяется. Поиск PAIRED_SCALE не дал результатов; это не исчерпывающий аудит. Попытка прочитать closing plan под `docs/routeB_bus/mythos/ROUTE_B_CLOSING_PLAN_2026-11-02.md` вернула 404; полного аудита старых журналов не заявляю.

Внешние импорты:

- **W1, THEOREM:** DLMF 25.16.3 — качественная PNT; 25.16.4 — RH-критерий. PNT используется только для исчезновения терминального члена.
- **W2, THEOREM:** DLMF 27.4.3, 27.4.5, 27.4.12 — ряды ζ, 1/ζ, −ζ′/ζ в полуплоскости абсолютной сходимости. Мероморфное продолжение и функциональное уравнение — стандартные свойства ζ; см. DLMF 25.4. Контурный обратный переход в §3.3 расписан, не принимается как новая гипотеза.
- **W3, THEOREM:** Johnston–Yang, arXiv:2204.01980v2, Theorem 1.4, equation (1.7), PDF p.2: явная безусловная оценка ψ. Формула и область `x≥23` проверены по screenshot страницы. Это импорт опубликованного результата, не независимая перепроверка всех его вычислительных зависимостей. Рекордность констант не заявляется.

```text
W1 https://dlmf.nist.gov/25.16
W2 https://dlmf.nist.gov/27.4
   https://dlmf.nist.gov/25.4
W3 https://arxiv.org/pdf/2204.01980v2
   Daniel R. Johnston and Andrew Yang,
   Some explicit estimates for the error term in the prime number theorem.
```

Далее `X=2^j≥8`, `D=4X`, логарифмы натуральные. Как в M,

\[
S(x)=\sum_{x/2<n\le x}(\Lambda(n)-1),\qquad
A(X)=X^{-2}\int_X^{2X}S(x)^2\,dx,
\]
\[
F(X)=A(X)-\tfrac12 A(2X)=C_{\rm long}(X)+R_X,
\quad |R_X|\le B(X),                                  \tag{O2}
\]
\[
B(X)=\tfrac32(1+\log(4X))^2+\tfrac34(1+\log X)^4.
\]

Для полного восстановления M(16) можно взять

\[
a_1=-1,\quad a_d=-\mu(d)\log d\ (d\ge2),\quad
N_d(x)=\lfloor x/d\rfloor-\lfloor x/(2d)\rfloor,\quad
r_d(x)=N_d(x)-x/(2d),
\]
\[
\rho_{de}=\frac{4\gcd(d,e)^2-\gcd(2d,e)^2-\gcd(d,2e)^2}{24de},
\quad J_d=\int_X^{2X}xr_d(x)dx-\tfrac18\int_{2X}^{4X}xr_d(x)dx,
\]
\[
\mathcal B_X(d,e)=\int_X^{2X}r_dr_e\,dx-
 \tfrac18\int_{2X}^{4X}r_dr_e\,dx-\tfrac{3X}{4}\rho_{de},
\]
\[
c_D=\sum_{d\le D}a_d/d,\quad J_D=\sum_{d\le D}a_dJ_d,\quad
B_>=\sum_{\substack{d,e\le D\\\operatorname{lcm}(d,e)>X}}
 a_da_e\mathcal B_X(d,e),\quad
C_{\rm long}=X^{-2}(c_DJ_D+B_>).
\]

`C_long` — буквально M(16), включая `c_D J_D`; определение не заменяется. Все простые степени сохранены. Норма, два физических окна, коэффициент `1/8` перед ненормированной второй энергией и все поздние диадические масштабы неизменны.

## 2. Обратное телескопирование с явной ценой

[COFINAL_FAMILY | PAPER.]

**Лемма.** Если для некоторого `0≤a<1`, `K≥0` и всех диадических `Y≥X₀` выполнено

\[
C_{\rm long}(Y)\le K Y^a,
\]

то для каждого диадического `X≥max(8,X₀)`

\[
\boxed{A(X)\le\frac{K X^a}{1-2^{a-1}}
                 +12(1+\log(4X))^4.}                 \tag{O3}
\]

**Доказательство.** Конечное, до всякого перехода к пределу, равенство:

\[
A(X)=2^{-r}A(2^rX)
  +\sum_{k=0}^{r-1}2^{-k}\bigl(C_{\rm long}(2^kX)+R_{2^kX}\bigr).
                                                               \tag{O4}
\]

Из W1 следует `S(x)=o(x)` и `A(Y)=o(Y)`. Поэтому первый член стремится к нулю при фиксированном X. Требование `o(Y)`, а не просто `O(Y)`, здесь существенно.

Для логарифмической суммы положим `L=1+log(4X)`, `h=log2`. При `X≥8` имеем `h/L<1/6`, а

\[
\sum_{k\ge0}2^{-k}B(2^kX)
 \le\tfrac94L^4\sum_{k\ge0}2^{-k}(1+k/6)^4
 =\frac{355}{32}L^4<12L^4.                             \tag{O5}
\]

Использованы точные моменты `Σ2⁻ᵏ=2`, `Σk2⁻ᵏ=2`, `Σk²2⁻ᵏ=6`, `Σk³2⁻ᵏ=26`, `Σk⁴2⁻ᵏ=150`. Степенная сумма — геометрическая с отношением `2^(a−1)<1`. Получается (O3). Достаточна односторонняя верхняя оценка: нижний знак C_long не предполагался. ∎

Обратно, из неотрицательности A(2X) и (O2) сразу

\[
 C_{\rm long}(X)\le A(X)+B(X).                         \tag{O6}
\]

Следовательно, для любого `0≤α<1` семейства оценок `C_long≪εX^(α+ε)` и `A≪εX^(α+ε)` эквивалентны. В прямом переходе выбирается достаточно малое `ε` с `α+ε<1`; большие ε затем следуют автоматически. Это устраняет проблему критического хвоста, но не даёт исходную верхнюю оценку.

## 3. Точный спектральный смысл показателя

[COFINAL_FAMILY | PAPER для эквивалентности; её неподтверждённые стороны не объявляются THEOREM.]

Для `0≤α<1` положим `θ=(1+α)/2`. Тогда

\[
\boxed{C_{\rm long}(X)\ll_\varepsilon X^{\alpha+\varepsilon}
\ (\forall\varepsilon>0)
\quad\Longleftrightarrow\quad
\zeta(s)\ne0\ (\Re s>\theta).}                         \tag{O7}
\]

### 3.1. Энергия исключает любой правый полюс — без «правейшего нуля»

При `Re s>1` абсолютная сходимость даёт исходный Mellin-transform:

\[
 H(s):=\int_1^\infty S(x)x^{-s-1}\,dx
 =\frac{1-2^{-s}}s\left(-\frac{\zeta'(s)}{\zeta(s)}-\zeta(s)\right).
                                                               \tag{O8}
\]

Действительно, вклад одного n интегрируется по `[n,2n)`. Член `−ζ`, а не произвольное непрерывное центрирование, возвращает ровно исходный `−1`.

На каждом диадическом окне Cauchy–Schwarz даёт

\[
 \int_X^{2X}|S(x)|x^{-\sigma-1}\,dx
 \le\sqrt{A(X)}X^{1/2-\sigma}.                        \tag{O9}
\]

Если `A(X)≪εX^(α+ε)` для всех ε, геометрическое суммирование с `ε<2σ−1−α` даёт абсолютную, локально равномерную сходимость (O8) в `Re s>θ`. Поэтому H голоморфна там. При `s=1` два главных полюса правой части сокращаются.

У любого нуля `ρ`, кратности m, с `Reρ>θ` правая часть имела бы вычет

\[
\boxed{\operatorname{Res}_{s=\rho}H(s)
       =-\frac{m(1-2^{-\rho})}{\rho}\ne0.}             \tag{O10}
\]

Неравенство следует из `|2^(-ρ)|<1`. Противоречие с голоморфностью. Никакого предположения о простоте нуля, существовании максимального β или разделённости ординат не нужно.

### 3.2. Один нуль убивает все предполагаемые верхние оценки данного порядка

Как непосредственное следствие: если настоящий нуль имеет `β>1/2`, то для каждого `0≤a<2β−1`

\[
\boxed{\limsup_{\substack{X\to\infty\\X=2^j}}
       \frac{C_{\rm long}(X)}{X^a}=+\infty.}           \tag{O11}
\]

Иначе существовала бы конечная поздняя верхняя граница, и (O3), (O9), (O10) исключили бы этот нуль. Это условное следствие существования нуля, не заявление, что такой нуль существует. Другие нули не могут «спасти» противоречащий ему cofinal-bound: вычет локален.

### 3.3. Обратное направление, включая несглаженный источник

Предположим `ζ(s)≠0` при `Re s>θ`. Фиксируем `θ<σ<1`. Покажем

\[
 \psi(x)-x=O_\sigma(x^\sigma\log^2(2x)).              \tag{O12}
\]

Нужная для контура оценка `ζ′/ζ(σ+it)=Oσ(log(|t|+2))` следует непосредственно из zero-free предположения. Вот её обоснование. В `Re s>0`

\[
\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{u\}u^{-s-1}\,du.
\]

Поэтому на фиксированной вертикальной полосе с положительной левой границей ζ имеет полиномиальный рост. Возьмём `θ<σ₀<σ` и диск с центром `2+it`, радиусом `2−σ₀`. При `|t|≥3` в нём нет ни нулей, ни полюса. Выберем аналитическую ветвь logζ, нормированную Euler-product значением в центре, которое ограничено. Borel–Carathéodory на меньшем диске даёт `logζ=Oσ(log|t|)`; Cauchy для производной — требуемую оценку, равномерную при `σ≤Re s≤2`. Компактный участок самой прямой `Re s=σ` без нулей оплачивается отдельной константой.

Для полуцелого `y≥3` берём `c=1+1/log y`, `T=y²`. Конечная Perron-формула даёт

\[
 \psi(y)=\frac1{2\pi i}\int_{c-iT}^{c+iT}
       -\frac{\zeta'(s)}{\zeta(s)}\frac{y^s}{s}\,ds
       +O\left(\frac{y\log^2y}{T}\right).             \tag{O13}
\]

Остаток можно проверить без гипотез о простых: применить стандартную оценку обрезанного Perron-ядра
`O((y/n)^c min(1,1/(T|log(y/n)|)))`, использовать `Λ(n)≤log n`, а при `y/2<n<2y` — расстояние `|n−y|≥1/2`. Ближняя гармоническая сумма и два дальних хвоста каждый дают `O(y log²y/T)`.

Сдвигаем контур на `Re s=σ`. Пересекается только полюс при 1 с вкладом y. Новая вертикаль стоит `Oσ(y^σ log²T)`; горизонтали — `Oσ(y log T/T)`. Это доказывает (O12) для полуцелых. Для любого действительного x берём `y=floor(x)+1/2`; тогда `ψ(y)=ψ(x)` и `|y−x|≤1/2`, так что оценка сохраняется. Несглаживание не потеряло степени.

Из (O12) следует `S(x)=Oσ(x^σ log²(2x))` и `A(X)=Oσ(X^(2σ−1)log⁴X)`. Выбирая σ сколь угодно близко к θ и используя (O6), получаем обратную сторону (O7). ∎

Для нынешней цели `α=1/2`, поэтому получается ровно `θ=3/4`, с допустимыми нулями на границе. Вместе с функциональным уравнением это ограничивает нетривиальные нули замкнутой полосой `[1/4,3/4]`; критическая линия ещё не получена.

## 4. Новая арифметическая попытка: полное объединение d и 2d

[COFINAL_FAMILY | PAPER; все действительные `x≥2`.]

Пусть

\[
 N_d(x)=\lfloor x/d\rfloor-\lfloor x/(2d)\rfloor,
 \qquad w_d(x)=N_d(x)-N_{2d}(x).
\]

Тогда точно

\[
\boxed{S(x)=\log2-N_1(x)
        -\sum_{\substack{d\le x\\d\ \mathrm{odd}}}
             \mu(d)\log d\,w_d(x).}                   \tag{O14}
\]

**Доказательство.** Если d нечётно, `μ(2d)=−μ(d)`; если `4|d`, то `μ(d)=0`. Поэтому делительные коэффициенты для Λ объединяются в

\[
 -\mu(d)\log d\,N_d
 +\mu(d)(\log d+\log2)N_{2d}
 =-\mu(d)\log d\,w_d+\log2\,\mu(d)N_{2d}.
\]

Далее

\[
 \sum_{d\ \mathrm{odd}}\mu(d)N_d(y)=1\qquad(y\ge1),       \tag{O15}
\]

поскольку сумма μ по нечётным делителям n равна единице ровно для степеней двойки, а в `(y/2,y]` содержится ровно одна степень `2^k`, `k≥0`. Подставляя `y=x/2`, получаем (O14). Отдельный `−N₁` возвращает исходное целочисленное центрирование. ∎

Это реальное точное сокращение: все чётные squarefree-делители включены, все степени двойки дают ровно `log2`. Однако две энергии надо строить из **полного** выражения `U(x)+log2−N₁(x)`, где U — сумма в (O14). Отбросить линейные взаимодействия с `log2−N₁` означало бы снова потерять компенсацию M(16).

### 4.1. Подписанный активный блок после свёртки остаётся положительным

Положим `b=floor(4X/3)`, `I=(X,b]∩ℕ`. Для любых `d,e∈I`, не обязательно нечётных, определим

\[
 K_X(d,e)=\int_X^{2X}w_dw_e\,dx
               -\tfrac18\int_{2X}^{4X}w_dw_e\,dx.
\]

Прямое вычисление даёт

\[
\boxed{K_X(d,e)=\frac{14X-2\min(d,e)-5\max(d,e)}8.}     \tag{O16}
\]

Но важнее **подписанная**, а не поэлементная форма. Для любых действительных `c_d` с носителем I положим

\[
 P(t)=\sum_{X<d\le t}c_d,\qquad T=P(b).
\]

Тогда

\[
\boxed{\sum_{d,e\in I}c_dc_e K_X(d,e)
 =\tfrac38\int_X^b P(t)^2dt
   +\tfrac12T\int_X^bP(t)dt
   +\tfrac78(2X-b)T^2}                                \tag{O17}
\]

и, следовательно,

\[
\boxed{\sum_{d,e\in I}c_dc_e K_X(d,e)
 \ge\tfrac14\int_X^b P(t)^2dt+\tfrac5{12}XT^2\ge0.}   \tag{O18}
\]

**Доказательство.** На первом окне `w_d=1_{x≥d}`. На втором

\[
 w_d=1+1_{x\ge3d}-1_{x\ge2d}.
\]

Отсюда первая энергия равна `∫P²+(2X−b)T²`, вторая —

\[
 2\int_X^b(T-P)^2dt+3\int_X^bP^2dt+(4X-3b)T^2.
\]

Вычитание с коэффициентом 1/8 даёт (O17). Неравенство
`TP/2 ≥ −P²/8−T²/2` и `b≤4X/3` дают (O18). Для (O16) достаточно применить тот же расчёт к двум координатам. ∎

Это строгая **нижняя огибающая** блока после полной знаковой сборки. Даже при `T=0` остаётся `3/8∫P²`. Поэтому просто сгруппировать арифметически связанные делители и надеяться на исчезновение всей активной энергии нельзя. Однако (O18) не является нижней оценкой полной C_long: вне блока остались смешанные члены, фон и отрицательная вторая энергия. **Ни целевая оценка, ни весь signed-маршрут этим не опровергнуты.**

### 4.2. Проверка механизма по Mellin, не по названию

При `Re s>1` положим

\[
 h(s)=1-2^{-s},\qquad
 M_o(s)=\sum_{d\ \mathrm{odd}}\mu(d)d^{-s}
       =\frac1{h(s)\zeta(s)}.
\]

Mellin-transform `w₁` равен `h(s)²ζ(s)/s`. Поэтому transform U из (O14) равен

\[
 M_o'(s)\frac{h(s)^2\zeta(s)}s
 =-\frac{h'(s)}s-\frac{h(s)}s\frac{\zeta'(s)}{\zeta(s)}.
\]

Глобально постоянный член (O14) имеет вид `log2·1_{x≥2}`; его transform равен `h′(s)/s`. Они сокращаются точно. Добавление `−N₁` возвращает (O8), с тем же ненулевым вычетом (O10). Значит, свёртка не спрятала полюс возможного правого нуля и не создала нового степенного множителя.

## 5. Верхняя огибающая всей исходной величины, действительно полученная без гипотез

[COFINAL_FAMILY | PAPER; все диадические `X≥64`; используется W3.]

Определим

\[
 g(u)=u^{3/5}(\log u)^{-1/5},\qquad
 E_X=\exp[-0.3706\,g(\log(X/2))].
\]

Из Theorem 1.4 Johnston–Yang следует

\[
\boxed{C_{\rm long}(X)\le
 0.0071\,X(\log(2X))^{3.602}E_X
 +\frac1{2X}+B(X).}                                   \tag{O19}
\]

**Доказательство.** Импортированная оценка для `t≥23`:

\[
 |\psi(t)-t|\le0.026\,t(\log t)^{1.801}
                e^{-0.1853g(\log t)}.
\]

При `x∈[X,2X]` оба аргумента x и x/2 не меньше 32. Функция g возрастает на нужном диапазоне: `g′/g=(3−1/log u)/(5u)>0`. Поэтому, обозначая

\[
 q_X=(\log(2X))^{1.801}e^{-0.1853g(\log(X/2))},
\]

получаем `|S(x)|≤0.039 x q_X+1/2`. Последняя половина — точная граница целочисленного центрирования, поскольку `|x/2−N₁(x)|≤1/2`. Тогда

\[
 A(X)\le\frac{14}{3}(0.039)^2Xq_X^2+\frac1{2X}
       =0.007098\,Xq_X^2+\frac1{2X}.
\]

Применяем (O6) и округляем коэффициент вверх. ∎

(O19) даёт, например, `C_long(X)≪_B X/log^B X` для каждого фиксированного B, но это перенос уже известной субэкспоненциальной PNT-оценки. **Нового степенного выигрыша нет.** Для любого фиксированного `0<η<1/2` отношение выписанной положительной мажоранты к `X^(1/2+η)` стремится к бесконечности. Это недостаточность мажоранты, не отрицание целевой оценки.

## 6. Сильнейшая атака, Pappus и точное место остановки

[ABSTRACT | PAPER для логических проверок; независимый знак полного источника не получен.]

**Атака на собственный результат.** Можно ошибочно назвать (O7) доказательством цели, (O18) запретом цели или (O19) степенной экономией. Ни один из этих выводов не следует. (O7) — калибровка силы; (O18) — только главный блок; (O19) имеет показатель `1−o(1)`.

Отрицательный контроль — ненулевой вычет (O10). Подсаженный источник с правым полюсом `β>3/4` несовместим с заявленной целью по (O9)–(O10), независимо от остальных полюсов. Полюс с `1/2<β≤3/4` эта цель сама по себе не исключает. При замене ζ на другую функцию надо изменить source и сохранить её полный logarithmic derivative; обычная μ не подставляется за DH/Beurling коэффициенты. Для положительного function-field контроля арифметический счёт должен оставаться собственным: при Frobenius-данных `α₁=i√3`, `α₂=−i√3` его ошибки `−α₁ⁿ−α₂ⁿ` ограничены `2·3^(n/2)`, то есть критический энергетический показатель равен нулю. Это алгебраическая проверка спектрального приёмника, не перенос обычных floor-формул и не новый аудит геометрического RH. Полная внешняя acceptance-проверка не заявлена.

Цепочка назад:

\[
 RH\ \Leftarrow\ [A(X)\ll_\varepsilon X^\varepsilon]
 \ \Leftarrow\ [\text{повторяемое уменьшение показателя}]
 \ \Leftarrow\ [\text{независимый signed-bound источника}].
\]

Нынешняя цель оплачивает только первый переход `1→1/2` для показателя A. Если отдельно доказать более сильный M(23), то из показателя a получится `a/2+ε`, и итерация достигнет нуля. Доказательство одной фиксированной степени **не разрешает** повторно применять её как функцию уже улучшенной энергии.

Таблица цены именно этой попытки:

| Кусок | Цена | Результат |
|---|---:|---|
| Перегруппировка d,2d | 0 | Точное тождество (O14) |
| Все степени двойки | log 2 | Точный постоянный вклад |
| Полный R из M | log⁴X | Уже оплачен; (O5) даёт возврат |
| Активный folded-блок | Сохранилась положительная энергия (O18) | Нет нужной верхней цены |
| Полная signed-форма с фоном и хвостом | Нужна ненормированная цена X^(5/2+η) | Не получена |

Операция сделала конкретный блок явно вычислимым, но не уменьшила трудность оставшейся верхней оценки. Поэтому эта попытка не продолжается повторными модулями и новыми сетками.

Две допустимые альтернативные репрезентации с точным обязательством, а не объявленные решения:

**A. Взвешенный Nyman–Beurling на границе 3/4.** Искать конечные Dirichlet-полиномы `P_N(s)=Σc_n n^(−s)`, `P_N(1)=0`, для которых

\[
 f_N(s)=\frac{1-\zeta(s)P_N(s)}s\in H^2(\Re s>3/4),
 \qquad \|f_N\|_{H^2}\longrightarrow0.
\]

Норма здесь `sup_(σ>3/4)(2π)⁻¹∫|f_N(σ+it)|²dt`. Условие в 1 убирает полюс. Любой правый нуль ρ даёт точную obstruction
`||f_N||²≥2(Reρ−3/4)/|ρ|²` через bounded point evaluation. Значит, такой cofinal-сертификат влечёт (O1). Его отличие от фиксированной μ — свобода выбора коэффициентов; он не объявлен обязательным методом. Различающая сила: один предел отвергает все правые нули. Цена: конечная квадратичная оптимизация плюс всё ещё недоказанный равномерный предел; аналитическая стоимость высокая. Это вариант известного receiver, не новое доказательство его посылки.

**B. Прямой logarithmic-derivative contour.** Доказать для каждого δ>0 отсутствие полюсов `−ζ′/ζ` и полиномиальный контроль на всей замкнутой полуплоскости `Re s≥3/4+δ`, с отдельно удалённым полюсом в 1. Тогда §3.3 возвращает нужную несглаженную оценку без делительного ядра. Цена: арифметический zero-exclusion на всех высотах, очень высокая; различающая сила максимальна, поскольку один ненулевой residue непосредственно запрещён. Это не облегчение само по себе. Уже замороженный Fourier-вариант N остаётся отдельной попыткой и здесь не переименовывается в новый план.

Минимальное недостающее утверждение на выбранном источнике осталось буквально целью владельца:

\[
\forall\eta>0\ \exists K_\eta,X_\eta\ \forall X=2^j\ge X_\eta:
\quad c_{4X}J_{4X}(X)+B_{>}(X)\le K_\eta X^{5/2+\eta}. \tag{O20}
\]

Его не надо выдавать за более простое только потому, что эквивалентности теперь полностью расписаны.

## 7. Проверки, прогнозы и closeout

[FINITE_CELL | PAPER для конечной точной алгебры; доказательства cofinal-утверждений — выше, не следствия сетки.]

До вычислительной проверки зарегистрированы P1–P5; предварительная карандашная алгебра уже предлагала формулы, поэтому прогнозы не называются слепыми. Проверки выполнены на `X=8,16,32,64,128`.

- P1 **HIT:** показатель цели даёт границу 3/4, не сразу 1/2; доказательство §2–3.
- P2 **HIT:** 982 source-ячейки проверены как равенства целых коэффициентов при формальных `log p` и отдельной константе. Ни floating point, ни гипотеза независимости этих логарифмов не использованы для вывода равенства.
- P3 **HIT:** 2334 точные пары ядра, 100 подписанных квадратичных форм; совпадение с (O16)–(O18). Неправильный коэффициент `1/4` вместо `1/8` намеренно обнаружен.
- P4 **HIT:** аналитический расчёт §4.2 возвращает тот же ненулевой вычет; пропуск `log2` обнаруживается уже при `x=2`.
- P5 **NOT_PROVED:** независимая целевая верхняя оценка не получена. Успех P1–P4 не засчитывается как успех P5.

Точная цена суммирования логарифмов — `355/32<12`. На объявленной сетке используемая целочисленная арифметика заведомо помещается в int64; дробные равенства проверяются `Fraction`. Нет тестов вида «число достаточно близко к нулю». DISCRIMINATOR для тождеств — ненулевой целый коэффициент; для полного cofinal-знака — (O10), а не численная малость.

**Что приблизилось к RH:** устранена неоднозначность силы конкретной цели, выполнен ещё один точный арифметический fold и установлен знак его блока. **Что не приблизилось:** первый показатель полной энергии не улучшен. Исторический приоритет этих алгебраических наблюдений не заявляется.

```yaml
iteration:
  target: C_LONG_LE_X_TO_ONE_HALF_PLUS_ETA
  status: OPEN
  cognitive_operator_used: EXACT_ODD_DIVISOR_FOLD_AND_POLE_DISCRIMINATOR
  new_gap_name: UNCHANGED_FULL_SIGNED_COARSE_POWER_BOUND
  invariant_learned: EXACT_EULER_FACTOR_FOLD_PRESERVES_NONZERO_ZERO_RESIDUES
  forbidden_future_move: CALL_LOCAL_BLOCK_OR_SUBEXPONENTIAL_PNT_A_COFINAL_POWER_GAIN
  next_decisive_test: INDEPENDENT_SOURCE_UPPER_ENVELOPE_BELOW_X_TO_ONE_HALF_PLUS_ETA
  route_score: 1
```

## 8. Dependency epistemics и доставка

Для долга (O20):

```yaml
DOWNSTREAM_CONSUMER: FIRST_GLOBAL_POWER_GAIN_THEN_A_SEPARATE_REPEATABLE_STEP_TO_RH
ACTUAL_CONSUMER_REQUIREMENT: COMPLETE_SOURCE_ONE_SIDED_BOUND_ON_ALL_LATE_DYADIC_SCALES
ORIGINAL_REQUESTED_OBJECT: C_LONG_LE_X_TO_ONE_HALF_PLUS_ETA
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
ORIGINAL_OBJECT_NOTE: LOGICAL_CONSEQUENCE_OF_RH_BY_O7_NOT_A_MANDATORY_PROOF_METHOD
KNOWN_WEAKER_INTERFACES:
  - WEIGHTED_HARDY_APPROXIMATION_AT_THREE_QUARTERS_IMPLIES_ZERO_EXCLUSION_IMPLIES_TARGET
  - DIRECT_ZERO_EXCLUSION_IMPLIES_TARGET_BY_O12_O13
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: EXACT_ODD_FOLD_AND_ITS_SIGNED_ACTIVE_BLOCK_NOT_A_NEW_ZERO_FREE_REGION
REOPEN_TRIGGER: AN_INDEPENDENT_FULL_SOURCE_BOUND_OR_A_FLAW_IN_THE_PINNED_IDENTITIES
KILL_SCOPE: NONE
```

Ни RH, ни поставленная цель, ни класс совместных signed-оценок не объявлены мёртвыми. Неуспех нынешнего supplier — исследовательский долг.

Записывается только этот новый Markdown под `docs/routeB_bus/` в `proshka_inbox_2026-10-31`. Старые документы, freeze N, state-файлы и Lean не меняются. Commit и blob сообщаются в квитанции после записи и readback; самореферентный commit в собственное содержимое не вставляется. Внешний независимый аудит и Lean/Arb не выполнялись.

## Приложение. Воспроизводимый точный тест

Сохрани следующий блок в `verify_c_long_fold.py`, выполни `uv run --with numpy verify_c_long_fold.py`. Подстановок не требуется. `X` — диадический масштаб из фиксированной сетки; `D=4X` — предел исходных коэффициентов; `ds` — активные делители; `K8` — матрица `8K_X`; `C` — значения P на единичных ячейках; `T` — сумма коэффициентов. JSON записывается рядом со скриптом. Проверяется конечная алгебра, не (O20).

```python
from __future__ import annotations
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path
import time
import numpy as np


def sieve(n: int):
    mu = np.ones(n + 1, dtype=np.int64)
    mu[0] = 0
    prime = np.ones(n + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, n + 1):
        if prime[p]:
            prime[p*p::p] = False
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
    ps = np.flatnonzero(prime).tolist()
    return mu, ps


def formal_source_check(X: int):
    D = 4 * X
    mu, primes = sieve(D)
    idx = {p: j + 1 for j, p in enumerate(primes)}
    logs = np.zeros((D + 1, len(primes) + 1), dtype=np.int64)
    lam = np.zeros_like(logs)
    for p in primes:
        q = p
        while q <= D:
            logs[q::q, idx[p]] += 1
            lam[q, idx[p]] = 1
            q *= p
    prefix = np.cumsum(lam, axis=0)
    odds = np.arange(1, D + 1, 2)
    tests = 0
    for n in range(2, D):
        wanted = prefix[n] - prefix[n//2]
        wanted[0] -= n - n//2
        N = n // odds - n // (2*odds)
        N2 = n // (2*odds) - n // (4*odds)
        folded = (-mu[odds] * (N-N2)) @ logs[odds]
        folded[0] -= n-n//2
        folded[idx[2]] += 1
        assert np.array_equal(wanted, folded), (X, n)
        tests += 1
    assert np.all(logs < 64)
    # Deliberate bad source: omit the log(2) term at n=2.
    assert not np.array_equal(lam[2] - np.eye(1, len(primes)+1, 0, dtype=np.int64)[0],
                              -np.eye(1, len(primes)+1, 0, dtype=np.int64)[0])
    return tests


def kernel_checks(X: int):
    b = 4*X//3
    ds = np.arange(X+1, b+1, dtype=np.int64)
    t = np.arange(X, 4*X, dtype=np.int64)[:, None]
    N = t//ds - t//(2*ds)
    N2 = t//(2*ds) - t//(4*ds)
    H = N-N2
    K8 = 8*(H[:X].T@H[:X]) - H[X:].T@H[X:]
    target = 14*X - 2*np.minimum(ds[:, None], ds[None, :]) - 5*np.maximum(ds[:, None], ds[None, :])
    assert np.array_equal(K8, target)
    wrong = 8*(H[:X].T@H[:X]) - 2*(H[X:].T@H[X:])
    assert not np.array_equal(wrong, target)
    cases = 0
    for seed in range(20):
        c = np.array([((i+1)*(seed+3)*7 % 17)-8 for i in range(len(ds))], dtype=np.int64)
        C = np.concatenate(([0], np.cumsum(c)))[:-1]  # cells X,...,b-1
        T = int(c.sum())
        I2 = int(C@C)
        I1 = int(C.sum())
        q = F(int(c@K8@c), 8)
        rhs = F(3,8)*I2 + F(1,2)*T*I1 + F(7,8)*(2*X-b)*T*T
        assert q == rhs, (X, seed, q, rhs)
        assert q >= F(1,4)*I2 + F(5,12)*X*T*T
        cases += 1
    return len(ds)**2, cases


def main():
    start = time.monotonic()
    grids = [8, 16, 32, 64, 128]
    report = dict(formal_source_cells=0, exact_kernel_pairs=0, signed_quadratic_forms=0,
                  deliberate_bad_source_detected=True, deliberate_bad_pairing_detected=True)
    for i, X in enumerate(grids, 1):
        report['formal_source_cells'] += formal_source_check(X)
        pairs, forms = kernel_checks(X)
        report['exact_kernel_pairs'] += pairs
        report['signed_quadratic_forms'] += forms
        elapsed = time.monotonic()-start
        eta = elapsed*(len(grids)-i)/i
        print(f"[{'#'*i}{'.'*(len(grids)-i)}] {i}/{len(grids)} X={X} ETA={eta:.1f}s", flush=True)
    moments = (2, 2, 6, 26, 150)
    c = F(9,4)*(moments[0]+4*F(1,6)*moments[1]+6*F(1,6)**2*moments[2]+4*F(1,6)**3*moments[3]+F(1,6)**4*moments[4])
    assert c == F(355,32) < 12
    report['dyadic_log_budget_exact_constant'] = str(c)
    report['elapsed_seconds'] = round(time.monotonic()-start, 3)
    report['all_passed'] = True
    print(json.dumps(report, indent=2))
    with Path(__file__).with_name('test_report.json').open('w') as f:
        json.dump(report, f, indent=2)


if __name__ == '__main__':
    main()

```
