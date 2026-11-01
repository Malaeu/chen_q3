# STATUS: TRY_SCALEJET_SIGNED_LOCALIZATION
```yaml
OPERATIVE_CLASS: TRY_SCALEJET_SIGNED_LOCALIZATION
DATE: 2026-10-31
AUTHORITY: DIRECT_OWNER_SCALE_AVERAGE_JET_BUDGET_AND_LOCALIZATION_REQUEST
PREDECESSOR: PROSHKA_VERDICT_SCALEBRIDGE_2026-10-31.md
PREDECESSOR_SHA256: 9e0b544b6953e520016f6e62e8a05e4bfe53f37f74b210fd805ff9e852af19d2
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
CARRIER: ORIGINAL_REAL_EVEN_CCM_N_EQUALS_M_L_EQUALS_LOG_M
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
FINITE_POSITIVE_SCALE_MIXTURE_EXACT_SMOOTHNESS: IMPOSSIBLE_EXCEPT_TRIVIAL_ZERO_MIXTURE
SMOOTH_CONTINUUM_MODEL: CONSTRUCTED_WITH_UNIFORM_DISCRETE_RETURN_ERROR
DISCRETE_RETURN_ERROR: O_ONE_OVER_SQRT_M_LOG_M
FIRST_LOG_MOMENT_BOUND: EXPLICIT_IN_JET_COEFFICIENTS_AND_WEIGHTED_NORM
GROWING_JET_UNIFORM_BOUND: PROVED_FOR_EXPLICIT_SUFFICIENT_HORIZON
CERTIFIED_HORIZON_ASYMPTOTIC: ONE_QUARTER_LOG_LOG_M_OVER_LOG_LOG_LOG_M
CERTIFIED_HORIZON_IS_INTRINSIC_MAXIMUM: false
ACTUAL_MAXIMAL_JET_ORDER: NOT_DETERMINED
FULL_CARRIER_RETURN_FOR_CERTIFIED_JETS: PAID_WITH_ENDPOINT_AND_RESIDUAL_BUDGETS
LOCALIZATION: EXACT_FINITE_GRAM_CONCENTRATION_PROBLEM_AND_EXPLICIT_BOUNDS
MEAN_PLUS_LIPSCHITZ_PLUS_BANDWIDTH_IMPLIES_UNIFORM_PEAK_BOUND: REFUTED_AT_GENERIC_THEOREM_SHAPE_SCOPE
COUNTEREXAMPLE_IS_LITERAL_PRIME_SOURCE: false
UNIFORM_ARITHMETIC_ALL_HEIGHT_UPPER_BOUND: NOT_PROVED
NEW_UNCONDITIONAL_HIGH_HEIGHT_REGION: LOG_HEIGHT_AT_LEAST_EXPLICIT_O_SQRT_M_OVER_LOG_M
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: QUANTITATIVE_GROWING_JET_AND_DISCRETE_SMOOTHING_BUDGETS_ONLY
SOURCE_SIGN_PROGRESS: NO_NEW_UNIFORM_BULK_UPPER_BOUND
COGNITIVE_OPERATOR: DUALIZE
VERIFIER: PAPER
EXACT_ALGEBRA_REPLAY: EIGHT_GROUPS_PASSED
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NEW_CCM_EIGENVALUE_SCAN: false
REPOSITORY_WRITTEN: false
RH_PROVED: false
T_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Итог и граница результата

**Пункты 5 и 7 SCALEBRIDGE соединены количественно, но их соединение не даёт пока верхней границы всего символа.** Получены явные неотрицательные веса по исходным целым ячейкам, гладкая непрерывная модель с оплаченной ошибкой, оценка первого логарифмического момента через коэффициенты джета, растущий порядок джета с общей константой и точная задача его частотной концентрации.

Разделены три утверждения, которые нельзя смешивать:

1. Для **явно заданного растущего** `K=K_cert(M)` доказан общий upper bound среднего по всем радикальным профилям этого джета. Это больше, чем прежнее `для каждого фиксированного r`.
2. `K_cert` — максимум, который разрешает **выписанная здесь грубая достаточная оценка**. Не доказано, что настоящие `M_r` так быстро растут или что более высокий порядок невозможен.
3. Даже положительность плотности, общие джетовые средние, полоса символа и его Lipschitz-бюджет **вместе** не дают равномерного pointwise upper. Приведён точный полосовой контрпример с высотой порядка `sqrt(M)/log M`. Он не является prime-source и запрещает только этот общий переход.

Восстановленный из пропуска в запросе главный рубеж:
\[
 \boxed{\exists C<\infty,\quad \overline B_{M_j}(t)\le Cw(t)
 \quad\forall t\in\mathbb R,\quad M_j\to\infty,}
 \tag{0.1}
\]
где веса усреднения неотрицательны, суммируются в единицу, а минимальная исходная ячейка уходит в бесконечность. Переход `(0.1) => RH` используется в ровно PAPER-scope SCALEBRIDGE, а **(0.1) не установлено**.

Никакого независимого исследователя, Lean/Arb-проверки или нового сканирования CCM в этом батче нет. Самопроверка и exact-algebra replay не называются независимым аудитом. Старые разрешения на запись определённых файлов не переносятся на новый вердикт; репозиторий не изменялся.

## 1. Источники и обозначения

SCALEBRIDGE прочитан целиком, включая остатки, кванторы и приложения. Для других предшественников использованы указанные ниже математические поставщики, не новый полный аудит всей цепочки.

| Код | Источник | Фактическое использование |
|---|---|---|
| S1 | `PROSHKA_VERDICT_SCALEBRIDGE_2026-10-31.md`, 70662 bytes, 830 LF, SHA256 `9e0b544b6953e520016f6e62e8a05e4bfe53f37f74b210fd805ff9e852af19d2` | §4 fixed-profile source consistency; §6 theta-средние; §7 positive scale-average consumer |
| S2 | `PROSHKA_VERDICT_ENERGYBOUND_2026-10-31.md`, SHA256 `255309f7a0c5bbd4240b626370b7ef3e0e854335c225a50187c880084bdfae26` | Фиксированная норма, full residual и endpoint-return, глобальная theta-радикальность как унаследованный вход |
| S3 | `PROSHKA_VERDICT_CONFINE_2026-10-30.md`, SHA256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb` | Theta-ряд, чётность, Fourier-конвенция, возврат на `N=m` |
| P | `Malaeu/chen_q3`, `rh_clean`, `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` | Прочитан через GitHub connector, включая конец; blob в header |
| E1 | NIST DLMF §§18.2(v),18.9(i),18.14(i) | Стандартные reproducing/Christoffel coordinates, recurrence и `|P_n(x)|<=1` для Legendre; все необходимые применения доказаны ниже |

Управляющее основание — текущая прямая команда владельца; не выбирался другой TXT или queue item. Никакая актуальная zero-free теорема не импортирована. Внешний поиск ограничен проверкой стандартного полиномиального аппарата, не используется вместо проектных файлов.

**[ABSTRACT | PAPER; inherited definitions]**
\[
 h(x)=\sum_{n\ge1}(16\pi^2n^4e^{9x/2}-24\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}},
 \qquad H(t)=\widehat h(t)=4\xi(1/2-it),
\]
\[
 \widehat f(t)=\int f(x)e^{-itx}dx,\quad p_f(t)=\frac{|\widehat f(t)|^2}{2\pi},
 \quad Q_f(s)=2\int f(x)f(x+s)dx.
\]
`h` — вещественная чётная функция, голоморфная в `|Im x|<pi/4`; все её фиксированные производные имеют любые фиксированные экспоненциальные пространственные моменты. Радикальность — относительно полной исходной Weil-формы, не утверждение её непрерывности в `G`.

Пусть
\[
 d\nu(s)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)-e^{s/2}ds,
 \quad s>0,
\]
\[
 B_L(t)=2\int_{(s_0,L]}(1-s/L)\cos(ts)d\nu(s),\qquad s_0\ge0\text{ фиксировано},
\]
\[
 j_+(s)=\frac{e^{-5s/2}}{1-e^{-2s}},\quad
 w(t)=1+2\int_0^\infty j_+(s)(1-\cos(ts))ds,
 \quad \mathscr G[f]=\|f\|_{\mathscr G}^2=\int w p_f.
 \tag{1.1}
\]
Используются проверенные в S2 границы
\[
 1+\tfrac12\log(1+4t^2/25)\le w(t)
 \le1+\tfrac12\log(1+4t^2/9),
\quad |w'(t)|\le18/25,\quad w(t)\le1+t^2.
 \tag{1.2}
\]
Последние две также следуют из `int s j_+ <=9/25`, `int s² j_+ <=26/125` и `1-cos v<=v²/2`.

Исходные матрицы всегда имеют `L=log m`, `N=m`, тот же фазированный ортонормированный базис и нулевое продолжение. Усреднение ниже — вспомогательное усреднение их символов, не изменение prime weights в какой-либо матрице.

## 2. Положительные веса: что можно сгладить точно

### Лемма 1. Конечная смесь не бывает гладкой; её гладкая модель имеет малую оплачиваемую ошибку

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

Для целого `M>=3` положим
\[
 \ell=\log M,\quad \Delta=\log2,\quad L_+=\ell+\Delta=\log(2M),\quad X_+=2M.
\]
Возьмём
\[
 b(v)=c_b^{-1}\exp[-1/(v(1-v))]\mathbf1_{(0,1)}(v),
 \quad c_b=\int_0^1\exp[-1/(v(1-v))]dv>0,
\]
\[
 \rho_M(L)=\Delta^{-1}b((L-\ell)/\Delta).
 \tag{2.1}
\]
Это неотрицательная `C^infinity`-плотность, плоская на концах, с интегралом 1. Определим **точные**, а не sampled, веса
\[
 \boxed{a_{M,m}=\int_{\log m}^{\log(m+1)}\rho_M(L)dL,
 \quad m=M,\ldots,2M-1.}
 \tag{2.2}
\]
Все веса неотрицательны и их сумма точно равна 1. Далее
\[
 q_M^{d}(s)=\sum_m a_{M,m}(1-s/\log m)_+,
\quad q_M^{c}(s)=\int\rho_M(L)(1-s/L)_+dL.
 \tag{2.3}
\]
В смысле распределений на `s>0`:
\[
 (q_M^d)''=\sum_m\frac{a_{M,m}}{\log m}\delta_{\log m},
 \qquad (q_M^c)''(s)=\frac{\rho_M(s)}s.
 \tag{2.4}
\]
Поэтому `q_M^d` кусочно-линейна и имеет положительный скачок первой производной в каждом узле с ненулевым весом. В частности, у последнего такого узла она не `C^1`. Гладкость последовательности коэффициентов этого не меняет. `q_M^c`, напротив, `C^infinity` и плоска у `L_+`.

Точное возвращённое усреднение:
\[
 \boxed{\overline B_M^d(t)=2\sum_{s_0<\log n\le L_+}
 \frac{\Lambda(n)}{\sqrt n}q_M^d(\log n)\cos(t\log n)
 -2\int_{s_0}^{L_+}e^{s/2}q_M^d(s)\cos(ts)ds.}
 \tag{2.5}
\]
Оба члена проходят через один и тот же фильтр. Определим `bar B^c` заменой `q^d` на `q^c` **только для сравнения**. Тогда
\[
 \boxed{\sup_t|\overline B_M^d(t)-\overline B_M^c(t)|
 \le\epsilon_M^{grid}:=
 \frac{4(1+4\log2)\sqrt{2M}}{M\log M}
 =O\bigl(M^{-1/2}/\log M\bigr).}
 \tag{2.6}
\]
Их производные отличаются не более чем на `L_+ epsilon_grid`.

**Доказательство.** Производные треугольника дают (2.4). Функция `(1-s/L)_+` по `L>=ell` Lipschitz с константой `1/ell`, равномерно по `s>=0`: там, где производная ненулевая, она равна `s/L²<=1/L`. В одной logarithmic cell длина не больше `1/M`; поэтому
\[
 \|q_M^d-q_M^c\|_\infty\le1/(M\ell).
\]
Используем элементарную, не PNT, границу
\[
 \psi(x)=\sum_{n\le x}\Lambda(n)\le c_\psi x,
 \qquad c_\psi=4\log2.
 \tag{2.7}
\]
Для полноты: каждое `p^k in (n,2n]` входит в `log binom(2n,n)` как минимум с одним `log p`, так как каждое слагаемое Legendre valuation неотрицательно. Значит `psi(2n)-psi(n)<=2n log2`. Суммирование на степенях 2 и округление `x` вверх до следующей степени 2 даёт (2.7).

Суммирование по частям теперь даёт
\[
 \sum_{n\le X}\Lambda(n)n^{-1/2}\le2c_\psi\sqrt X,
 \quad |\nu|((0,\log X])\le2(c_\psi+1)\sqrt X.
 \tag{2.8}
\]
Множитель 2 в символе и (2.8) доказывают (2.6). Для производной добавляется `s<=L_+`. Это бюджет ошибки дискретизации, а не попытка оценить по модулю всю целевую форму. ∎

**Техническая поправка к запросу:** у точного дискретного `q_M` вторая производная не просто имеет конечные скачки — она является атомарной мерой. Мы не заменили её гладкой функцией бесплатно. Новые веса сохраняют целочисленный источник; модель `q^c` служит аналитическим инструментом с явной ценой возврата.

Для `0<=s<=ell` неизбежно
\[
 q_M^d(s)=1-\beta_Ms,\qquad
 \beta_M=\sum_m\frac{a_{M,m}}{\log m},\qquad
 \frac1{L_+}\le\beta_M\le\frac1\ell.
 \tag{2.9}
\]
Таким образом никакая неотрицательная смесь на этом диапазоне масштабов не устраняет первый логарифмический момент. Изменение bump-профиля улучшает верхний край, но не заменяет `1/log M` более быстрым порядком в (2.9). При более широком диапазоне остаётся `beta>=1/(max L)`; перенос масштаба не равен отмене момента.

## 3. Какие высоты действительно оплачены сглаживанием

### Лемма 2. Полный высотный хвост имеет явный, но очень большой порог

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER; literal arithmetic envelopes]**

Для обоих профилей (2.3):
\[
 0\le q(s)\le(L_+-s)_+/\ell.
\]
Положим
\[
 \boxed{A_M=\frac{8(1+4\log2)\sqrt{2M}}{\log M}.}
 \tag{3.1}
\]
Тогда
\[
 |\overline B_M^{d,c}(t)|\le A_M,\qquad
 |(\overline B_M^{d,c})'(t)|\le L_+A_M.
 \tag{3.2}
\]
Следовательно
\[
 \boxed{|t|\ge T_0(M):=\frac52e^{A_M}
 \quad\Longrightarrow\quad
 \overline B_M^{d,c}(t)\le w(t).}
 \tag{3.3}
\]
Это настоящая unconditional all-tail оценка, но `log T0=O(sqrt M/log M)`: она оставляет огромный диапазон и не решает (0.1).

**Доказательство.** Пусть `g(y)=y^{-1/2}log(X_+/y)`. Она убывает на `[1,X_+]`, `g(X_+)=0`. По (2.7), Stieltjes integration by parts даёт
\[
 \sum_{n\le X_+}\frac{\Lambda(n)}{\sqrt n}\log(X_+/n)
 \le c_\psi\int_1^{X_+}y(-g'(y))dy
 =c_\psi(4\sqrt{X_+}-\log X_+-4)
 \le4c_\psi\sqrt{X_+}.
\]
Континуум удовлетворяет
\[
 \int_0^{L_+}e^{s/2}(L_+-s)ds
 =4e^{L_+/2}-4-2L_+\le4\sqrt{X_+}.
\]
Делим на `ell` и учитываем 2 в символе. Производная добавляет не более `L_+`. Из (1.2), при `|t|>=5e^{A_M}/2`, имеем `w(t)>=1+A_M`, что доказывает (3.3). ∎

Здесь абсолютные envelopes расходуются на высотное отсечение, derivative-бюджет и error ledgers. Они не объявлены искомой постоянной `C` и не заменяют знаковую форму на всём диапазоне.

### Почему endpoint-smoothing не даёт decay prime-суммы

**[FINITE_CELL | PAPER]** Для непрерывной модели обозначим `v(s)=e^{s/2}q_M^c(s)`. Верхний конец плоский, но у фиксированной нижней отсечки обычно `v(s0)!=0`. Интегрирование по частям даёт, для `t!=0`,
\[
 \left|\int_{s_0}^{L_+}v(s)\cos(ts)ds\right|
 \le\frac{v(s_0)+\|v'\|_1}{|t|}
 \le\frac{e^{s_0/2}+4\sqrt{2M}/\ell}{|t|}.
 \tag{3.4}
\]
Повторные интегрирования оплачиваются производными `rho` и сохраняют нижние endpoint terms. Это законно для континуума.

Однако prime-часть остаётся конечным cosine polynomial
\[
 P_M(t)=2\sum c_nq_M^c(\log n)\cos(t\log n).
\]
Если хотя бы один коэффициент ненулевой, то
\[
 \lim_{T\to\infty}\frac1T\int_0^T P_M(t)^2dt
 =2\sum c_n^2q_M^c(\log n)^2>0.
 \tag{3.5}
\]
Ортогональность различных частот в Cesaro-среднем доказывает формулу напрямую. Поэтому `P_M(t)` не убывает как `O(|t|^{-a})` ни при каком `a>0`.

Более того, одновременное приближение фаз конечного числа простых к нулю возвращает сумму коэффициентов вдоль сколь угодно больших t; степени простых следуют тем же фазам. Это доказывается pigeonhole-приближением в конечномерном торе; если последовательность возвратов ограничена, возникает точный период, кратные которого дают неограниченные возвраты. При каждом фиксированном M это не противоречит (3.3), поскольку `w(t)->infinity`.

**Вывод:** интегрирование по частям в Stieltjes prime-сумме не заменяет атомарную меру гладкой плотностью. Для большей безрезонансной области нужна отдельная оценка сумм с настоящими фазами `t log n`. Из гладкого верхнего края такая область не получена.

## 4. Первый логарифмический момент: явная цена каждого джета

### Лемма 3. Коэффициентный и norm-бюджет с полной бесконечной мерой

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** Положим
\[
 T_q(r)=\|e^{q|x|}r\|_2,\qquad
 M_r=\int_{(s_0,\infty)}sQ_r(s)d\nu(s).
\]
При `T3(r)<infinity`:
\[
 \boxed{|M_r|\le c_3T_3(r)^2,\qquad c_3=124/75.}
 \tag{4.1}
\]
Для `r=sum_(k=0)^(K-1) alpha_k h^(2k)` это, в частности,
\[
 |M_r|\le\frac{124}{75}
 \left(\sum_{k=0}^{K-1}|\alpha_k|\,T_3(h^{(2k)})\right)^2.
 \tag{4.2}
\]

**Доказательство.** Из `|x|+|x+s|>=s` и Cauchy–Schwarz:
\[
 |Q_r(s)|\le2T_3(r)^2e^{-3s}.
\]
Поэтому
\[
 |M_r|\le2T_3(r)^2
 \left[\sum_{n\ge2}(\log n)^2n^{-7/2}
       +\int_0^\infty se^{-5s/2}ds\right].
\]
Для `x>=1`, `(log x)^2<=x`, и `sum_(n>=2)n^(-5/2)<=2/3`. Интеграл равен `4/25`. Получаем (4.1). Все proper powers присутствуют, а использование `Lambda<=log` — верхний бюджет этого auxiliary error, не замена целевого арифметического спаривания. ∎

**[COFINAL_FAMILY | PAPER]** Пусть `gamma=5/2` и
\[
 t_M=2M^{-5/2}\left[
 \frac{2L_++2}{\gamma}
 +\frac{3+1/\ell}{\gamma^2}
 +\frac{2}{\ell\gamma^3}\right].
 \tag{4.3}
\]
Для **точных дискретных весов** (2.2), при `ell>s0`:
\[
 \boxed{\int p_r\overline B_M^d
 =\mathcal H_+[r]+c_0\|r\|_2^2-\mathcal S^{near}[r]
 -\beta_MM_r+\mathcal E_M(r),}
 \tag{4.4}
\]
\[
 \boxed{|\mathcal E_M(r)|\le t_MT_3(r)^2,
 \quad |\beta_MM_r|+|\mathcal E_M(r)|
 \le e_M T_3(r)^2,
 \quad e_M=\frac{124}{75\ell}+t_M.}
 \tag{4.5}
\]
Это количественная версия S1 (6.1), теперь равномерная по весам (2.2) и явно зависящая от r.

**Доказательство.** Для каждого `L=log m` точный хвост относительно `S_infinity-M_r/L` равен
\[
 E_L(r)=\int_{(L,\infty)}(s/L-1)Q_r(s)d\nu(s).
\]
Его модуль не больше интеграла `(1+s/L)|Q_r|` против полной вариации. `Lambda<=log` и интегральная оценка убывающей функции
`(log x+(log x)^2/L)x^(-7/2)` при `x>=m>=2` дают
\[
 |E_L(r)|\le2T_3(r)^2m^{-5/2}
 \left[\frac{2L+2}{\gamma}
 +\frac{3+1/L}{\gamma^2}+\frac{2}{L\gamma^3}\right].
\]
Для `m in [M,2M]` это не больше (4.3) `T3²`. Усредняем без смены знака весов. Радикальность r используется только для выражения `S_infinity^far[r]` через первые три члена (4.4). ∎

Не нужно добавлять (2.6) к (4.5): последнее относится непосредственно к дискретному average. При замене его непрерывной моделью дополнительно платится `epsilon_grid ||r||₂²`.

### Что оптимизация положительных весов не исправляет

Из (2.9) коэффициент перед `M_r` имеет размер `1/ell` при любой выбранной положительной плотности на `[ell,ell+log2]`. Если M_r неблагоприятен по знаку, нельзя убрать его первым моментом фильтра с неотрицательными весами. Это утверждение о фильтре, **не** утверждение, что `|M_r|` достигает верхнего бюджета (4.1).

## 5. Полностью явная оценка по степени, включая conditioning

### Лемма 4. Производные theta-функции: никаких скрытых констант, зависящих от K

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** Введём фиксированные константы
\[
 d=\pi/16,\quad a=\pi\cos(2d)>0,\quad v=e^{-a},
\]
\[
 U=16\pi^2\frac{1+11v+11v^2+v^3}{(1-v)^5}
   +24\pi\frac{1+v}{(1-v)^3},
\]
\[
 \boxed{C_q=e^{qd}U
 \left(\frac{\Gamma(q+9/2)}{(2a)^{q+9/2}}\right)^{1/2}\quad(q>0).}
 \tag{5.1}
\]
Тогда для каждого целого `n>=0`
\[
 \boxed{T_q(h^{(n)})\le C_q n!d^{-n}.}
 \tag{5.2}
\]

**Доказательство.** Для `x>=0`, `|y|<=d`, `u=e^{2x}>=1`, модуль ряда ограничен
\[
 |h(x+iy)|\le Ue^{9x/2}e^{-ae^{2x}}.
\]
Действительно, `sum n^p exp(-a n²u)<=exp(-au) sum n^p exp(-a(n²-1))`, а `n²-1>=n-1`. Две оставшиеся суммы ограничиваются положительными generating functions для `sum n²v^(n-1)` и `sum n⁴v^(n-1)`, выписанными в U. Чётность, продолженная в полосу, даёт ту же оценку для отрицательных x.

Отсюда
\[
 \sup_{|y|\le d}\|e^{q|x|}h(x+iy)\|_2^2
 \le U^2\int_1^\infty u^{q+7/2}e^{-2au}du
 \le U^2\Gamma(q+9/2)/(2a)^{q+9/2}.
\]
Cauchy formula на круге радиуса d, Minkowski и `e^(q|x|)<=e^(qd)e^(q|x+Re z|)` доказывают (5.2). Используются действительные theta-коэффициенты и допустимая полоса, не RH. ∎

### Лемма 5. Явная нижняя граница Gram-матрицы

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** Определим
\[
 H_*=\frac{16\pi^2-24\pi}{5}\exp[-\pi e^{1/5}]>0,
 \quad h_*:=H_*/2,
 \quad \tau=\min\{1,\sqrt{H_*\sqrt{162}/C_3}\}>0.
 \tag{5.3}
\]
При `|t|<=tau` имеем `H(t)>=h_*`.

Для `K>=1`, `n=2K-2`, положим
\[
 \boxed{g_K=\frac{h_*^2\tau^{2n+1}}
 {\pi(n+1)(2n+1)9^n}.}
 \tag{5.4}
\]
Тогда для любого действительного коэффициентного вектора alpha:
\[
 \boxed{\left\|\sum_{k=0}^{K-1}\alpha_kh^{(2k)}\right\|_2^2
 \ge g_K\sum_k|\alpha_k|^2.}
 \tag{5.5}
\]
Следовательно, с
\[
 \boxed{D_K=\frac{C_3^2K(n!)^2d^{-2n}}{g_K},}
 \tag{5.6}
\]
\[
 \boxed{T_3(r)^2\le D_K\|r\|_2^2\le D_K\mathscr G[r].}
 \tag{5.7}
\]

**Доказательство.** `h(x)>0` для `x>=0`, поскольку каждый summand имеет фактор `2pi n²e^(2x)-3>0`; чётность даёт положительность на всей прямой. Интегрирование только первого summand по `0<=x<=1/10` даёт `H(0)>=H_*`. Кроме того,
\[
 \int x^2h(x)dx\le T_3(h)\left(\int x^4e^{-6|x|}dx\right)^{1/2}
 \le C_3/\sqrt{162}.
\]
Из `1-cos(tx)<=t²x²/2` следует `H(t)>=H(0)-H_*/2>=h_*` в указанном интервале.

Пусть `P(t)=sum alpha_k(-1)^k t^(2k)`. Тогда
\[
 \|r\|_2^2\ge\frac{h_*^2\tau}{2\pi}
 \int_{-1}^1|P(\tau x)|^2dx.
\]
Для полинома `Q` степени не больше n его monomial coefficient vector b удовлетворяет
\[
 \|b\|_2^2\le\frac{(n+1)(2n+1)9^n}{2}\int_{-1}^1|Q|^2.
 \tag{5.8}
\]
Чтобы проверить (5.8), разложим Q по Legendre `P_j`: `||P_j||₂²=2/(2j+1)`, а сумма модулей его коэффициентов не больше `3^j`. Последняя граница следует индукцией из `(j+1)P_(j+1)=(2j+1)xP_j-jP_(j-1)`. Cauchy–Schwarz по j и грубая оценка конечной суммы дают (5.8). Стандартные нормировки сверены с E1.

В `Q(x)=P(tau x)` квадрат коэффициентной нормы не меньше `tau^(2n) sum|alpha|²`; это даёт (5.4)–(5.5). Наконец (5.2), Cauchy–Schwarz по k и `d<1` дают
`T3(r)<=C3 sqrt(K)n!d^(-n)||alpha||₂`, откуда (5.7). ∎

Эта граница не объявляет monomial basis хорошо обусловленным. Наоборот, её conditioning полностью учтено в `g_K`. Числа очень консервативны; это аналитический certificate, не рекомендация вычислять большие jets в мономиальном базисе.

### Теорема 6. Явный растущий горизонт вместо прежнего качественного квантора

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]** Положим
\[
 \boxed{K_{cert}(M)=\max\{K\ge1:D_Ke_M\le1/2\},}
 \tag{5.9}
\]
а при пустом множестве `K_cert=0`. Для всех `K<=K_cert(M)` и всех `r in R_K=span{h,...,h^(2K-2)}`:
\[
 \boxed{|\beta_MM_r|+|\mathcal E_M(r)|
 \le\tfrac12\|r\|_2^2\le\tfrac12\mathscr G[r].}
 \tag{5.10}
\]
Поэтому с одним конечным
\[
 C_0=2+|c_0|+C_{s_0},\qquad
 C_{s_0}=2\sum_{n\le e^{s_0}}\Lambda(n)/\sqrt n+4(e^{s_0/2}-1),
\]
\[
 \boxed{\int p_r(t)\overline B_M^d(t)dt\le C_0\mathscr G[r]
 \quad\text{одновременно для всех }r\in R_{K_{cert}(M)}.}
 \tag{5.11}
\]
Именно для явно определённого достаточного горизонта (5.9):
\[
 \boxed{K_{cert}(M)=\left(\frac14+o(1)\right)
 \frac{\log\log M}{\log\log\log M}\quad(M\to\infty).}
 \tag{5.12}
\]

**Доказательство.** (5.10) — непосредственное соединение (4.5) и (5.7), не перестановка кванторов. Для near-части платится фиксированная `C_s0 ||r||₂²`, после чего (4.4) даёт (5.11).

Из явного (5.6), при `n=2K-2`,
\[
 \log D_K=4K\log K+O(K),
\]
где константа O зависит только от выписанных d,tau,C3,h*, не от M. При этом `e_M=(124/75+o(1))/log M`. Поскольку D_K возрастает, порог (5.9) задаётся `4K log K=(1+o(1))log log M`; это доказывает (5.12). ∎

**Критическая оговорка.** (5.12) не является верхним ограничением на настоящую разрешённую степень. Верхняя оценка `D_K` не доказывает нижнего роста `M_r`. Нельзя заключать «более высокие jets математически запрещены» из дороговизны этого certificate. При умеренных M грубый (5.9) вообще может быть пустым; результат асимптотический и константы не оптимизированы.

Для проверки истинной цены имеются точные конечные объекты:
\[
 G_K=(\langle h^{(2i)},h^{(2j)}\rangle_{\mathscr G})_{ij},
 \quad T_{K,3}=\left(\int e^{6|x|}h^{(2i)}h^{(2j)}dx\right)_{ij},
\]
\[
 D_K^{sharp}=\lambda_{max}(G_K^{-1/2}T_{K,3}G_K^{-1/2})\le D_K,
\]
\[
 (\mathbb M_K)_{ij}=\int_{(s_0,\infty)}s\,Q_h^{(2i+2j)}(s)d\nu(s).
 \tag{5.13}
\]
Дважды чётное интегрирование по частям доказывает последнюю, Hankel-по-индексам формулу. Ни `mathbb M_K>=0`, ни её равномерная нормированная граница не предполагаются. Более точный достаточный error-budget использует
`beta_M ||G_K^(-1/2) mathbb M_K G_K^(-1/2)|| + t_M D_K^sharp`.
Эта операторная норма относится к **ошибке первого момента на конечном jet**, не к запрещённой полной норме `Z_m`.

## 6. Возврат растущего джета на исходный носитель

### Лемма 7. Зависимость старых residual-констант от K также оплачена

**THIS STEP IS PROVED HERE using inherited mixed-source estimate. [COFINAL_FAMILY | PAPER]**

Предыдущие средние проверялись на глобальных r; это законно, потому что `B_m` — ограниченная функция при каждом конечном m. Чтобы не скрыть eventual CCM-return, приведём также его равномерный бюджет на (5.9).

Зафиксируем один гладкий чётный cutoff `vartheta`, равный 1 на `[-1/2,1/2]`, нулю вне `(-3/4,3/4)`, с `0<=vartheta<=1`. Для каждой исходной `m in [M,2M]` положим
\[
 z=\vartheta(x/b)r,\quad u=P_mz,\quad e=u-z,
 \quad v=r-z,\quad b=(\log m)/2.
\]
Все carrier-векторы имеют **N=m**, не увеличенный cutoff.

Для фиксированных целых `p>=2`, `q>0` определим
\[
 R_{K,p}^{(q)}=\frac{C_q\sqrt K(n+p)!d^{-(n+p)}}{\sqrt{g_K}},
 \quad B_{\vartheta,p}=\sum_{j=0}^p\binom pj\|\vartheta^{(j)}\|_\infty.
 \tag{6.1}
\]
При `L>=2` имеем
\[
 \|z^{(p)}\|_2\le B_{\vartheta,p}R_{K,p}^{(q)}\|r\|_2=:A_{r,p}^{bound}.
\]
По Fourier Parseval и полной tail-summation:
\[
 \epsilon_0:=\|e\|_2\le A_{r,p}^{bound}(L/(2\pi m))^p,
 \quad\epsilon_1:=\|e'_{int}\|_2\le A_{r,p}^{bound}(L/(2\pi m))^{p-1},
\]
\[
 \epsilon_\infty:=\|e\|_\infty\le
 \frac{A_{r,p}^{bound}}{\sqrt L}(L/(2\pi))^p
 \sqrt{2/(2p-1)}m^{1/2-p}.
 \tag{6.2}
\]
Обе крайние полоски нулевого продолжения дают
\[
 \|e\|_{\mathscr G}^2\le\epsilon_0^2+	frac{26}{125}\epsilon_1^2
                              +\tfrac{18}{25}\epsilon_\infty^2.
 \tag{6.3}
\]
Это следует из `||T_s e-e||²<=s²epsilon1²+2s epsilonInf²`; при `s>L` неравенство остаётся верным по `2||e||²<=2L epsilonInf²<=2s epsilonInf²`. Глобальная H1-гладкость не используется.

Возьмём `q=12`. Так как поддержка v начинается при `|x|>=L/4`:
\[
 \|v\|_2\le m^{-3}T_{12}(r),\quad
 \|v'\|_2\le m^{-3}\bigl[T_{12}(r')+2\|\vartheta'\|_\infty T_{12}(r)/L\bigr],
\]
\[
 \|e^{|x|}v\|_2\le m^{-11/4}T_{12}(r),\quad
 \int e^{|x|/2}|v(x)|dx\le\sqrt2m^{-11/4}T_{12}(r).
 \tag{6.4}
\]
По S2–S3 полный источник, не только arch-часть, удовлетворяет
\[
 \boxed{\|A_mu\|_2\le(2+4L)\sqrt m\epsilon_0+10\epsilon_1
 +20\epsilon_\infty\sqrt{3m/L}+\tau_{r,m},}
 \tag{6.5}
\]
\[
 \tau_{r,m}=c_*\|v\|_2+10\|v'\|_2
 +2m^{1/4}\int e^{|x|/2}|v|dx
 +2\sqrt m S_\Lambda\|e^{|x|}v\|_2,
 \quad S_\Lambda=\sum_{n\ge2}\log n/n^{3/2}\le16.
 \tag{6.6}
\]
Грубая последняя константа получается из `log n<=4 n^(1/4)` и `sum_(n>=2)n^(-5/4)<=4`. Бесконечный внешний prime-power хвост в (6.6) сохранён. Цена полюсов и обоих endpoint traces присутствует в (6.5)–(6.6).

Для `p=4` все правые части явны через (5.1), (5.4), (6.1). Более того,
\[
 R_{K,p}^{(12)}=\frac{C_{12}}{C_3}\sqrt{D_K}
 \frac{(n+p)!}{n!}d^{-p}.
 \tag{6.7}
\]
На (5.9) `D_K=O(ell)`, `K=O(log ell/log log ell)`. Поэтому при `G[r]=1`, равномерно по всем таким r и `m in [M,2M]`,
\[
 \|u-r\|_{\mathscr G}\to0,\qquad\|A_mu\|_2\to0.
 \tag{6.8}
\]
Для второй величины, например, (6.2)–(6.6) дают fixed-constant multiple от
\[
 R_{K,4}^{(12)}[L^5m^{-7/2}+L^3m^{-3}+m^{-9/4}],
\]
которая стремится к нулю. Для внешней G-нормы используется
`G[v]<=||v||₂²+(26/125)||v'||₂²`.

Замена r на u в каждом finite smoothed average оплачивается независимо:
\[
 \left|\int(p_u-p_r)B_{\log m}\right|
 \le2\epsilon(2\|r\|_2+\epsilon)\,2(c_\psi+1)\sqrt m,
 \quad\epsilon=\|u-r\|_2.
 \tag{6.9}
\]
Это опять o(1) равномерно на указанном растущем классе. При необходимости резерв `1/2` в (5.9) оставляет ещё `1/2` для этого возврата на достаточно поздних M. Для нормированного trial остаток eigen-equation не подменяется нижним уровнем спектра: здесь утверждается только операторный residual quasimode.

**Доказательство (6.8).** Формулы (6.1)–(6.7) контролируют все ранее profile-dependent constants. Их рост — не быстрее `sqrt(ell)` на фиксированный полином K, тогда как возвращающие множители имеют отрицательные фиксированные степени m. Корреляционная ошибка в (6.9) следует из унитарности сдвигов и полного конечного variation budget (2.8). ∎

## 7. Насколько узок доступный положительный detector

### Лемма 8. Точное разрешение задаётся конечной concentration-матрицей

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** Введём
\[
 b_K(t)=(1,-t^2,\ldots,(-1)^{K-1}t^{2K-2})^T,
 \quad \mu(t)=w(t)|H(t)|^2/(2\pi),
\]
\[
 G_K=\int b_K(t)b_K(t)^T\mu(t)dt>0.
\]
Для `r in R_K` энергетически нормированная плотность равна
\[
 d\sigma_r(t)=\frac{w(t)p_r(t)dt}{\mathscr G[r]}.
\]
Её точный pointwise максимум:
\[
 \boxed{\sup_{r\in R_K\setminus0}\frac{w(t)p_r(t)}{\mathscr G[r]}
 =\mathcal C_K(t):=\mu(t)b_K(t)^TG_K^{-1}b_K(t).}
 \tag{7.1}
\]
Это стандартные Christoffel/reproducing coordinates, применённые к конкретной theta-мере, а не импорт неизвестной asymptotic формулы.

Для интервала или симметричной пары интервалов I максимальная доля массы равна
\[
 \boxed{p_K^*(I)=\lambda_{max}
 \left(G_K^{-1/2}\left[\int_Ib_Kb_K^T\mu\right]G_K^{-1/2}\right).}
 \tag{7.2}
\]
Она достижима соответствующим конечным eigenvector. В частности,
\[
 p_K^*(I)\le\int_I\mathcal C_K(t)dt.
 \tag{7.3}
\]
Для `t0>0` надо брать `I=[t0-delta,t0+delta] union [-t0-delta,-t0+delta]`: все рассматриваемые плотности чётны. Нельзя обещать массу почти 1 только возле одного ненулевого t0.

**Доказательство.** (7.1) — Cauchy–Schwarz в метрике `G_K`, с равенством на `alpha proportional G_K^{-1}b_K(t)`, когда `H(t)!=0`. При `H(t)=0` обе стороны нулевые. (7.2) — конечное обобщённое Rayleigh-отношение; (7.3) следует интегрированием (7.1). Нормировка именно G, не Euclidean norm коэффициентов. ∎

### Явный low-height предел разрешения

**[ABSTRACT | PAPER]** Положим `H_max=C3/sqrt3`, так что `|H(t)|<=||h||1<=Hmax`, и
\[
 R_*=w(\tau)H_{\max}^2/h_*^2.
\]
Для `0<delta<=tau`, `n=2K-2`:
\[
 \boxed{p_K^*([-\delta,\delta])
 \le\min\{1,(R_*/\tau)(n+1)^2\delta\}.}
 \tag{7.4}
\]

**Доказательство.** На `[-tau,tau]` плотность mu не меньше `h_*²/(2pi)` и не больше `w(tau)H_max²/(2pi)`. Legendre reproducer для всех полиномов степени <=n, с `|P_j|<=1`, даёт
\[
 |P(t)|^2\le\frac{(n+1)^2}{2\tau}\int_{-\tau}^{\tau}|P(s)|^2ds
 \quad(|t|\le\tau).
\]
Ограничивая G-интеграл этим интервалом и интегрируя pointwise bound по `[-delta,delta]`, получаем (7.4). Even-subspace — подпространство всех degree-n полиномов, поэтому цена допустима. ∎

При `delta=1/ell` и `K=K_cert(M)`:
\[
 \boxed{p_{K_{cert}(M)}^*([-1/\ell,1/\ell])
 \le O(K_{cert}(M)^2/\ell)\longrightarrow0.}
 \tag{7.5}
\]
Чтобы получить хотя бы половину энергетической массы на этой шкале, (7.4) требует
\[
 n+1\ge\sqrt{\tau\ell/(2R_*)}.
 \tag{7.6}
\]
Следовательно **доказанный здесь растущий пакет** ещё не имеет даже постоянной доли массы в потенциальном пике ширины `1/log M` у нуля. Более высокий, пока не оплаченный, K этим не запрещён.

На другом фиксированном интервале, где H не зануляется, действует та же локальная формула с его собственными `mu_min,mu_max`. При вещественном нуле H порядка j вся конечная jet-плотность обращается в нуль порядка `2j`; из (7.1) масса узкой окрестности имеет upper `C_(K,t0) delta^(2j+1)`. Константа зависит от K; из этого не делается запрет аппроксимации при K->infinity.

### Все высоты, включая произвольный t0

**[ABSTRACT | PAPER]** Из той же полосы, сдвигом Fourier-контура на `d=pi/16`,
\[
 |H(t)|\le C_H e^{-d|t|},\qquad C_H=e^{-3d}C_3/\sqrt3.
\]
По (5.5), (7.1) и `w<=1+t²`, для `T>=1`:
\[
 \boxed{\sup_{r\in R_K\setminus0}\sigma_r(|t|\ge T)
 \le\min\left\{1,
 \frac{2C_H^2K}{\pi g_K}(2d)^{-(2n+3)}
 \Gamma(2n+3,2dT)\right\}.}
 \tag{7.7}
\]
Это явный контроль возможностей detector во всём `[0,T0(M)]`, а не предположение, что H не имеет вещественных нулей.

**Доказательство.** `sum_(k<K)t^(4k)<=K t^(2n)` при `|t|>=1`; `w<=2t²`. Применяем `||alpha||²<=||r||₂²/g_K<=G[r]/g_K`, интегрируем обе Fourier-полуоси. Получается указанная неполная Gamma-функция. Контурный сдвиг оправдан double-exponential theta decay в закрытой меньшей полосе. ∎

В частности, при `T=C K log(K+2)`, любом фиксированном `C>2/d`, правая часть стремится к нулю: в логарифме доминирует `(-2dC+4)K log K`. Для certified K это высота порядка `log log M`, а не `T0=exp(O(sqrt M/log M))`. Это граница проверенного detector-пакета, не утверждение, что у настоящего символа обязательно есть плохие пики на остальных высотах.

## 8. Знак: точный количественный переход от среднего к пику

### Лемма 9. Цена отрицательной утечки не исчезает при положительной плотности

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]** Положим
\[
 F_M(t)=\overline B_M^d(t)/w(t),\quad
 D_M=A_M(L_++18/25).
\]
Из (3.2), (1.2): `F_M>=-A_M`, `|F_M'|<=D_M`. Пусть `F_M(t0)=b`, I — симметричная delta-окрестность `+/-t0`, а `r in R_(K_cert)` имеет энергетическую массу `p=sigma_r(I)>0`. Тогда
\[
 \boxed{b\le D_M\delta+
 \frac{C_0+A_M(1-p)}p.}
 \tag{8.1}
\]
Более информативная версия сохраняет действительную знаковую утечку:
\[
 \mathcal N_M(r,I)=\int_{I^c}(-F_M(t))_+d\sigma_r(t),
\]
\[
 \boxed{b\le D_M\delta+\frac{C_0+\mathcal N_M(r,I)}p.}
 \tag{8.2}
\]

**Доказательство.** На I: `F_M>=b-D_M delta`. На дополнении отрицательная часть стоит `mathcal N_M`. Поэтому
`int F_M d sigma_r >=(b-D_M delta)p-mathcal N_M`.
Левая часть не больше C0 по (5.11). Это доказывает (8.2); `mathcal N_M<=A_M(1-p)` даёт (8.1). ∎

Для получения одной постоянной через **грубую** (8.1) достаточно было бы иметь одновременно `D_M delta=O(1)` и `1-p=O(1/A_M)`. Здесь `D_M=O(sqrt M)`; требуемые ширина и утечка гораздо меньше, чем разрешает доказанный jet-пакет. Это не необходимое условие для любого возможного арифметического доказательства: оно является ценой именно данной Lipschitz-plus-absolute-outside majorization.

Даже если повысить K до порядка `sqrt(log M)` и получить массу на шкале `1/log M`, останется отрицательный внешний вклад. Улучшение одной только spatial/frequency concentration без signed leakage не завершает переход.

### Лемма 10. Полосовой контрпример, сохраняющий все доказанные общие ограничения

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER; SYNTHETIC SYMBOL, NOT CCM]**

Для M с непустым certified jet возьмём `K=K_cert(M)` и
\[
 \eta_M=\frac{D_K}{3\ell},\qquad
 U_\ell(t)=\left(\frac{\sin(\ell t/2)}{\ell t/2}\right)^2,
\]
\[
 \boxed{Z_M^{test}(t)=A_M\,[U_\ell(t)-\eta_M].}
 \tag{8.3}
\]
Тогда:
\[
 |Z_M^{test}|\le A_M,\quad |(Z_M^{test})'|\le A_M\ell/3\le A_ML_+;
\]
`Z_M^test` вещественен, чётен, имеет Fourier-полосу `[-ell,ell]`, лежащую внутри допустимой полосы символа. Для **всех** r из certified jet:
\[
 \boxed{\int p_r(t)Z_M^{test}(t)dt\le0,}
 \tag{8.4}
\]
но
\[
 \boxed{\frac{Z_M^{test}(0)}{w(0)}
 \ge\left(1-\frac1{6c_3}\right)A_M\longrightarrow+\infty.}
 \tag{8.5}
\]
Следовательно upper-средние по всему доказанному растущему jet, положительность плотности, правильная полоса и derivative-budget не дают pointwise bound с общей константой.

**Доказательство.** Cauchy–Schwarz в физическом пространстве даёт
\[
 \|r\|_1^2\le T_3(r)^2\int e^{-6|x|}dx=T_3(r)^2/3,
\]
\[
 \sup_t p_r(t)\le D_K\|r\|_2^2/(6\pi).
\]
Поскольку `int U_ell=2pi/ell`,
\[
 \int p_rU_\ell\le D_K\|r\|_2^2/(3\ell)=\eta_M\|r\|_2^2.
\]
Вычитание постоянной в (8.3) доказывает (8.4). Из `D_Ke_M<=1/2` и `e_M>=c3/ell` следует `eta_M<=1/(6c3)<1/2`, что даёт (8.5).

Точное представление
\[
 U_\ell(t)=\ell^{-1}\int_{-\ell}^{\ell}(1-|s|/\ell)e^{its}ds
\]
даёт и полосу, и `|U_ell'|<=ell/3`. Остальные оценки непосредственны. ∎

Контроль можно симметрично перенести к любой фиксированной паре `+/-t0`, заменив U на полусумму `U(t-t0)+U(t+t0)`; peak остаётся положительным порядка A_M. Он не предполагает ненулевое H в центре.

**Точная область опровержения:** это не настоящий prime/continuum символ и не его positive-scale mixture. В частности, отрицательная константа имеет искусственную source-массу в нуле, что не допускается в реальном far-источнике при s0>0. Контроль показывает лишь недостаточность извлечённых в этом цикле **norm/moment/bandwidth/Lipschitz** свойств без дополнительного арифметического ограничения. Он не опровергает (0.1), RH или более сильное использование точных finite moment matrices.

`KILL_SCOPE: THEOREM_SHAPE`. `KILL_EVIDENCE_KIND: EXPLICIT_BANDLIMITED_SPIKE_WITH_NEGATIVE_BASELINE`. Для любой предложенной постоянной C величина `C-Z_M^test(0)/w(0)` имеет строго отрицательную верхнюю границу при всех достаточно больших M. Это counterexample, не провал достаточной оценки.

## 9. Где теперь находится оставшийся барьер

**[COFINAL_FAMILY | PAPER/CONDITIONAL, distinctions explicit]**

Доказаны, с общими константами и полными кванторами:

- точный положительный discrete scale-average и гладкая модель с uniform error (2.6);
- source-error bound (4.5), factorial/Gram dependence (5.1)–(5.7);
- uniform radical upper на `K_cert(M)->infinity`, формула (5.11);
- uniform исходниковый возврат этого класса с полной невязкой (6.2)–(6.9);
- точная concentration-задача (7.2) и явные пределы возможностей (7.5), (7.7);
- sharp-in-information obstruction (8.3)–(8.5): высота порядка разрешённого общего A_M совместима с перечисленными средними и геометрическими ограничениями.

**Не доказаны:** true maximal K(M); полезная общая bound для всех `t in [0,T0(M)]`; source-dependent upper на отрицательную утечку, достаточный в (8.2); RH.

Первый содержательный неоплаченный переход данного detector-механизма — **не просто размер K**, а совместная возможность выбрать polynomial detector, который одновременно:
\[
 p=\sigma_r(I)>0\text{ имеет оплаченный нижний предел},\quad
 D_M\delta\text{ ограничено},\quad
 \mathcal N_M(r,I)\text{ ограничено на его реальной source-мере}.
 \tag{9.1}
\]
Формула (8.2) показывает точно, что эти три оценки дали бы верхушке. (9.1) не объявлено обязательным или эквивалентным всякому доказательству RH; оно является более специализированным достаточным способом перейти от jet-тестов к pointwise upper. Контроль (8.3) показывает, почему оно не следует из уже оплаченных общих входов.

Нельзя назвать `D_K=exp(4K log K+O(K))` доказанным барьером самого theta-источника. Это цена грубой оценки. Для её улучшения естественны **подписанная** матрица `mathbb M_K` и точно нормированная concentration-матрица, а не величина coefficients в плохо обусловленном базисе.

### Два допустимых продолжения, до какого-либо увеличения вычислений

| Представление | Что действительно меняет решение | Сила / стоимость | Главный риск |
|---|---|---|---|
| Точные `G_K`, `mathbb M_K`, local concentration matrix вместо factorial-majorant | Доказанная signed moment цена и detector с учтённой negative leakage на нужной шкале | Высокая / высокая; finite falsifier дешёвый, cofinal theorem дорогой | Выдать улучшение малого K или conditioning за общий квантор |
| Прямая arithmetic bound для `2 int q_M cos(ts)dnu` по frequency blocks | Совместная cancellation prime powers и continuum на всех оставшихся высотах, не требующая theta-localizer | Решающий / высокая | Интегрировать по частям атомы как гладкую плотность или потерять главный канал |

Три cross-domain перехода здесь выполнены предметно: положительные convex kernels дают (2.4); Cauchy/Legendre дают (5.7); weighted polynomial concentration даёт (7.2). Ни один не подменён названием теоремы. Vanishing identity — исходная радикальность, использованная только в (4.4). Collapse-object остаётся одна общая верхняя константа (0.1), не коллекция finite jet-проверок.

## 10. Сильнейшая атака, зависимости и следующая директива

**Возражение:** «Теперь есть K(M)->infinity, значит плотность закрывает все частоты». Нет. Плотность — утверждение при фиксированном тесте/объекте; символ и его пики меняются с M. (7.5) и (8.3) дают количественный отказ именно этому переходу. Нельзя сначала подобрать приближение к движущемуся пику, а затем объявить его порядок уже разрешённым (5.9).

**Возражение:** «Контрпример опровергает настоящую арифметику». Нет: его отрицательная константа и triangular source density искусственны. Для реальной меры может существовать сильная знаковая совместимость, которой наш контроль не обладает. Она пока не получена.

**Возражение:** «Параметр K_cert слишком консервативен, значит весь анализ бесполезен». Он не предъявляется как оптимальный. Он впервые оплачивает явный растущий класс и отделяет его от требуемой частотной концентрации. Улучшение D_K само по себе не отменит знак в (8.2).

**[ABSTRACT | PAPER; dependency ledger]**

- DOWNSTREAM_CONSUMER: SCALEBRIDGE positive-scale-average criterion => RH on inherited literal-source premises.
- ACTUAL_CONSUMER_REQUIREMENT: one independently proved uniform all-height arithmetic upper bound, or a rigorously weaker consumer-spendable form bound.
- ORIGINAL_REQUESTED_OBJECT: smooth nonnegative scale filter + quantitative growing theta-jet + localized positive detector.
- ORIGINAL_OBJECT_IS: NOT_NECESSARY as a unique route; the assembled package is a candidate sufficient mechanism.
- KNOWN_WEAKER_INTERFACES: same sparse/averaged source form criterion from S1; uniform full R/Hankel bounds are not required.
- FAILURE_TYPE: NO_DERIVATION for the real signed leakage/height bound; COUNTEREXAMPLE for generic peak-from-moments rule.
- EPISTEMIC_STATUS: RESEARCH_DEBT for actual CCM comparison; MATHEMATICALLY_DEAD only for that precisely stated generic inference.
- NOVELTY_AXIS: EXPLICIT_GROWING_JET_CONSTANTS_AND_LOCALIZATION_COST.
- REOPEN_TRIGGER: actual-source estimate improving the signed matrix/negative-leakage budget, not simply extending the coefficient majorant.
- DISCRIMINATOR: can the proposed estimate distinguish the actual source from (8.3), while remaining valid on all admitted profile coefficients and frequencies?

**CODEX DIRECTIVE — signed moment / localization price audit, read-only.**

Independently check (4.5), (5.4)–(5.12), (6.4)–(6.9), and (8.3)–(8.5). Then work on the **specific next supplier**, not another pointwise reformulation: the actual-source matrix `mathbb M_K` in (5.13), with energy Gram `G_K`, and its compatibility with the exact local mass matrix (7.2). Determine whether the dangerous sign of the first-log correction can be bounded more cheaply than `c3 T3²` on the detector which maximizes mass in a prescribed symmetric interval. Retain all prime powers, continuum and the negative outside contribution in (8.2). A finite test may falsify a proposed monotonicity/sign, but cannot certify the growing-K theorem.

Success: a new justified signed source estimate with explicit degree/height cost that improves one side of (8.2). Failure: `SIGNED_MOMENT_OR_NEGATIVE_LEAKAGE_FIRST_UNPAID` with exact hypotheses and the first unpaid term. A replay-only pass closes algebra checking, not the arithmetic target. No repository/Lean changes or RH-promotion are authorized by this research directive.

## 11. Prediction closeout and execution record

P1–P5 were recorded before new exact checks in `scalejet_checks/predictions.txt`.

| Prediction | Fate |
|---|---|
| P1 finite positive scale mixture remains piecewise linear | Confirmed by (2.4); repaired by (2.6), not by deleting the discrete source |
| P2 endpoint smoothing alone gives no decay of finite prime atoms | Confirmed by (3.5); all-height sign still open |
| P3 explicit growing sufficient horizon exists | Confirmed by (5.9)–(5.12); intrinsic maximum not predicted or established |
| P4 moment/bandwidth/Lipschitz inputs alone do not bound peaks | Confirmed by exact family (8.3); not a prime-source counterexample |
| P5 moduli pay only auxiliary errors | Preserved: total signed target never replaced by a claimed uniform absolute bound |

The proof of a uniform bound on the explicitly growing jet closes an actual family quantifier, but not the full source upper-bound quantifier. The synthetic control narrows only the detector inference. Route score: 4 for quantitative scope clarification and falsification, not proximity to a completed RH proof.

CAS execution note: the first version of the symbolic replay timed out during general-purpose integration of a parameterized logarithmic expression. It was replaced by checking an explicit antiderivative and exact polynomial integration. The corrected replay below completed all eight groups. Timeouts are not counted as passed checks. No finite arithmetic evidence is promoted to a universal theorem.

Strategy memory:
```yaml
iteration:
  target: positive_scale_average_plus_growing_theta_jet
  status: PROGRESS
  failed_strategy: moment_upper_plus_bandwidth_automatically_bounds_peaks
  cognitive_operator_used: DUALIZE
  new_gap_name: actual_source_signed_detector_leakage_and_degree_price
  invariant_learned: positive_scale_weights_cannot_cancel_first_log_moment
  forbidden_future_move: treat_a_sufficient_K_horizon_as_a_necessary_degree_barrier
  next_decisive_test: signed_first_log_moment_in_the_local_concentration_eigenvector
```

## 12. External reference locators

Only standard polynomial facts were checked externally. Primary HTML:

- NIST DLMF §18.2(v): `https://dlmf.nist.gov/18.2#v`.
- NIST DLMF §18.9(i): `https://dlmf.nist.gov/18.9#i`.
- NIST DLMF §18.14(i), (18.14.1), specialized to Legendre: `https://dlmf.nist.gov/18.14#i`.

No external asymptotic for our theta-weighted Christoffel function was assumed. No new prime-distribution theorem or RH assumption entered the quantitative budgets.

## Appendix A. Exact replay

This code checks factors, elementary integral identities, the discrete/continuous kernel distinction, standard polynomial normalization and the explicit synthetic detector. It does **not** verify the analytic cofinal proofs numerically. Variables `ell,L` are logarithmic scales, `X` is a positive cutoff, `x,u` are integration variables. The polynomial density on `[1,2]` used by the replay checks the curvature identity; the main construction uses the C-infinity bump (2.1).

```python
"""Exact algebra checks for SCALEJET. Not an interval or RH certificate."""
import sympy as s

x, z, u, L, X = s.symbols('x z u L X', positive=True, real=True)
# 1. A finite positive mixture has nonzero derivative jumps.
nodes = [s.Rational(1), s.Rational(2), s.Rational(3)]
weights = [s.Rational(1, 6), s.Rational(1, 3), s.Rational(1, 2)]
assert sum(weights) == 1
for j, node in enumerate(nodes):
    before = -sum(weights[k] / nodes[k] for k in range(j, len(nodes)))
    after = -sum(weights[k] / nodes[k] for k in range(j + 1, len(nodes)))
    assert s.simplify(after - before - weights[j] / node) == 0
print('PASS discrete derivative jumps')

# 2. Continuous positive density test: C1 density, enough to check q''=rho/s.
rho = 30 * (L - 1)**2 * (2 - L)**2
assert s.integrate(rho, (L, 1, 2)) == 1
q = s.integrate(rho * (1 - x / L), (L, x, 2))
assert s.simplify(s.diff(q, x, 2) - rho.subs(L, x) / x) == 0
assert s.simplify(q.subs(x, 2)) == 0
assert s.simplify(s.diff(q, x).subs(x, 2)) == 0
print('PASS continuous curvature and upper endpoint')

# 3. Elementary weighted Chebyshev integration factors.
g = x**(-s.Rational(1, 2)) * s.log(X / x)
primitive = 2*s.sqrt(x)*s.log(X/x)+4*s.sqrt(x)
assert s.simplify(s.diff(primitive,x)-g)==0
I = s.simplify(primitive.subs(x,X)-primitive.subs(x,1))
assert s.simplify(I-(4*s.sqrt(X)-2*s.log(X)-4))==0
J=s.simplify(s.log(X)+I)
assert s.simplify(J-(4*s.sqrt(X)-s.log(X)-4))==0
print('PASS tapered coefficient-mass integral')

# 4. Source error constant at spatial weight 3.
c3 = 2 * (s.Rational(2, 3) + s.Rational(4, 25))
assert c3 == s.Rational(124, 75)
assert s.integrate(x**4 * s.exp(-6*x), (x, 0, s.oo))*2 == s.Rational(1, 162)
print('PASS log-moment and second-moment constants')

# 5. The positive-series bounds used in the strip estimate.
r = s.symbols('r', positive=True)
S0 = 1 / (1-r)
S2 = s.diff(r*s.diff(r*S0, r), r)
# sum n^p r^(n-1) from repeated Euler differentiation of sum r^n.
def moment_series(p):
    v = r/(1-r)
    for _ in range(p):
        v = s.simplify(r*s.diff(v, r))
    return s.simplify(v/r)
assert s.simplify(moment_series(2) - (1+r)/(1-r)**3) == 0
assert s.simplify(moment_series(4) - (1+11*r+11*r*r+r**3)/(1-r)**5) == 0
print('PASS theta envelope generating functions')

# 6. Finite checks of an inequality also proved by recurrence in the text.
for n in range(16):
    P = s.Poly(s.legendre(n, z), z)
    assert sum(abs(c) for c in P.all_coeffs()) <= 3**n
    P2=s.Poly(P.as_expr()**2,z)
    integ=sum(coeff*s.Rational(2,power[0]+1) for power,coeff in P2.terms() if power[0]%2==0)
    assert integ == s.Rational(2,2*n+1)
print('PASS Legendre normalization and coefficient controls (n<=15)')

# 7. The band-limited spike really is sinc squared and has the claimed slope cost.
ell, t = s.symbols('ell t', positive=True, real=True)
F = 2/ell * s.integrate((1-u/ell)*s.cos(t*u), (u, 0, ell))
assert s.trigsimp(F - 4*s.sin(ell*t/2)**2/(ell**2*t**2)) == 0
assert s.integrate(2*u*(1-u/ell)/ell, (u, 0, ell)) == ell/3
# Horizon with a half-unit error margin forces a baseline < 1/2.
assert 1/(6*c3) < s.Rational(1, 2)
print('PASS band-limited spike, slope, and baseline margin')

# 8. Exact conversion of a signed mean to a peak bound.
b, D, delta, p, A = s.symbols('b D delta p A', positive=True)
mean_lower = (b-D*delta)*p - A*(1-p)
peak_rhs = D*delta + (s.Symbol('C')+A*(1-p))/p
assert s.simplify(mean_lower.subs(b, peak_rhs)-s.Symbol('C')) == 0
print('PASS signed leakage factor and peak inequality')
```

Фактический stdout:

```text
PASS discrete derivative jumps
PASS continuous curvature and upper endpoint
PASS tapered coefficient-mass integral
PASS log-moment and second-moment constants
PASS theta envelope generating functions
PASS Legendre normalization and coefficient controls (n<=15)
PASS band-limited spike, slope, and baseline margin
PASS signed leakage factor and peak inequality
```

### Хеши фактически исполненных локальных материалов

```json
{
  "predictions.txt": "b03988c8d32b87261eaca8a907d1233fef6d1d66bf454976ed2b313be8896102",
  "exact_stdout.txt": "fbd5f38d0eb31cef07140825695dda292411e0d93ee77055447a53dc6992e0d4",
  "exact_checks.py": "413c12c2de43567f67a357eef79dc9dada96ca28699c2e6d3f229a3b813e47de"
}
```

Самопроверка выполнена, независимый audit-gate не закрыт. Ни этот replay, ни явный растущий горизонт не являются доказательством общей арифметической верхушки. **RH остаётся открытой в этом вердикте.**
