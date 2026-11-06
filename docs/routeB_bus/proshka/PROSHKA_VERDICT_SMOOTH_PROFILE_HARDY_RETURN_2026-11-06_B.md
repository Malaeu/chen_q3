# STATUS: TRY_EXACT_NB_SINE_WEIGHTED_ISOMETRY_B

```yaml
STATUS: TRY_EXACT_NB_SINE_WEIGHTED_ISOMETRY_B
OPERATIVE_CLASS: TRY_EXACT_NB_SINE_WEIGHTED_ISOMETRY_B
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_RH_AFTER_MOBIUS_RECIPROCITY
ANSWER: PARTIAL_EXACT_ISOMETRY_PAID_COMPLEMENT_AND_OPEN_ENDPOINT_ENERGY
FULL_RH_ACCEPTANCE: NOT_COMPLETE
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: ba1a6b496b496a0f9b64c2c81df83d131a456fdc
SPEC_FREEZE_BLOB: a1ba4c582b8cb17cc585a940e4d4ea3d905a33de
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_SMOOTH_PROFILE_HARDY_RETURN_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
FROZEN_P1: MISS_SPURIOUS_BOUNDARY_SUBTRACTION
INPUT_VERDICT_COMMIT: aabf1a70584f4151a27f8d99a23d47e33da34b9a
INPUT_VERDICT_BLOB: f568cd803251872ae9f7a5c7f1058abf03d62170
OPTIMAL_DIAG_COMMIT: ec1e2e961e07899824890db7f5fe39a89f2aa795
SMOOTH_DIAG_COMMIT: cffc56a52e0cf415c51d3a1a03c026d623e3d50c
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SMOOTH_PROFILE_HARDY_RETURN_2026-11-06_B.md
PROVED_STEPS:
  - {id: EXACT_ALL_COEFFICIENT_NB_TO_SINE_WEIGHTED_ISOMETRY, scope: FINITE_CELL, verifier: PAPER}
  - {id: MIDPOINT_JUMP_RETURN_WITH_ALL_BOUNDARY_TERMS_CANCELLED, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_SIGNED_PREFIX_SUPERPOSITION_FOR_SMOOTH_PROFILES, scope: FINITE_CELL, verifier: PAPER}
  - {id: UNIFORM_SMOOTH_PROFILE_FOURIER_BOUND_7_A_OVER_LOG_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: NORMALIZED_ENDPOINT_IS_NECESSARY_FOR_FIXED_PROFILE_CAPTURE, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: TRUE_LOG_TAPER_COMPLEMENT_COST_AT_MOST_63_ON_S, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: RIGHT_ZERO_FORCES_EXPLICIT_LOG_POWER_ENDPOINT_ENERGY, scope: COFINAL_FAMILY, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: EXACT_ONE_PARAMETER_PROFILE_IMPROVEMENT_FORMULA, scope: FINITE_CELL, verifier: PAPER}
RH_GAP: SOURCE_SPECIFIC_UPPER_BOUND_FOR_THE_WEIGHTED_ENDPOINT_LAYER
MINIMAL_MISSING_IDENTITY: "Exists C<infinity such that {N in S: J_N<=C} is unbounded; J_N=pi^2 integral_(1/N)^(1/log N) F_N(x)^2/sin^2(pi x) dx, for the unmodified linear Mobius taper. This is equivalent to the old core obligation, not newly proved."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: EXACT_POSITIVE_NORM_RETURN_AND_UNIFORM_COMPLEMENT_NOT_RH_SIGN
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: FROZEN_P1_EXTRA_SUBTRACTION
    KILL_SCOPE: ATTEMPT
    KILL_EVIDENCE_KIND: EXACT_ZERO_FREE_COEFFICIENT_COUNTEREXAMPLE
    EVIDENCE: SECTION_0_E_EQ_1_VERSUS_PROPOSED_RHS_EQ_0
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_FORMULA_ONLY
DOES_NOT_KILL: [RH, TRUE_CORE_ON_S, SMOOTH_PROFILES, OPTIMAL_NB_COEFFICIENTS, EXACT_RECIPROCITY, SOURCE_SPECIFIC_ENDPOINT_BOUNDS]
DISCRIMINATOR: EXACT_MELLIN_UNIT_AT_A_RIGHT_ZERO_AND_EXPLICIT_ENDPOINT_ENERGY_LOWER_ENVELOPE
REOPEN_TRIGGER: A source upper bound on J_N, or a bounded normalized smooth-profile family with the same paid endpoint control.
K8A:
  DOWNSTREAM_CONSUMER: SOURCE_CORRECT_NB_CAPTURE_THEN_RH
  ACTUAL_CONSUMER_REQUIREMENT: BOUNDED_POINTWISE_ZERO_RESIDUAL_SUBSEQUENCE
  ORIGINAL_REQUESTED_OBJECT: RH_PROOF
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_THE_STATED_GOAL
  TESTED_REPRESENTATION_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES: OPTIMAL_NB_CAPTURE_OR_DIRECT_LITERAL_WEIL_LOWER_BOUND
  FAILURE_TYPE: NO_DERIVATION_FOR_THE_ACTUAL_ENDPOINT_UPPER_BOUND
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: PROJECT_SPECIFIC_EXACT_SINE_WEIGHTED_RETURN_AND_PAID_COMPLEMENT_NOT_A_CLAIM_OF_HISTORICAL_PRIORITY
CLOSES: [SIGNED_RATIONAL_TRACE_AS_AN_EXTRA_RETURN_STEP, SMOOTH_PROFILE_BOUNDARY_NORMALIZATION, CORE_OUTSIDE_THE_ENDPOINT_LAYER]
OPENS: []
COGNITIVE_OPERATOR: DISCRETE_CHAIN_RULE_AND_WEIGHTED_ENERGY
ROUTE_SCORE: 3
NUMERICAL_TESTS: DIAGNOSTIC_ONLY_40_AND_70_DIGITS
EXACT_TESTS: POLYNOMIAL_IDENTITIES_AND_ZERO_COEFFICIENT_COUNTEREXAMPLE
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE
```

Ы. **RH не доказана.** Получен точный положительный возврат полной NB-нормы, без неоплаченного рационального sampling-функционала:

\[
 \boxed{\quad E_N=\frac{\pi^2}{2}\int_0^1
             \frac{|F_N(x)|^2}{\sin^2(\pi x)}\,dx.\quad}       \tag{1}
\]

Это равенство для всех конечных коэффициентов, а не только для μ. Но вес сингулярен у концов: малость обычной Fourier-нормы не доказывает малости (1). Для настоящего линейного taper на S весь вклад, кроме явно названного слоя, оплачен постоянной 63:

\[
 J_N\le E_N\le J_N+63,\qquad
 J_N=\pi^2\int_{1/N}^{1/\log N}
                 \frac{F_N(x)^2}{\sin^2(\pi x)}\,dx.          \tag{2}
\]

Нужная верхняя оценка J_N на неограниченной части S не получена. В отличие от неё, условная нижняя оценка при наличии правого нуля доказана количественно в §7. Для гладких профилей доказаны точная суперпозиция по префиксам, униформная аддитивная оценка и обязательная нормировка P(1). Численная подгонка профилей не названа доказательством ни одной cofinal-посылки.

## 0. Ошибка собственного freeze: результат проверки, не скрытая правка

[FINITE_CELL | PAPER.]

В P1 freeze была предсказана формула E=(π²/2)I−(1+u). Она **ложна**. При всех свободных коэффициентах a_n=0, n≥2, имеем E=1, u=0, F=sin(2πx)/π и I=2/π². Предсказанная правая часть равна 0. Это точный контрпример, не near-zero DIAG.

Причина: α=Σq_n=2b−2, а не 2b−1. После правильного учёта обеих граничных частей они сокращаются полностью и получается (1). Freeze оставлен побайтно неизменным; P1 получает MISS. Исправленная теорема ниже доказана заново. Ей не приписывается успешность неверного прогноза. Остальные объекты и целевой источник не изменены.

## 1. Источники и точная область использования

[FINITE_CELL | PAPER для source lock; прежние результаты — inherited PAPER, не новый независимый аудит.]

Короткие внутренние пути имеют префикс `docs/routeB_bus/`.

| Ref | Pin и blob | Использование |
|---|---|---|
| R | `proshka/PROSHKA_VERDICT_MOBIUS_RECIPROCITY_2026-11-06_B.md`; aabf1a70584f4151a27f8d99a23d47e33da34b9a; f568cd803251872ae9f7a5c7f1058abf03d62170 | Полный Gram, нормировки и bound 7/log N. Локальные 43508 bytes пересчитаны. |
| R8 | `proshka/PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md`; 70c4e6b097bc714689fb9226aeaea12a46127c95; e0c22e09de31ce8c3ee37e8c53343477168b2063 | S, его бесконечность, полный остаток и 0≤E_N−H_N≤6/log²N на S. Локальные 50860 bytes совпали. |
| D1 | `diag/OPTIMAL_VS_MOBIUS_2026-11-06/PART_A.md`; ec1e2e961e07899824890db7f5fe39a89f2aa795; c0855ca23d78857843b3ecd608449e6afa29c1b4 | Только finite коэффициентные сравнения. |
| D1b | `diag/OPTIMAL_VS_MOBIUS_2026-11-06/PART_B.md`; тот же commit; 563fab520e5b55b3e25139610940311514a2e0ec | Нет успешной общей гипотезы о локализации выигрыша по нулям. |
| D2 | `diag/SMOOTH_TAPER_FIT_2026-11-06/REPORT.md`; cffc56a52e0cf415c51d3a1a03c026d623e3d50c; e32f725326ec74c4269af613dc4f8ee81a9a564d | Подгонка меняется с N; raw a_1=1; численные ошибки — DIAG. |
| D2b | `diag/SMOOTH_TAPER_FIT_2026-11-06/PART_B.md`; тот же commit; 191c721e808f5fe910f2195ed2540cbbcc836dea | Корректная divisor-формула и граничные соглашения. |
| Context | Summary rh_clean 1c870b51, blob df730a5d44e5aee76b02e9c1532e4970d593f942; literature 15398196, blob 3c69a4d7f54507c4aeee385d1879f1457214ee8d | Указатели из запроса; не поставщики нового знака. |

**THEOREM T1:** Bettin–Conrey, *Period functions and cotangent sums*, arXiv:1111.0931v2, (13), печатная p.12; опубликовано Algebra & Number Theory 7 (2013), 215–242. Импортируется точная Vasyunin-формула, не оценка мёбиусовой квадратичной формы. Прочитаны arXiv-текст и издательская версия. Попытки web-screenshot страниц 12–13 arXiv вернули cache miss; визуальная проверка этих страниц не заявляется. Целевой поиск erratum/correction отдельного исправления используемой формулы не выявил; это ограниченный поиск.

**THEOREM T2, только контекст обратного NB-критерия:** Báez-Duarte, arXiv:math/0202141v2, Theorem 1.1. Первая страница прочитана и проверена screenshot. Карточка v2 указывает исправление трёх опечаток и добавленную ссылку. Прямая достаточность нашей остаточной леммы доказывается в §8, не импортируется как безусловная сходимость.

```text
https://arxiv.org/pdf/1111.0931v2
https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf
https://arxiv.org/pdf/math/0202141v2
```

Историческая новизна изометрии или общих Stieltjes-приёмов не заявляется. Цель — точный возврат в данном source-locked маршруте. BCF, гипотезы о простоте нулей и RH не являются посылками новых оценок.

## 2. Определения и точное положительное представление

[FINITE_CELL | PAPER.]

Пусть N≥2, a_2,…,a_N вещественны, а фиктивный raw a_1=1. Определим

    r_n(k)=(k mod n)/n, w_k=1/[k(k+1)],
    R(k)=1+sum_(n=2)^N a_n r_n(k), E=sum_(k>=1)w_k R(k)^2,
    s=1+sum_(n=2)^N a_n/n, u=sum_(n=2)^N a_n log(n)/n,
    q_1=1-s, q_n=a_n (n>=2), alpha=sum q_n,
    b=1+alpha/2, sum q_n/n=0.

B_1(x)={x}−1/2 вне целых, B_1(x)=0 на целых. Положим

\[
 F(x)=\frac{\sin(2\pi x)}\pi+
       \sum_{n=2}^N\frac{a_n}{n}\bigl(B_1(nx)-B_1(x)\bigr).
                                                               \tag{3}
\]

Это та же F из R. На (0,1), вне конечного множества скачков,

\[
 F(x)=\alpha x-\sum_{n=2}^N\frac{a_n}{n}\lfloor nx\rfloor
                         +\frac{\sin(2\pi x)}\pi.              \tag{4}
\]

Имеем F(1−x)=−F(x), midpoint в каждом скачке, F(x)=O(x) при x↓0 и F(x)=O(1−x) при x↑1. Поэтому интеграл в (1) конечен. Ни одно сглаживание скачков не требуется.

### Теорема 1 — изометрия без дефекта

Для всех конечных комплексных c_0,a_2,…,a_N:

\[
 \sum_{k\ge1}\frac{|c_0+\sum_{n=2}^N a_n r_n(k)|^2}{k(k+1)}
 =\int_0^1\left|c_0\phi_0(x)+\sum_{n=2}^N a_n\phi_n(x)\right|^2dx,
                                                               \tag{5}
\]
\[
 \phi_0(x)=\sqrt2\cos(\pi x),\qquad
 \phi_n(x)=\frac{\pi}{\sqrt2\,n}
              \frac{B_1(nx)-B_1(x)}{\sin(\pi x)}.               \tag{6}
\]

В частности (1) верно. Цепочка `I на L²(0,1) → Gram(φ_0,…,φ_N)` положительна для любых коэффициентов и даёт ПОЛНЫЙ бесконечный NB-Gram точно. Обратимость на всём L² или совпадение с пространством CCM не утверждается: изометрия определена на алгебраическом линейном пространстве цели и остатков и продолжается на его замыкание.

### Доказательство: сначала полный source-return, затем все скачки

J переводит последовательность z(k) в ступенчатую функцию z(k) на (1/(k+1),1/k]; длина этой ячейки равна w_k, поэтому J — изометрия. В частности Jr_n(y)={1/(ny)}−{1/y}/n.

Для ρ_h(y)={1/(hy)}, d=(h,k), T1 со масштабированием даёт

    <rho_h,rho_k> = C0(1/h+1/k)/2
       +(k-h)log(h/k)/(2hk)
       -pi*d[V((h/d)/(k/d))+V((k/d)/(h/d))]/(2hk),
    C0=log(2*pi)-gamma_E,
    V(h/k)=sum_(r=1)^(k-1){rh/k}cot(pi*r/k) для (h,k)=1.

Множитель d сохранён. Комбинация g=Σq_nρ_n равна Σa_n Jr_n на (0,1) и нулю на (1,∞), поскольку Σq_n/n=0. Из исходного целочисленного словаря <1,Jr_n>=log(n)/n, поэтому <1,g>=u. При суммировании Gram C0-часть исчезает, логарифмическая часть равна αu. С конечным T=Σq_hq_k(h,k)V((h/d)/(k/d))/(hk) получаем

    E=1+(alpha+2)u-pi*T.

Котангенсная multiplication-формула, включая общие делители, даёт для функционала из R

    L_q(F)=sum_(n=2)^N (a_n/n) sum_(r=1)^(n-1)cot(pi*r/n)F(r/n)
          =T+(alpha+1-s)/pi.

Следовательно старый возврат для произвольных вещественных коэффициентов:

\[
 E=(\alpha+2)(1+u)-s-\pi\mathfrak L_q(F).                     \tag{7}
\]

Теперь используем, что sampler взят на той же F, чьи скачки он содержит. Обозначим конечную signed measure

    dnu=sum_(n=2)^N (a_n/n) sum_(r=1)^(n-1)delta_(r/n).

Внутри (0,1), как меры,

\[
 dF=(\alpha+2\cos(2\pi x))dx-d\nu.
\]

Для конечных скачков точное правило цепочки имеет вид d(F²)=2F_mid dF: на атоме это равенство (F_+)²−(F_−)²=(F_++F_−)(F_+−F_−). Поэтому интегрирование по частям даёт

\[
 \mathfrak L_q(F)=\int_0^1\cot(\pi x)F(x)
                    (\alpha+2\cos(2\pi x))dx
                   -\frac\pi2\int_0^1\frac{F(x)^2}{\sin^2(\pi x)}dx.
                                                               \tag{8}
\]

Граничный член cot(πx)F(x)²/2 стремится к нулю на обоих концах. Внутренние скачки учтены midpoint-правилом, а не отброшены.

Остаются два элементарных интеграла:

\[
 \int_0^1F(x)\cot(\pi x)dx=\frac{1+u}\pi,
 \qquad \int_0^1F(x)\sin(2\pi x)dx=\frac{s}{2\pi}.             \tag{9}
\]

Для первого положим Z=F−sin(2πx)/π. Интегрируем против d log sin(πx). Формула
`product_(r=1)^(n-1) 2 sin(pi*r/n)=n` следует из (z^n−1)/(z−1) при z=1. Значит сумма log sin по скачкам равна u−α log2; непрерывный член даёт α log2, поскольку ∫log sin=−log2. Получаем ∫Z cot=u/π, а синус добавляет 1/π. Второе равенство — первая Fourier-компонента B_1: у F коэффициент sin(2πx) равен s/π.

Наконец cot(πx)cos(2πx)=cot(πx)−sin(2πx). Подстановка (9) в (8) даёт

\[
 \pi\mathfrak L_q(F)=(\alpha+2)(1+u)-s-\frac{\pi^2}{2}I.
\]

Сравнение с (7) доказывает E=π²I/2. Для общего c_0 сначала применяем однородность при c_0≠0 и непрерывность при c_0=0. Равенство вещественных квадратичных форм доказывает равенство их вещественных симметричных Gram-матриц; поляризация переносит его на комплексные коэффициенты. □

**Сохранено:** все индексы, исходный вес 1/[k(k+1)], target 1, полная бесконечная норма и centering. Никакой остаток на большом k, q_1 или рациональном скачке не скрыт. Положительность (5) сама по себе не доказывает приближение цели.

## 3. Что новые численные данные действительно меняют

[FINITE_CELL | PAPER для формул; числа D1/D2 — DIAG.]

Пусть R=1+g — любой один кандидат, E=||R||², m=<R,1>=1+u, v=||g||²=E−2m+1>0. Простое масштабирование свободных коэффициентов даёт

\[
 E(t)=\|1+tg\|^2=1+2tu+t^2v,
 \quad t_*=-u/v,\quad
 E(t_*)=\frac{E-m^2}{E-2m+1},
 \quad E-E(t_*)=\frac{(E-m)^2}{E-2m+1}.                       \tag{10}
\]

Это точная одномерная ортопроекция, не новая RH-оценка. На N=5000 D2 сообщает E_log=0.0233363799923, E_opt=0.00530702068301, E_linear_free=0.00660972470835 и E_cubic_free=0.00631003487605. Из этих округлённых DIAG-чисел:

    закрытая доля gap одной свободной амплитудой: 92.77454%;
    закрытая доля gap свободной кубикой:          94.43677%;
    первая доля от всего кубического улучшения:  98.23985%.

Поэтому 94% нельзя целиком приписывать новой форме кубики: почти всё конечное улучшение уже даёт масштабирование исходного луча. Это не отрицание оставшегося выигрыша кубики и не асимптотическая теорема.

У свободной конечномерной оптимизации автоматически E_min≤1 (доступен нулевой вектор коэффициентов). Такая ограниченность не доказывает RH: остатки могут не стремиться поточечно к нулю. Пример a_n=0 даёт E=1 и R(k)=1 навсегда. Нормировка профиля в следующем разделе не факультативна.

## 4. Гладкий профиль: точная смесь префиксов, а не новый источник

[FINITE_CELL / COFINAL_FAMILY | PAPER, без RH.]

Пусть P(0)=0, P' абсолютно непрерывна на [0,1], P''∈L¹. Это включает полиномы и C¹-сплайны D2. Обозначим

    A(P)=|P'(0)|+integral_0^1 |P''(v)|dv,
    a_1=1, a_n=mu(n)P(log(N/n)/L), 2<=n<=N, L=log N.

Для реального X>1 определим прежний линейный taper с n≤X и log X вместо log N. Индекс 1 всегда raw=1. Обозначения R_X,F_X,s_X относятся к этому непрерывному префиксу, а R_{N,P},F_{N,P},s_{N,P} — к новому профилю.

Тейлорово равенство с интегральным остатком даёт

\[
 P(t)=P'(0)t+\int_0^1P''(v)(t-v)_+dv.
\]

Поскольку (log(N/n)/L−v)_+=(1−v)log(X/n)/log X при X=N^{1−v}, n≤X, получаем ТОЧНО

\[
 R_{N,P}=(1-P(1))\,1+P'(0)R_N+
       \int_0^1(1-v)P''(v)R_{N^{1-v}}\,dv,                  \tag{11}
\]
\[
 F_{N,P}=(1-P(1))\frac{\sin(2\pi x)}\pi+P'(0)F_N+
       \int_0^1(1-v)P''(v)F_{N^{1-v}}\,dv.                  \tag{12}
\]

Точка v=1 имеет нулевой вес; при X<2 свободный словарь пуст. Равенства конечномерны для каждого N, поэтому нет непроверенной перестановки бесконечных сумм. Масса signed-весов равна P(1), но они вообще не неотрицательны. Например, у (3t−t³)/2 второе производное равно −3t. Применять к (11) Jensen как к вероятностной смеси нельзя.

### Теорема 2 — все аддитивные ошибки гладкого профиля оплачены

Для N≥3:

\[
 \left\|F_{N,P}-(1-P(1))\frac{\sin(2\pi x)}\pi\right\|_2
            \le\frac{7A(P)}L,\qquad
 |s_{N,P}-(1-P(1))|\le\frac{5A(P)}L.                         \tag{13}
\]

Доказательство: линейные bounds R, ||F_X||≤7/log X и |s_X|≤5/log X, верны и для вещественного X≥3 — те же конечные divisor-суммы и tail-сравнения. Для 1<X<3 имеется не более одной свободной координаты и эти грубые константы верны непосредственно. Вторую оценку можно получить без R: положим B(X)=Σ_{n≤X}μ(n)log(X/n)/n. Из Σμ(d)floor(X/d)=1 следует |Σμ(n)/n|≤2; из Σμ(d)H_floor(X/d)/d=1 и |H_floor(y)−log y−γ_E|≤2/y следует |B(X)|<5. Поэтому |s_X|≤5/log X.

Применяем Minkowski к (12) и аналогичному равенству для s. В интеграле (1−v)/log(N^{1−v})=1/L. Это доказывает (13). □

Для полноты линейная Fourier-оценка использует точные коэффициенты

    sum_(n|r,n<=X) mu(n)(1-log n/log X)
       =1_(r=1)+Lambda(r)/log X,  r<=X.

Все степени простых сохранены. Parseval даёт конечный положительный Λ²-член плюс хвост, который мажорируется Σ_{r>X}d_4(r)/r². Элементарный divisor-count даёт хвост ≤2[(log X)^3+6(log X)^2+15log X+16]/X. Это перенос прежней доказанной аддитивной оценки, не предположение о NB-норме.

**Поправка raw a_1.** Для полинома P(t)=Σp_jt^j точный head при r≤N равен

\[
 \sum_{n\mid r}a_n=1-P(1)+
 \sum_j\frac{p_j}{L^j}\sum_{k=0}^j{j\choose k}
       \log(N/r)^{j-k}\Lambda_k(r),\quad
 \Lambda_k=\mu*\log^k.                                      \tag{14}
\]

Здесь Λ_0(r)=1_{r=1}. Член 1−P(1) относится к каждому r. Формула следует раскрытием log(N/n)=log(N/r)+log(r/n), без изменения μ. В частности P=t²,N=4,r=2 даёт 3/4, а не 1/4. Неверная исходная формула диагностического задания не импортируется.

### Нормировка цели: необходимое условие, не эстетика fit

Для фиксированного k и N≥k точная floor-формула вместе с (13) даёт

\[
 |R_{N,P}(k)-(1-P(1))|
 \le\frac{5kA(P)+\|P'\|_\infty
          \sum_{n=2}^k\log n\lfloor k/n\rfloor}{L}.          \tag{15}
\]

В выводе использованы Σ_{n≤k}μ(n)floor(k/n)=1 и |P(1−log n/L)−P(1)|≤||P'||∞log n/L. Следовательно фиксированный профиль имеет R_{N,P}(k)→1−P(1). По Fatou

\[
 \liminf_{N\to\infty}E_{N,P}\ge|1-P(1)|^2.                  \tag{16}
\]

Для семейства P_N с sup A(P_N)<∞ и P_N(1)→1 формула (15) обеспечивает поточечный нулевой предел. Без этой нормировки одно E_min≤1 не даёт bounded-pointwise-zero receiver. Четыре значения P_N(1) из fit не доказывают его предел.

## 5. Оплаченная область и точный остаток у края

[COFINAL_FAMILY | PAPER.]

Вернёмся к неизменённому линейному taper. N∈S, N≥8, L=log N, δ=1/L. Определим J_N из (2), то есть вклад двух симметричных слоёв [1/N,1/L] и [1−1/L,1−1/N]. Положим

\[
 V_N=\frac{\pi^2}{2}\int_\delta^{1-\delta}
                         \frac{F_N(x)^2}{\sin^2(\pi x)}dx,
\]
\[
 C_N=\pi^2\int_0^{1/N}\frac{F_N(x)^2}{\sin^2(\pi x)}dx.
\]

Изометрия даёт трёхчастный ТОЧНЫЙ объект

\[
                       E_N=J_N+V_N+C_N,\qquad J_N,V_N,C_N\ge0.
                                                               \tag{17}
\]

Все три интеграла вычислимы из конечной кусочно-аналитической F_N; это не усечение исходной бесконечной нормы без remainder.

**Средняя область.** При δ≤x≤1−δ имеем sin(πx)≥2δ. Из ||F_N||≤7/L:

\[
                         V_N\le49\pi^2/8<62.                \tag{18}
\]

**Самый край.** На 0<x<1/N ещё нет ни одного внутреннего скачка, и ТОЧНО

\[
 F_N(x)=2b_Nx+\frac{\sin(2\pi x)-2\pi x}{\pi}.
                                                               \tag{19}
\]

По |sin y−y|≤|y|³/6 и sin(πx)≥2x получаем

\[
 C_N\le\frac{2\pi^2b_N^2}{N}+\frac{8\pi^6}{45N^5}
       \le\frac{\pi^2}{2NL^2}+\frac{8\pi^6}{45N^5}<1.        \tag{20}
\]

Здесь использовано только доказанное R8 |b_N|≤1/(2L) на S. Для последнего строгого неравенства достаточно π²<10, π⁶<1000, L>2 и N≥8. (17)–(20) доказывают (2).

Для нормированного гладкого P(1)=1 те же рассуждения дают, без отбора S,

\[
 E_{N,P}\le J_{N,P}+\frac{49\pi^2}{8}A(P)^2
             +\frac{2\pi^2b_{N,P}^2}{N}
             +\frac{8\pi^6}{45N^5}.                          \tag{21}
\]

Последние два параметра не объявлены малыми у всех переобученных профилей. Гладкость по log n сама по себе не устраняет скачки по x.

**Что осталось.** R8 даёт на S 0≤E_N−H_N≤6/L². Вместе с (2)

    J_N <= H_N+6/L²,       H_N <= J_N+63.              (22)

Поэтому bounded J_N на неограниченной части S эквивалентно прежнему bounded-core обязательству. (18)–(20) закрывают новые равномерные кванторы о дополнении слоя, но не доказывают его малость.

## 6. Попытка оплатить сам слой и точное место остановки

[FINITE_CELL | PAPER для раскрытия; COFINAL_FAMILY | CONDITIONAL для нужной верхней границы.]

Внутри слоя остаётся настоящая конечная signed-сумма. Из (4), для x∈(0,1), вне скачков,

\[
 F_N(x)=(2b_N-2)x+\frac{\sin(2\pi x)}\pi
   -\sum_{j\le Nx}\ 
       \sum_{\max(2,\lceil j/x\rceil)\le n\le N}
          \frac{\mu(n)}n\frac{\log(N/n)}L.                    \tag{23}
\]

На скачках используется midpoint; их значения не меняют интеграл. Это совместные суммы на интервалах, связанных одним x. Ни знаки μ, ни общая история не заменены независимыми амплитудами. Взятие модулей до суммирования теряет именно эту связь.

Ни (23), ни точная polynomial convolution (14), ни profile-superposition (11) не дали независимой постоянной upper envelope для J_N. На S остаётся лишь прежняя грубая оценка

\[
             0\le J_N\le E_N\le(290N+6)/L^2.                \tag{24}
\]

Она взята из R8 и не является новым выигрышем. Раздельная оплата норм в signed смеси (11) требует неизвестных NB-норм меньших префиксов; оценка (13) относится к другой, невзвешенной норме. Ни одно из этих мест не превращено в скрытую посылку RH.

Основная неоплаченная строка:

\[
 \exists C<\infty:\quad
             \{N\in\mathcal S:J_N\le C\}\text{ неограниченно}. \tag{25}
\]

**(25) не доказано.** Это не новое более слабое арифметическое условие. Новое — точная изометрия и доказанная стоимость дополнения сингулярного слоя, а не доказательство (25). No unconditional NB-rate, no new Weil lower floor, RH_SIGN_PROGRESS=NONE.

## 7. Правый нуль вынуждает количественный рост именно этого слоя

[COFINAL_FAMILY | PAPER: импликация при наличии указанного нуля, не утверждение о его существовании.]

Это дополнительное аналитическое следствие, не записанное задним числом как предсказание freeze.

Пусть настоящий нуль ζ равен ρ=β+iγ, 1/2<β<1. Mellin-равенство исходного словаря даёт для любого N

\[
 \int_0^1 (JR_N)(y)y^{\rho-1}dy=1/\rho.                     \tag{26}
\]

Для целых 1≤k≤N имеем R_N(k)=k s_N−ψ(k)/L и |R_N(k)|≤17k/L: |s_N|≤5/L, ψ(k)≤12k, все prime powers сохранены. При 1≤K≤N разделим (26) в y=1/(K+1). На оставшейся части |JR_N(y)|≤17/(Ly); на малой части применим Cauchy–Schwarz. Получаем конечное неравенство

\[
 \sqrt{E_N}\ge\sqrt{2\beta-1}(K+1)^{\beta-1/2}
 \left[\frac1{|\rho|}-\frac{17}{L}
       \frac{(K+1)^{1-\beta}-1}{1-\beta}\right]_+.           \tag{27}
\]

Оно не использует простоты нуля и не предполагает, что он единственный вне линии.

Положим Y=[(1−β)L/(34|ρ|)]^{1/(1−β)}. Когда 2≤Y≤N (что верно при всех достаточно больших N), берём K=floor(Y)−1. Тогда

\[
 E_N\ge\frac{2\beta-1}{4|\rho|^2}
                  (Y/2)^{2\beta-1}.                        \tag{28}
\]

На S из (2):

\[
 J_N\ge\frac{2\beta-1}{4|\rho|^2}
       \left[\frac12\left(\frac{(1-\beta)L}{34|\rho|}\right)^{
                         1/(1-\beta)}\right]^{2\beta-1}-63.
                                                               \tag{29}
\]

Показатель L равен (2β−1)/(1−β)>0. Например, **для гипотетического настоящего ζ-нуля** β=5/6 он равен 4. Это не перенос старого μ-head на искусственно изменённую completion: для planted мира нужно сначала построить его собственный source-match, см. §9. Оценка (29) делает (25) несовместимым с любым настоящим правым нулём, но сама по себе не поставляет upper bound и не исключает такой нуль.

## 8. Полный receiver: где именно кончается доказанное

[COFINAL_FAMILY | PAPER для импликации; CONDITIONAL для (25).]

При (25) выберем N_j∈S→∞ с J_{N_j}≤C. По (2) E_{N_j}≤C+63. По точной head-формуле R_{N_j}(k)→0 для каждого фиксированного k. В H=ell²(w) ограниченная поточечно нулевая последовательность слабо стремится к нулю: сначала конечная поддержка, затем Cauchy–Schwarz на хвосте фиксированного теста.

Из неё выбирается подпоследовательность с |<R_i,R_j>|≤2^{−i−j}. Тогда для её средних

\[
 e_{N_J}\le\left\|\frac1J\sum_{j=1}^J R_{N_j}\right\|^2
               \le\frac{C+63}{J}+\frac1{J^2}\longrightarrow0. \tag{30}
\]

Среднее остаётся допустимым конечным NB-приближением. Mellin-формула для Jr_n(y)={1/(ny)}−{1/y}/n есть

\[
 \int_0^1 Jr_n(y)y^{s-1}dy
                 =\zeta(s)(1/n-n^{-s})/s,\quad\Re s>0.       \tag{31}
\]

В каждом правом нуле она обнуляется; target transform равен 1/ρ. Значит e_N≥(2β−1)/|ρ|². Это противоречит (30). Стандартное функциональное уравнение отражает левый нуль вправо, поэтому (25)⇒RH. Можно также прямо использовать (29).

После capture прежний R7 finite bridge возвращает для каждого достигнутого e_N≤1/m буквальный A_m с ценой 36000(1+log m)^3G_m. Это inherited PAPER-стрелка, а не новая finite-cell сертификация A_m. Невыполненная стрелка остаётся единственной: источник ⇒ (25).

Для меняющихся нормированных профилей (21), sup A(P_N)<∞, bounded b_{N,P_N}²/N и bounded J_{N,P_N} на неограниченной последовательности аналогично дали бы bounded E и поточечный нулевой предел по (15), затем RH. Существование такой семьи с этими bounds не доказано; конечные fitted profiles D2 её не заменяют.

## 9. Сильнейшая атака и собственные источники отрицательных миров

[ABSTRACT / COFINAL_FAMILY | PAPER; используется прежний source dictionary, не новый аудит расположения нулей фейков.]

**Не доказали ли мы RH из малого обычного L²?** Нет. Множитель 1/sin²(πx) не ограничен. (18) оплачивает только среднюю область; (19) оплачивает самый узкий конец; слой между ними не исчезает. На всём классе пробных функций остаётся aliasing-контрпример R. Здесь он не применялся как F: новый возврат связывает sampler с собственными скачками конкретной F. Противоречия нет.

**Контрмассив R9.** Изометрия (5) верна и для его изменённых коэффициентов: это all-input identity, не детектор μ. Но head convolution (14) и малая нормированная Fourier-ошибка уже не следуют. На первом изменённом индексе n_0 имеем Σ_{d|n_0}c_d=−2β_{n_0}≠0. Так названа ровно потерянная арифметика, а не объявлено, что чужой коэффициентный вектор разрушает общую изометрию.

**DMV.** Целые интервалы (1/(k+1),1/k] и остатки k mod n в (31) представляют обычную ζ, не Beurling Z. Для собственного источника DMV ломается additive Mellin source-match; стандартное функциональное уравнение ему не приписывается. Любой корректный L²-null-словарь при его правом нуле имел бы тот же положительный evaluation barrier, несовместимый с bounded-pointwise-zero capture. Обычная F_N не объявляется собственным Fourier-остатком DMV.

**DH.** Требуются его Dirichlet-коэффициенты, odd-Gamma, conductor 5, отсутствие ζ-полюса. Подстановка D(s) вместо ζ(s) в (31) неверна. Для source-correct null-словаря правый DH-нуль запрещает capture той же нормой функционала оценки. Никакой обычный μ не подменяет его источник.

**Подсадка a=1/3.** При стандартной Gamma новый uncompleted фактор Z_Q(s)=Q(s−1/2)ζ(s)/Q(1/2) не равен ζ. Формула (31) со старым словарём не представляет Z_Q. В полной Weil-форме Q'/Q и квартетное ядро сохраняются. Для корректного заменяющего словаря правый нуль даёт evaluation obstruction; конкретный коэффициент 17 из (27) нельзя переносить без доказательства собственного head-bound.

**Самодуальные v_b.** У них арифметическая ζ может остаться прежней, но local Mellin factor меняется на Q_b(s−1/2) times Gaussian/Gamma. Наш вывод о нулях ζ не удаляет нули Q_b. Последний шаг к стандартной ξ использует ТОЧНО

    integral_0^infinity exp(-pi x²)x^(s-1)dx
         =(1/2)pi^(-s/2)Gamma(s/2), Re s>0,
    xi(s)=(1/2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s).

Здесь же входят стандартная функциональная симметрия и отсутствие нулей Γ. Положительность/self-duality без точного множителя не заменяют source-match.

**Кривая E/F3.** Собственный источник h=log3 имеет точную положительную форму

    W_E[f]=2h integral_0^(2h) |sum_(j in Z)(-1)^j f(x+2hj)|² dx.

При компактной поддержке сумма локально конечна, а Parseval даёт собственную спектральную гребёнку. Буквальные оконные сжатия PSD с нулевым дефектом. Обычный μ-профиль ей не навязывается. Это положительный контроль сохранённого source-return, не утверждение, что построен универсальный ζ/curve dictionary.

## 10. Проверки, прогнозы и delivery

[FINITE_CELL | PAPER для точной алгебры; вычисления — DIAG.]

После freeze проверены 27 случаев при 40 и 70 десятичных знаках: N=2,3,4,8,16; P=t,t²,2t−t²,(3t−t³)/2,2t; отдельный рациональный вектор и отдельный r_2-контроль. Сопоставлены независимо: полный Vasyunin-Gram, рациональный cotangent trace и кусочная квадратура weighted integral. Для N≤8 дополнительно просуммирован ВЕСЬ периодический остаток с точными digamma-весами, без отбрасывания хвоста:

    Q=lcm(1,...,N),
    W_j=[digamma((j+1)/Q)-digamma(j/Q)]/Q,
    E=sum_(j=1)^Q W_j |R(j)|².

Максимальные абсолютные ошибки:

| dps | weighted integral против полного Gram | cotangent return | полный период |
|---:|---:|---:|---:|
| 40 | 4.60e-41 | 5.03e-41 | 1.15e-40 |
| 70 | 5.44e-71 | 6.57e-71 | 8.16e-71 |

Это не Arb-интервалы. Универсальные равенства доказаны в §§2–5; десятичные near-zero не используются как доказательство. Точные polynomial checks подтвердили P(t)=P'(0)t+∫(t-v)P''(v)dv для пяти тестовых профилей. Доказательства (18)–(21), (27)–(29) не зависят от сетки.

**Скорборд freeze.** P1 — MISS, с точным counterexample §0; corrected theorem (1) не переименован в HIT. P2 — HIT: (11)–(16), скачки не исчезают. P3 — HIT: константа 63 вне слоя. P4 — HIT как конечная проверка: 92.77% закрывает одно масштабирование; cofinal-стабильность не установлена. P5 — RH-upper-bound NOT_PROVED, остановка (25). Дополнительный zero-implies-log-power вывод §7 не был прогнозом и не получил ретроспективный HIT.

**Две оставшиеся репрезентации.** (A) Оценивать реальную source-coupled сумму (23) непосредственно в положительной endpoint-энергии J_N; kill-power высокий благодаря (29), аналитическая стоимость высокая. (B) Работать с полным рациональным upper Gram R8 или малым profile-Galerkin Gram, сохраняя все перекрёстные элементы и нормировку цели; достаточная обязанность — source-correct bounded pointwise-zero family, а не малая обычная Fourier-норма. Стоимость конечного контроля ниже в малой profile-модели, но uniform-in-N арифметическая цена не установлена. Оба пути открыты, ни один не объявлен бесплатным.

**K8A.** DOWNSTREAM_CONSUMER=RH через NB capture. ACTUAL_CONSUMER_REQUIREMENT — bounded pointwise-zero residual subsequence либо другой доказанный source receiver. ORIGINAL_REQUESTED_OBJECT=RH proof; выбранная weighted coordinate не обязательна. KNOWN_WEAKER_INTERFACES — оптимальное NB capture, true-core bound, прямой signed Gaussian receiver. FAILURE_TYPE=NO_DERIVATION для (25), EPISTEMIC_STATUS=RESEARCH_DEBT. Reopen trigger — новый upper bound для реального слоя или source-controlled normalized profile family. Для собственного ошибочного P1: KILL_SCOPE=ATTEMPT, evidence §0, reopen только после изменения ложной формулы, не переписывания freeze. Полный путь RH не объявляется мёртвым.

```yaml
iteration:
  target: SOURCE_SPECIFIC_SMOOTH_PROFILE_RETURN_TO_NB
  status: PROGRESS
  cognitive_operator_used: DISCRETE_CHAIN_RULE_AND_WEIGHTED_ENERGY
  new_gap_name: TRUE_MOBIUS_ENDPOINT_ENERGY_ON_ONE_LOGARITHMIC_LAYER
  invariant_learned: THE_FULL_NB_NORM_IS_EXACTLY_THE_SINE_WEIGHTED_FOURIER_NORM
  forbidden_future_move: REPLACE_THE_SINGULAR_WEIGHT_BY_UNWEIGHTED_L2_SMALLNESS
  next_decisive_test: SOURCE_BOUND_FOR_THE_ACTUAL_ENDPOINT_LAYER_NOT_ANOTHER_FINITE_FIT
  route_score: 3
```

**Verification handoff.** Записываются только отдельный freeze и этот новый вердикт под `docs/routeB_bus/proshka/` в `proshka_inbox_2026-10-31`. Commit/blob freeze указаны в YAML. Финальный commit и blob сообщаются в квитанции после записи и повторного чтения; сам файл не содержит собственного будущего SHA. Старые verdicts, state и Lean не редактируются. Независимый аналитический аудит, Lean и Arb не выполнены.

## 11. Воспроизводимая конечная проверка

Код ниже проверяет нормировки, а не RH. `dps` — десятичная точность; `a[2:]` — реальные свободные коэффициенты. Начальные `a[0]=0,a[1]=1` фиксированы. Например `[0,1,-1]` задаёт R=1−r_2. Требуется mpmath: `uv run --with mpmath python check.py`. Изменение точности не является интервальной сертификацией.

```python
from fractions import Fraction
from math import gcd, lcm
import mpmath as mp

mp.mp.dps = 70

def vasyunin(h, k):
    return sum(mp.mpf((r*h) % k)/k * mp.cot(mp.pi*r/k)
               for r in range(1, k))

def gram_rho(h, k):
    d = gcd(h, k)
    return ((mp.log(2*mp.pi)-mp.euler)*(mp.mpf(1)/h+mp.mpf(1)/k)/2
            +mp.mpf(k-h)*mp.log(mp.mpf(h)/k)/(2*h*k)
            -mp.pi*d*(vasyunin(h//d,k//d)+vasyunin(k//d,h//d))/(2*h*k))

def check(values):
    a = list(map(mp.mpf, values)); N = len(a)-1
    assert N >= 2 and a[0] == 0 and a[1] == 1
    E = 1+2*sum(a[n]*mp.log(n)/n for n in range(2,N+1))
    for h in range(2,N+1):
        for k in range(2,N+1):
            E += a[h]*a[k]*(gram_rho(h,k)-gram_rho(h,1)/k
                            -gram_rho(1,k)/h+gram_rho(1,1)/(h*k))
    alpha = sum(a[n]*(1-mp.mpf(1)/n) for n in range(2,N+1))
    knots = sorted({Fraction(j,n) for n in range(1,N+1)
                    for j in range(n//2+1)} | {Fraction(1,2)})
    weighted = mp.mpf(0)
    for left,right in zip(knots,knots[1:]):
        middle = (left+right)/2
        offset = -sum(a[n]/n*((n*middle.numerator)//middle.denominator)
                      for n in range(2,N+1))
        lo = mp.mpf(left.numerator)/left.denominator
        hi = mp.mpf(right.numerator)/right.denominator
        # Centering is imposed algebraically: no rounded endpoint constant.
        def F(x):
            return alpha*x+offset+mp.sin(2*mp.pi*x)/mp.pi
        weighted += mp.pi**2 * mp.quad(
            lambda x: (F(x)/mp.sin(mp.pi*x))**2, [lo,hi])
    print('E=',mp.nstr(E,35), 'weighted=',mp.nstr(weighted,35),
          'difference=',mp.nstr(abs(E-weighted),8))
    if N <= 8:
        Q = lcm(*range(1,N+1))
        direct = mp.mpf(0)
        for j in range(1,Q+1):
            w = (mp.digamma(mp.mpf(j+1)/Q)-mp.digamma(mp.mpf(j)/Q))/Q
            R = 1+sum(a[n]*mp.mpf(j % n)/n for n in range(2,N+1))
            direct += w*R**2
        print('complete periodic error=',mp.nstr(abs(E-direct),8))

check([0,1,-1])
check([0,1,'0.2','-0.8','1.4','-0.1'])
```

**Итог:** доказаны (1), (5), (13), (18)–(21), (27)–(29). Не доказана (25). Полная цепь к RH остаётся условной ровно в этом месте.
