# STATUS: TRY_PAIRED_SCALE_DIVISOR_WITH_PAID_SHORT_PERIODS_M

```yaml
OPERATIVE_CLASS: TRY_PAIRED_SCALE_DIVISOR_WITH_PAID_SHORT_PERIODS_M
DATE: 2026-11-07
AUTHORITY: OWNER_GO_PAIRED_SCALE_DIVISOR_ESTIMATE_BEFORE_ABSOLUTE_VALUES
ANSWER: PAID_SHORT_DIVISORS_AND_SHORT_PERIODS_WITH_OPEN_LONG_PERIOD_SIGNED_BOUND
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
FULL_SOURCE_EXPONENT_GAIN: NOT_OBTAINED
FULL_RH_ACCEPTANCE: NOT_COMPLETE
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_PLAN_COMMIT: c3f80b9871ca022d307b27331a2753dbc386e97a
INPUT_PLAN_BLOB: 7e8920ceac98f25b2da19a968c026baf37c76b7f
INPUT_K_COMMIT: 06238eb5dd6d06887d9b088aca089fdb3c05b9cc
INPUT_K_BLOB: cd777de92a512c2bb1f5cbb1aedbc38fa83d8757
SPEC_FREEZE_COMMIT: 7c82bc24e15a0620be9ff7c9ad715cadb45e0644
SPEC_FREEZE_BLOB: 8725658c527cde25b4465ecc0cd9eca84a50f532
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
SOURCE_MOBIUS_CHANGED: false
ALL_PRIME_POWERS_PRESERVED: true
PROVED_STEPS:
  - {id: EXACT_PAIRED_KERNEL_WITH_PERIODIC_PRIMITIVE_BOUNDARIES, scope: FINITE_CELL, verifier: PAPER}
  - {id: SHORT_DIVISOR_ABSOLUTE_PRICE_LE_2_X_U_SQUARED_LOG_CUBED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: ALL_DIVISOR_PERIODIC_MEAN_PRICE_LE_3_OVER_2_X_SQUARED_LOG_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: ALL_LCM_LE_X_BOUNDARY_PRICE_LE_3_OVER_4_X_SQUARED_LOG_FOURTH, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: COMPLETE_SOURCE_REDUCTION_TO_LONG_PERIODS_PLUS_LINEAR_COMPENSATION, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: LONG_TAIL_PRINCIPAL_BLOCK_IS_NEGATIVE_SEMIDEFINITE, scope: FINITE_CELL, verifier: PAPER}
  - {id: TRUE_SOURCE_POSITIVE_ENTRY_PRICE_GE_7_X_CUBED_LOG_SQUARED_OVER_27648, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: NO_ONE_SIDED_FEEDBACK_BOUND_FOR_LONG_PERIOD_BOUNDARIES_AND_LINEAR_COMPENSATION_TOGETHER
MINIMAL_MISSING_IDENTITY: "For every eta>0, C_long(X) <= C_eta X^eta (sqrt(A(2X))+1) on every sufficiently large dyadic X, with the unchanged source and C_long defined in (16). This bound is NOT proved."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: UNIFORM_SUBBLOCK_BUDGETS_AND_SCOPED_CERTIFICATE_OBSTRUCTION_NOT_FULL_PRIME_EXPONENT
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: TERMWISE_POSITIVE_PAYMENT_AFTER_EXACT_TWO_SCALE_PAIRING
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: TRUE_MOBIUS_SQUAREFREE_SLAB_STRICT_NEGATIVE_UPPER_MARGIN
    EVIDENCE: SECTIONS_6_7_EQUATIONS_18_TO_21
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_CERTIFICATE_ONLY
DOES_NOT_KILL: [RH, ACTUAL_SIGNED_TWO_SCALE_FORM, JOINT_DIVISOR_ESTIMATES, RETAINED_NEGATIVE_TAIL_SQUARES, OTHER_FEEDBACKS, ORIGINAL_NB_ROUTE]
CLOSES: [SHORT_DIVISOR_PAIRED_PRICE, FULL_PERIODIC_MEAN_PRICE, LCM_AT_MOST_WINDOW_BOUNDARY_PRICE]
OPENS: []
COGNITIVE_OPERATOR: PAIRED_SCALE_PRIMITIVES_AND_LCM_LOCALIZATION_BEFORE_MODULI
ROUTE_SCORE: 2
DISCRIMINATOR: EXACT_RATIONAL_COEFFICIENTS_FOR_IDENTITIES_STRICT_SOURCE_ENVELOPES_FOR_PRICE_AND_NONZERO_MELLIN_RESIDUE_FOR_RH
NUMERICAL_SOURCE_CLAIMS: NONE
EXACT_TESTS: 21504_KERNEL_PAIRS_144_COVARIANCES_312_PRIMITIVE_CELLS_AND_FORMAL_LOG_SOURCE_RETURN
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE
```

Ы. **Совместное вычитание масштабов даёт доказанную экономию степени для короткого делительного блока и позволяет оплатить все граничные пары с НОК не больше X. Но для ПОЛНОЙ формы первый новый показатель не получен.** Также доказано: если после точного вычитания масштабов оплачивать положительные слагаемые по отдельности, цена всё равно не меньше константы, умноженной на X³ log²X, на настоящих коэффициентах μ. Это запрещает конкретный способ оценки, не исходную совместную сумму.

Ни малость конечной сетки, ни положительность Gram, ни новое имя остатка не используются как посылка RH. Все результаты ниже относятся к полной функции Λ, включая собственные степени простых.

## 1. Source lock, цель и критерий успеха

[FINITE_CELL | PAPER для сверки; старые receiver-утверждения — inherited PAPER.]

План L прочитан полностью через GitHub и из локальной копии: 17971 байт, Git blob `7e8920ceac98f25b2da19a968c026baf37c76b7f`. Источник K: 33383 байта, Git blob `cd777de92a512c2bb1f5cbb1aedbc38fa83d8757`. Пины — в YAML. Протокол и Pappus skill получены заново; найденных новых дублей по поиску PAIRED_SCALE не было. Поиск не является исчерпывающим аудитом репозитория. Отдельный freeze записан до завершённых доказательств и проверок, затем прочитан обратно. Предварительный алгебраический анализ в нём раскрыт, не выдан за слепое предсказание.

Внешние нормировки проверены в первичных HTML-источниках:

- **THEOREM T1:** DLMF 27.5.2, 27.5.5 — μ*1=ε и μ*log=Λ. Видимая поправка относится к обозначению логарифма. Конечные перегруппировки ниже доказаны непосредственно.
- **THEOREM T2:** DLMF 25.16.3–4 — качественная PNT и ε-формулировка RH. Видимая поправка к гармоническим числам относится к другому подразделу. PNT используется только для терминального o(X), не для нового степенного остатка.
- **THEOREM T3:** DLMF 27.4.3, 27.4.12 и 25.4.3–4 — Dirichlet-ряды ζ и −ζ′/ζ в Re s>1 и стандартное функциональное уравнение для финального receiver.
- DLMF 24.2 — нормировка полиномов Бернулли. Нужный квадратичный примитив ниже проверяется собственной элементарной формулой; никакая внешняя оценка корреляций не импортируется.

```text
https://dlmf.nist.gov/27.5
https://dlmf.nist.gov/25.16
https://dlmf.nist.gov/24.2
https://dlmf.nist.gov/27.4
https://dlmf.nist.gov/25.4
```

Исчерпывающий поиск исторических исправлений и исторический приоритет не заявляются. PDF не использовались. Никакие гипотезы о парах простых, RH, GRH, GUE или случайности μ не приняты.

Пусть X=2^j, j≥3, D=4X, и

\[
 a_1=-1,\qquad a_d=-\mu(d)\log d\quad(d\ge2),
\]
\[
 N_d(x)=\lfloor x/d\rfloor-\lfloor x/(2d)\rfloor,
 \quad S(x)=\sum_{x/2<n\le x}(\Lambda(n)-1),
 \quad \mathcal A(X)=X^{-2}\int_X^{2X}S(x)^2\,dx.
\]

Для каждого n≥1, включая n=1, точно \(\sum_{d\mid n}a_d=\Lambda(n)-1\). Поэтому на обоих используемых масштабах

\[
 S(x)=\sum_{d\le D}a_dN_d(x),\qquad X\le x\le4X.       \tag{1}
\]

Обозначим

\[
 M_X(d,e)=\int_X^{2X}N_d(x)N_e(x)\,dx
              -\frac18\int_{2X}^{4X}N_d(x)N_e(x)\,dx.
\]

Тогда

\[
 \boxed{\mathcal F(X):=\mathcal A(X)-\tfrac12\mathcal A(2X)
       =X^{-2}\sum_{d,e\le D}a_da_eM_X(d,e).}           \tag{2}
\]

Искомая верхняя цена полной суммы — \(C_\eta X^{2+\eta}(\sqrt{\mathcal A(2X)}+1)\) для каждого η>0 и всех больших dyadic X. При безусловном старте \(\mathcal A(2X)\le42X\) это \(O_\eta(X^{5/2+\eta})\). Успех лишь на части пар не выдаётся за успех (2).

## 2. Точное сокращение масштабов и все граничные члены

[FINITE_CELL | PAPER; формулы для каждого d,e≥1, X>0.]

Положим

\[
 r_d(x)=N_d(x)-\frac{x}{2d}
       =\{x/(2d)\}-\{x/d\}.
\]

Это функция периода 2d, среднего ноль, \(|r_d|\le1/2\). При \(t=x/d\pmod2\)

\[
 r_d(x)=\begin{cases}-t/2,&0\le t<1,\\1-t/2,&1\le t<2.\end{cases}
\]

Значения в конечном числе концов интегралов ничего не меняют. Используем НЕ грубую цену \(\int x|r_d|\), а периодический примитив

\[
 p_d(x)=dB_2(\{x/(2d)\})-\frac d2B_2(\{x/d\}),
 \qquad B_2(t)=t^2-t+\frac16.
\]

Он непрерывен, \(p_d'=r_d\) почти всюду, имеет нулевое среднее и

\[
 p_d/d=\begin{cases}1/12-t^2/4,&0\le t\le1,\\
 -t^2/4+t-11/12,&1\le t\le2,\end{cases}
 \qquad |p_d|\le d/6.                                 \tag{3}
\]

Обозначим

\[
 J_d(X)=\int_X^{2X}x r_d(x)\,dx
                  -\frac18\int_{2X}^{4X}x r_d(x)\,dx.
\]

Интегрирование по частям с (3) даёт

\[
 \left|\int_X^{2X}x r_d(x)dx\right|\le\frac23Xd,
 \qquad \boxed{|J_d(X)|\le\frac56Xd.}                 \tag{4}
\]

Это настоящая экономия от нулевого среднего: до интегрирования цена была порядка X². Для точного вычисления можно использовать

\[
 q_d(x)=\frac{2d^2}{3}B_3(\{x/(2d)\})
                   -\frac{d^2}{6}B_3(\{x/d\}),
 \quad B_3(t)=t^3-\tfrac32t^2+\tfrac12t;
\]

\(q_d'=p_d\), поэтому первообразная \(x r_d(x)\) равна \(x p_d(x)-q_d(x)\). Все концы в J_d тем самым явные; при целых X,d они рациональны.

### 2.1. Совместное среднее, без подмены им исходного окна

Пусть \(g=\gcd(d,e)\), \(P=2\operatorname{lcm}(d,e)\). Точное среднее произведения равно

\[
 \boxed{\rho_{de}=\frac1P\int_0^P r_d r_e
 =\frac{4g^2-\gcd(2d,e)^2-\gcd(d,2e)^2}{24de}.}         \tag{5}
\]

**Элементарный вывод.** Для целых A,B положим A=gp, B=gq, (p,q)=1. В среднем произведении \(B_1(x/A)B_1(x/B)\) сначала масштабируем x на g, затем делим общий период на единичные ячейки. CRT делает пару остатков modulo p,q равномерной. При внутренней координате u∈[0,1) среднее произведение равно \((u-1/2)^2/(pq)\); интеграл — \(1/(12pq)\). Следовательно общее среднее равно \(\gcd(A,B)^2/(12AB)\). Применяем это к четырём членам \((B_1(x/(2d))-B_1(x/d))(B_1(x/(2e))-B_1(x/e))\). Получается (5).

В частности,

\[
 \rho_{de}=\begin{cases}
 g^2/(12de),&d/g,e/g\text{ оба нечётны},\\
 -g^2/(24de),&\text{иначе},
 \end{cases}
 \qquad |\rho_{de}|\le\frac{g^2}{12de}.                \tag{6}
\]

Определим точный остаточный примитив

\[
 Q_{de}(t)=\int_0^t(r_d(x)r_e(x)-\rho_{de})dx,
\]

периодичный с периодом P, и границу

\[
 \mathcal B_X(d,e)=\frac98Q_{de}(2X)-Q_{de}(X)
                                      -\frac18Q_{de}(4X).
\]

Полный ответ для ядра:

\[
 \boxed{M_X(d,e)=\frac{J_e(X)}{2d}+\frac{J_d(X)}{2e}
           +\frac{3X}{4}\rho_{de}+\mathcal B_X(d,e).} \tag{7}
\]

Главный член сократился ДО любого модуля:

\[
 \int_X^{2X}\frac{x^2}{4de}dx
     -\frac18\int_{2X}^{4X}\frac{x^2}{4de}dx=0.
\]

Формула (7) не заменяет фиксированное окно полным периодом: вся несовместимость концов с периодами находится в явно сохранённой \(\mathcal B_X\).

## 3. Доказанная цена короткого делительного блока

[COFINAL_FAMILY | PAPER; все целые U≥1 и dyadic X≥8.]

Из (4), \(|r_dr_e|\le1/4\) и длин обоих интегралов:

\[
 \boxed{|M_X(d,e)|\le\frac{5X}{12}
          \left(\frac de+\frac ed\right)+\frac{5X}{16}.} \tag{8}
\]

Положим \(\ell_U=1+\log U\). Для настоящих коэффициентов

\[
 \sum_{d\le U}|a_d|/d\le\ell_U^2,\quad
 \sum_{d\le U}d|a_d|\le U^2\ell_U,\quad
 \sum_{d\le U}|a_d|\le U\ell_U.
\]

Первая оценка, например, следует из \(\sum_{d=2}^U1/d\le\log U\). Поэтому

\[
 \begin{split}
 \sum_{d,e\le U}|a_da_e M_X(d,e)|
 &\le\frac{5X}{6}
       \left(\sum|a_d|/d\right)\left(\sum d|a_d|\right)
         +\frac{5X}{16}\left(\sum|a_d|\right)^2\\
 &\le\boxed{2XU^2\ell_U^3.}                           \tag{9}
 \end{split}
\]

В частности, при \(U=\lfloor\sqrt X\rfloor\),

\[
 \boxed{\sum_{d,e\le U}|a_da_e M_X(d,e)|
                  \le2X^2(1+\log U)^3.}              \tag{10}
\]

Это уже доказанная экономия степени для данного блока: кубический непрерывный член исчез, оставшийся блок имеет лишь полилогарифмическую цену после деления на X². Порог U выбран из цены U²/X, не просто назначен по привычке. (10) НЕ оценивает смешанные пары или весь источник.

## 4. Периодический главный член оплачен для ВСЕХ делителей

[COFINAL_FAMILY | PAPER; D=4X, X≥8.]

Матрица \(\rho\) положительно полуопределена: это Gram функций r_d на общем периоде. Для настоящего вектора положим

\[
 V_D=\sum_{d,e\le D}a_da_e\rho_{de}\ge0.
\]

При \(\ell_D=1+\log D\), \(|a_d|\le\ell_D\). Кроме того,

\[
 \sum_{d,e\le D}\frac{\gcd(d,e)^2}{de}
 \le D\sum_{r,s\ge1}\frac1{rs\max(r,s)}
 \le2D\sum_{r\ge1}\frac{H_r}{r^2}\le6D.
\]

Первая строка получается из d=gr,e=gs, затем (r,s)=1 можно отбросить в положительной сумме. Для последней оценки достаточно \(H_r\le1+\log r\) и
\(\sum_{r\ge1}(1+\log r)/r^2\le1+\int_1^\infty(1+\log t)t^{-2}dt=3\).

Из (6):

\[
 \boxed{0\le\frac{3X}{4}V_D
               \le\frac32X^2\ell_D^2.}              \tag{11}
\]

Это ограничивает полный периодический главный член, включая большие d,e. Сам по себе он не является всей формой (2); граничные и линейные части (7) остаются.

## 5. Весь граничный сектор с НОК ≤ X тоже оплачен

[COFINAL_FAMILY | PAPER; все X≥8.]

Поскольку \(|r_dr_e-\rho_{de}|\le1/3\), а интеграл этой функции по полному периоду P равен нулю, на любом интервале длины H его модуль не больше \(\min(H,P)/3\). Следовательно

\[
 \boxed{|\mathcal B_X(d,e)|
   \le\min\left(\frac{5X}{12},\frac34\operatorname{lcm}(d,e)\right).} \tag{12}
\]

Здесь P=2 lcm(d,e). Константа 3/4 получается из \((1+1/8)P/3\); никакой случайной фазы не вводится.

Пусть \(m(q)=\#\{(d,e):\operatorname{lcm}(d,e)=q\}\), пары упорядочены. Тогда

\[
 m(q)=\prod_{p^v\parallel q}(2v+1)\le d_3(q),
\]

поскольку \(2v+1\le(v+1)(v+2)/2\). Элементарно

\[
 \sum_{q\le R}d_3(q)
 =\#\{abc\le R\}\le R H_{\lfloor R\rfloor}^2
 \le R(1+\log R)^2.
\]

Если lcm(d,e)≤R, то d,e≤R и \(|a_da_e|\le(1+\log R)^2\), включая индекс 1. Поэтому для каждого R≥1

\[
 \sum_{\substack{d,e\le D\\[d,e]\le R}}
       |a_da_e\mathcal B_X(d,e)|
   \le\boxed{\frac34 R^2(1+\log R)^4}.                \tag{13}
\]

При R=X получаем O(X² log⁴X) для ВСЕХ таких пар, не только для квадрата d,e≤√X. Доказательство использует точную границу периода, а не равенство фиксированного среднего периодическому.

### 5.1. Полный источник после двух оплаченных частей

Определим конечные реальные величины

\[
 c_D=\sum_{d\le D}\frac{a_d}{d},\qquad
 J_D(X)=\sum_{d\le D}a_dJ_d(X),
\]
\[
 B_{\le}(X)=\sum_{\substack{d,e\le D\\[d,e]\le X}}
               a_da_e\mathcal B_X(d,e),\quad
 B_{>}(X)=\sum_{\substack{d,e\le D\\[d,e]>X}}
               a_da_e\mathcal B_X(d,e).
\]

Суммирование (7) даёт ТОЧНО

\[
 \boxed{X^2\mathcal F(X)
   =c_DJ_D(X)+B_{>}(X)+\frac{3X}{4}V_D+B_{\le}(X).}    \tag{14}
\]

Итак,

\[
 \mathcal F(X)=\mathcal C_{\rm long}(X)+\mathcal R_X,
 \qquad
 \boxed{|\mathcal R_X|\le\frac32\ell_D^2+\frac34\ell_X^4,} \tag{15}
\]
\[
 \boxed{\mathcal C_{\rm long}(X)
     =X^{-2}\bigl[c_DJ_D(X)+B_{>}(X)\bigr].}            \tag{16}
\]

**Не терять линейную компенсацию.** c_DJ_D не зануляется тождественно и не оплачивается (11) или (13). Его нельзя удалить на том основании, что кубический непрерывный член исчез. Большие периоды и эта линейная часть должны оцениваться совместно, со знаком.

Оценка (10) — дополнительный локальный контроль исходного M, а не ещё один непересекающийся член (14). Складывать её с (11),(13) как три disjoint-части было бы двойным счётом.

## 6. Полезный знак большого хвоста и точный активный блок

[FINITE_CELL | PAPER.]

Если d,e>2X, первая энергия не видит ни одного кратного, а на [2X,4X] \(N_d(x)=\mathbf1_{x\ge d}\). Поэтому

\[
 \boxed{M_X(d,e)=-\frac{4X-\max(d,e)}8\quad(2X<d,e\le4X).} \tag{17}
\]

Для любых коэффициентов этот главный блок отрицательно полуопределён:

\[
 \sum_{d,e>2X}a_da_eM_X(d,e)
   =-\frac18\int_{2X}^{4X}
        \left(\sum_{2X<d\le x}a_d\right)^2dx\le0.
\]

Его модуль оплачивать нельзя, если нужен верхний bound. Однако это не устраняет смешанные пары с d≤2X<e.

Теперь другой, активный диапазон:

\[
 I_X=\{d\in\mathbb N:X<d\le4X/3\}.
\]

На [X,2X] \(N_d=\mathbf1_{x\ge d}\). На [2X,4X] для d∈I_X имеем \(N_d=1+\mathbf1_{x\ge3d}\) почти всюду. Прямое интегрирование даёт

\[
 \boxed{M_X(d,e)=\frac{2X+3\min(d,e)-2\max(d,e)}8
                    \ge\frac{7X}{24}>0,
             \quad d,e\in I_X.}                      \tag{18}
\]

Масштабы уже полностью вычтены, а оставшийся вес в этом блоке всё ещё порядка X. Следовательно надежда на дополнительный фактор X^{-1/2} В КАЖДОЙ паре неверна. Для настоящего источника нужны связи знаков между парами; следующий раздел проверяет это количественно, без замены μ.

## 7. Строгий source-свидетель против поэлементной положительной оплаты

[COFINAL_FAMILY | PAPER; каждый dyadic X≥4096.]

Рассмотрим допустимую, но более сильную цену

\[
 \mathfrak P_X=\sum_{d,e\le4X}(a_da_eM_X(d,e))_+.
\]

Она действительно мажорирует полную ненормированную форму. Абсолютная цена \(\sum|a_da_eM_X|\) ещё больше. Но:

\[
 \boxed{\mathfrak P_X\ge
          \frac7{27648}X^3\log^2X.}                  \tag{19}
\]

**Доказательство с настоящим квадратсвободным носителем.** Число целых в I_X равно \(H=\lfloor4X/3\rfloor-X\ge X/3-1\). Каждое неквадратсвободное число делится на k² для некоторого 2≤k≤√(4X/3). Union bound и
\(\sum_{k\ge2}k^{-2}\le1/4+\int_2^\infty t^{-2}dt=3/4\)
дают

\[
 \#\{d\in I_X:\mu(d)^2=1\}
 \ge H/4-\sqrt{4X/3}\ge X/12-1/4-2\sqrt X
 \ge X/24 \quad(X\ge4096).                            \tag{20}
\]

Разделим эти настоящие d по двум знакам a_d. Пусть суммы их модулей равны P и Q. Тогда \(P+Q\ge(X/24)\log X\). В (18) все пары одного знака дают положительный вклад, поэтому

\[
 \mathfrak P_X\ge\frac{7X}{24}(P^2+Q^2)
     \ge\frac{7X}{48}(P+Q)^2
     \ge\frac7{27648}X^3\log^2X.
\]

Не потребовалось ни распределения знаков μ, ни PNT, ни существования внеосевых нулей. Это не искусственный контрмассив.

### Строгая верхняя огибающая отрицательного margin

Элементарная Chebyshev-оценка \(\psi(x)<3x\) даёт \(\mathcal A(X)\le21X\). Короткий вывод: каждое prime power в (m,2m] входит в p-adic valuation центрального binomial; отсюда \(\psi(2m)-\psi(m)\le2m\log2\). Dyadic-суммирование и монотонность дают \(\psi(x)<4x\log2<3x\). Затем \(|S(x)|\le3x\) и интегрирование квадрата дают 21X.

Поэтому для любого фиксированного η<1/2, C>0,

\[
 \begin{split}
 C X^{2+\eta}(\sqrt{\mathcal A(2X)}+1)-\mathfrak P_X
 &\le C(\sqrt{42}+1)X^{5/2+\eta}
                  -\frac7{27648}X^3\log^2X\\
 &<0
 \end{split}                                         \tag{21}
\]

при всех достаточно больших dyadic X. Это строгая отрицательная ВЕРХНЯЯ огибающая. Следовательно поэлементная положительная цена не может выполнить требуемый feedback, даже ПОСЛЕ точного pairing двух масштабов.

**Scope:** KILL_SCOPE=THEOREM_SHAPE. Запрещено только терять все отрицательные межпарные вклады и оплачивать \(\mathfrak P_X\) или её абсолютную мажоранту. Не запрещены (2), (16), сохранённый отрицательный блок (17), коллективное сложение строк и любые другие source-specific signed-оценки. Из (19) НЕ следует нижняя оценка настоящей \(\mathcal F\) или \(\mathcal A\). Не утверждается, что в положительном блоке I_X его подписанная сумма столь же велика: противоположные знаки не включены в P²+Q².

## 8. Попытка полного bound: цена, остановка и точная цепочка

[COFINAL_FAMILY | PAPER для доказанных цен; целевой bound CONDITIONAL.]

После сокращения до модулей есть такая таблица:

| Часть | Ненормированная цена | Что доказано |
|---|---:|---|
| Непрерывный x²/(4de) | 0 | Точно сокращён для каждой пары |
| Весь периодический главный член | ≤(3/2)X²ℓ_D² | Оплачен для всех d,e≤4X |
| Все граничные пары с [d,e]≤X | ≤(3/4)X²ℓ_X⁴ | Оплачены без подмены фазы |
| Главный блок d,e>2X | Неположителен | Знак (17) сохранён; mixed-блок не исчез |
| c_DJ_D + границы [d,e]>X | Требуется верхняя цена X^(2+η)(√A(2X)+1) | НЕ ПОЛУЧЕНА |
| Поэлементная положительная оплата всей формы | ≥(7/27648)X³log²X | Слишком дорогой сертификат, строго опровергнут |

Проверенная прямая оценка оставшейся совместной величины даёт лишь кубическую цену. Действительно,

\[
 |c_D|\le\ell_D^2,\quad
 |J_D(X)|\le\frac56XD^2\ell_D,\quad
 |B_{>}(X)|\le\frac{5X}{12}D^2\ell_D^2,
\]

а при D=4X

\[
 |c_DJ_D+B_{>}|\le20X^3\ell_D^3.                      \tag{22}
\]

Это НЕ нужный X^(5/2+η) и не повторяемый выигрыш. Контролируемые константы и сохранённые знаки (14),(17) сами не дали новой оценки совместного остатка. Эта модульная ветвь остановлена, как было предусмотрено планом L. Остановка не является запретом всей signed-техники.

Минимальная строка оставшейся сборки:

\[
 \boxed{\forall\eta>0\ \exists C_\eta,X_\eta:\quad
 \mathcal C_{\rm long}(X)\le
 C_\eta X^\eta(\sqrt{\mathcal A(2X)}+1)
 \quad\forall\text{ dyadic }X\ge X_\eta.}             \tag{23}
\]

Она **не доказана**. Благодаря (15) она достаточна и, с произвольными η-потерями, равносильна прежнему flux-bound. Запись (16) не называется уменьшением сложности сама по себе. Новое — доказанная цена всех короткопериодических граничных пар и точный предел поэлементной оплаты.

Возврат из (23): (15) и log^kX≪_ηX^η дают критическую рекурсию для A. Качественная PNT даёт A(2^j)=o(2^j). Лемма K затем даёт A(2^j)=O_δ(2^(δj)) для каждого δ>0. Здесь нужны все поздние dyadic-масштабы, не подпоследовательность S.

Прямой source-check для последнего перехода, без смены норм: при Re s>1 абсолютная сходимость даёт

\[
 \int_1^\infty S(x)x^{-s-1}dx
   =\frac{1-2^{-s}}s\left(-\frac{\zeta'(s)}{\zeta(s)}-\zeta(s)\right). \tag{24}
\]

Член −ζ(s), а не произвольный полюсный вычет, соответствует исходному целочисленному −1. При s=1 главные полюса сокращаются. Субполиномиальная энергия обеспечила бы локально равномерную абсолютную сходимость исходного интеграла при Re s>1/2, поскольку на [X,2X]
\(\int |S|x^{-\sigma-1}\le\sqrt{\mathcal A(X)}X^{1/2-\sigma}\).
Правый нуль ρ кратности m оставлял бы ненулевой вычет \(-m(1-2^{-\rho})/\rho\), что невозможно для такого голоморфного интеграла. Стандартное функциональное уравнение исключило бы левую половину. Это проверяет условную стрелку к RH, не доказывает (23).

## 9. Сильнейшая атака и источниковые контроли

[ABSTRACT | PAPER для логических/алгебраических границ; полные исторические false-world модели здесь не пересчитывались.]

Главная опасность — объявить (10), (11) или (13) оценкой всей (2). Это неверно: неполные длинные периоды и линейный член остались. Вторая опасность — из кубической цены положительных слагаемых вывести кубический размер подписанной суммы. Это тоже неверно. Третья — использовать периодический Gram как fixed-phase bound; точная граница в (7) специально препятствует такой подмене.

DMV/Берлинг: точный N_d считает обычные целые кратные, с единичными ячейками и обычным lcm. Для другого counting-source не сохраняются одновременно эти floor-формулы и Mellin-match (24). Абстрактные primitive bounds сами по себе миры не различают.

DH: обратные коэффициенты и completed factor не равны обычным μ и стандартной ζ. Перестановка конечных сумм универсальна, но равенство с Λ−1 в (1) — source-specific; заменять DH обычной μ нельзя.

Подсаженный квартет и самодуальные подсадки: если меняется uncompleted source, надо менять reciprocal coefficients; если меняется только Gamma/Gaussian-фактор, (24) описывает ζ, но не добавочные нули Q. Нельзя потерять Q'/Q и объявить стандартным другой completed source.

R9: kernel-идентичности и модульные цены остаются верными для подходящих коэффициентов, однако его изменённый массив не проходит полную μ-свёртку в (1). Ни положительность, ни наши короткопериодические bounds сами по себе не являются RH-дискриминатором.

Кривая над F3: сохраняется собственный положительный периодизационный источник из предыдущих pins, но ordinary-floor формулы ему не навязываются. Здесь не построен новый универсальный RH-сертификат, для которого заявлялся бы полный численный аудит всех моделей. Будущий поставщик (23) должен сохранять их собственные полюса и корректно отказывать в ложных мирах.

## 10. Выполненные проверки и судьба freeze

[FINITE_CELL | PAPER для конечной точной алгебры; это не Lean и не ARB_INTERVAL.]

После freeze на X=8,16,32 проверены **21504 упорядоченные пары (d,e)**, d,e≤4X. Независимые способы: исходный overlap-Gram по n,m; incidence-перенос на делители; прямой cell-count integral. Проверены (7),(8),(12),(17),(18) и все конечные концы. Source-return проверен как равенство рациональных матриц при формальных log простых и отдельной константе для a_1. Переменных log: 11,18,31 соответственно.

Для 1≤d,e≤12 выполнены **144 точные проверки ковариации** полным периодом; для примитива — **312 единичных ячеек**. Намеренно неверный коэффициент 1/4 вместо 1/8 обнаруживается уже непрерывным членом: дефект −7X³/(12de)≠0. Нет сравнения «достаточно маленького» decimal с нулём. В integer-matrix части максимальные промежуточные величины на объявленной сетке меньше 2^63; дробная часть использует fractions.Fraction.

Проверки не являются доказательством cofinal-оценок: доказательства (9),(11),(13),(19),(21) аналитические и независимы от сетки. Больших source-прогонов и численных утверждений о росте энергии не было.

- M/P1 HIT; L/P1 HIT: точное масштабное сокращение, deliberate wrong-factor detector сработал.
- M/P2 HIT: (9)–(10), с явной областью, не вся форма.
- M/P3 HIT: (5),(7),(11),(13); граница полностью сохранена.
- M/P4 HIT: отрицательный хвост и настоящий квадратсвободный slab-свидетель. L/P2 HIT: именно границы большого периода остаются существенны.
- M/P5 и L/P3: целевой независимый feedback **NOT_PROVED**. Факторизация с одним субполиномиальным множителем не построена. Это не успешный прогноз нового показателя.

## 11. K8A, следующий допустимый ход и доставка

Для опровергнутой цены: DOWNSTREAM_CONSUMER=(23); ORIGINAL_REQUESTED_OBJECT=термовая положительная/абсолютная мажоранта после exact pairing; ORIGINAL_OBJECT_IS=NOT_NECESSARY; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для этого сертификата. KILL_SCOPE=THEOREM_SHAPE. Пин доказательства — этот verdict, (18)–(21), freeze `7c82bc24`; source-coefficients неизменны. Reopen trigger: ошибка в (18)–(21), либо другой способ оценки с сохранёнными совместными отрицательными вкладами.

Для полной цели: ACTUAL_CONSUMER_REQUIREMENT=source-correct уменьшение показателя энергии на всех поздних масштабах; ORIGINAL_REQUESTED_OBJECT=совместная двухмасштабная оценка; ORIGINAL_OBJECT_IS=NOT_NECESSARY как метод RH; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; KNOWN_WEAKER_INTERFACES=иной повторяемый gain или исходный NB subsequence receiver. NOVELTY_AXIS=оплата полного short-lcm сектора и source-level предел поэлементного pairing-бюджета; исторический приоритет не заявляется.

Две оставшиеся репрезентации, не дополнительные посылки:

**A. Коллективные signed-блоки длинных периодов.** Сохранять (17), смешанные пары и c_DJ_D совместно; использовать реальные связи коэффициентов, например точное a_{2d}=−a_d+μ(d)log2 для нечётного d≥3, до каких-либо квадратов. Различающая сила высокая при действительном feedback, аналитическая стоимость высокая. Само это соотношение не даёт bound (23); нельзя назвать его уже выполненным сокращением.

**B. Совместный сдвиговой prime-pair источник K.** Перенести длиннопериодический остаток в суммы по h с точными двумя масштабами, сохраняя линейную компенсацию и фиксированные концы. Различающая сила высокая, стоимость очень высокая. Периодическое усреднение и conjectural Hardy–Littlewood не являются заменой нужной односторонней оценки.

DISCRIMINATOR: для равенств — ненулевой рациональный/formal-log коэффициент; для запрета цены — строгая верхняя огибающая (21); для будущего RH-gain — source-correct верхняя оценка, несовместимая с ненулевым Mellin-вычетом правого нуля. Near-zero DIAG этого не проверяет.

```yaml
iteration:
  target: PAIRED_SCALE_SIGNED_DIVISOR_FEEDBACK
  status: PROGRESS
  cognitive_operator_used: PERIODIC_PRIMITIVES_AND_LCM_LOCALIZATION
  new_gap_name: LONG_PERIOD_ENDPOINTS_WITH_LINEAR_COMPENSATION
  invariant_learned: PAIRING_REMOVES_VOLUME_BUT_NOT_LARGE_DIVISOR_SIGN_CORRELATIONS
  forbidden_future_move: TERMWISE_POSITIVE_PAYMENT_AFTER_PAIRING_AS_A_POWER_SAVING
  next_decisive_test: SOURCE_BOUND_RETAINING_LONG_PERIOD_CROSS_TERMS_AND_NEGATIVE_TAIL_SQUARE
  route_score: 2
```

Только freeze и этот новый verdict записываются в `docs/routeB_bus/proshka/` ветки `proshka_inbox_2026-10-31`. Старые verdicts, план L, state-файлы и чужие документы не изменяются. Финальный commit/blob и SHA256 сообщаются в квитанции после удалённого readback: самореферентный commit не подставляется заранее. Уровень PAPER, без независимого аналитического аудита. **Первого безусловного улучшения показателя полной энергии и доказательства RH нет.**

## Приложение: воспроизводимый точный судья

Сохрани блок как `verify_paired_scale.py`, затем выполни `uv run --with numpy verify_paired_scale.py`. Ничего в параметрах заменять не нужно. X — фиксированная тестовая сетка; D=4X — максимальный индекс делителя. `M8` и `Pi8` — целые матрицы, умноженные на 8; `C` и `B` — коэффициенты при константе и формальных log простых. Итоговый JSON проверяет конечную алгебру, не RH.

```python
from __future__ import annotations
from fractions import Fraction as F
from math import gcd, lcm, isqrt
import json, time
import numpy as np

def mobius_sieve(n):
    mu=np.ones(n+1,dtype=np.int64); mu[0]=0
    prime=np.ones(n+1,dtype=bool); prime[:2]=False
    for p in range(2,n+1):
        if prime[p]:
            prime[p*p::p]=False
            mu[p::p]*=-1
            mu[p*p::p*p]=0
    return mu,[p for p in range(2,n+1) if prime[p]]

def coeffs(D):
    mu,ps=mobius_sieve(D); idx={p:i+1 for i,p in enumerate(ps)}
    C=np.zeros((D,len(ps)+1),dtype=np.int64); C[0,0]=-1
    B=np.zeros_like(C); B[:,0]=-1
    for n in range(2,D+1):
        k=n; factors=[]
        for p in ps:
            if p*p>k: break
            v=0
            while k%p==0:
                v+=1; k//=p
            if v: factors.append((p,v))
        if k>1: factors.append((k,1))
        for p,v in factors: C[n-1,idx[p]]=-int(mu[n])*v
        if len(factors)==1: B[n-1,idx[factors[0][0]]]=1
    return mu,ps,C,B

def Nval(t,d): return t//d - t//(2*d)
def integral_x_r(a,b,d):
    return sum((F(Nval(t,d)*(2*t+1),2) for t in range(a,b)),F()) - F(b**3-a**3,6*d)
def integral_rr(a,b,d,e):
    z=F()
    for t in range(a,b):
        nd=Nval(t,d); ne=Nval(t,e)
        z+=nd*ne - (F(nd,2*e)+F(ne,2*d))*F(2*t+1,2)+F(3*t*t+3*t+1,12*d*e)
    return z

def rho(d,e):
    g=gcd(d,e)
    return F(4*g*g-gcd(2*d,e)**2-gcd(d,2*e)**2,24*d*e)

def beta2(x):
    t=x-(x.numerator//x.denominator)
    return t*t-t+F(1,6)
def primitive(d,x): return d*beta2(F(x,2*d))-F(d,2)*beta2(F(x,d))

def main():
    start=time.monotonic(); report={}; cases=0
    # Exact mean covariance and periodic primitive.
    for d in range(1,13):
        for e in range(1,13):
            P=2*lcm(d,e)
            assert integral_rr(0,P,d,e)/P == rho(d,e)
            assert abs(rho(d,e))<=F(gcd(d,e)**2,12*d*e)
            cases+=1
    report['covariance_cases']=cases
    for d in range(1,13):
        for t in range(0,4*d):
            # Integral of r on a unit cell equals primitive difference.
            ri=F(Nval(t,d))-F(2*t+1,4*d)
            assert primitive(d,t+1)-primitive(d,t)==ri
            assert abs(primitive(d,t))<=F(d,6)
    report['primitive_cases']=sum(4*d for d in range(1,13))
    grids=[]
    for counter,X in enumerate((8,16,32),1):
        D=4*X
        t=np.arange(X,4*X,dtype=np.int64)[:,None]
        d=np.arange(1,D+1,dtype=np.int64)[None,:]
        counts=t//d-t//(2*d)
        M8=8*(counts[:X].T@counts[:X])-(counts[X:].T@counts[X:])
        n=np.arange(1,D+1,dtype=np.int64)
        nn=n[:,None]; mm=n[None,:]
        L=np.maximum(0,np.minimum(np.minimum(2*X,2*nn),2*mm)-np.maximum(np.maximum(X,nn),mm))
        L2=np.maximum(0,np.minimum(np.minimum(4*X,2*nn),2*mm)-np.maximum(np.maximum(2*X,nn),mm))
        Pi8=8*L-L2
        div=(nn%mm==0).astype(np.int64)
        assert np.array_equal(M8,div.T@Pi8@div)
        mu,ps,C,B=coeffs(D)
        assert np.array_equal(div@C,B)
        source=C.T@M8@C
        assert np.array_equal(source,B.T@Pi8@B)
        source_cells=counts@C
        assert np.array_equal(source,8*(source_cells[:X].T@source_cells[:X])-(source_cells[X:].T@source_cells[X:]))
        J=[integral_x_r(X,2*X,dd)-integral_x_r(2*X,4*X,dd)/8 for dd in range(1,D+1)]
        # Coefficients of exact rr integrals avoid a repeated cell loop.
        prod_first=counts[:X].T@counts[:X]
        prod_second=counts[X:].T@counts[X:]
        xN_first=(counts[:X].T@(2*np.arange(X,2*X)+1))
        xN_second=(counts[X:].T@(2*np.arange(2*X,4*X)+1))
        for dd in range(1,D+1):
            assert abs(J[dd-1])<=F(5*X*dd,6)
            for ee in range(1,D+1):
                v=F(int(M8[dd-1,ee-1]),8)
                # Q boundaries via integrated residual products on each interval.
                rr1=F(int(prod_first[dd-1,ee-1]))-F(int(xN_first[dd-1]),4*ee)-F(int(xN_first[ee-1]),4*dd)+F((2*X)**3-X**3,12*dd*ee)
                rr2=F(int(prod_second[dd-1,ee-1]))-F(int(xN_second[dd-1]),4*ee)-F(int(xN_second[ee-1]),4*dd)+F((4*X)**3-(2*X)**3,12*dd*ee)
                assert v==J[ee-1]/(2*dd)+J[dd-1]/(2*ee)+rr1-rr2/8
                cov=rho(dd,ee)
                boundary=(rr1-X*cov)-(rr2-2*X*cov)/8
                assert v==J[ee-1]/(2*dd)+J[dd-1]/(2*ee)+F(3*X,4)*cov+boundary
                assert abs(boundary)<=min(F(5*X,12),F(3*lcm(dd,ee),4))
                assert abs(v)<=F(5*X,12)*(F(dd,ee)+F(ee,dd))+F(5*X,16)
                if dd>2*X and ee>2*X:
                    assert v==-F(4*X-max(dd,ee),8)
                if X<dd<=4*X//3 and X<ee<=4*X//3:
                    assert v==F(2*X+3*min(dd,ee)-2*max(dd,ee),8)
                    assert v>=F(7*X,24)
        # Wrong 1/4 instead of 1/8: already the volume term is nonzero.
        wrong_volume=F(7*X**3,12)-F(1,4)*F(56*X**3,12)
        assert wrong_volume==-F(7*X**3,12) !=0
        grids.append({'X':X,'pairs':D*D,'formal_log_variables':len(ps),'source_equal':True,'wrong_factor_detected':True})
        eta=(time.monotonic()-start)/counter*(3-counter)
        print('['+'#'*counter+'-'*(3-counter)+f'] {counter}/3 ETA {eta:.1f}s',flush=True)
    report['grids']=grids
    report['total_pairs']=sum(x['pairs'] for x in grids)
    report['no_arb_or_lean']=True
    report['elapsed_seconds']=time.monotonic()-start
    print(json.dumps(report,indent=2))
    from pathlib import Path
    Path('paired_scale_exact_report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__': main()
```
