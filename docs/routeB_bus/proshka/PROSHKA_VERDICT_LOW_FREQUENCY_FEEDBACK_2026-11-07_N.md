# STATUS: TRY_LOW_FREQUENCY_SOURCE_RETURN_WITH_OPEN_SIGN_N

```yaml
OPERATIVE_CLASS: TRY_LOW_FREQUENCY_SOURCE_RETURN_WITH_OPEN_SIGN_N
DATE: 2026-11-07
AUTHORITY: OWNER_PROVE_THE_EXACT_C_LONG_TARGET_FROM_M
ANSWER: UNIFORM_FREQUENCY_COMPLEMENT_PAID_BUT_REQUESTED_SOURCE_BOUND_NOT_PROVED
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
REQUESTED_C_LONG_BOUND: NOT_PROVED_AND_NOT_REFUTED
FULL_SOURCE_EXPONENT_GAIN: NOT_OBTAINED
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_COMMIT: 45afff3806bd7671919f5330830b246b1229c75c
INPUT_BLOB: 27168a1a764b5254b53d87e5772673017b7f5d37
INPUT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAIRED_SCALE_DIVISOR_2026-11-07_M.md
SPEC_FREEZE_COMMIT: 5393c758e76d78a1668d3a0b787aede3cf66f0d9
SPEC_FREEZE_BLOB: 256a47d2d08064771712c62718e98072b41e3395
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_LOW_FREQUENCY_FEEDBACK_2026-11-07_N.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_LOW_FREQUENCY_FEEDBACK_2026-11-07_N.md
PROVED_STEPS:
  - {id: COMMON_SOURCE_HIGH_FREQUENCY_ENERGIES_LE_64_LOG_AND_16_LOG, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: NONZERO_LOW_MODES_OF_SHORT_DIVISORS_HAVE_POLYLOG_WINDOW_COST, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: TWO_SCALE_ROOT_FLUX_RETURN_WITH_EXPLICIT_POLYLOG_ERROR, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_LONG_DIVISOR_LOW_MODE_COEFFICIENTS_WITH_FULL_ZERO_MODE, scope: FINITE_CELL, verifier: PAPER}
  - {id: C_LONG_TARGET_EQUIVALENT_TO_COMPRESSED_ONE_SIDED_ROOT_BOUND, scope: COFINAL_FAMILY, verifier: PAPER, type: EQUIVALENCE_ONLY}
  - {id: CRITICAL_ROOT_TELESCOPING_WITH_PNT_TERMINAL, scope: ABSTRACT, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: ZERO_MODE_SELF_FLUX_EQUALS_MEAN_SQUARED_OVER_8X, scope: FINITE_CELL, verifier: PAPER}
  - {id: COHERENT_POWER_SOURCE_REFUTES_SOURCE_BLIND_LOW_MODE_BOUND, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: NO_INDEPENDENT_ONE_SIDED_BOUND_FOR_ACTUAL_LONG_DIVISOR_LOW_FREQUENCIES_AND_ZERO_MODE_TOGETHER
MINIMAL_MISSING_IDENTITY: "For every epsilon>0, d_low(X)<=C_epsilon X^epsilon for all sufficiently large dyadic X, where d_low is (15) from the actual coefficients (11). Equivalent to the requested C_long target; NOT proved."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: UNIFORM_PAID_COMPLEMENT_NOT_FULL_SOURCE_SIGN_OR_EXPONENT_GAIN
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: SOURCE_BLIND_LOW_MODE_CONTRACTION_FROM_PNT_AND_DIAGONAL_SIZE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_COHERENT_POWER_SOURCE_AND_NEGATIVE_UPPER_MARGIN
    EVIDENCE: SECTION_8_EQUATIONS_25_TO_28
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THE_STATED_GENERIC_INFERENCE_ONLY
DOES_NOT_KILL: [RH, REQUESTED_C_LONG_BOUND, ACTUAL_MOBIUS_LOW_MODE_BOUND, SIGNED_DIVISOR_COUPLING, NEGATIVE_TAIL_COMPLETION, ORIGINAL_NB_ROUTE]
COGNITIVE_OPERATOR: SOURCE_PRESERVING_SPECTRAL_COMPRESSION_AND_ROOT_ENERGY_FLUX
ROUTE_SCORE: 2
CLOSES: [UNPAID_HIGH_FREQUENCY_COMPLEMENT, NONZERO_LOW_SHORT_DIVISOR_MODES, SAME_SOURCE_TWO_SCALE_NORM_RETURN]
OPENS: []
DISCRIMINATOR: EXACT_SOURCE_CONVOLUTION_AND_A_NONZERO_MELLIN_RESIDUE_AT_ANY_RIGHT_ZERO
NUMERICAL_TESTS: DIAG_ONLY_50_AND_80_DIGITS
EXACT_TESTS: 476_SOURCE_ROWS_360_WINDOW_ROWS_8_MULTIPLICITY_BOUNDS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **Целевая оценка C_long и RH не доказаны.** Получен другой независимый шаг: для того же полного источника все высокие аддитивные частоты имеют нормированную энергию O(log X). Дополнительно оплачены ненулевые низкие моды коротких делителей. После количественного возврата неизвестный знак остаётся в 2 floor(sqrt X)+1 частотах длинной делительной суммы и в сохранённой общей нулевой моде. Никакой асимптотической малости этого оставшегося блока я не доказал.

Это не утверждение, что высокие/низкие части ортогональны в физическом оконном скалярном произведении. Их смешанные члены учитываются сравнением НОРМ, а не отбрасываются. В частности, доказанная цена высокой части не выдается за абсолютную цену всех её перекрёстных произведений.

## 1. Источник и оплаченная часть M

[FINITE_CELL | PAPER для сверки; результаты M — inherited PAPER.]

Вход M получен по указанному commit/path. Локальная полная копия: 45312 bytes, Git blob 27168a1a764b5254b53d87e5772673017b7f5d37, SHA256 f5be2f27cbdb7a74053bd1614ee34ee030f66afd098ad4223f85b3be36aac564. Bytes и blob пересчитаны. Прочитаны актуальный протокол, Pappus skill и верхняя часть конструктора (blob dee2c8200d6ad59e3eb7336e497f43e17a273f98). Поиск LOW_FREQUENCY_FEEDBACK на индексируемой ветке не дал результатов; исчерпывающий аудит отсутствия дублей не заявляется. Freeze создан отдельным коммитом и не изменяется.

Сохраняем именно источник M:

    a_1=-1; a_d=-mu(d)log d (d>=2),
    S(x)=sum_(x/2<n<=x)(Lambda(n)-1),
    A(X)=X^(-2) integral_X^(2X) S(x)^2 dx,
    F(X)=A(X)-A(2X)/2,   X=2^j, j>=3.

Все простые степени сохранены. На каждой ячейке [N,N+1) S(x)=S(N), поскольку floor x=N и floor(x/2)=floor(N/2). Из M, (14)-(16), берём только уже доказанное:

    F(X)=C_long(X)+R_M(X),
    |R_M(X)|<=R0(X),
    R0(X)=3(1+log(4X))^2/2+3(1+log X)^4/4.          (1)

Здесь C_long — ровно цель владельца: совместная длиннопериодическая граница и линейная компенсация M. Никакой предполагаемый bound C_long не используется как вход.

Внешние нормировки просмотрены в первичных HTML-источниках NIST DLMF:
T1: 27.5.2 и 27.5.5, обычная Möbius-инверсия и Lambda;
T2: 25.16.3, качественная PNT;
T3: 27.4.12, ряд -zeta'/zeta при Re s>1;
T4: 25.16.4, epsilon-критерий RH; 25.4.3-4, стандартное функциональное уравнение.
Видимые исправления обозначений логарифма и гармонических чисел не меняют эти входы. Исчерпывающий поиск errata не заявляется. Новая конечная Fourier-оценка доказана ниже самостоятельно; внешняя гипотеза об экспоненциальных суммах не импортирована.

```text
https://dlmf.nist.gov/27.5
https://dlmf.nist.gov/25.16
https://dlmf.nist.gov/27.4
https://dlmf.nist.gov/25.4
```

## 2. Конечный общий источник для двух физических окон

[FINITE_CELL | PAPER; X=2^j>=8.]

Положим m=4X, K=U=floor(sqrt X). На циклических индексах 0,...,m-1 зададим

    u_X(0)=0,
    u_X(n)=Lambda(n)-1, 1<=n<m,
    uhat_X(k)=(1/m)sum_(n=0)^(m-1)u_X(n) exp(-2pi i k n/m).

DFT здесь — точная конечная смена координат. Циклическая структура нужна для диагонализации разности, а НЕ для периодизации настоящих простых. Физические суммы используют только обычные индексы:

    B_Y(v;N)=sum_(floor(N/2)<n<=N)v(n),
    ||B_Y v||_Y^2=Y^(-2)sum_(N=Y)^(2Y-1)|B_Y(v;N)|^2,
    Y=X или 2X.                                      (2)

На обоих окнах 0<floor(N/2)<N<m; wrap-around отсутствует. Поэтому ||B_X u_X||_X^2=A(X) и ||B_(2X)u_X||_(2X)^2=A(2X) ТОЧНО. Индекс 4X имеет меру ноль в исходном интеграле и не удаляет никакого энергетического члена.

Низкие частоты: |k|_m=min(k,m-k)<=K, включая k=0. Их 2K+1. Пишем u_X=u_lo+u_hi по точной DFT-проекции. Обе части вещественны по сопряжённой симметрии.

## 3. Вся высокая часть имеет полилогарифмическую цену

[COFINAL_FAMILY | PAPER; каждый dyadic X>=8.]

### Теорема 1

    ||B_X u_hi||_X^2 <=64 log(4X),
    ||B_(2X)u_hi||_(2X)^2 <=16 log(4X).              (3)

Обе оценки используют ОДНУ проекцию u_X. Нормировка второй строки не означает повторного построения u_(2X).

**Доказательство.** Для общего конечного u с нулевой высокой модой k=0 определим циклический примитив

    vhat(k)=uhat(k)/(1-exp(-2pi i k/m))  на |k|_m>K,
    vhat(k)=0 в остальных модах.

Тогда v(n)-v(n-1)=u_hi(n). Конечный Parseval и sin(pi r/m)>=2r/m при 0<=r<=m/2 дают

    sum_n |v(n)|^2
      =m sum_(|k|_m>K) |uhat(k)|^2/(4sin^2(pi k/m))
      <=m^2/[16(K+1)^2] sum_n |u(n)|^2.              (4)

Для источника Lambda-1:

    sum_(n=0)^(m-1)|u_X(n)|^2
      <=sum_(n<m)Lambda(n)^2+m
      <=log(m)psi(m)+m
      <m(3log m+1).                                 (5)

Элементарное psi(t)<3t не требует PNT: из центральных биномиальных коэффициентов psi(2r)-psi(r)<=2r log2; суммирование до верхней степени 2 даёт psi(t)<4t log2<3t. Здесь это только источник явной конечной константы. Отрицательный член -2Lambda в (Lambda-1)^2 можно отбросить в верхней оценке.

По телескопированию B_Y(u_hi;N)=v(N)-v(floor(N/2)). При N=Y,...,2Y-1 верхние индексы лежат в [Y,2Y), нижние — в [Y/2,Y); области не пересекаются, каждый нижний индекс возникает дважды. Поэтому

    sum_(N=Y)^(2Y-1)|v(N)-v(floor(N/2))|^2
                 <=4 sum_(n=0)^(m-1)|v(n)|^2.        (6)

Обозначим h_X=3log(4X)+1. Из (4)-(6):

    ||B_Y u_hi||_Y <=4 sqrt(X^3 h_X)/(Y(K+1)).        (7)

Поскольку K+1>sqrt X, для Y=X это <=4sqrt(h_X), а для Y=2X — <=2sqrt(h_X). Так как log(4X)>1, h_X<=4log(4X). Получаем (3). QED.

В ненормированных единицах это O(X^2 log X), а не O(X^3), для всей высокой части. Это доказанный выигрыш степени только для данного компонента; он не является выигрышем полной ошибки простых.

## 4. Короткие делители: ненулевые низкие моды тоже оплачены

[COFINAL_FAMILY | PAPER. Это следствие получено после основного freeze. До его численной проверки отдельно зарегистрирована ставка P6 в сообщении владельцу и pretest_manifest; основной freeze не изменён.]

Для 1<=n<m положим

    s_X(n)=sum_(d<=U,d|n)a_d,  s_X(0)=0,
    L_U=sum_(d<=U)|a_d|<=U(1+log U),
    H_K=sum_(k=1)^K 1/k<=1+log K.

Пусть s_lo^circ — только НЕНУЛЕВЫЕ низкие частоты s_X. Среднее s_X из общего источника НЕ вычитается.

### Теорема 2

    |shat_X(k)|<=2L_U/m, 0<|k|_m<=K,
    ||B_Y s_lo^circ||_Y<=2L_U H_K/sqrt Y.             (8)

**Доказательство коэффициента.** Точно

    shat_X(k)=(1/m)sum_(d<=U)a_d G_(k,d),
    G_(k,d)=sum_(r=1)^floor((m-1)/d) exp(-2pi i k d r/m).

Пусть R=floor((m-1)/d), delta=m-dR, так что 1<=delta<=d. Для 1<=k<=K и d<=U имеем kd<=X=m/4. Геометрическая сумма удовлетворяет

    |G_(k,d)|=|sin(pi k d R/m)|/sin(pi k d/m)
             <=(pi k delta/m)/(2kd/m)
             <=pi/2<2.                              (9)

Случай d|m включён: тогда delta=d, R=m/d-1. Негативные частоты — сопряжённые. Значит первая строка (8) доказана.

Для любого физического окна модуль суммы exp(2pi i k n/m) не больше 1/|sin(pi k/m)|<=m/(2|k|_m). Поэтому, складывая обе половины низкой полосы,

    |B_Y(s_lo^circ;N)|<=2L_U H_K.

В окне Y слагаемых; после нормировки получаем вторую строку (8). QED.

При U=K<=sqrt X:

    ||B_X s_lo^circ||_X<=2(1+log K)^2,
    ||B_(2X)s_lo^circ||_(2X)<=sqrt(2)(1+log K)^2.     (10)

Это контролирует удаляемый СИГНАЛ в физической норме, а не только его отдельный главный квадрат. Следующее сравнение норм учитывает также его смешанные связи с длинной частью. Общая нулевая мода остаётся в неизвестной величине.

## 5. Явный оставшийся источник и точный возврат

[FINITE_CELL / COFINAL_FAMILY | PAPER.]

Определим коэффициенты c_X(k) на |k|_m<=K:

    c_X(0)=uhat_X(0)=[psi(m-1)-(m-1)]/m,
    c_X(k)=uhat_X(k)-shat_X(k)
      =(1/m)sum_(U<d<m)a_d
               sum_(r=1)^floor((m-1)/d)exp(-2pi i k d r/m),
                         0<|k|_m<=K.                (11)

Последняя строка использует полную свёртку sum_(d|n)a_d=Lambda(n)-1. Никакие настоящие длинные коэффициенты или prime powers не заменяются независимыми знаками.

Положим

    g_X(n)=sum_(|k|_m<=K)c_X(k)exp(2pi i k n/m),
    Lminus(X)=||B_X g_X||_X^2,
    Lplus(X)=||B_(2X)g_X||_(2X)^2.                   (12)

Это две положительные формы в одних и тех же 2K+1 коэффициентах. Если w_k(N)=sum_(floor(N/2)<n<=N)exp(2pi i k n/m), их Gram-матрицы имеют элементы Y^(-2)sum_N conjugate(w_k(N))*w_l(N), с Y=X,2X соответственно. Все внедиагональные связи сохраняются.

Точно u_X-g_X=u_hi+s_lo^circ. Теоремы 1-2 и обратное неравенство треугольника в физической норме дают

    |sqrt(A(X))-sqrt(Lminus(X))|<=rminus(X),
    |sqrt(A(2X))-sqrt(Lplus(X))|<=rplus(X),           (13)
    rminus=4sqrt(h_X)+2(1+log K)^2,
    rplus=2sqrt(h_X)+sqrt(2)(1+log K)^2.

Ортогональность DFT в физическом окне для (13) не предполагается. Отрицательный член второго масштаба не оценен модулем отдельно.

### Корневой поток

    G(X)=sqrt(A(X))-sqrt(A(2X))/sqrt(2),
    d_low(X)=sqrt(Lminus(X))-sqrt(Lplus(X))/sqrt(2),  (14)
    Delta_X=(4+sqrt(2))*sqrt(3log(4X)+1)
                                      +3(1+log K)^2.

Тогда для каждого dyadic X>=8

    |G(X)-d_low(X)|<=Delta_X.                        (15)

Это аддитивная полилогарифмическая цена. Коэффициент второго масштаба остался РОВНО 1/sqrt(2), без потери epsilon*A(2X).

Если t_X=max(d_low(X),0)+Delta_X, то (1),(15) дают конечную верхнюю оценку исходного объекта:

    C_long(X)<=sqrt(2)*t_X*sqrt(A(2X))+t_X^2+R0(X).  (16)

Действительно, sqrt(A(X))<=sqrt(A(2X))/sqrt(2)+t_X; обе стороны неотрицательны. Возведение в квадрат и (1) доказывают (16).

**Что (16) не доказывает:** t_X пока не ограничен субполиномиально. Он вычисляется из явной меньшей матрицы, но малая размерность сама по себе не оценивает её значение на настоящем векторе.

**Область и когерентность.** Lplus(X) не равна Lminus(2X): во втором случае период и cutoff другие. Ниже итерация применяется только к настоящей A(2^j), после возврата (15). Незаконной итерации по меняющимся проекциям нет.

### Нулевая мода не исчезла

Для постоянной последовательности g(n)=c_X(0) её собственный вклад в разность (12) равен

    Lminus_0(X)-Lplus_0(X)/2=|c_X(0)|^2/(8X).        (17)

Это следует из sum_(N=X)^(2X-1)ceil(N/2)^2=7X^3/12+X/6. По Chebyshev |c_X(0)|<2, так что (17)<=1/(2X). Однако смешанные произведения нулевой моды с остальными низкими модами не равны нулю. Они остаются в (12), и не объявлены оплаченными (17).

## 6. Точный контракт для исходной цели, без нового предположения

[COFINAL_FAMILY | PAPER для эквивалентности; обе арифметические посылки CONDITIONAL.]

Следующие два утверждения эквивалентны:

    TARGET: for every eta>0,
      C_long(X)<=C_eta X^eta(sqrt(A(2X))+1)
      for all sufficiently large dyadic X;

    LOW: for every epsilon>0,
      d_low(X)<=D_epsilon X^epsilon
      for all sufficiently large dyadic X.           (18)

LOW здесь НЕ ДОКАЗАНО. Это тот же уровень трудности, но с независимо ограниченным частотным дополнением.

**LOW => TARGET.** Для заданного eta применяем LOW с epsilon=eta/2. Из Delta_X=O_epsilon(X^epsilon) получаем t_X=O_eta(X^(eta/2)). Подставляем в (16); R0 — полилогарифм. Получаем TARGET.

**TARGET => LOW.** Положим a=sqrt(A(X)), b=sqrt(A(2X)). Из (1) и TARGET следует a^2<=b^2/2+t(b+1), где t=C'_eta X^eta>=1. Но

    (b/sqrt(2)+2t)^2-(b^2/2+t(b+1))
      =(2sqrt(2)-1)tb+4t^2-t>=0.

Значит G(X)<=2t. По (15), d_low(X)<=2t+Delta_X=O_eta(X^eta). Квантор по eta сохраняется. QED.

### Прямое критическое телескопирование корней

[ABSTRACT | PAPER: условная лемма.]

Пусть z_j>=0, z_j=o(2^(j/2)), и для каждого 0<epsilon<1/2 при всех поздних j

    z_j-z_(j+1)/sqrt(2)<=C_epsilon 2^(epsilon*j).    (19)

Тогда, разворачивая конечное число раз и затем используя терминал,

    z_j<=2^(-R/2)z_(j+R)
           +C_epsilon 2^(epsilon*j)
                        sum_(r=0)^(R-1)2^((epsilon-1/2)r),
    z_j<=C_epsilon 2^(epsilon*j)
                          /(1-2^(epsilon-1/2)).      (20)

Первый член стремится к нулю по o-условию. Все j+r остаются допустимыми. Никакой равномерности констант по epsilon не требуется. Это корневая форма критического bootstrap K; для неё не нужна повторная индукция по показателям энергии.

Для настоящего источника PNT даёт S(x)=o(x), A(2^j)=o(2^j). Поэтому z_j=sqrt(A(2^j)) имеет требуемый терминал. LOW и (15) обеспечили бы (19), а (20) — A(2^j)=O_delta(2^(delta*j)) для каждого delta>0.

Финальный source-return, только для проверки зависимости: в Re s>1

    integral_1^infinity S(x)x^(-s-1)dx
      =(1-2^(-s))/s * [-zeta'(s)/zeta(s)-zeta(s)].    (21)

Субполиномиальная энергия обеспечила бы абсолютную, локально равномерную сходимость самого интеграла при Re s>1/2: на [X,2X] его модульная цена <=sqrt(A(X))*X^(1/2-Re s). Нуль rho кратности r>0 оставлял бы вычет -r(1-2^(-rho))/rho !=0. Поэтому правых нулей не было бы; функциональное уравнение исключило бы левые. Это доказывает условную цепочку LOW => TARGET => RH, но НЕ LOW.

## 7. Попытка получить недостающую оценку на настоящих коэффициентах

[FINITE_CELL | PAPER для следующих расчётов; требуемый cofinal gain НЕ ПОЛУЧЕН.]

Проверены два естественных способа оценивать оставшийся (11), не меняя источник.

**Конечная делительная форма.** В (11) одновременно сохранены все d>sqrt X и их короткие кофакторы r. Поэлементные модули возвращают прежнюю большую цену; отрицательный хвост и смешанные связи должны оставаться в двух Gram-формах (12). Универсального порядка между этими двумя формами для произвольного вектора c нет. Положительность каждой из них не даёт upper bound их корневой разности.

**Abel-return с настоящей ошибкой простых.** Пусть D(n)=psi(n)-n, B(t)=1+sup_(1<=x<=t)|psi(x)-x|, z=exp(-2pi i k/m). Точное суммирование по частям даёт

    m*uhat_X(k)=D(m-1)z^(m-1)
                 +(1-z)sum_(n=1)^(m-2)D(n)z^n.

Отсюда

    |uhat_X(k)|<=[1+2pi|k|_m] B(m)/m.                (22)

Это честный source-bound, но не новый выигрыш. На физическом окне уже |S(N)|<=2B(4X), поэтому

    max(d_low(X),0)<=2B(4X)/sqrt X+Delta_X.           (23)

Если входной показатель B(X)=O(X^(theta+epsilon)), правая часть имеет показатель theta-1/2+epsilon; требуемое деление этого излишка пополам из (22) или (23) не следует. Раздельная оплата низких мод не создала нужного сокращения.

Из независимого старта A(X)<=21X и PNT остаётся лишь

    max(d_low(X),0)<=sqrt(21X)+Delta_X,
    max(d_low(X),0)=o(sqrt X).                       (24)

Это не X^epsilon для каждого epsilon>0. Таким образом ни TARGET, ни новый показатель ошибки простых здесь не получены. Я не называю (18) новой более слабой гипотезой и не объявляю вычисление c_X(k) доказательством их нужной совместной оценки.

## 8. Сильнейшая атака: что общие нормы не могут доказать

[ABSTRACT / COFINAL_FAMILY | PAPER. Это согласованный искусственный источник, НЕ изменение настоящей mu внутри результата.]

Для beta=3/4 возьмём последовательность

    b_1^*=-1, b_n^*=n^(beta-1) (n>=2),
    lambda^*(n)=1+b_n^*.

Она неотрицательна, lambda^*(1)=0, сумма lambda^* до x равна x+O(x^beta), а sum_(n<m)|b_n^*|^2<=m. Значит PNT-подобный главный член, diagonal-energy budget и общая Fourier-лемма выполняются. Это не prime-supported von Mangoldt и не обычная zeta.

У неё есть единая делительная история a^*=mu*b^*, не зависящая от X:

    a_d^*=d^(beta-1) product_(p|d)(1-p^(1-beta))-2mu(d),
    a_1^*=-1,  |a_d^*|<=3.                          (25)

Для prime power p^r первый множитель равен p^((r-1)(beta-1))*(p^(beta-1)-1), по модулю <=1; multiplicativity доказывает (25). Поэтому удаление коротких ненулевых мод также стоит только O(log X) в норме. Все представления применяются к СОБСТВЕННЫМ a^*, а не к ложному переименованию -mu log d.

Элементарное сравнение с интегралом даёт

    sum_(floor(N/2)<n<=N)b_n^*
      =c_beta N^beta+O(N^(beta-1)),
    c_beta=(1-2^(-beta))/beta>0.

Следовательно

    A^*(X)=C_beta X^(2beta-1)+O(X^(2beta-2)),
    C_beta=c_beta^2*(2^(2beta+1)-1)/(2beta+1)>0,
    G^*(X)=sqrt(C_beta)*(1-2^(beta-1))*X^(beta-1/2)
                                      +O(X^(beta-3/2)).       (26)

При beta=3/4 коэффициент перед X^(1/4) строго положителен. Доказанные цены частотного и короткоделительного дополнений для этого источника — O(log X), поэтому его compressed d_low^*(X) имеет тот же главный член:

    d_low^*(X)>=c_* X^(1/4)/2                       (27)

при всех достаточно больших dyadic X, где c_*=sqrt(C_beta)*(1-2^(beta-1))>0.

Для любого C>0 и любого epsilon<1/4 margin предполагаемой универсальной LOW-оценки имеет строгую отрицательную верхнюю огибающую:

    C X^epsilon-d_low^*(X)
      <=C X^epsilon-c_* X^(1/4)/2<0.                 (28)

Его собственное Mellin-преобразование равно K0(s)*(zeta(s+1-beta)-2), K0=(1-2^(-s))/s, и имеет настоящий полюс при s=beta. Поэтому spectral compression сохраняет, а не стирает ложный показатель.

KILL_SCOPE=THEOREM_SHAPE только для вывода LOW из общих PNT/положительности/диагонального размера без специальной информации о Lambda. Это НЕ контрпример к TARGET для настоящей zeta и НЕ запрет совместной оценки коэффициентов (11).

## 9. Pappus: что оплачено, что осталось и источниковые границы

[ABSTRACT / COFINAL_FAMILY | PAPER для доказанных переходов, CONDITIONAL для LOW.]

| Часть | Доказанная цена | Где используется |
|---|---:|---|
| M: переход F=C_long+R_M | O(log^4 X) | Точный возврат к поручению |
| Высокие аддитивные частоты | <=64log(4X), <=16log(4X) в соответствующих квадратах норм | (3), без фазового усреднения |
| Ненулевые низкие моды d<=sqrt X | O(log^2 X) в норме | (8)-(10), с общей нулевой модой внутри остатка |
| Смешанные связи с удалёнными частями | <=Delta_X в корневом потоке | (15), не отдельные модули пар |
| Оставшиеся 2floor(sqrt X)+1 мод | Нужна LOW | Независимого subpolynomial bound нет |

Три вопроса: LOW имеет точные кванторы; её достаточность следует из (16),(20),(21); более доступным стало только частотное дополнение, которое независимо оплачено. Алгебраической лёгкости оставшейся LOW не доказано. Размерность O(sqrt X) — не оценка сложности доказательства RH.

Сохранены: обычные целые, реальные Lambda и mu, все prime powers, фиксированные окна и все поздние dyadic X, исходная A, общий центр и все смешанные произведения внутри (12). Отброшенные компоненты имеют явный нормовый бюджет. Никакой переход к подпоследовательности S или к period-average не сделан.

**DMV/Beurling:** общий конечный Fourier-bound может работать на произвольном дискретном источнике, потому сам не различает миры. Ordinary integer-cell Mellin-match (21) нельзя переносить на generalized counting measure. Специальная LOW-оценка для обычной Lambda должна была бы использовать информацию, отсутствующую у ложного источника; такой оценки нет.

**DH:** его собственные Dirichlet-коэффициенты и completion не представлены обычными a_d=-mu(d)log d и формулой (21). Универсальная Parseval-часть не является доказательством RH для DH.

**Подсаженный квартет и self-dual plants:** при сохранённой ordinary zeta и изменении Gamma/local factor на Q(s-1/2) прежний источник описывает zeta, а не добавочные нули Q. Для полного изменённого источника обязателен Q'/Q. Он не удалён каким-либо frequency cutoff.

**R9 counterarray:** конечные Fourier-тождества универсальны, но отождествление sum_(d|n)a_d=Lambda(n)-1 требует настоящей свёртки. Изменённые коэффициенты не проходят этот source-match.

**Положительный контроль F3:** его собственная Xi_E(s)=2cosh((log3)(s-1/2)) имеет нули на Re s=1/2 непосредственно. Ordinary-Lambda Fourier-словарь ему не навязывается. Проверка полной новой RH-теоремы на всех мирах не объявляется завершённой, поскольку LOW отсутствует.

## 10. Проверки, прогнозы и closeout

[FINITE_CELL | PAPER для рациональных проверок; mpmath-часть — DIAG.]

После отдельного freeze выполнены точные проверки 476 исходных строк mu/divisor-свёртки в формальных рациональных коэффициентах при log простых; 360 строк телескопирования оконной матрицы с циклической разностью; 8 проверок multiplicity<=4. Проверены оба окна для X=8,16,32,64. Выборка не доказывает общих теорем: их доказательства выше независимы от неё.

На той же сетке при 50 и 80 десятичных знаках сверены DFT-реконструкция, высокий примитив, обе физические энергии, точные длинноделительные коэффициенты, low-short removal, root-return и DC-формула (17). Максимальная невязка тождеств меньше 1.4e-49 и 1.7e-79 соответственно. Это НЕ интервальные сертификаты.

| X | число оставшихся частот | G(X), DIAG | d_low(X), DIAG |
|---:|---:|---:|---:|
| 8 | 5 | 0.0701198228715 | 0.0625936611082 |
| 16 | 9 | 0.116819226981 | -0.0277683685708 |
| 32 | 11 | 0.0375426701756 | -0.0946791083925 |
| 64 | 17 | 0.103140076713 | 0.00714180200950 |

Различие знаков в отдельных строках допустимо: у возврата аддитивная ошибка, а не сохранение знака каждого конечного значения. Из таблицы не выводится LOW, RH или asymptotic rate.

P1 HIT: доказательство (3)-(7). P2 HIT: (15), без изменения критического коэффициента. P3 HIT: обе проекции/области явно разделены, итерации по Lplus(X)=Lminus(2X) нет. P4 HIT только в generic scope (25)-(28), не source-specific запрет. P5: целевой bound NOT_PROVED. P6 (после основного freeze, зарегистрирована отдельно ДО тестов): (8)-(10), HIT. Freeze не переписан задним числом.

K8A для цели: DOWNSTREAM_CONSUMER=исходный C_long затем RH; ACTUAL_CONSUMER_REQUIREMENT=source-specific односторонняя оценка на всех поздних dyadic X; ORIGINAL_REQUESTED_OBJECT=TARGET; ORIGINAL_OBJECT_IS=достаточный интерфейс, не единственный метод; KNOWN_WEAKER_INTERFACES=корневой поток с количественным возвратом или другой полный receiver; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=доказанная цена всего частотного дополнения и ненулевых коротких мод, а не новая RH-эквивалентность.

K8A для generic kill: ORIGINAL_OBJECT_IS=NOT_NECESSARY; FAILURE_TYPE=COUNTEREXAMPLE; KILL_SCOPE=THEOREM_SHAPE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для source-blind вывода; точный свидетель (25), огибающая (28). Специальные свойства настоящей Lambda отсутствуют у свидетеля и остаются допустимыми входами будущего доказательства.

Два оставшихся представления:
A. Полная совместная оценка двух Gram-форм (12) на настоящих длинноделительных коэффициентах (11), включая нулевую моду. Различающая сила высокая; аналитическая стоимость высокая. Нужна LOW, не малость отдельных мод.
B. Возврат к M: сохранить отрицательный квадрат d,e>2X и его смешанный блок через source-specific completion, не оптимизируя хвост как свободный вектор. Различающая сила высокая; стоимость высокая. Независимой цены ошибки такого completion пока нет.

REOPEN_TRIGGER: новый совместный source-bound для (11)-(12), или строгая ошибка в нормовом возврате. DISCRIMINATOR: точный коэффициентный вектор для finite identities; для RH — upper envelope на LOW и ненулевой остаток Mellin-полюса, не near-zero decimal.

```yaml
iteration:
  target: EXACT_C_LONG_FEEDBACK_FROM_M
  status: OPEN
  cognitive_operator_used: SOURCE_PRESERVING_SPECTRAL_COMPRESSION_AND_ROOT_ENERGY_FLUX
  new_gap_name: LONG_DIVISOR_LOW_MODES_PLUS_COMMON_ZERO_MODE
  invariant_learned: BOTH_SCALES_USE_ONE_PROJECTION_AND_RETURN_TO_THE_TRUE_ENERGY
  forbidden_future_move: PAY_LOW_MODES_FROM_GENERIC_DIAGONAL_SIZE_OR_IDENTIFY_CHANGING_PROJECTIONS
  next_decisive_test: SOURCE_SPECIFIC_ONE_SIDED_ROOT_BOUND_ON_THE_RETAINED_COEFFICIENTS
  route_score: 2
```

RH_PROVED=false. Никакого нового полного показателя ошибки простых нет. Историческая новизна DFT, Parseval или Poincare-оценки не заявляется. Записываются только новый freeze и этот verdict; прежние закрытые файлы и state не изменяются. Полный commit/blob и SHA256 сообщаются после удалённого readback. Уровень PAPER, без Lean/Arb и независимого аналитического аудита.

## Приложение: воспроизводимый судья

Переменные: X — основание двух окон; M=4X — длина конечной DFT; K=floor(sqrt X) — частотный cutoff и короткий divisor cutoff. n — ordinary integer source index; d — divisor; k — Fourier index. Никакие placeholder-значения заменять не нужно. Сохранить блок как verify_N.py и выполнить `uv run --with mpmath verify_N.py`. Выход — точные счётчики и отдельные DIAG-данные; обычный ASCII progress/ETA. Код не сертифицирует cofinal LOW.

```python
from __future__ import annotations
import hashlib, json, math, time
from fractions import Fraction
from pathlib import Path
import mpmath as mp

GRIDS=(8,16,32,64)
MANIFEST={
    'freeze_commit':'5393c758e76d78a1668d3a0b787aede3cf66f0d9',
    'grid':GRIDS,'precisions':(50,80),
    'post_freeze_pre_test_prediction':
      'For U=K=floor(sqrt(X)), M=4X, every nonzero retained frequency of the short-divisor source has modulus <=2*L_U/M. Its low-frequency window norm is <=2*L_U*H_K/sqrt(Y) for Y=X,2X. The full zero mode is retained. No cofinal low-source bound is assumed.',
    'tests':'exact source convolution, cyclic difference/window telescoping, multiplicities; DIAG DFT, two scale energy errors, low-short removal, original-source coefficient and bounds'
}
ROOT=Path(__file__).parent
(ROOT/'pretest_manifest.json').write_text(json.dumps(MANIFEST,indent=2))

def sieve(m: int):
    mu=[1]*(m+1); prime=[True]*(m+1)
    prime[0]=prime[1]=False
    for p in range(2,m+1):
        if prime[p]:
            for n in range(p,m+1,p):
                mu[n]=-mu[n]
                if n>p: prime[n]=False
            for n in range(p*p,m+1,p*p):mu[n]=0
    mu[0]=0
    pp=[0]*(m+1)
    for p in range(2,m+1):
        if prime[p]:
            q=p
            while q<=m:
                pp[q]=p;q*=p
    return mu,pp

def exact():
    source_rows=window_rows=multiplicity=0
    for X in GRIDS:
        M=4*X;mu,pp=sieve(M)
        avec=[{} for _ in range(M)]
        avec[1]={0:Fraction(-1)}
        for d in range(2,M):
            if mu[d]:
                n=d
                for p in range(2,d+1):
                    if n%p==0:
                        e=0
                        while n%p==0:n//=p;e+=1
                        avec[d][p]=Fraction(-mu[d]*e)
                    if n==1:break
        for n in range(1,M):
            got={}
            for d in range(1,n+1):
                if n%d==0:
                    for p,c in avec[d].items():got[p]=got.get(p,Fraction(0))+c
            got={p:c for p,c in got.items() if c}
            expect={0:Fraction(-1)}
            if pp[n]:expect[pp[n]]=Fraction(1)
            assert got==expect,(X,n,got,expect)
            source_rows+=1
        for Y in (X,2*X):
            mult=[0]*M
            for N in range(Y,2*Y):
                a=N//2;got=[0]*M
                for n in range(a+1,N+1):
                    got[n]+=1;got[(n-1)%M]-=1
                expect=[0]*M;expect[N]=1;expect[a]=-1
                assert got==expect
                assert 0<=a<N<M
                window_rows+=1
                mult[N]+=2;mult[a]+=2
            assert max(mult)<=4
            multiplicity+=1
    return dict(source_rows=source_rows,window_rows=window_rows,multiplicity_bounds=multiplicity)

def fft(data, inverse=False):
    a=list(map(mp.mpc,data)); n=len(a)
    assert n and n&(n-1)==0
    j=0
    for i in range(1,n):
        bit=n>>1
        while j&bit:j^=bit;bit>>=1
        j^=bit
        if i<j:a[i],a[j]=a[j],a[i]
    length=2;sign=1 if inverse else -1
    while length<=n:
        wlen=mp.exp(sign*2j*mp.pi/length)
        for st in range(0,n,length):
            w=mp.mpc(1)
            for j in range(length//2):
                u=a[st+j];v=a[st+j+length//2]*w
                a[st+j]=u+v;a[st+j+length//2]=u-v;w*=wlen
        length*=2
    if inverse:a=[z/n for z in a]
    return a

def windows(u,Y):
    pre=[mp.mpc(0)]
    for z in u:pre.append(pre[-1]+z)
    return [pre[N+1]-pre[N//2+1] for N in range(Y,2*Y)]

def energy(vals,Y):return mp.fsum(abs(z)**2 for z in vals)/Y**2

def run(X,dps):
    mp.mp.dps=dps;M=4*X;K=math.isqrt(X);mu,pp=sieve(M)
    u=[mp.mpf(0)]+[(mp.log(pp[n]) if pp[n] else mp.mpf(0))-1 for n in range(1,M)]
    a=[mp.mpf(0),mp.mpf(-1)]+[-mu[d]*mp.log(d) for d in range(2,M)]
    short=[mp.mpf(0)]*M
    for d in range(1,K+1):
        for n in range(d,M,d):short[n]+=a[d]
    fu=fft(u);fs=fft(short)
    low=[min(k,M-k)<=K for k in range(M)]
    hi=fft([0 if low[k] else fu[k] for k in range(M)],True)
    lo=fft([fu[k] if low[k] else 0 for k in range(M)],True)
    sl=fft([fs[k] if low[k] and k else 0 for k in range(M)],True)
    g=fft([fu[0]]+[fu[k]-fs[k] if low[k] else 0 for k in range(1,M)],True)
    vf=[mp.mpc(0)]*M
    for k in range(1,M):
        if not low[k]:vf[k]=fu[k]/(1-mp.exp(-2j*mp.pi*k/M))
    v=fft(vf,True)
    errs=[max(abs(u[n]-lo[n]-hi[n]) for n in range(M)),
          max(abs(v[n]-v[(n-1)%M]-hi[n]) for n in range(M)),
          max(abs(g[n]-(lo[n]-sl[n])) for n in range(M))]
    LU=mp.fsum(abs(a[d]) for d in range(1,K+1))
    HK=mp.fsum(1/mp.mpf(k) for k in range(1,K+1))
    logM=mp.log(M);theta=3*logM+1
    assert mp.fsum(abs(z)**2 for z in u)<4*X*theta
    for k in range(1,K+1):
        z=mp.exp(-2j*mp.pi*k/M)
        coef=mp.fsum(a[d]*mp.fsum(z**(d*r) for r in range(1,(M-1)//d+1)) for d in range(1,M))/M
        errs.append(abs(coef-fu[k]/M))
        assert abs(fs[k]/M)<=2*LU/M+mp.mpf(10)**(-dps+8)
    energies={};norms=[]
    for Y in (X,2*X):
        wu=windows(u,Y);wh=windows(hi,Y);wl=windows(lo,Y);ws=windows(sl,Y);wg=windows(g,Y)
        for N,z in zip(range(Y,2*Y),wh):errs.append(abs(z-(v[N]-v[N//2])))
        Au=energy(wu,Y);Ah=energy(wh,Y);Al=energy(wl,Y);As=energy(ws,Y);Ag=energy(wg,Y)
        rhi=4*mp.sqrt(X**3*theta)/(Y*(K+1));rshort=2*LU*HK/mp.sqrt(Y)
        tol=mp.mpf(10)**(-dps+8)
        assert mp.sqrt(Ah)<=rhi+tol
        assert mp.sqrt(As)<=rshort+tol
        assert abs(mp.sqrt(Au)-mp.sqrt(Al))<=rhi+tol
        assert abs(mp.sqrt(Au)-mp.sqrt(Ag))<=rhi+rshort+tol
        energies[Y]=(Au,Al,Ag)
        norms.append((mp.sqrt(Ah),rhi,mp.sqrt(As),rshort))
    Af=mp.sqrt(energies[X][0])-mp.sqrt(energies[2*X][0]/2)
    Gl=mp.sqrt(energies[X][2])-mp.sqrt(energies[2*X][2]/2)
    delta=(4+mp.sqrt(2))*mp.sqrt(theta)+3*(1+mp.log(K))**2
    assert abs(Af-Gl)<=delta
    c0=fu[0]/M
    e0minus=abs(c0)**2*mp.fsum(mp.mpf(N-N//2)**2 for N in range(X,2*X))/X**2
    e0plus=abs(c0)**2*mp.fsum(mp.mpf(N-N//2)**2 for N in range(2*X,4*X))/(2*X)**2
    errs.append(abs(e0minus-e0plus/2-abs(c0)**2/(8*X)))
    err=max(errs)
    assert err<mp.mpf(10)**(-dps+9),(X,dps,err)
    return {'X':X,'dps':dps,'K':K,'dimension':2*K+1,
            'A_X':mp.nstr(energies[X][0],18),'A_2X':mp.nstr(energies[2*X][0],18),
            'root_flux':mp.nstr(Af,18),'compressed_root_flux':mp.nstr(Gl,18),
            'root_difference':mp.nstr(abs(Af-Gl),18),'error_bound':mp.nstr(delta,18),
            'identity_max_error':mp.nstr(err,8),
            'high_norms_and_bounds':[[mp.nstr(t,12) for t in row] for row in norms]}

def main():
    start=time.time();result={'exact':exact(),'diagnostics':[]}
    total=2*len(GRIDS);step=0
    for dps in (50,80):
        for X in GRIDS:
            result['diagnostics'].append(run(X,dps));step+=1
            elapsed=time.time()-start;eta=elapsed*(total-step)/step
            print(f"[{'#'*step}{'.'*(total-step)}] {step}/{total} ETA {eta:.1f}s",flush=True)
    result['manifest_sha256']=hashlib.sha256((ROOT/'pretest_manifest.json').read_bytes()).hexdigest()
    (ROOT/'verification_results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
```
