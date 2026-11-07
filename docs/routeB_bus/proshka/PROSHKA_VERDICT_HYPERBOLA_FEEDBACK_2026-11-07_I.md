# STATUS: TRY_HYPERBOLA_FEEDBACK_WITH_DIAGONAL_OBSTRUCTION_I

```yaml
STATUS: TRY_HYPERBOLA_FEEDBACK_WITH_DIAGONAL_OBSTRUCTION_I
OPERATIVE_CLASS: TRY_HYPERBOLA_FEEDBACK_WITH_DIAGONAL_OBSTRUCTION_I
DATE: 2026-11-07
AUTHORITY: OWNER_OK_GO_AFTER_BACKWARD_BOOTSTRAP_DESIGN_H
ANSWER: PAID_SHORT_DIVISOR_RETURN_AND_SOURCE_EXACT_DIAGONAL_OBSTRUCTION
FULL_RH_ACCEPTANCE: NOT_COMPLETE
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_H_COMMIT: ba7a9b51624fde27858082a5662a24fe3f9bfbe2
INPUT_H_BLOB: 33732fd86c8439e8188cc8a1274d9c4b8af8d05a
INPUT_F_COMMIT: ed480327be4c37df57519cc5c06d4d7ecc3090e0
INPUT_F_BLOB: 642e3d6e6842a18ad04d7d11049404e356823413
SPEC_FREEZE_COMMIT: a02374da22450bc6c8f677ede785f74fec69820c
SPEC_FREEZE_BLOB: ebcf03b8bc4e5af8029099bafbbadb5656b8599d
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_HYPERBOLA_FEEDBACK_2026-11-07_I.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_HYPERBOLA_FEEDBACK_2026-11-07_I.md
SOURCE_MOBIUS_CHANGED: false
FULL_PRIME_POWERS_PRESERVED: true
CROSS_PREFIX_SOURCE_COHERENCE_PRESERVED: true
PROVED_STEPS:
  - {id: EXACT_FIXED_WINDOW_HYPERBOLA_RETURN, scope: FINITE_CELL, verifier: PAPER}
  - {id: SHORT_DIVISOR_ROUNDING_LE_SQRT_N_LOG_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: SQUARED_RETURN_WITH_LINEAR_B_COST_AND_FAVORABLE_SIGNS, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: TRUE_FIRST_ROW_MELLIN_POLE_WITNESS, scope: ABSTRACT, verifier: PAPER}
  - {id: DIAGONAL_ENERGY_NOT_O_N_TO_ONE_MINUS_DELTA, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: DIAGONAL_FEEDBACK_FALSE_FOR_EVERY_FIXED_ETA_BELOW_ONE_SIXTH, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: NO_JOINT_SIGNED_HYPERBOLA_UPPER_BOUND_WITH_EXPONENT_GAIN
MINIMAL_MISSING_IDENTITY: "For every eta>0, T_N^2 <= C_eta*(N^(1/2+eta)*B(2N)+N^(1+eta)) for every sufficiently large integer N, with T_N defined in (4). This sufficient source inequality is NOT proved."
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROGRESS_SCOPE: SHORT_DIVISOR_BUDGET_CLOSED_AND_ONE_OVERSTRONG_SUPPLIER_REFUTED
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: UNWEIGHTED_DIAGONAL_HYPERBOLA_ENERGY_FEEDBACK
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: ACTUAL_MOBIUS_BAND_MELLIN_POLE_AND_FEEDBACK_CONTRADICTION
    EVIDENCE: THIS_VERDICT_SECTIONS_4_TO_5_EQUATIONS_11_TO_18
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THE_DEFINED_DIAGONAL_INTERFACE
DOES_NOT_KILL:
  - RH
  - THE_TRUE_SIGNED_T_N_BOUND
  - NONLINEAR_FEEDBACK_IN_GENERAL
  - NONDIAGONAL_OR_DIFFERENTLY_WEIGHTED_ENERGIES
  - SOURCE_SPECIFIC_CROSS_TERM_CANCELLATION
  - SPARSE_SUBSEQUENCE_ESTIMATES_WITH_THEIR_OWN_RECEIVER
  - THE_ORIGINAL_NB_GREEN_ROUTE
DISCRIMINATOR: "A nonzero exact Mellin multiplier at a genuine zeta zero; no small decimal or hypothetical off-line zero is used."
REOPEN_TRIGGER: "A bound retaining the signed hyperbola cross terms, or an error in the exact split or pole witness."
COGNITIVE_OPERATOR: EXACT_HYPERBOLA_SPLIT_AND_MELLIN_FALSIFIER
ROUTE_SCORE: 3
CLOSES: [SHORT_DIVISOR_ROUNDING_AT_THE_BOOTSTRAP_SCALE, THE_TESTED_DIAGONAL_CAUCHY_SUPPLIER]
OPENS: []
NUMERICAL_TESTS: NO_FLOATING_POINT_SOURCE_CLAIMS
EXACT_TESTS: FORMAL_PRIME_LOG_VECTORS_AND_RATIONAL_POLYNOMIAL_IDENTITIES
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
DELIVERY: COMMIT_AND_REMOTE_BLOB_REPORTED_AFTER_WRITE
```

Ы. **Первая независимая часть разложения оплачена: короткие делители дают ошибку не больше sqrt(N) log N, с точным возвратом к исходному фиксированному окну. Но попытка получить самоулучшение через отдельные квадраты длинных блоков оказалась слишком сильной: она противоречит настоящей функции Мёбиуса.**

Это не доказательство RH. Получены равномерная цена короткого остатка и узкий запрет одного поставщика обратной связи. Нужная совместная знаковая оценка длинной части остаётся открытой. Свидетель запрета не меняет mu и не предполагает внеосевых нулей: достаточно уже существующих нулей на критической прямой.

## 1. Источники и граница новизны

[FINITE_CELL | PAPER: сверка источников; прежние теоремы остаются inherited PAPER.]

H — `docs/routeB_bus/proshka/PROSHKA_VERDICT_BACKWARD_BOOTSTRAP_DESIGN_2026-11-07_H.md`, commit/blob в YAML. Полная локальная копия: 22933 bytes, Git blob совпал. Используются глобальная цель B, dyadic-окно W_N, определение совместного остатка и доказанный receiver показателей. Его условную рекурсию заново за новую арифметику не выдаём.

F — `docs/routeB_bus/proshka/PROSHKA_VERDICT_SQRT_WINDOW_BALANCE_2026-11-06_F.md`, commit/blob в YAML. Полная локальная копия: 39496 bytes, Git blob совпал. Используется только унаследованная оценка 0<=V_N<=7N/2 и точный источник; фазовое среднее не подменяет фиксированное окно.

До freeze прочитаны обновлённый протокол, Pappus skill, верхняя часть конструктора `ROUTE_B_CONSTRUCTOR_PROVEN_2026-11-06.md` (blob dee2c8200d6ad59e3eb7336e497f43e17a273f98), а также `SELF_IMPROVEMENT_TEMPLATE_CHECK_2026-11-07.md`, eacc5128, blob 3d9b58e0a276dd1b07f05b698d4011dbcab5a09f. Короткое усреднение вокруг точки не повторяется. Утверждение о плотности d(psi-x) относительно dx из этого контекстного файла не импортируется: у psi есть атомы. Ниже используются точные целые части, без такого дифференциального предположения. Поиск Rjoint в доступном GitHub code search не дал результатов; это не исчерпывающий аудит отсутствия дублей. Непосредственный родитель inbox до freeze указан в frozen-файле.

Внешние входы:

- **THEOREM T1:** NIST DLMF 27.4.5: sum mu(n)n^(-s)=1/zeta(s), Re s>1. Используется только в области абсолютной сходимости.
- **THEOREM T2:** NIST DLMF 25.10(i): бесконечно много нетривиальных нулей, симметрия относительно Re s=1/2; там же дано существование бесконечного числа нулей на критической прямой. Достаточно одного с |Im rho|>4. Простота не нужна.
- **THEOREM T3:** DLMF 25.16.4, RH эквивалентна ошибке O_epsilon(x^(1/2+epsilon)) для каждого epsilon>0; DLMF 25.4.3–25.4.4 фиксирует стандартную завершённую функцию. Это только конечный receiver, не посылка нового bound.

Текущий HTML этих страниц прочитан; видимые поправки к Riemann–Siegel/notation и гармоническим числам не затрагивают перечисленные входы. Исчерпывающий поиск всех исторических исправлений не заявляется. PDF не импортировался.

```text
T1 https://dlmf.nist.gov/27.4#E5
T2 https://dlmf.nist.gov/25.10#i
T3 https://dlmf.nist.gov/25.16#E4
   https://dlmf.nist.gov/25.4#E3
   https://dlmf.nist.gov/25.4#E4
```

Гиперболическая перестановка и Mellin-полюсный метод классические. Историческая новизна этих приёмов не утверждается. Результат здесь — точный бюджет для выбранного feedback и проверка его конкретного диагонального поставщика.

## 2. Точное разложение фиксированного окна

[FINITE_CELL / COFINAL_FAMILY | PAPER; каждый целый N>=8.]

Сохраняем

    D(x)=psi(x)-x,
    B(X)=1+sup_(1<=x<=X)|D(x)|,
    h=floor(N/2), H=N-h, L=log N,
    W_N=psi(N)-psi(h)-H=D(N)-D(h).

Все степени простых входят в psi. Положим

    Y=ceil(sqrt N),
    b_(N,d)=mu(d)log(N/d), 1<=d<=N,
    C_(N,Y)=sum_(d<=Y)b_(N,d)/d.                       (1)

В частности b_(N,1)=log N, не 1. Это сырой логарифмический коэффициент; его не смешиваем с нормированным taper a_1=1 прежних файлов.

Для k>1 точная обычная свёртка даёт

    sum_(d|k)b_(N,d)=Lambda(k).

Поэтому, без приближения и пропуска границ,

    W_N=sum_(d<=N)b_(N,d)
           [floor(N/d)-floor(h/d)]-H.                 (2)

Здесь используется именно арифметика обычных целых: mu*1=epsilon и -sum_(d|k)mu(d)log d=Lambda(k). На рабочем окне h<k<=N индекс k=1 не возникает.

Для 1<=m<=Y определим

    U_(N,m)=sum_(max(Y,floor(h/m))<d<=floor(N/m))
                           mu(d)log(N/d),
    epsilon_N=sum_(2<=d<=Y)b_(N,d)
           [floor(N/d)-floor(h/d)-H/d].                (3)

Пустая сумма равна нулю. Границы эквивалентны d>Y и h<md<=N. Если d>Y, то m<=N/(Y+1)<Y. Следовательно включение всех m=1,...,Y законно, а последняя строка U_(N,Y)=0.

**Теорема 1 — source-exact возврат.**

    T_N=H*(C_(N,Y)-1)+sum_(m=1)^Y U_(N,m),
    W_N=T_N+epsilon_N,                                (4)
    |epsilon_N|<=sqrt(N)log N.                        (5)

Доказательство (4): в (2) для d<=Y выделить H/d; для d>Y поменять местами конечные суммы по d и m. d=1 не даёт rounding-error, поскольку N-h=H точно.

Для (5)

    floor(N/d)-floor(h/d)-H/d={h/d}-{N/d},
    |{h/d}-{N/d}|<1.

Отсюда

    |epsilon_N|<=sum_(2<=d<=Y)|mu(d)|log(N/d)
                <=(Y-1)log N < sqrt(N)log N.

Ни PNT, ни RH, ни оценка Mertens remainder здесь не использованы. Цена не скрывает растущего количества фаз. Точный длинный остаток T_N не заменяется суммой модулей.

**Что сохранилось.** То же W_N на каждом целом N, тот же глобальный B, настоящий ряд mu для всех префиксов, все prime powers, исходные границы h и N. Точные зависимости длинных U_(N,m) и короткого C_(N,Y) сохранены. Числа C_(N,Y) и c_N из H не объявлены равными.

## 3. Квадрат возвращается с нужной, а не линейной по N ценой

[COFINAL_FAMILY | PAPER; каждый N>=8.]

Из (4), не теряя знака,

    W_N^2=T_N^2+2 epsilon_N W_N-epsilon_N^2.            (6)

Поскольку |W_N|<=2B(2N),

    W_N^2 <= T_N^2+4 sqrt(N)log(N) B(2N),
    T_N^2 <= W_N^2+4 sqrt(N)log(N) B(2N)+N log^2(N).   (7)

Отрицательный квадрат в первой строке не оплачен модулем — он действительно полезен.

Унаследованный остаток H равен Rjoint_N=W_N^2-V_N. Поэтому получен прямой возврат именно к нему:

    Rjoint_N=T_N^2+2 epsilon_N W_N-epsilon_N^2-V_N,
    Rjoint_N <= T_N^2+4 sqrt(N)log(N)B(2N),
    |Rjoint_N-T_N^2|
       <=4 sqrt(N)log(N)B(2N)+N log^2(N)+7N/2.         (8)

Все дополнительные члены (7)–(8) укладываются в требуемое семейство
N^(1/2+eta)B(2N)+N^(1+eta), для каждого eta>0, с изменением константы. В частности, доказать

    T_N^2 <= C_eta*[N^(1/2+eta)B(2N)+N^(1+eta)]        (9)

на всех достаточно больших N было бы достаточно для receiver H. **(9) не доказано.** Формулы (4)–(8) закрывают rounding-часть разложения, а не превращают (9) в более слабое арифметическое утверждение автоматически.

## 4. Испытанный поставщик: квадратный корень из отдельной энергии

[FINITE_CELL | PAPER для построения; предлагаемая оценка ниже проверяется, а не принимается.]

Положим

    gamma_N=H*(C_(N,Y)-1)/Y,
    v_(N,m)=U_(N,m)+gamma_N,
    Dcal_N=sum_(m=1)^Y v_(N,m)^2,
    Jcal_N=2 sum_(1<=m<r<=Y) v_(N,m)v_(N,r).

Это полностью вычислимый конечный Gram плюс его точный signed cross:

    T_N^2=Dcal_N+Jcal_N,
    Dcal_N>=0,
    T_N^2<=Y*Dcal_N.                                  (10)

В естественной попытке применить Cauchy–Schwarz корень возникает, но платится Y~sqrt N. Для запуска желаемой обратной связи достаточным казался бы поставщик

    Dcal_N <= C_eta*[N^eta B(2N)+N^(1/2+eta)].          (D_eta)

**Теорема 2. Для каждого фиксированного 0<=eta<1/6 оценка (D_eta) на всех достаточно больших N ЛОЖНА.** В частности, ложен поставщик с квантором «для каждого eta>0». Это точное отрицание указанного утверждения для настоящей mu, не вывод из того, что оценку не удалось получить.

### 4.1. Явный источник препятствия: первая и последняя строки

Для N>=8 имеем h>=Y, поэтому

    U_(N,1)=sum_(N/2<d<=N)mu(d)log(N/d),
    U_(N,Y)=0.                                        (11)

Для любого общего центра gamma, не обязательно выбранного выше,

    2 sum_(m=1)^Y (U_(N,m)+gamma)^2 - U_(N,1)^2
      =(U_(N,1)+2gamma)^2
         +2 sum_(m=2)^(Y-1)(U_(N,m)+gamma)^2 >=0.

Следовательно на настоящем источнике

    Dcal_N >= U_(N,1)^2/2.                             (12)

Этот положительный свидетель сохраняет все значения mu и всю историю N. Он не является контрмассивом и не требует сведения ошибки psi к случайной модели.

### 4.2. Настоящий dyadic mu-band не может иметь показатель меньше 1/2

[ABSTRACT / COFINAL_FAMILY | PAPER; без RH и без простоты нулей.]

Для вещественного X>=1 определим

    U(X)=sum_(X/2<n<=X)mu(n)log(X/n).

**Лемма. Для каждого 0<=a<1/2 неверно U(N)=O(N^a) по всем целым N.**

При Re s>1 абсолютная сходимость позволяет переставить сумму и интеграл:

    integral_1^infinity U(X) X^(-s-1)dX=K(s)/zeta(s),
    K(s)=integral_(1/2)^1 log(1/u) u^(s-1)du
        =[1-2^(-s)(1+s log 2)]/s^2.                   (13)

Действительно, вклад каждого n интегрируется по n<=X<2n, после X=n/u равен n^(-s)K(s). Области исходного интеграла и Dirichlet-ряда ПЕРЕСЕКАЮТСЯ: Re s>1. Здесь нет ошибочного перехода из несовместимых полуплоскостей. K — целая функция, особенность при s=0 устранима, K(0)=(log 2)^2/2.

Предположим integer-bound U(N)=O(N^a). На каждом открытом интервале (N,N+1) набор n постоянен, а

    |U'(X)|=|sum_(X/2<n<=X)mu(n)|/X<=1, X>=2.

В верхнем конце новый член имеет нулевой вес; исчезновение нижнего члена происходит только при целых чётных X. U(N) задан правосторонней конвенцией, поэтому на [N,N+1) имеем |U(X)-U(N)|<=1. Следовательно U(X)=O(X^a) и для всех вещественных X>=2.

Тогда I(s)=integral_1^infinity U(X)X^(-s-1)dX голоморфен при Re s>a. Из (13) по единственности продолжения

    (s-1)zeta(s) I(s)=(s-1)K(s)

во всей этой полуплоскости. Выберем настоящий нетривиальный нуль rho=beta+i gamma с beta>=1/2 и |gamma|>4; его существование следует из T2, без RH. Но

    |1+rho log 2|>=|gamma|log 2>2>2^beta=|2^rho|,

так что K(rho)!=0. В rho левая часть равна нулю, правая — ненулю. Противоречие. Нулевая производная zeta в rho не мешает: порядок нуля может быть любым. Лемма доказана.

Из (12) следует для каждого 0<delta<1:

    limsup_(N->infinity) Dcal_N/N^(1-delta)=+infinity.  (14)

Это lower witness только для ДИАГОНАЛЬНОЙ цены. Никакая такая нижняя оценка T_N^2 или W_N^2 не выводится.

## 5. Почему ложна именно обратная связь D_eta, а не только удобная асимптотика

[COFINAL_FAMILY | PAPER.]

Для полноты достаточно элементарного старта B(X)<=3X. Один вывод: из центральных биномиальных коэффициентов

    psi(2m)-psi(m)<=log binom(2m,m)<=2m log 2.

Суммирование по степеням 2 и монотонность дают psi(x)<4x log 2<3x. Так как psi>=0, |psi(x)-x|<=2x и B(X)<=1+2X<=3X при X>=1. Никакой количественной PNT здесь нет.

Предположим (D_eta) с фиксированным 0<=eta<1/6. Из Y<=2sqrt N, (5),(10) и (x+y)^2<=2x^2+2y^2:

    W_N^2<=2Y Dcal_N+2N log^2 N
          << N^(3/2+eta)+N log^2 N,
    W_N << N^(3/4+eta/2).                             (15)

Телескопирование W_N=D(N)-D(floor(N/2)) на ВСЕХ больших N даёт

    B(X)<<X^(3/4+eta/2).

Возвращаем это в ПРЕДПОЛАГАЕМОЕ (D_eta):

    Dcal_N << N^(3/4+3eta/2).                         (16)

Показатель справа меньше 1 при eta<1/6. Это противоречит (14). Теорема 2 доказана. Полная RH даже не потребовалась: одного условного шага от стартовой оценки уже достаточно для противоречия внутри этого поставщика.

Для зарегистрированного eta=1/8 цепочка особенно прозрачна:

    D_(1/8) => B(X)<<X^(13/16)
            => Dcal_N<<N^(15/16)
            => U(N)<<N^(15/32),                       (17)

а 15/32<1/2 запрещено точным Mellin-полюсом (13).

**Строгая отрицательная огибающая.** Для любого A>0 и 0<delta<1 существуют сколь угодно большие N с U(N)^2>2(A+1)N^(1-delta). На них

    A*N^(1-delta)-Dcal_N
       <=A*N^(1-delta)-U(N)^2/2
       <-N^(1-delta)<0.                               (18)

Это явное направление upper-envelope для ложного следствия (16). Следовательно (D_eta), доказательно влекущее (16), тоже опровергнуто, а не просто неоплачено. Эквивалентно, при eta<1/6 отношение Dcal_N к N^eta B(2N)+N^(1/2+eta) имеет бесконечный limsup. Для каждого предполагаемого C нарушение имеет отрицательный margin C*[...]-Dcal_N. Номера нарушающих N не вычислены; доказательство аналитическое, не ARB_INTERVAL и не конечная сетка.

### Точный scope запрета

KILL_SCOPE=THEOREM_SHAPE: запрещён ровно (D_eta) для определённых (11) блоков, выбранного общего центра и диагонального Cauchy-перехода (10), с квантором по всем достаточно большим N. Внутренние знаки каждого U сохранены; потеря возникает при отдельной оплате их квадратов.

Не запрещены другие веса в Cauchy, недиагональные энергии, точный signed Jcal_N, иные разрезы, оценки на специальных подпоследовательностях с собственным receiver, NB/Green и RH. Более слабый диагональный бюджет может быть верен, но не давать нужного улучшения показателя. Формула (14) не говорит, что Dcal_N стремится к бесконечности на КАЖДОЙ подпоследовательности.

## 6. Что осталось после этого разреза

[FINITE_CELL | PAPER для равенства; COFINAL_FAMILY | CONDITIONAL для требуемой оценки.]

Полная сборка имеет вид

    Rjoint_N = Dcal_N + Jcal_N
                 +2 epsilon_N W_N-epsilon_N^2-V_N.    (19)

Dcal>=0 вычислима; Jcal — точный signed cross; остальные члены оплачены в (8). Вся арифметика ordinary mu сохранена. **Малость Dcal не является нужной задачей и даже несовместима с выбранной обратной связью.** Нужен совместный bound

    Dcal_N+Jcal_N=T_N^2
       <= C_eta*[N^(1/2+eta)B(2N)+N^(1+eta)]           (20)

для каждого eta>0 на всех достаточно больших N. Это прежний nonlinear supplier с независимо оплаченными короткими делителями, не новая доказанная оценка распределения простых.

Проверенный прямой модульный путь не даёт (20). Элементарно |C_(N,Y)|<=L(1+log Y), а суммирование модулей длинной части даёт бюджет O(N L^2); его квадрат порядка N^2 L^4. Само точное равенство T=W-epsilon вместе с Chebyshev улучшает грубый бюджет лишь до T=O(N). Если подставить желаемый W-bound в этот возврат, получится круг. В этой работе независимый upper bound (20) **не получен**, ни одно улучшение theta для настоящей psi не доказано.

**Минимальная недостающая строка — (20).** Она достаточна по (7) и receiver H. Зафиксированные кванторы не заменяются бесконечностью S: здесь нужны все большие N. Доказанный bounded-subsequence NB receiver является другой архитектурой и остаётся доступным.

## 7. Pappus: цены, сильнейшая атака и два оставшихся представления

[ABSTRACT / COFINAL_FAMILY | PAPER для контрактов; supplier (20) CONDITIONAL.]

| Часть | Цена | Итог |
|---|---|---|
| Divisor/hyperbola return (2)–(4) | 0 | Тождество того же источника |
| Короткие rounding-ошибки | <=sqrt N log N | Доказано для каждого N |
| Возврат квадратов | <=4sqrt N log N B(2N)+N log^2 N | Допустимый feedback-бюджет |
| Периодическая V_N | <=7N/2 | Унаследована; фиксированная фаза не заменена средней |
| Диагональная Dcal_N | Не O(N^(1-delta)) ни при каком delta>0 | Доказанная цена запрещает (D_eta) |
| Совместная Dcal_N+Jcal_N | Нужен (20) | OPEN; это носитель недоказанного выигрыша |

**Три вопроса.** Что именно: доказать (20), а не малость отдельно Dcal. Почему достаточно: (7) возвращает W, dyadic-телескопирование возвращает B, H замыкает показатели. Что стало доступнее: короткий divisor-rounding получил независимую цену нужного типа; ложный диагональный supplier исключён до длительных вычислений. Совместная арифметическая трудность автоматически не уменьшилась.

**Сильнейшая атака на результат.** T=W-epsilon; поэтому ограниченность короткого остатка не является первым шагом theta->theta/2+1/4. Большая Dcal также не делает большим T: cross может компенсировать её. На искусственном векторе (u,-u) диагональ равна 2u^2, квадрат суммы ноль. В нашем доказательстве свидетель для диагонали — настоящая mu, но это логическое различие сохраняется.

Оставшиеся репрезентации:

**A. Подписанная гиперболическая связь.** Сохранять общий центр и все Jcal, раскрывая связи между короткими m и длинными d, а не оплачивать независимые блоки. Требуется (20) или достаточная односторонняя форма с коэффициентом поглощения строго меньше 1. Kill-power высокий: проверяется реальный gain при theta=1 и совместимость с Mellin-полюсами. Аналитическая стоимость высокая. Такого supplier здесь нет.

**B. Длиннооконная энергия исходной ошибки psi вместо sup.** Строить собственный Mellin-возврат и нелинейную оценку энергии, сохраняя все знаковые связи; не отождествлять её с NB Z_N без количественной теоремы. Kill-power высокий, стоимость очень высокая: сначала domain/receiver, затем независимый bound. Это другой способ избежать чрезмерной отдельной цены U(N), не выполненное доказательство и не задание на повторное короткое усреднение.

Для near-zero алгебры discriminator — нулевой формальный вектор коэффициентов при log простых. Для cofinal-утверждения discriminator — строгий upper bound с полным возвратом; в отрицательном тесте — ненулевой K(rho), а не малая численная невязка.

## 8. Источниковые контроли

[ABSTRACT | PAPER для границ source-match; законченный новый RH-supplier не заявляется.]

**DMV/Берлинг.** В (2) кратность считает обычные целые пары d*m в фиксированном интервале, с ошибкой целой части <1. Для generalized integers эта единичная counting-решётка не сохраняется. Подстановка их собственного zeta-источника не имеет права пользоваться обычной mu и этим floor-budget. Наличие операции сложения на вещественных числах здесь не предмет запрета.

**DH.** Собственные обратные Dirichlet-коэффициенты DH не являются обычной mu; его odd-Gamma/conductor не заменяются стандартной xi. Именно source-равенство перед (2), а не абстрактный Cauchy, не переносится.

**Квартет и самодуальные подсадки.** При изменённом uncompleted источнике Q*zeta обычная mu не представляет полный reciprocal source. При изменении только локального Gaussian/Gamma-множителя ordinary mu описывает zeta, но не дополнительные нули Q*xi. Q'/Q в полном источнике не удаляется. Точный стандартный local factor остаётся обязанностью финального RH-return.

**Контрмассив R9.** Перестановка конечных сумм верна для любых коэффициентов, но отождествление с настоящей Lambda в (2) требует неизменённой mu*1 и mu*log. У R9 это ломается в первом изменённом divisor-индексе.

**Кривая над F3.** Проходит свой унаследованный положительный периодизационный источник, не ordinary-mu формулу (2). Настоящий false-supplier (D_eta) не требуется даже от мира с RH: его запрещают уже критические нули самой zeta. Это контроль того, что выбранная техника сильнее цели, а не отрицание положительного контроля кривой.

Полная приёмка нового RH-доказательства не выполнена, поскольку (20) отсутствует. Эти source-контроли не превращены в заявление, что один лишь разрез по sqrt N различил все миры и доказал нужный знак.

## 9. Проверки и судьба прогнозов

[FINITE_CELL | PAPER для точной алгебры; без численных оценок zeta.]

После freeze проверены N=8,9,16,31,32,64,128. На 288 divisor-индексах суммарно проверены буквальные floor-counts, source-свёртка и перестановка d*m. Для всех семи N точно проверены W=T+epsilon, U_Y=0, первая строка (11), T=sum v и положительный полиномиальный сертификат (12). Вычисления выполнены над fractions.Fraction с формальными коэффициентами при log простых и отдельной рациональной константой.

Дополнительно SymPy проверил первообразную для K(s), формулу (13) и предел K(0); рационально проверены показатели 1/8 -> 13/16 -> 15/16 -> 15/32. Эти проверки не являются доказательством бесконечных кванторов; доказательства §§2–5 независимы от удачных малых N. Никаких новых таблиц нулей, большой сетки, Lean или Arb не использовалось.

P1 HIT: (5). P2 HIT: точный центр C_(N,Y), без предположения c_N~1. P3 HIT в заявленном узком scope: (D_eta) опровергнуто, не signed T_N. P4 HIT: (7)–(8), с сохранённым благоприятным знаком. P5: целевой joint-bound NOT_PROVED; это не отдельный успешный арифметический прогноз.

## 10. K8A и closeout

Для kill: DOWNSTREAM_CONSUMER — (20), затем RH; ORIGINAL_REQUESTED_OBJECT — диагональный поставщик для Cauchy; ORIGINAL_OBJECT_IS=NOT_NECESSARY; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для (D_eta), eta<1/6. Пин свидетеля — этот файл, §§4–5, определения (11),(13), и неизменяемый freeze a02374da. Reopen trigger — ошибка в точном полюсном свидетеле или изменение интерфейса с доказанной ценой, а не увеличение диапазона DIAG.

Для цели: ACTUAL_CONSUMER_REQUIREMENT — действительное улучшение показателя того же B с доступным стартом; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS — короткий feedback-budget и опровержение конкретного чрезмерного поставщика на настоящей mu. Другие receivers, включая NB-подпоследовательность, не объявляются обязательствами этого proof attempt.

```yaml
iteration:
  target: INDEPENDENT_JOINT_PHASE_CENTERING_UPPER_BOUND
  status: PROGRESS
  cognitive_operator_used: EXACT_HYPERBOLA_SPLIT_AND_MELLIN_FALSIFIER
  new_gap_name: SIGNED_LONG_DIVISOR_HYPERBOLA_FEEDBACK_WITH_PAID_SHORT_ERROR
  invariant_learned: TRUE_MOBIUS_BAND_POLES_CANNOT_BE_REMOVED_BY_SEPARATE_SQUARE_BUDGETS
  forbidden_future_move: USE_D_ETA_AS_A_CONVENIENT_WEAKER_LEMMA_OR_BIG_DIAGONAL_AS_BIG_TOTAL
  next_decisive_test: SOURCE_BOUND_RETAINING_JCAL_AND_THE_SHARED_CENTER
  route_score: 3
```

RH_PROVED=false. Ни одного unconditional улучшения theta в этой попытке нет. Отдельный freeze и новый verdict — единственные файлы, записываемые в repo; предыдущие verdicts, state и чужие файлы не меняются. Commit/blob финальной записи и локальный SHA256 сообщаются после удалённого чтения. Уровень PAPER, без независимого аналитического аудита.
