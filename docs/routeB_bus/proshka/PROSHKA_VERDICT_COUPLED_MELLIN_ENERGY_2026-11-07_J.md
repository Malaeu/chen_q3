# STATUS: TRY_SIGNED_REASSEMBLY_WITH_OPEN_ENERGY_CONTRACTION_J

```yaml
STATUS: TRY_SIGNED_REASSEMBLY_WITH_OPEN_ENERGY_CONTRACTION_J
OPERATIVE_CLASS: TRY_SIGNED_REASSEMBLY_WITH_OPEN_ENERGY_CONTRACTION_J
DATE: 2026-11-07
AUTHORITY: OWNER_USE_ALL_AND_PROVE_CHAIN_TO_RH
ANSWER: EXACT_CANCELLED_CHANNEL_AND_COMPLETE_CONDITIONAL_RETURN_NOT_RH_PROOF
FULL_RH_ACCEPTANCE: NOT_COMPLETE
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_I_COMMIT: 3934348594d25a8a4b9ec8102d75a22ff7ba3688
INPUT_I_BLOB: 8850b2e211917743c5b88cc7e256cb661fddf024
INPUT_H_COMMIT: ba7a9b51624fde27858082a5662a24fe3f9bfbe2
INPUT_H_BLOB: 33732fd86c8439e8188cc8a1274d9c4b8af8d05a
SPEC_FREEZE_COMMIT: 33747314a59c316ebaab9b8e2a24ae4b6c3c496f
SPEC_FREEZE_BLOB: 276efa7aac378668734b73f3640c41aa96c7d5cd
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_COUPLED_MELLIN_ENERGY_2026-11-07_J.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_COUPLED_MELLIN_ENERGY_2026-11-07_J.md
SOURCE_MOBIUS_CHANGED: false
FULL_PRIME_POWERS_PRESERVED: true
CROSS_PREFIX_SOURCE_COHERENCE_PRESERVED: true
PROVED_STEPS:
  - {id: COMPLETE_DILATION_U1_CHANNEL_CANCELS_EXACTLY, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: SIGNED_FACTORIAL_HYPERBOLA_REASSEMBLY, scope: FINITE_CELL, verifier: PAPER}
  - {id: FACTORIAL_ROUNDING_LE_6_SQRT_N_LOG_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: JOINT_RECIPROCAL_POLES_REDUCE_TO_EXPLICIT_SIMPLE_POLES, scope: ABSTRACT, verifier: PAPER}
  - {id: PAID_ERROR_MELLIN_HOLOMORPHIC_RIGHT_OF_HALF, scope: ABSTRACT, verifier: PAPER}
  - {id: DYADIC_ENERGY_ERROR_LE_4_LOG_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: SOURCE_ENERGY_SUBPOLYNOMIAL_IMPLIES_RH, scope: COFINAL_FAMILY, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: DOUBLED_SCALE_ABSORPTION_WITH_KAPPA_LT_HALF, scope: ABSTRACT, verifier: PAPER, type: IMPLICATION_ONLY}
RH_GAP: NO_INDEPENDENT_ARITHMETIC_UPPER_BOUND_FOR_THE_FULL_SIGNED_DYADIC_ENERGY
MINIMAL_MISSING_IDENTITY: "Prove, for some fixed 0<=kappa<1/2 and every eta>0, E_j<=kappa*E_(j+1)+C_eta*2^(eta*j)*(sqrt(E_(j+1))+1) for all sufficiently large integers j, with the actual E_j of (12). No such estimate is proved here."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: EXACT_SOURCE_CANCELLATION_AND_ENERGY_RECEIVER_NOT_A_NEW_PRIME_ERROR_EXPONENT
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: [COMPLETE_U1_DILATION_CHANNEL, PAID_LONG_WINDOW_NORM_CHANGE, QUANTITATIVE_ENERGY_TO_ZERO_RECEIVER]
OPENS: []
DOES_NOT_KILL: [RH, JOINT_HYPERBOLA_BOUNDS, ORIGINAL_NB_GREEN_ROUTE, OTHER_SOURCE_CORRECT_RECEIVERS]
DISCRIMINATOR: "A right zero rho of multiplicity m leaves residue -m*(1-2^(-rho))/rho; its modulus is strictly positive. A bound on a meromorphic continuation is not convergence of the source Mellin integral."
REOPEN_TRIGGER: A source-derived energy contraction, or an error in the source reassembly or Mellin receiver.
COGNITIVE_OPERATOR: SIGNED_REASSEMBLY_BEFORE_SQUARING_AND_MELLIN_ENERGY
ROUTE_SCORE: 2
NUMERICAL_TESTS: DIAG_ONLY_50_AND_80_DIGITS
EXACT_TESTS: RATIONAL_PRIME_LOG_FORMS_AND_SYMBOLIC_LOCAL_POLES
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **Безусловную цепочку до RH не замкнул.** Получено настоящее совместное сокращение до нуля для целого семейства мёбиусовых блоков; оно не требует малости отдельных блоков. Затем построен точный Mellin-возврат полной связанной величины и проверена достаточная рекурсия энергии. Но независимая арифметическая оценка, запускающая эту рекурсию, отсутствует. Старые условные переходы не превращены в безусловные посылки.

## 1. Source lock и что именно собрано

[FINITE_CELL | PAPER: сверка источников, не независимый аудит всех прежних доказательств.]

Основной вход I — `PROSHKA_VERDICT_HYPERBOLA_FEEDBACK_2026-11-07_I.md` с commit/blob в YAML. Полная локальная копия имеет 36048 байт, Git blob пересчитан. H — `PROSHKA_VERDICT_BACKWARD_BOOTSTRAP_DESIGN_2026-11-07_H.md`, 22933 байта, также совпадает с pin. Короткие пути имеют префикс `docs/routeB_bus/proshka/`. Прочитаны актуальные протокол, Pappus skill и верхняя часть конструктора, blob `dee2c8200d6ad59e3eb7336e497f43e17a273f98`. Поиск имени новой попытки не дал результата; это не исчерпывающая проверка всего репозитория. Freeze создан отдельным коммитом и не редактировался.

Использование наработок не означает смешение норм:

| Наработка | Что сохраняется | Чего она не поставляет |
|---|---|---|
| I: гипербола | Точный T_N и ошибка sqrt(N) log N | Малость совместного T_N |
| G/H: bootstrap | Доступный старт и законная итерация показателей | Арифметический шаг улучшения |
| F: периодическая дисперсия | Доказанный bound по фазовому среднему | Контроль заданной фазы; это не среднее по меняющемуся N |
| E: Ramanujan head-tail | Исправленные коэффициенты, точный cross | Оценку всей положительной формы |
| a337b335: balanced Green | Собственный двухсторонний NB-return | Изометрию с новой E_j ниже; такой изометрии не заявлено |
| R6 и prime-only receiver | Необходимость полного source-match, включая Gamma и prime powers | Недостающий арифметический знак |

Формулы D, отозванные в E, не используются. «Используй всё» не является разрешением применять несовместимые или опровергнутые слоты.

Внешние THEOREM-входы: DLMF 27.4.5, 27.4.12–13 — Dirichlet-ряды в Re s>1; 27.5.2, 27.5.5 — две divisor-свёртки; 25.4.3–4 — стандартная xi и её симметрия; 25.16.4 — RH-оценка psi для каждого epsilon>0. HTML прочитан. Видимые исправления обозначений логарифма и гармонических чисел не меняют используемые формулы; исчерпывающий исторический поиск errata не заявляется. PDF не импортировался.

```text
https://dlmf.nist.gov/27.4#E5
https://dlmf.nist.gov/27.4#E12
https://dlmf.nist.gov/27.4#E13
https://dlmf.nist.gov/27.5#E2
https://dlmf.nist.gov/27.5#E5
https://dlmf.nist.gov/25.4#E3
https://dlmf.nist.gov/25.4#E4
https://dlmf.nist.gov/25.16#E4
```

Ни RH, ни простота нулей, ни bound на 1/zeta'(rho) не приняты как посылки. Общие Möbius-inversion и Mellin-приёмы классические: историческая новизна не заявляется.

## 2. Неизменный объект I

[FINITE_CELL / COFINAL_FAMILY | PAPER; для каждого целого N>=8.]

Пусть

    h=floor(N/2), H=N-h, Y=ceil(sqrt N), L=log N,
    b_(N,d)=mu(d)log(N/d), C_N=sum_(d<=Y)b_(N,d)/d,
    U_(N,m)=sum_(max(Y,floor(h/m))<d<=floor(N/m))b_(N,d),
    T_N=H(C_N-1)+sum_(m=1)^Y U_(N,m),
    W_N=psi(N)-psi(h)-H.

Нормировка b_(N,1)=log N сохранена. Вход I даёт, а прямое раскрытие целых частей проверяет:

    W_N=T_N+epsilon_N,
    epsilon_N=sum_(2<=d<=Y)b_(N,d)
                  ({h/d}-{N/d}),
    |epsilon_N|<=sqrt(N)log N.                         (1)

Все proper prime powers входят в psi. Отдельные квадраты U_(N,m) не заменяют квадрат связанной суммы T_N.

## 3. Точное знаковое сокращение целого семейства

[FINITE_CELL / COFINAL_FAMILY | PAPER; каждый вещественный x>=1.]

Определим конечные суммы, равные нулю при x<1:

    U0(x)=sum_(x/2<n<=x)mu(n),
    U1(x)=sum_(x/2<n<=x)mu(n)log(x/n),
    C(x)=log(x)*1_(1<=x<2).

### Теорема 1

    sum_(m<=x) U1(x/m) = C(x),
    sum_(m<=x) log(m) U0(x/m) = psi(x)-psi(x/2).        (2)

В частности, при x>=2 первый полный signed-канал равен НУЛЮ.

Доказательство. В первой сумме группируем пары mn=k. На каждой k вес log(x/(mn)) равен log(x/k), и сумма mu(n) по n|k равна 1_(k=1). Во второй вес log(m)=log(k/n), поэтому сумма по n|k равна Lambda(k). Область в обоих случаях — x/2<k<=x, со строгой нижней границей. При k=1 первая сумма даёт именно C(x); вторая даёт ноль. Все перестановки конечны. QED.

Следовательно для x>=2, положив u_m=U1(x/m), получаем также ТОЧНО

    sum_m u_m^2 + 2 sum_(m<r)u_m u_r = 0.             (3)

Здесь cross действительно равен минус ВСЕЙ диагонали. Большой отдельный U1, обнаруженный в I, не запрещает этого сокращения. Но (3) относится к полному каналу U1(x/m), а НЕ ко всему T_N: веса log(m)U0 и короткие делители ещё остаются.

### 3.1. Как сокращение действует на настоящую гиперболу

Пусть

    V_(N,m)=sum_(max(Y,floor(h/m))<d<=floor(N/m))mu(d).

Длинная строка из I раскладывается как log(m)V_(N,m) плюс соответствующая часть U1(N/m). По (2) сумма длинных U1-частей равна минус сумме коротких U1-частей. Поэтому

    W_N = sum_(d<=Y) mu(d) log( floor(N/d)! / floor(h/d)! )
          +sum_(m<=Y) log(m)V_(N,m)-H.                (4)

Это новое в данной сборке точное представление; в основе классическая свёртка mu*log=Lambda. Проверка непосредственно: для d<=Y суммируем log(m) по h<dm<=N, а для d>Y меняем порядок d,m. Границы и все знаки остаются.

В (4) строка m=1 исчезает из длинной части, поскольку log 1=0. Это не доказательство малости остальных строк и не оправдание нового диагонального Коши. Устраняется конкретный канал, а не сама проблема распределения простых.

### 3.2. Короткий factorial-блок имеет допустимую цену

Положим F(t)=t log t-t, t>=1, и

    Tstar_N=sum_(d<=Y)mu(d)[F(N/d)-F(h/d)]
             +sum_(m<=Y)log(m)V_(N,m)-H.

Тогда

    W_N=Tstar_N+epsilonstar_N,
    |epsilonstar_N|<=6 sqrt(N)log N.                  (5)

Для целого n>=1 сравнение суммы log(k) с интегралом даёт
F(n)+1<=log(n!)<=F(n+1)+1. Если n=floor(t), отсюда

    |log(floor(t)!)-F(t)|<=1+log(t+1).

При N>=8 имеем h>=Y, поэтому обе аргументные точки N/d и h/d не меньше 1. Цена двух концов для всех d<=Y не больше 2Y[1+log(N+1)]. Используем Y<=3sqrt(N)/2 и 1+log(N+1)<=2log N. Это (5). Квадратнокорневая ошибка оплачена независимо от RH. Для дальнейшей энергии сохраняется именно первоначальный T_N из (1); Tstar не подставлен молча вместо него.

## 4. Какие полюса сокращаются — и какие НЕ сокращаются

[ABSTRACT | PAPER.]

Обозначим

    K0(s)=(1-2^(-s))/s,
    K1(s)=[1-2^(-s)(1+s log2)]/s^2=-K0'(s).

Обе функции целые с устранимыми особенностями при s=0. Для Re s>1 абсолютная сходимость даёт

    int_1^infinity U0(x)x^(-s-1)dx=K0(s)/zeta(s),
    int_1^infinity U1(x)x^(-s-1)dx=K1(s)/zeta(s).       (6)

Каждый n интегрируется по n<=x<2n. Это общая область сходимости интегралов и Dirichlet-ряда, а не незаконная подстановка из другой полуплоскости.

Mellin-преобразование суммирования по m в (2) умножает на zeta(s); вес log(m) умножает на -zeta'(s). Поэтому

    zeta(s)*K1(s)/zeta(s)=K1(s),
    -zeta'(s)*K0(s)/zeta(s)=-K0(s)zeta'(s)/zeta(s).     (7)

Первый канал устраняет reciprocal-полюса полностью. Во втором исчезают коэффициенты 1/zeta'(rho) и высокие порядки reciprocal-полюсов: остаётся логарифмическая производная.

Если rho — нуль кратности m, то локально zeta(s)=(s-rho)^m h(s), h(rho)!=0. Следовательно

    Res_(s=rho)[-K0(s)zeta'(s)/zeta(s)]=-m K0(rho).    (8)

При Re rho=beta>0:

    |K0(rho)| >= (1-2^(-beta))/|rho| > 0.

**Оставшийся полюс не сокращён.** Полная signed-сборка не доказывает его отсутствия. Для простого нуля коэффициент больше не содержит 1/zeta'(rho), но сам нуль по-прежнему виден. Это точный предел достигнутого сокращения.

## 5. Полный Mellin-return для исходного T_N с оплаченным остатком

[ABSTRACT / COFINAL_FAMILY | PAPER.]

Определим

    W(x)=psi(x)-psi(x/2)-x/2, x>=1,
    Tstep(x)=T_floor(x), x>=8; Tstep(x)=0, 1<=x<8,
    r(x)=W(x)-Tstep(x).

Если x=N+t, N>=8, 0<=t<1, то обе psi-функции постоянны на ячейке, и

    W(x)-W_N=(N mod 2-t)/2,
    |r(x)|<=sqrt(x)log x+1/2.                         (9)

На 1<=x<8 достаточно |r(x)|<12: psi(8)=log840<7. Поэтому

    R(s)=int_1^infinity r(x)x^(-s-1)dx

голоморфна в Re s>1/2, причём для sigma=Re s>1/2

    |R(s)| <= 25/(2 sigma) + 1/(sigma-1/2)^2.         (10)

Это абсолютный интеграл с локально равномерной сходимостью. Логарифмические производные по s также интегрируемы на каждом компактном подмножестве. Не использовано расположение нулей.

В исходной области Re s>1:

    Phi_T(s):=int_1^infinity Tstep(x)x^(-s-1)dx
       =-K0(s)zeta'(s)/zeta(s)-1/[2(s-1)]-R(s).        (11)

Главный полюс при s=1 сокращается, поскольку K0(1)=1/2. Правая часть задаёт мероморфное продолжение Phi_T в Re s>1/2. В каждом настоящем правом нуле rho его вычет равен (8); R его уничтожить не может.

**Критическая оговорка:** мероморфное продолжение (11) не означает, что исходный интеграл уже сходится в Re s>1/2. Это как раз потребует оценки энергии из следующего раздела.

## 6. Длиннооконная энергия без потери степенного показателя

[FINITE_CELL / COFINAL_FAMILY | PAPER.]

Для j>=3 положим X=2^j и

    E_j=(1/X^2) int_X^(2X) |Tstep(x)|^2 dx
       =(1/X^2) sum_(N=X)^(2X-1) T_N^2.              (12)

Это конечная положительная квадратичная форма. Внутри КАЖДОГО T_N сначала складываются все signed-строки и общий центр, только затем берётся квадрат. E_j не равна старой NB-энергии E_N, balanced Green Z_N или периодической дисперсии V_N.

Также обозначим

    EW_j=X^(-2) int_X^(2X) W(x)^2 dx,
    ER_j=X^(-2) int_X^(2X) r(x)^2 dx.

Из (9), (a+b)^2<=2a^2+2b^2:

    ER_j<=3log^2(2X)+1/(2X)<=4log^2(2X),
    |sqrt(E_j)-sqrt(EW_j)|<=2log(2X).                 (13)

Последнее — обратное неравенство треугольника в нормированном L2. В частности E_j<=2EW_j+8log^2(2X) и обратно. Остаток имеет лишь полилогарифмическую цену; никакой N^delta потерей не скрыт.

Доступен безусловный старт

    0<=E_j<=64*2^j.                                  (14)

Действительно, элементарная Chebyshev-граница psi(N)<3N даёт |W_N|<=3N. Она выводится из центральных биномиальных коэффициентов и dyadic-суммирования, как в I. Из log N<=sqrt N и (1) следует |T_N|<=4N. Подставляем в (12), используя N<2X. Ни PNT, ни RH не нужны.

### Теорема 2: energy receiver

Если для некоторого b>=0 выполнено E_j=O(2^(b j)), то у zeta нет нетривиальных нулей с

    Re rho > 1/2+b/2.

Доказательство. Для sigma>1/2+b/2, по Cauchy–Schwarz на [X,2X],

    int_X^(2X)|Tstep(x)|x^(-sigma-1)dx
                      <=sqrt(E_j)*X^(1/2-sigma).

Сумма по j сходится геометрически, локально равномерно в s. Следовательно исходный интеграл Phi_T голоморфен в этой полуплоскости. По (11) настоящий нуль в ней дал бы ненулевой полюс (8), что невозможно. QED.

Отсюда

    [для каждого delta>0, E_j=O_delta(2^(delta j))]
                                  ==> RH.            (15)

Функциональное уравнение стандартной xi исключает левую половину после исключения правой. Нет предположения о простоте нулей. Обратно, RH и DLMF 25.16.4 дают (15)'s premise с помощью (1) и (12). Поэтому субполиномиальная энергия — RH-эквивалентный интерфейс, не новая безусловная оценка.

Дискриминатор: если существует настоящий нуль beta+i gamma с beta>1/2, то для каждого 0<=b<2beta-1

    limsup_(j->infinity) E_j / 2^(b j) = infinity.     (16)

Это следствие теоремы 2 от противного, а не утверждение о существовании такого нуля. Нельзя переносить (16) на старую Z_N без отдельного сравнения.

## 7. Рекурсия, которая завершила бы цепочку

[ABSTRACT | PAPER для импликации; source-посылка ниже CONDITIONAL и НЕ ДОКАЗАНА.]

Предлагаемый supplier:

    существует фиксированное 0<=kappa<1/2 такое, что
    для каждого eta>0 существуют C_eta,j_eta:
    E_j <= kappa E_(j+1)
           + C_eta 2^(eta*j)(sqrt(E_(j+1))+1)
    для ВСЕХ целых j>=j_eta.                          (17)

### Теорема 3: (14)+(17) влекут (15)

При 0<kappa<1/2 и любом целом R>=1 итерация по масштабу даёт

    E_j <= kappa^R E_(j+R)
          +C_eta sum_(r=0)^(R-1) kappa^r 2^(eta*(j+r))
                                         (sqrt(E_(j+r+1))+1).

По (14) первый член <=64*2^j*(2kappa)^R ->0. Если уже известно E_j=O(2^(b j)), 0<=b<=1, то при 0<eta<1/4 геометрический ряд имеет отношение kappa*2^(b/2+eta)<1. Значит

    E_j=O(2^((b/2+eta)j)).                            (18)

При kappa=0 вывод непосредственный. Для заданного 0<delta<1 берём eta=delta/4 и начинаем с b_0=1. Конечная индукция даёт

    b_n=2eta+(1-2eta)/2^n.

За конечное число шагов b_n<delta. Это (15). Константы могут зависеть от delta и конечного n; униформность по n не требуется. Все масштабы j+r остаются в области исходного supplier. QED.

**Порог поглощения проверен.** Если разрешить kappa=1/2, последовательность E_j=2^j удовлетворяет E_j=kappa E_(j+1) и (14), но не (15). Следовательно строгая граница kappa<1/2 существенна для этого контракта с линейным стартом. Это скалярный судья, не контрпример для настоящей mu.

При RH (17) автоматически выполнено даже с kappa=0, поскольку E_j субполиномиальна и sqrt(E_(j+1))+1>=1. Поэтому (17), со всеми eta, тоже RH-эквивалентно. Его польза — конкретная форма совместной оценки, а не логическое ослабление RH.

## 8. Главная попытка: что оценено и где нет поставщика

[COFINAL_FAMILY | CONDITIONAL для (17); PAPER для следующих границ.]

В этой работе независимо доказаны точное сокращение U1-канала, конечный factorial-return и цена ошибки (10),(13). Они не дают (17).

После (2) оставшаяся полная сумма равна sum_m log(m)U0(x/m)=psi(x)-psi(x/2). Её замена суммой модулей теряет signed-связи. Её точное Mellin-преобразование сохраняет все возможные правые полюса, как показано в (8). Отсюда нет ни коэффициента kappa<1/2, ни нужного корня из энергии следующего масштаба. Исходный bound (14) остаётся лучшим полученным здесь степенным бюджетом; ни один настоящий показатель theta не уменьшен.

Ещё один проверенный ложный shortcut: продолжить правую часть (11), затем объявить её L2-норму на новой вертикали нормой исходной функции. Уже f(x)=x^beta, x>=1, имеет Mellin-transform 1/(s-beta) лишь при Re s>beta. На вертикали sigma<beta мероморфная функция всё ещё имеет конечную норму

    int_R |1/(sigma+it-beta)|^2 dt=pi/|sigma-beta|,

но исходный интеграл int_1^infinity x^(2beta-2sigma-1)dx расходится. Значит такой перенос через полюс неправомерен. Это точный domain-judge, не запрет source-specific Mellin-метода.

Полная логическая цепочка имеет РОВНО одну недоказанную source-стрелку:

    настоящий signed источник
       -- НЕ ДОКАЗАНО: (17) --> повторяемый energy gain
       -- теорема 3 --> E_j=O_delta(2^(delta j)) для всех delta>0
       -- теорема 2 и (11) --> нет правых нулей
       -- стандартная xi(s)=xi(1-s) --> RH.

Старый путь I/H также сохраняется: достаточна совместная оценка T_N^2 через sqrt(N)*B(2N), с указанными eta-потерями. Она здесь тоже НЕ получена. Нельзя выдать новое energy-представление за её доказательство или использовать её как вход.

## 9. Pappus, источниковые контроли и дальнейшие варианты

[ABSTRACT | PAPER для контрактов; новые арифметические supplier'ы CONDITIONAL.]

Цены: совместное (2) — 0; factorial-rounding — <=6sqrt(N)log N; переход I к длинной энергии — <=4log^2(2X); источник имеет старт E_j<=64*2^j; улучшение (17) — OPEN. Наличие положительной формы не является её верхней оценкой.

**DMV/Берлинг.** Общая Möbius-инверсия возможна и там; нельзя объявлять (2)'s абстрактный multiplicative механизм уникальным для Q. Но обычный integer m, factorial-short block и unit cells x in [N,N+1) не сохраняют их counting measure. На корректном собственном источнике правый нуль также должен оставить полюс; доказанный supplier ниже его exponent там невозможен. Никакая неподтверждённая completion DMV не вводится.

**DH.** Обычная mu не является reciprocal Dirichlet-источником DH. Замена zeta на DH только справа (6),(7) запрещена; его conductor и odd-Gamma также нельзя заменить стандартной xi.

**Квартет и самодуальные подсадки.** При изменении uncompleted source на Q*zeta меняются reciprocal коэффициенты. Если меняется только local factor завершённой функции, ordinary mu продолжает описывать лишь zeta, не дополнительные нули Q*xi. Q'/Q в полном источнике нельзя удалять. Заключение (15) относится к стандартной zeta со стандартным Gamma-фактором.

**Контрмассив R9.** Для произвольных c_n первая сумма (2) равна sum_(x/2<k<=x)(c*1)(k)log(x/k), а не C(x). У R9 первая ненулевая ошибка (c*1)(n0) видна при x чуть больше n0. Поэтому exact cancellation требует настоящей полной mu*1=epsilon. Нулевая Gram-невязка сама это не заменяет.

**Кривая над F3.** Сохраняется её собственная положительная периодизация из прежних source-controls; ordinary mu/factorial formula ей не навязывается. Наша новая энергия не объявлена универсальным представлением её формы. Полная RH-приёмка отсутствует прежде всего потому, что (17) не доказано.

Два оставшихся направления:

A. Работать с factorial-short block и log(m)V_(N,m) совместно, сохраняя общий центр. Требуется независимый one-sided bound (17) или прежний feedback I. Различающая сила высокая, аналитическая стоимость высокая. Дальнейшее взятие независимых модулей не предлагается.

B. Остаться в полном NB/Green источнике и доказывать ограниченную source-correct подпоследовательность его собственной нормой. Различающая сила высокая, стоимость высокая; предыдущие receiver'ы доступны, но пересаживать их bounds на E_j нельзя. Это альтернатива, не дополнительная обязательная гипотеза.

K8A: DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=source-correct bound, исключающий правые нули; ORIGINAL_REQUESTED_OBJECT=полная цепочка без недоказанных посылок; ORIGINAL_OBJECT_IS=PROVED_NECESSARY для заявленной цели; PARTICULAR_METHOD_IS=NOT_NECESSARY; KNOWN_WEAKER_INTERFACES=любой самостоятельный NB/Weil receiver с доказанной source-посылкой; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=точно сокращённый канал и количественный energy-return, не историческая новизна классической свёртки; REOPEN_TRIGGER=первое независимое source-улучшение (17).

## 10. Проверки, closeout и передача

[FINITE_CELL | PAPER для точной алгебры; десятичные вычисления — DIAG.]

После freeze для N=8,9,16,31,32,64,128 проверены исходный W=T+epsilon, полная нулевая U1-сумма и factorial-reassembly через Fraction-векторы коэффициентов при log простых. Для N=8,16 также точно проверено diag+cross=0 как полиномиальное тождество при ненулевой диагонали. Символически проверены K1=-K0', значения при s=0 и residue -m*K0(rho) для local zero orders 1,2,3.

Диагностика при 50 и 80 десятичных знаках покрывает все N=8,...,255 и пять полных dyadic-окон. Максимальные невязки W-T-epsilon: 5.56e-49 и 5.94e-79; factorial-return: 1.20e-48 и 9.45e-79. Они НЕ являются интервальными сертификатами.

| X=2^j | E_j, DIAG | EW_j, DIAG | ER_j, DIAG |
|---:|---:|---:|---:|
| 8 | 0.01050084623 | 0.1252006426 | 0.09706110596 |
| 16 | 0.02827298723 | 0.1446485161 | 0.1038265708 |
| 32 | 0.03851980849 | 0.1131822591 | 0.08935973033 |
| 64 | 0.09612926952 | 0.1679589055 | 0.07766284703 |
| 128 | 0.1429342764 | 0.1828364180 | 0.06136229560 |

Ни одна строка таблицы не используется для (17), ограничения нулей или extrapolation. Основные доказательства не зависят от численной сетки.

P1 HIT: точное сокращение U1 и остаточный ненулевой simple pole. P2 HIT: (9),(10),(13). P3 HIT как receiver, не как полученная субполиномиальная оценка. P4 HIT: поглощение при kappa<1/2 и точный scalar boundary judge. P5: искомый source supplier NOT_PROVED. Новый factorial-return — следствие основной попытки после freeze, не задним числом отдельная ставка.

```yaml
iteration:
  target: JOINT_SIGNED_HYPERBOLA_EXPONENT_GAIN
  status: OPEN
  cognitive_operator_used: SIGNED_REASSEMBLY_BEFORE_SQUARING_AND_MELLIN_ENERGY
  new_gap_name: INDEPENDENT_FULL_SOURCE_DYADIC_ENERGY_CONTRACTION
  invariant_learned: ONE_COMPLETE_MOBIUS_CHANNEL_CANCELS_BUT_THE_LOG_DERIVATIVE_POLES_SURVIVE
  forbidden_future_move: TREAT_EXACT_CANCELLATION_OF_U1_OR_MEROMORPHIC_CONTINUATION_AS_RH
  next_decisive_test: PROVE_A_ONE_SIDED_BOUND_FOR_THE_REMAINING_LOG_WEIGHTED_COUPLED_SOURCE
  route_score: 2
```

**Итог:** реальное полное signed-сокращение найдено для одного канала. Оно не является всей нужной компенсацией. Ни первого выигрыша theta, ни безусловной цепочки до RH не получено. Freeze и прежние закрытые файлы не изменены. Уровень PAPER; Lean, Arb и независимого аналитического аудита не было. Финальный commit и blob сообщаются после удалённого чтения; собственный hash не включается в содержимое файла.

## Приложение: исполненный проверочный код

Сохранить блок как `verify_J.py` и выполнить `uv run --with sympy --with mpmath verify_J.py`. N — размер исходного префикса, Y — ceil(sqrt N), j — номер dyadic-окна. Никаких repository placeholders не нужно. Скрипт пишет `verification_J.json` рядом с собой; это локальная диагностическая квитанция, не RH-сертификат.

```python
"""Exact algebra and finite diagnostics for the signed hyperbola reassembly.
No interval certification and no test of an infinite RH quantifier.
"""
from fractions import Fraction as F
from collections import defaultdict
from math import isqrt
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

LIMIT = 256
mu = [int(sp.mobius(n)) if n else 0 for n in range(LIMIT + 1)]
factors = [sp.factorint(n) if n >= 2 else {} for n in range(LIMIT + 1)]
# Linear forms: key 0 means rational constant, key p means log(p).
def add(a, b):
    r = dict(a)
    for k,v in b.items():
        r[k] = r.get(k,F(0)) + v
        if not r[k]: del r[k]
    return r

def scale(a, c):
    c=F(c)
    return {k:v*c for k,v in a.items() if v*c}

def logform(n):
    return {int(p):F(v) for p,v in factors[n].items()}

def logratio(n,d):
    return add(logform(n),scale(logform(d),-1))

def sumforms(seq):
    out={}
    for v in seq: out=add(out,v)
    return out

def mangoldt_form(n):
    fac=factors[n]
    return {int(next(iter(fac))):F(1)} if len(fac)==1 else {}

def product(a,b):
    r=defaultdict(F)
    for p,u in a.items():
        for q,v in b.items(): r[tuple(sorted((p,q)))] += u*v
    return {k:v for k,v in r.items() if v}

source_checks=[]
for N in (8,9,16,31,32,64,128):
    h=N//2; H=N-h; Y=isqrt(N-1)+1
    W=add(sumforms(mangoldt_form(k) for k in range(h+1,N+1)),{0:F(-H)})
    C=sumforms(scale(logratio(N,d),F(mu[d],d)) for d in range(1,Y+1))
    U=[]; V=[]
    for m in range(1,Y+1):
        ds=range(max(Y,h//m)+1,N//m+1)
        U.append(sumforms(scale(logratio(N,d),mu[d]) for d in ds))
        V.append(sum(mu[d] for d in ds))
    T=add(scale(add(C,{0:F(-1)}),H),sumforms(U))
    eps=sumforms(scale(logratio(N,d),mu[d]*(F(N//d-h//d)-F(H,d))) for d in range(2,Y+1))
    assert add(T,eps)==W
    u1=[]; logu0=[]
    for m in range(1,N+1):
        ds=range(N//(2*m)+1,N//m+1)
        u1.append(sumforms(scale(add(logratio(N,d),scale(logform(m),-1)),mu[d]) for d in ds))
        logu0.append(scale(logform(m),sum(mu[d] for d in ds)))
    assert sumforms(u1)=={}
    assert sumforms(logu0)==add(W,{0:F(H)})
    short_factorial=sumforms(scale(sumforms(logform(m) for m in range(h//d+1,N//d+1)),mu[d]) for d in range(1,Y+1))
    long_counts=sumforms(scale(logform(m),V[m-1]) for m in range(1,Y+1))
    assert add(add(short_factorial,long_counts),{0:F(-H)})==W
    if N in (8,16):
        diag=sumforms(product(v,v) for v in u1)
        cross=sumforms(scale(product(u1[m],u1[r]),2) for m in range(N) for r in range(m+1,N))
        assert add(diag,cross)=={}
        assert diag # nonzero polynomial, despite exact cancellation.
    source_checks.append({'N':N,'Y':Y,'source_identity':True,'full_u1_sum_zero':True,'factorial_reassembly':True})

s=sp.symbols('s', nonzero=True)
a=sp.log(2)
K0=(1-sp.exp(-a*s))/s
K1=(1-sp.exp(-a*s)*(1+a*s))/s**2
assert sp.simplify(K1+sp.diff(K0,s))==0
assert sp.limit(K0,s,0)==a
assert sp.limit(K1,s,0)==a*a/2
z=sp.symbols('z')
k0,k1=sp.symbols('k0 k1')
residues=[]
for order in (1,2,3):
    model=z**order*(2+z+3*z*z)
    R=sp.limit(z*(-(k0+k1*z)*sp.diff(model,z)/model),z,0)
    assert R == -order*k0
    residues.append(str(R))

numeric={}
for precision in (50,80):
    mp.mp.dps=precision
    logs=[mp.mpf(0)]+[mp.log(n) for n in range(1,LIMIT+1)]
    psi=[mp.mpf(0)]*(LIMIT+1)
    for n in range(1,LIMIT+1):
        psi[n]=psi[n-1]+(logs[int(next(iter(factors[n])))] if len(factors[n])==1 else 0)
    Ts={}; Ws={}; epss={}; max_res=mp.mpf(0); max_factorial=mp.mpf(0)
    for N in range(8,256):
        h=N//2; H=N-h; Y=isqrt(N-1)+1
        C=mp.fsum(mu[d]*(logs[N]-logs[d])/d for d in range(1,Y+1))
        long=mp.fsum(mp.fsum(mu[d]*(logs[N]-logs[d]) for d in range(max(Y,h//m)+1,N//m+1)) for m in range(1,Y+1))
        T=H*(C-1)+long
        eps=mp.fsum(mu[d]*(logs[N]-logs[d])*(mp.mpf(N//d-h//d)-mp.mpf(H)/d) for d in range(2,Y+1))
        W=psi[N]-psi[h]-H
        max_res=max(max_res,abs(W-T-eps))
        short=mp.fsum(mu[d]*mp.fsum(logs[m] for m in range(h//d+1,N//d+1)) for d in range(1,Y+1))
        long2=mp.fsum(logs[m]*sum(mu[d] for d in range(max(Y,h//m)+1,N//m+1)) for m in range(1,Y+1))
        max_factorial=max(max_factorial,abs(short+long2-H-W))
        assert abs(eps) <= mp.sqrt(N)*logs[N]
        Ts[N]=T; Ws[N]=W; epss[N]=eps
    rows=[]
    for j in range(3,8):
        X=2**j
        E=mp.fsum(Ts[n]**2 for n in range(X,2*X))/(X*X)
        Wenergy=mp.fsum((Ws[n]+mp.mpf(n%2)/2)**2-(Ws[n]+mp.mpf(n%2)/2)/2+mp.mpf(1)/12 for n in range(X,2*X))/(X*X)
        Renergy=mp.fsum((epss[n]+mp.mpf(n%2)/2)**2-(epss[n]+mp.mpf(n%2)/2)/2+mp.mpf(1)/12 for n in range(X,2*X))/(X*X)
        mixed=mp.fsum(2*Ts[n]*(epss[n]+mp.mpf(n%2)/2-mp.mpf(1)/4) for n in range(X,2*X))/(X*X)
        assert abs(Wenergy-E-Renergy-mixed)<mp.power(10,-precision+5)
        assert Renergy <= 4*mp.log(2*X)**2
        assert abs(mp.sqrt(E)-mp.sqrt(Wenergy))<=mp.sqrt(Renergy)+mp.power(10,-precision+5)
        rows.append({'j':j,'X':X,'E':mp.nstr(E,35),'Wenergy':mp.nstr(Wenergy,35),'Renergy':mp.nstr(Renergy,35)})
    numeric[str(precision)]={'max_return_residual':mp.nstr(max_res,12),'max_factorial_residual':mp.nstr(max_factorial,12),'rows':rows}

# The generic threshold judge is exact: E_j=2^j satisfies E_j=(1/2)E_(j+1).
for j in range(3,12): assert F(2**j)==F(1,2)*2**(j+1)
report={'exact_source_checks':source_checks,'symbolic_residues':residues,'numeric_DIAG_only':numeric,'not_RH_certificate':True}
p=Path(__file__).with_name('verification_J.json')
p.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))

```
