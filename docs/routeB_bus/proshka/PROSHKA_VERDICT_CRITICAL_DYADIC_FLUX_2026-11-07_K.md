# STATUS: TRY_CRITICAL_DYADIC_PRIME_FLUX_K

```yaml
OPERATIVE_CLASS: TRY_CRITICAL_DYADIC_PRIME_FLUX_K
DATE: 2026-11-07
AUTHORITY: OWNER_USE_LAST_RESULTS_AND_PROVE_CHAIN_TO_RH
ANSWER: CRITICAL_FEEDBACK_REPAIR_AND_EXACT_PRIME_PAIR_RETURN_WITH_OPEN_SOURCE_BOUND
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
FULL_RH_ACCEPTANCE: NOT_COMPLETE
PROTOCOL_BLOB: aff942c4ca9e9fb1f92c6f849702f70b6a3b5162
PAPPUS_SKILL_BLOB: 91ad33ee1a45e256fbe2b229ef1abf74c672d26b
INPUT_J_COMMIT: ef09e34ba5e74fa443b748339a27891baf15cc0d
INPUT_J_BLOB: 4c46ce316e795fc58eb5e66f96454cc94978b0eb
INPUT_I_COMMIT: 3934348594d25a8a4b9ec8102d75a22ff7ba3688
INPUT_I_BLOB: 8850b2e211917743c5b88cc7e256cb661fddf024
SPEC_FREEZE_COMMIT: 1f736737a769ac9f2bfa1dec8e08b85a71de9692
SPEC_FREEZE_BLOB: 0d18bc869ef1995e7b62993fb25c0c4bd7647616
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_CRITICAL_DYADIC_FLUX_2026-11-07_K.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CRITICAL_DYADIC_FLUX_2026-11-07_K.md
PROVED_STEPS:
  - {id: PNT_TERMINAL_DECAY_O_SMALL_OF_2J, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: CRITICAL_HALF_FEEDBACK_CLOSURE, scope: ABSTRACT, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: PRIME_POWER_ENERGY_NORM_AT_MOST_21, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_PARITY_ENERGY_CORRECTION_AT_MOST_3_OVER_X, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: PRIME_ONLY_TO_ORIGINAL_T_ENERGY_RETURN, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_FINITE_OVERLAP_GRAM_AND_CRITICAL_PAIR_KERNEL, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_CRITICAL_BACKGROUND_ONE_OVER_8X, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: CRITICAL_PRIME_DIAGONAL_LOGARITHMIC_BUDGET, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: NO_INDEPENDENT_ONE_SIDED_BOUND_FOR_THE_SIGNED_PRIME_PAIR_AND_LINEAR_COMPENSATION
MINIMAL_MISSING_IDENTITY: "For every eta>0, Cpr(X)<=C_eta*X^eta*(sqrt(P(2X))+1) at all sufficiently large dyadic X; Cpr and P are exactly (13) and (1). NOT PROVED."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: CRITICAL_ABSORPTION_AND_PAID_SOURCE_CHANGES_NOT_A_PRIME_ERROR_EXPONENT_GAIN
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: [NEED_FOR_FIXED_GAP_BELOW_HALF_IN_THIS_FEEDBACK, PRIME_POWER_ENERGY_PRICE, LATTICE_CENTERING_PRICE, CRITICAL_FLUX_DIAGONAL_PRICE]
OPENS: []
DOES_NOT_KILL: [RH, SIGNED_PRIME_PAIR_METHODS, ORIGINAL_NB_GREEN_ROUTE, OTHER_SOURCE_CORRECT_RECEIVERS]
DISCRIMINATOR: NONZERO_MELLIN_RESIDUE_AT_ANY_RIGHT_ZERO_AND_EXACT_COEFFICIENT_TESTS_FOR_FINITE_IDENTITIES
COGNITIVE_OPERATOR: CRITICAL_SCALE_TELESCOPING_AND_INTEGER_CENTERED_PAIR_ENERGY
ROUTE_SCORE: 2
NUMERICAL_SOURCE_CLAIMS: NONE
EXACT_TESTS: INTEGER_AND_RATIONAL_PRIME_LOG_POLYNOMIALS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **Доказательство RH не получено.** Совместное использование I/J даёт не готовое сжатие энергии, а следующие дополнительные результаты: критический коэффициент **ровно 1/2** допустим благодаря PNT; собственные степени простых имеют постоянную цену в норме энергии; целочисленное центрирование сокращается по чётности с ошибкой O(1/X); критическая разность энергий имеет явный конечный prime-pair source с оплаченной диагональю. Необходимую одностороннюю оценку его подписанной части я не доказал. Ни один новый безусловный показатель ошибки простых не получен.

## 1. Источники и неизменная цель

[FINITE_CELL | PAPER для сверки; прежние результаты — inherited PAPER.]

I/J — два файла с pins в YAML, под `docs/routeB_bus/proshka/`. Локальные полные файлы имеют соответственно 36048 и 39855 bytes; Git blobs пересчитаны и совпали. Использованы I, §§2–3, и J, §§3,5–7: тот же dyadic-остаток, оплаченный короткий дефект и Mellin-приёмник. Открытая рекурсия J не импортируется как теорема. Bootstrap и Pappus skill получены заново через GitHub. Поиск имени новой попытки не дал результатов; это не исчерпывающий аудит репозитория. Freeze записан отдельным коммитом и прочитан обратно.

**THEOREM T1:** NIST DLMF 25.16.3: psi(x)=x+o(x). Используется качественная PNT, не степенная оценка ошибки. **THEOREM T2:** DLMF 27.4.12: сумма Lambda(n)n^(-s) равна -zeta'(s)/zeta(s) при Re s>1. **THEOREM T3:** DLMF 25.16.4 и 25.4.3–25.4.4: epsilon-формулировка RH, функциональное уравнение и стандартный Gamma-фактор. Текущие HTML-формулировки просмотрены. Видимая поправка 25.16 к гармоническим числам не относится к используемым формулам; 27.4 отмечает изменение обозначения логарифма. Исчерпывающий поиск всех исправлений не заявляется. PDF не использовались.

```text
https://dlmf.nist.gov/25.16#E3
https://dlmf.nist.gov/25.16#E4
https://dlmf.nist.gov/27.4#E12
https://dlmf.nist.gov/25.4#E3
https://dlmf.nist.gov/25.4#E4
```

Здесь нужны **все достаточно большие dyadic-масштабы**, а не только N из S. Это продолжение глобального energy-bootstrap J. Оно не объявляет доказанной оценку на S и не отождествляет новую энергию с прежней NB-формой Z_N.

## 2. Prime-only энергия с полным количественным возвратом

[FINITE_CELL / COFINAL_FAMILY | PAPER.]

Пусть X=2^j, j>=3. Обозначим

    lambda_1(n)=log(n), если n простое, и 0 иначе;
    vartheta(x)=sum_(p<=x) log p;
    b_n=lambda_1(n)-1;
    S_1(x)=sum_(x/2<n<=x)b_n;
    P(X)=X^(-2) integral_X^(2X) S_1(x)^2 dx
        =X^(-2) sum_(N=X)^(2X-1) S_1(N)^2.                 (1)

S_1 постоянна на каждой полуоткрытой единичной ячейке. Это положительная конечная энергия настоящих первых степеней простых, с фиксированной исходной фазой. Для сравнения пусть S_Lambda использует Lambda(n)-1, а A(X) — ту же норму S_Lambda. Тогда S_Lambda(N)=W_N из I точно, поскольку число целых в (N/2,N] равно N-floor(N/2).

### 2.1. Все собственные степени простых оплачены константой 21

Элементарно psi(x)<3x при x>=1. Действительно,

    psi(2m)-psi(m)<=log binom(2m,m)<=2m log 2;

каждая простая степень в (m,2m] даёт единицу в соответствующем p-adic valuation. Суммирование по степеням 2 и монотонность дают psi(x)<4x log 2<3x. Поэтому vartheta(x)<3x.

Далее

    0<=psi(x)-vartheta(x)
      =sum_(a>=2) vartheta(x^(1/a))
      <=3 sqrt(x)+3 x^(1/3) log(x)/log 2
      <17 sqrt(x).                                       (2)

Использовано sup_(t>=0) t exp(-t/6)=6/e<3 и log 2>2/3. Оценка грубая, но без RH/PNT.

Разность S_Lambda(N)-S_1(N) неотрицательна и не больше 17 sqrt(N). Отсюда

    X^(-2) sum_(N=X)^(2X-1) |S_Lambda(N)-S_1(N)|^2
      <(3/2)*17^2<21^2,
    |sqrt(A(X))-sqrt(P(X))|<21.                          (3)

Из I, |T_N-W_N|<=sqrt(N)log N, отдельно следует

    |sqrt(E_j)-sqrt(A(X))|<=sqrt(3/2)log(2X),
    |sqrt(E_j)-sqrt(P(X))|
         <=21+sqrt(3/2)log(2X),                          (4)

где E_j — **именно исходная энергия J**, не новая сумма отдельных квадратов. Так все собственные степени и короткие делители сохраняются с явной ценой; они не удалены из источника без остатка. Субполиномиальность P(2^j) эквивалентна субполиномиальности E_j.

### 2.2. Доступный старт и важная добавка PNT

Число целых в (x/2,x] отличается от x/2 не более чем на 1/2. Из vartheta(x)<3x получаем |S_1(x)|<=3x при x>=1, следовательно

    0<=P(X)<=21X.                                       (5)

PNT и (2) дают vartheta(x)=x+o(x), поэтому S_1(x)=o(x) и

    P(2^j)=o(2^j).                                     (6)

По (4) также E_j=o(2^j). Это сильнее простого O(2^j) именно для снятия крайнего члена обратной рекурсии. **Никакой фиксированный степенной выигрыш из (6) не извлечён.**

## 3. Чётность точно сокращает ошибку центрирования

[COFINAL_FAMILY | PAPER; все dyadic X>=8.]

Пусть

    W_1(x)=vartheta(x)-vartheta(x/2)-x/2,
    W_Lambda(x)=psi(x)-psi(x/2)-x/2,
    EW_1(X)=X^(-2) integral_X^(2X) W_1(x)^2 dx,
    EW_Lambda(X)=X^(-2) integral_X^(2X) W_Lambda(x)^2 dx.

Тогда

    EW_1(X)-P(X)
       =[vartheta(2X)-vartheta(X)]/(2X^2)-1/(6X),
    EW_Lambda(X)-A(X)
       =[psi(2X)-psi(X)-log 2]/(2X^2)-1/(6X).          (7)

В частности, модули обеих разностей меньше 3/X.

**Доказательство.** На x=N+t, 0<=t<1, положим e=N mod 2. Для обоих источников

    W(x)=S(N)+(e-t)/2,
    integral_N^(N+1) (W(x)^2-S(N)^2)dx
        =(e-1/2)S(N)+1/12.

Теперь парно складываем соседние чётный и нечётный N. Точно

    S(2k+1)-S(2k)=lambda(2k+1)-1.

Для lambda_1 на (X,2X] нет чётного простого. Для Lambda имеется ровно одна чётная простая степень, дающая log 2. Число нечётных индексов равно X/2. Это доказывает (7), включая константу -1/(6X). По 0<=vartheta(2X)-vartheta(X)<6X и такому же bound для суммы нечётных prime powers получаем

    -1/(6X)<=EW-P<17/(6X)<3/X.

Здесь «сдвиг на единицу» используется буквально: соседние ячейки сокращают линейный смешанный член. Просто |W-S|<=1/2 дало бы гораздо более грубую цену. Ни (7), ни малая цена центрирования не оценивают саму P(X).

## 4. Критический коэффициент 1/2 теперь допустим

[ABSTRACT | PAPER: условная теорема с полностью указанной посылкой.]

**Лемма.** Пусть u_j>=0, u_j=o(2^j). Предположим, что для каждого eta>0 существуют C_eta,j_eta такие, что

    u_j <= (1/2)u_(j+1)
           +C_eta*2^(eta*j)*(sqrt(u_(j+1))+1)
    для всех целых j>=j_eta.                           (8)

Тогда для каждого delta>0, u_j=O_delta(2^(delta*j)).

**Доказательство.** Для конечного R итерация даёт

    u_j <= 2^(-R)u_(j+R)
      +C_eta sum_(r=0)^(R-1)2^(-r)2^(eta*(j+r))
                                (sqrt(u_(j+r+1))+1).

Первый член равен 2^j[u_(j+R)/2^(j+R)] и стремится к нулю по дополнительному o-условию. Если уже известно u_j=O(2^(b*j)), 0<=b<=1, то при 0<eta<1/4 ряд справа имеет отношение 2^(-1+b/2+eta)<1. Получаем u_j=O(2^((b/2+eta)*j)). Старт b=1 доступен. Для заданного delta выбираем eta=delta/4 при 0<delta<1 и делаем конечное число шагов:

    b_r=2eta+(1-2eta)/2^r < delta

при достаточно большом конечном r. Остальные delta тривиальны. Константы и пороги могут зависеть от delta и номера конечной итерации. QED.

В J требовалось kappa<1/2, поскольку использовался лишь O(2^j) старт. Тамошний пример u_j=2^j корректен, но нарушает новое условие u_j=o(2^j). Теперь PNT оплачивает ровно критическую границу. Это не исправление ложной теоремы J, а ослабление её достаточного интерфейса с новым законным входом.

Больше 1/2 автоматически разрешить нельзя: для любого фиксированного kappa>1/2 существует 0<b<1 с kappa*2^b>=1. Тогда u_j=2^(b*j)=o(2^j) удовлетворяет u_j<=kappa u_(j+1), но не субполиномиальна. Это скалярный судья границы, не утверждение о настоящем prime source.

## 5. Полный конечный source: пересечение двух окон

[FINITE_CELL / COFINAL_FAMILY | PAPER.]

Для положительных целых n,m определим

    L_X(n,m)=[min(2X,2n,2m)-max(X,n,m)]_+.

Это длина пересечения [X,2X], [n,2n] и [m,2m]. Все концы целые; выбор открытого или закрытого конца не меняет длину. Из (1)

    P(X)=X^(-2) sum_(n,m<=2X) b_n b_m L_X(n,m).        (9)

Матрица L_X — положительный Gram индикаторов для любых входных коэффициентов. Для нового source-bound важны именно настоящие b_n; одной положительности недостаточно.

Продолжим L_X нулём на индексы до 4X и положим

    Pi_X(n,m)=L_X(n,m)-(1/8)L_(2X)(n,m).              (10)

Коэффициент 1/8, а не 1/2, возникает из нормировки (2X)^(-2) и внешнего множителя 1/2. Тогда точно

    P(X)-(1/2)P(2X)=X^(-2) sum_(n,m<=4X)b_n b_m Pi_X(n,m).

Pi_X вообще не положительна. Никакой PSD-перенос на её подписанную часть не применяется.

### 5.1. Весь целочисленный фон вычисляется без оценки

Пусть a=max(X,n), b=min(2X,2n). Тогда

    R_X(n):=sum_m L_X(n,m)
       =floor(b^2/4)-floor(a^2/4), если b>a;
       =0 иначе.                                    (11)

Действительно, на ячейке [t,t+1) число целых в (x/2,x] равно ceil(t/2), а sum_(0<=t<M)ceil(t/2)=floor(M^2/4). Кроме того, при чётном X

    sum_(n,m)L_X(n,m)
       =sum_(t=X)^(2X-1)ceil(t/2)^2
       =7X^3/12+X/6.

Следовательно

    sum_(n,m<=4X)Pi_X(n,m)=X/8.                       (12)

Главный кубический член сократился **точно**. После энергетической нормировки остаётся 1/(8X). Это оценка/вычисление фона, не доказательство сокращения неизвестных prime correlations.

### 5.2. Настоящие пары простых, диагональ и точная линейная компенсация

Положим RPi_X(p)=R_X(p)-R_(2X)(p)/8 и

    Dpr(X)=X^(-2) sum_(p<=4X)(log p)^2 Pi_X(p,p),
    Cpr(X)=(2/X^2)*[
       sum_(p<q<=4X)log p log q Pi_X(p,q)
       -sum_(p<=4X)log p RPi_X(p)].                   (13)

Все p,q здесь настоящие простые. Cpr — **совместно** парный член и его линейная плотностная компенсация, а не только необработанная сумма по p!=q. Раскрытие b=lambda_1-1 в (9)–(12) даёт

    P(X)-(1/2)P(2X)=Dpr(X)+Cpr(X)+1/(8X).            (14)

Веса двух масштабов, все перекрёстные члены и все целочисленные концы сохранены. Эта Cpr не обозначает прежний cross X_N между головой и хвостом NB-формы.

### Теорема: диагональ стоит только логарифм

Для каждого dyadic X>=8

    Dpr(X)<=6 log(2X),
    |Dpr(X)|<=6log(2X)+3log(4X)<=9log(4X).            (15)

Доказательство: L_X(p,p)<=X, L_(2X)(p,p)<=2X,

    sum_(p<=M)(log p)^2<=log(M)*vartheta(M)<3M log M.

Подстановка в обе части (10) даёт (15). Dpr как разность диагоналей может иметь любой знак; для верхнего bound отрицательная часть благоприятна.

## 6. Независимая арифметическая попытка и точная остановка

[COFINAL_FAMILY | PAPER для доказанных границ; требуемая новая оценка CONDITIONAL.]

Достаточная source-строка теперь имеет вид

    для каждого eta>0 существуют C_eta,X_eta:
    Cpr(X)<=C_eta X^eta*(sqrt(P(2X))+1)
    для каждого dyadic X>=X_eta.                     (K*)

Это **односторонняя** совместная оценка. Большая отрицательная Cpr допустима и полезна. (K*) НЕ ДОКАЗАНО.

Проверенная независимая модульная оплата (13) даёт только

    |Cpr(X)|<=90X.                                   (16)

Для парной части: |Pi|<=L_X+L_(2X)/8, L_X<=X, L_(2X)<=2X, поэтому её абсолютная цена не больше

    X^(-2)[X*vartheta(2X)^2+(X/4)*vartheta(4X)^2]<=72X.

Для линейной части (11) даёт R_X<=3X^2/4, R_(2X)<=3X^2. С сохранением областей p<=2X и p<=4X её цена не больше 18X. Это доказывает (16) без обращения к неизвестной P(X). Цена слишком велика для (K*).

Качественная PNT улучшает только до Cpr(X)=o(X): по (6) левая разность в (14) есть o(X), а (15) логарифмична. Никакого фиксированного выигрыша степени это не даёт.

Точное U1-сокращение J уже учтено в возврате к настоящей psi/Lambda. Второе тождество J, с весом log m, возвращает именно этот prime source, а не bound для (13). Периодическая дисперсия F не применяется к (13): здесь фиксированное начало и другая область усреднения. Диагональный Cauchy-поставщик I не возвращается под новым именем. Разложение (14) также не делает (K*) легче автоматически: Cpr равна разности полных энергий минус оплаченные части. Нужен независимый аргумент на настоящих парах простых. Его в этой попытке нет.

## 7. Что замкнулось условно — и что не доказано

[COFINAL_FAMILY | PAPER для импликации, CONDITIONAL для (K*).]

Из (14),(15),(K*) после поглощения log X в X^eta следует

    P(2^j)<=(1/2)P(2^(j+1))
       +C'_eta 2^(eta*j)*(sqrt(P(2^(j+1)))+1).

По (6) и лемме §4, P(2^j)=O_delta(2^(delta*j)) для каждого delta>0. По (4) та же субполиномиальность верна для исходной E_j из J. Его Mellin-приёмник тогда исключает все правые нули; функциональное уравнение исключает левые.

Для контроля источника: J задаёт Tstep(x)=T_floor(x) при x>=8, ноль ниже, и в Re s>1

    integral_1^infinity Tstep(x)x^(-s-1)dx
      =-[(1-2^(-s))/s]*zeta'(s)/zeta(s)
        -1/[2(s-1)]-R(s),

где R голоморфна при Re s>1/2. Субполиномиальность E_j обеспечивает сходимость **исходного** интеграла при Re s>1/2: сумма dyadic оценок sqrt(E_j)*2^((1/2-Re s)j) сходится локально равномерно. Нуль rho кратности m оставил бы вычет

    -m*(1-2^(-rho))/rho !=0,   Re rho>1/2.

Поэтому он невозможен при (K*). Аналитическое продолжение без доказанной сходимости интеграла здесь не подменяет оценку энергии.

Обратно, RH даёт P(X)=O_eta(X^eta) для каждого eta>0. По (14),(15), Cpr(X)<=P(X)+|Dpr(X)|, поэтому (K*) выполняется. Таким образом полный новый supplier снова RH-эквивалентен. **Ослаблен технический порог коэффициента, а не доказана новая zero-free область.**

## 8. Сильнейшая атака, Pappus и границы переноса

[ABSTRACT | PAPER для логических проверок.]

Качественной PNT недостаточно даже для похожей скалярной ошибки. Пусть D_beta(x)=x^beta с 1/2<beta<1. Тогда D_beta=o(x), но его dyadic-ошибка (1-2^(-beta))x^beta имеет энергию c_beta X^(2beta-1), c_beta>0. Её критическая разность равна

    c_beta*(1-2^(2beta-2))*X^(2beta-1)>0.

При 0<eta<beta-1/2 она превосходит любой постоянный множитель X^eta*(X^(beta-1/2)+1). Это судья недостаточности PNT и абстрактной квадратичной геометрии, **не подмена настоящей psi** и не опровержение (K*).

Цепочка Паппа в этой попытке:

    RH <- исходный Mellin-приёмник J
       <- субполиномиальность P(X) по (4)
       <- критическая рекурсия + доказанная PNT-граница
       <- (K*) + оплаченные диагональ и целочисленный фон.

Работа над последней стрелкой дала (13),(15),(16), но не (K*). Цены: смена I/J-нормы — O(log X); собственные степени — постоянная 21 в норме; lattice correction — O(1/X); диагональ — O(log X); совместный prime-pair supplier — только O(X), затем качественное o(X), **без выигрыша показателя**.

**Источниковые контроли.** Для DMV единичная counting-решётка, обычные prime powers и пересечения [n,2n] не являются автоматически его собственным Mellin-источником. DH не имеет ordinary-Lambda source с нашим reciprocal mu и стандартным Gamma-factor. При добавлении квартета Q к completion прежние prime coefficients описывают zeta, но не дополнительные нули Q; нельзя отбросить Q'/Q. При изменении самого uncompleted источника старые mu/Lambda уже неверны. Контрмассив R9 не сохраняет source-convolution, переводящую его коэффициенты в настоящую Lambda. Унаследованный положительный контроль кривой над F3 использует собственную периодизационную форму; ordinary-prime kernel (13) ему не навязывается. Универсальная Hilbert-лемма §4 намеренно не различает эти миры; различать должен отсутствующий arithmetic supplier (K*). Новый всеобщий сертификат RH не заявляется.

**Два оставшихся представления.** A: точная взвешенная сумма пар простых (13), совместно с линейным членом, без модулей; различающая сила высокая, аналитическая стоимость высокая. B: исходный оптимальный NB-захват с движущимися коэффициентами и его собственным finite-to-global receiver, без обязательной малости фиксированного taper; различающая сила высокая, стоимость очень высокая. Ни одно не является выполненным доказательством. Последовательные новые названия одного остатка не считаются арифметическим прогрессом.

K8A: DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=source-correct small energy or another proved receiver; PARTICULAR_CRITICAL_FEEDBACK_IS=NOT_NECESSARY as a method; FAILURE_TYPE=NO_DERIVATION for (K*); EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=critical-half terminal repair and exact paid lattice/prime-power return, not historical priority of PNT or overlap Grams; REOPEN_TRIGGER=independent joint upper bound for (13), not a larger diagnostic grid.

## 9. Проверки и closeout

[FINITE_CELL | PAPER для точной алгебры; бесконечные кванторы доказываются выше, не тестами.]

После freeze на X=8,16,32,64 проверены точные рациональные коэффициенты полиномов по log простых: step-energy против overlap Gram, critical-scale difference, parity formula для Lambda и prime-only source. Проверены 43760 пар концов и 480 рациональных точек единичных ячеек. Дополнительно точно проверены (11),(12), pure-prime expansion (13)–(14), девять рациональных шагов скалярной рекурсии и судья kappa=3/4. Ни таблицы нулей, ни floating-point source estimates не использовались.

P1 HIT: критический коэффициент разрешён с PNT-terminal condition. P2 HIT: вместо предполагаемого O(1) получено точное (7) и O(1/X). P3 HIT: (10)–(15). P4: целевой source-bound NOT_PROVED; (16) недостаточно. P5 HIT: степенной аналитический судья §8. Prime-only цена 21 и закрытая row-sum формула получены после исходного freeze; им не приписывается задним числом отдельный успешный прогноз. Дополнительные конечные row-sum проверки зарегистрированы до своего запуска.

Ниже компактный воспроизводимый точный судья. Ключ 0 в линейной форме обозначает константу 1; ключ p обозначает log p. Ключ (p,q) — их произведение. Нулевой формальный коэффициентный словарь служит точным discriminator, а не близость decimal к нулю.

```python
from collections import defaultdict
from fractions import Fraction as F

def add(a, b, scale=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + scale*v
        if out[k] == 0:
            del out[k]
    return out

def mul(a, b):
    out = defaultdict(int)
    for p, u in a.items():
        for q, v in b.items():
            out[tuple(sorted((p, q)))] += u*v
    return {k: v for k, v in out.items() if v}

def linear(a):
    return {(0, p): v for p, v in a.items() if v}

def source(M, prime_only=False):
    spf = list(range(M+1))
    for p in range(2, int(M**0.5)+1):
        if spf[p] == p:
            for n in range(p*p, M+1, p):
                if spf[n] == n:
                    spf[n] = p
    out = [{}] + [{0: -1} for _ in range(M)]
    for n in range(2, M+1):
        p, r = spf[n], n
        while r % p == 0:
            r //= p
        if r == 1 and (not prime_only or n == p):
            out[n][p] = 1
    return out

def overlap(X, n, m):
    return max(0, min(2*X, 2*n, 2*m) - max(X, n, m))

def step(a, X, continuous=False):
    out = {}
    for n in range(X, 2*X):
        v = {}
        for k in range(n//2+1, n+1):
            v = add(v, a[k])
        out = add(out, mul(v, v))
        if continuous:
            out = add(out, linear(v), F(n % 2)-F(1, 2))
            out = add(out, {(0, 0): F(1, 12)})
    return out

def pair(a, X):
    out = {}
    for n in range(1, 2*X+1):
        for m in range(n, 2*X+1):
            w = overlap(X, n, m)*(1 if n == m else 2)
            if w:
                out = add(out, mul(a[n], a[m]), w)
    return out

for X in (8, 16, 32, 64):
    for prime_only in (False, True):
        a = source(4*X, prime_only)
        for scale in (X, 2*X):
            assert step(a, scale) == pair(a, scale)
        correction = add(step(a, X, True), step(a, X), -1)
        mass = {}
        for n in range(X+1, 2*X+1):
            mass = add(mass, add(a[n], {0: 1}))
        if not prime_only:
            mass = add(mass, {2: 1}, -1)
        expected = {k: F(v, 2) for k, v in linear(mass).items()}
        expected = add(expected, {(0, 0): -F(X, 6)})
        assert correction == expected
    for scale in (X, 2*X):
        total = 0
        for n in range(1, 4*X+1):
            left, right = max(scale, n), min(2*scale, 2*n)
            expected = right*right//4-left*left//4 if right > left else 0
            row = sum(overlap(scale, n, m) for m in range(1, 4*X+1))
            assert row == expected
            total += row
        assert F(total) == F(7*scale**3, 12)+F(scale, 6)
    a = source(4*X, True)
    primes = [p for p in range(2, 4*X+1) if a[p].get(p) == 1]
    flux = add({k: 8*v for k, v in step(a, X).items()}, step(a, 2*X), -1)
    rhs = {(0, 0): X}
    for p in primes:
        diag = 8*overlap(X, p, p)-overlap(2*X, p, p)
        rhs = add(rhs, {(p, p): 1}, diag)
        row = sum(8*overlap(X, p, n)-overlap(2*X, p, n)
                  for n in range(1, 4*X+1))
        rhs = add(rhs, {(0, p): 1}, -2*row)
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            w = 8*overlap(X, p, q)-overlap(2*X, p, q)
            rhs = add(rhs, {(p, q): 1}, 2*w)
    assert flux == rhs
    print('X =', X, ': exact identities verified')
```

```yaml
iteration:
  target: INDEPENDENT_SIGNED_ENERGY_CONTRACTION
  status: OPEN
  cognitive_operator_used: CRITICAL_SCALE_TELESCOPING_AND_INTEGER_CENTERED_PAIR_ENERGY
  new_gap_name: ONE_SIDED_PRIME_PAIR_FLUX_WITH_EXACT_LINEAR_COMPENSATION
  invariant_learned: PNT_PAYS_THE_CRITICAL_TERMINAL_BUT_NOT_THE_ARITHMETIC_FLUX
  forbidden_future_move: TREAT_PAID_DIAGONAL_OR_U1_ZERO_CHANNEL_AS_FULL_ENERGY_GAIN
  next_decisive_test: INDEPENDENT_SIGNED_ESTIMATE_OF_CPR_NOT_ITS_RENAMING_AS_ENERGY_DIFFERENCE
  route_score: 2
```

Записаны только новый freeze и этот verdict под `docs/routeB_bus/proshka/`; чужие файлы, предыдущие verdicts и state не изменены. Freeze commit/blob указаны в YAML. Финальный commit/blob и SHA-256 локальной копии передаются после удалённого чтения, поскольку файл не может содержать собственный commit SHA. PAPER, без Lean, Arb и независимого аналитического аудита. **Новый arithmetic supplier отсутствует; безусловная цепочка до RH остаётся незамкнутой.**
