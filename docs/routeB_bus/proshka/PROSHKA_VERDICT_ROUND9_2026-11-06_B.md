# STATUS: KILL_ROUND9_ENDPOINT_MOMENT_CORE_CONTROL_B

```yaml
STATUS: KILL_ROUND9_ENDPOINT_MOMENT_CORE_CONTROL_B
OPERATIVE_CLASS: KILL_ROUND9_ENDPOINT_MOMENT_CORE_CONTROL_B
DATE: 2026-11-06
ANSWER: C_FOR_PREDECLARED_MOMENT_ONLY_METHOD_CLASS
ORIGINAL_TRUE_MOBIUS_CORE_BOUND: NOT_PROVED_AND_NOT_REFUTED
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_COMMIT: 9d8a6d48a0efdeaea7987748d242a3844e91a6dc
REQUEST_BLOB: 2227c094d0cf36b7aa19b71f1eee68e80d1a330e
INPUT_R8_COMMIT: 70c4e6b097bc714689fb9226aeaea12a46127c95
INPUT_R8_BLOB: e0c22e09de31ce8c3ee37e8c53343477168b2063
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: a0f1bf806c576a241ef03936c5b793fee2a5064b
SPEC_FREEZE_BLOB: 7018cceed5a0fcdca3054dbb0e15a95c69ec57ca
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_ROUND9_CORE_ON_S_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND9_2026-11-06_B.md
PROVED_STEPS:
  - {id: TRUE_TAPER_EXACT_SQUARE_PLUS_IMPULSE_ENERGY_IDENTITY, scope: ABSTRACT, verifier: PAPER}
  - {id: FOUR_MOMENT_NULL_SQUAREFREE_INTEGER_BLOCK, scope: FINITE_CELL, verifier: PAPER}
  - {id: SHARP_ENVELOPE_AND_EXACT_FUTURE_SCALAR_TRAJECTORIES_PRESERVED, scope: FINITE_CELL, verifier: PAPER}
  - {id: SAME_S_POINTWISE_CONVERGENT_TRIANGULAR_COUNTEREXAMPLE_WITH_DIVERGENT_CORE, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: RELAXED_CORE_SCALE_THETA_N_OVER_LOG_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EVERY_FIXED_FINITE_ENDPOINT_JET_HAS_THE_SAME_OBSTRUCTION, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: FULL_PAST_MEAN_TRAJECTORY_RECOVERS_FIXED_COEFFICIENTS, scope: ABSTRACT, verifier: PAPER}
RH_GAP: BOUNDED_ACTUAL_MOBIUS_CORE_ON_AN_UNBOUNDED_SUBSET_OF_S
MINIMAL_MISSING_IDENTITY: "Exists B<infinity such that {N>=3: b_N*b_(N+1)<=0 and H_N<=B} is unbounded, for the unmodified mu(n)(1-log(n)/log(N))."
PROGRESS_CLASS: FALSIFICATION_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: MOMENT_ONLY_UNIFORM_CORE_BOUND_ON_S
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_ARITHMETIC_COUNTERARRAY_AND_STRICT_NEGATIVE_UPPER_ENVELOPE
    EVIDENCE: SECTIONS_3_4_EQUATIONS_18_21
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
DOES_NOT_KILL: [RH, ACTUAL_R8_CONDITION_26, OPTIMAL_NB_COEFFICIENTS, FULL_MOBIUS_CONVOLUTION_METHODS, CROSS_PREFIX_SOURCE_COHERENCE]
DISCRIMINATOR: "Exact divisor identity for every coefficient, not endpoint moments. At the first changed squarefree integer the divisor convolution fails. Full source matching and the exact Gamma factor remain mandatory."
REOPEN_TRIGGER: "A joint true-Mobius estimate using information not retained by the counterarray, or an error in its explicit moment and core bounds."
K8A:
  DOWNSTREAM_CONSUMER: RH_VIA_CENTERED_NB_CAPTURE
  ACTUAL_CONSUMER_REQUIREMENT: SOURCE_CORRECT_BOUNDED_POINTWISE_ZERO_RESIDUAL_SUBSEQUENCE
  ORIGINAL_REQUESTED_OBJECT: TRUE_R8_CORE_ON_S
  ORIGINAL_OBJECT_IS: UNKNOWN
  KNOWN_WEAKER_INTERFACES: OPTIMAL_NB_CAPTURE_OR_OTHER_SOURCE_CORRECT_CONVEX_AVERAGES
  FAILURE_TYPE: NO_DERIVATION_FOR_TRUE_CORE
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: SAME_SCALAR_SELECTION_AND_SQUAREFREE_ENVELOPE_WITH_SHARP_SCALE_DIVERGENT_INTEGER_RESIDUE_CORE
CLOSES: [SCALAR_SELECTION_PLUS_GENERIC_R8_BOUNDS_AS_A_SUFFICIENT_ARGUMENT]
OPENS: []
COGNITIVE_OPERATOR: SOURCE_MOMENT_NULLSPACE_AND_ENERGY_AUDIT
ROUTE_SCORE: 2
NUMERICAL_TESTS: SMALL_NORMALIZATION_DIAGNOSTICS_ONLY
EXACT_TESTS: RATIONAL_COEFFICIENTS_PRIME_EXPONENT_VECTORS_AND_CONSTANTS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **RH не доказана. Доказан узкий исход (в): из скалярного отбора S, модуля коэффициентов, квадратсвободного носителя, точности растущего начального блока и универсальных Gram/хвостовых оценок нельзя вывести ограниченность ядра.** Это не опровержение (26) для настоящей функции Мёбиуса.

Свидетель живёт в ТОМ ЖЕ словаре `(k mod n)/n`, а не в свободном пространстве рациональных частот. Для каждого достаточно большого N он сохраняет обе скалярные траектории b(X),s(X) при всех X>=N, сохраняет настоящие коэффициенты и строки до N/1024, удовлетворяет исходной границе |c_n|<=1 и имеет тот же квадратсвободный носитель. Тем не менее можно явно выбрать треугольную систему с

    H_N^bad >= N/[2,000,000,000 log^2 N] -> infinity

для КАЖДОГО N>=10^7, в том числе на настоящем бесконечном S. Её остатки при этом поточечно стремятся к нулю. Поэтому не помогает даже добавление поточечной сходимости к перечисленным данным.

Утрачены точные мёбиусовы значения, полная свёртка mu*1=epsilon и согласованность одного набора коэффициентов между всеми префиксами. Методы, использующие эти свойства количественно, теоремой не запрещены. Новый выигрыш по расположению нулей не заявляется.

## 1. Источники, объект и граница импортов

[FINITE_CELL | PAPER: сверка источников, не независимый аудит всех прежних результатов.]

Бриф и bootstrap получены через GitHub с совпавшими blobs. Локальный полный R8 содержит 50860 байт; его Git blob совпал с INPUT_R8_BLOB, SHA256 `28f666b27379087ee02e801f2780e21569dd7f49af39b293ba305e2477fd56f0`. Использованы R8 §§2–7,10: словарь, полная норма, хвост, множество S и прямой Mellin-судья. Freeze записан отдельно до проверок; не редактировался. При чтении указанной папки `docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/` на rh_clean получен 404. Новые данные этой папки не использованы.

**THEOREM, контекст, не поставщик нового знака:** Báez-Duarte, *A strengthening of the Nyman–Beurling criterion*, arXiv:math/0202141v2, Theorem 1.1, p.1. Страница 2 отдельно обсуждает Selberg taper и попытки отбора подпоследовательностей по нулям мёбиусовой суммы. Обе страницы прочитаны и проверены screenshot. Карточка v2 сообщает об исправлении трёх опечаток и добавлении ссылки. Целевой поиск correction/erratum не выявил дополнительного исправления используемой теоремы; это ограниченная проверка, не исчерпывающая библиография. Прямая достаточность bounded residual subsequence ниже доказана без импорта обратной NB-теоремы.

**CONDITIONAL, только граница:** Bettin–Conrey–Farmer, arXiv:1211.5191v1, результат при RH плюс reciprocal-derivative moment hypothesis. Карточка авторов проверена. Не применяется для оценки истинного H_N. Просмотренная статья Maier–Rassias arXiv:1806.05070 не импортируется как bound на H_N: перенос её оценок отдельных сумм в полный выбранный core не доказан. Для этой PDF screenshot нужной страницы вернул cache miss; визуальная проверка не заявляется. Интернет-тексты без проверенного вывода не используются как новые теоремы.

```text
https://arxiv.org/abs/math/0202141
https://arxiv.org/pdf/math/0202141v2
https://arxiv.org/abs/1211.5191
https://arxiv.org/pdf/1806.05070
```

Новая обструкция §§3–5 элементарна и не использует PNT, плотность знаков mu, RH, таблицы нулей или предположение о простоте нулей. Историческая новизна общего приёма зануления моментов не заявляется.

Положим, как в R8,

    ell=log N, w_k=1/[k(k+1)], r_n(k)=(k mod n)/n,
    R_N(k)=1+sum_(2<=n<=N) mu(n)(1-log n/ell)r_n(k),
    E_N=||R_N||_H^2, H=ell^2(k>=1,w_k),
    K_N=ceil(N^(3/2)), H_N=sum_(k<K_N)w_k R_N(k)^2,
    s(X)=sum_(n<=X)mu(n)(1-log n/log X)/n,
    b(X)=1+(1/2)sum_(2<=n<=X)mu(n)(1-log n/log X)(1-1/n),
    S={N>=3:b(N)b(N+1)<=0}.                           (1)

R8 доказывает безусловно: S неограниченно; |s(N)|<=5/ell; на S |b(N)|<=1/(2ell) и E_N<=H_N+6/ell^2. Всякий будущий вывод об исходном кандидате обязан сохранить именно mu, а не лишь |mu|<=1.

## 2. Попытка непосредственно оценить настоящий core

### 2.1. Положительный квадрат и точный подписанный остаток

[ABSTRACT / FINITE_CELL | PAPER.]

Для t>0 зададим в настоящем H

    Y(t)=t*v+sum_(n>=2)mu(n)(t-log n)_+ r_n,
    v(k)=1,
    V(t)=v+sum_(log n<t)mu(n)r_n.                     (2)

На каждом компактном t-интервале суммы конечны. Y непрерывна и кусочно аффинна; Y(t)=t R_(exp t). В смысле распределений

    d^2/dt^2 ||Y(t)||^2
      =2||V(t)||^2 dt
       +2 sum_(n>=2)mu(n) Re<Y(log n),r_n> delta_(log n).
                                                               (3)

Отсюда ТОЧНО, поскольку Y(0)=0 и производная нормы в 0 равна нулю,

    ||Y(T)||^2 = P(T)+J(T),
    P(T)=2 int_0^T (T-t)||V(t)||^2 dt >=0,
    J(T)=2 sum_(2<=n<=exp T)(T-log n)
                     mu(n) Re<Y(log n),r_n>.          (4)

Те же равенства верны с любой фиксированной конечной суммой по строкам k<K; тогда все Gram-элементы рациональны. Это требуемые явно вычислимая часть, положительная часть и точный остаток. Но положительный квадрат находится в уравнении УСКОРЕНИЯ энергии, а не является верхней оценкой энергии.

Доказательство (3): между событиями Y'=V, Y''=0; в t=log n производная Y скачком меняется на mu(n)r_n, и производная ||Y||^2 — на указанный коэффициент. Уже при n=2 атом равен `-(log 2)^2<0`, поскольку <v,r_2>=(log 2)/2. Это опровергает автоматическую выпуклость, но НЕ является запретом eventual boundedness на S.

Отбор b=0 не зануляет внутренние произведения в J. Не получена нужная совместная оценка P+J на S. Раздельная оплата модулей снова даёт растущий бюджет; она не записывается как новый RH-результат. Ни (3), ни этот конечный отрицательный атом не являются доказательством невозможности (26).

### 2.2. Что именно измеряют два скаляра

Пусть V_N(z)=sum_(n<=N)mu(n)(1-log n/ell)n^(-z). Тогда

    s(N)=V_N(1), b(N)=1+[V_N(0)-V_N(1)]/2.            (5)

Итак, S контролирует комбинацию двух endpoint-значений Dirichlet-полинома. Чтобы проверить, достаточно ли этого совместно с остальными уже доказанными bounds, ниже сохраняются не приближённые значения (5), а обе целые будущие траектории b(X),s(X).

## 3. Арифметическая поправка, невидимая обоим скалярам

### 3.1. Четыре точных момента

[ABSTRACT / FINITE_CELL | PAPER.]

Определим конечный Dirichlet-полином

    Pi(z)=(1-2^(-z))(1-3^(-z))
                 (1-5^(1-z))(1-7^(1-z))/35
         =sum_(a|210) gamma_a a^(-z),
    gamma_a=mu(a)gcd(a,35)/35.                        (6)

Все gamma_a рациональны, |gamma_a|<=1. В 0 и 1 стоят двойные нули. Поэтому

    sum gamma_a = sum gamma_a log a = 0,
    sum gamma_a/a = sum gamma_a log a/a = 0.           (7)

Это не приближённое совпадение логарифмов. При раскрытии log a по четырём простым каждый коэффициент в (7) обращается в нуль рационально.

Для каждого N>=10^7 положим

    D=840 floor(N/430080), 430080=512*840.             (8)

Тогда D>=10080, N/1024<=D<=N/512. Среди d в [D,5D/4), взаимно простых с 210 и квадратсвободных, выберем тот знак eta in {+1,-1}, который встречается у mu(d) чаще; при равенстве выберем +1. Обозначим множество выбранных d через T_D.

**Явная оценка количества:** |T_D|>=D/100. Действительно, в интервале ровно 2D/35 чисел, взаимно простых с 210: D кратно 840. Неквадратсвободное такое число делится на p^2 для p>=11. Даже разрешив ВСЕ целые j>=11, их число не больше

    (D/4)sum_(j>=11)j^(-2)+sqrt(5D/4)
       <=D/40+sqrt(5D/4).

Значит квадратсвободных не меньше `9D/280-sqrt(5D/4)>=D/50` при D>=10080. Большинство одного из двух знаков даёт D/100. Не использованы ни асимптотика M(x), ни равномерное распределение его знаков.

Зададим beta на обычных целых:

    beta_(ad)=eta*gamma_a, a|210, d in T_D;
    beta_n=0 на остальных n.                         (9)

Представление n=ad единственно: d взаимно просто с 210, а a состоит только из его простых делителей. Носитель квадратсвободен и лежит в [D,525D/2), строго ниже N. Более того,

    beta_n=mu(n)gcd(a,35)/35 на n=ad.                 (10)

Из (6)–(7) для B_N(z)=sum beta_n n^(-z) следует

    B_N(z)=eta Pi(z)sum_(d in T_D)d^(-z),
    B_N(0)=B_N'(0)=B_N(1)=B_N'(1)=0.                 (11)

### 3.2. Сохраняются острые коэффициентные границы и все будущие скаляры

Рассмотрим два исходных ряда коэффициентов, каждый определён на всех натуральных:

    c_n^(0)=mu(n), c_n^(1)=mu(n)-2beta_n.             (12)

Вне конечного блока они совпадают. По (10) на блоке

    c_n^(1)=mu(n)[1-2gcd(a,35)/35],
    |c_n^(1)|<=1, c_n^(1)=0 если mu(n)=0.             (13)

Множитель в скобках не равен нулю, поэтому squarefree support совпадает точно, не только содержится в исходном. До D коэффициенты буквально равны mu.

Для любого X, включающего весь блок, изменение tapered Dirichlet-полинома равно

    -2[B_N(z)+B_N'(z)/log X].                        (14)

При z=0,1 оно нулевое. Следовательно

    s_(c^(1))(X)=s_mu(X), b_(c^(1))(X)=b_mu(X)
                          для всех X>=N,             (15)

на самом деле уже для X>=max supp beta. В частности сохраняются оба значения, определяющие членство N в S, а не только малость одного из них.

### 3.3. Невидимая в скалярах поправка даёт явное плато в строках

Пусть

    Delta_N(k)=sum beta_n(1-log n/ell)r_n(k).

Благодаря нулевому 1/n-моменту ТОЧНО

    Delta_N(k)=-sum beta_n(1-log n/ell)floor(k/n).

Отсюда

    Delta_N(k)=0 при k<D;
    Delta_N(k)=-eta A_N при 5D/4<=k<2D,
    A_N=(1/35)sum_(d in T_D)(1-log d/ell)>D/(700ell).
                                                               (16)

На последнем интервале присутствует только a=1 и каждый floor(k/d)=1. Все a>=2 имеют ad>=2D. Оценка A_N использует |T_D|>=D/100 и `log(N/d)>log(2048/5)>5`; последнее следует уже из e<3 и 3^5<2048/5.

Весь этот интервал входит в core k<K_N. Его масса равна

    W_I=sum_(k=5D/4)^(2D-1)1/[k(k+1)]=3/(10D).

Следовательно положительный квадрат поправки имеет строгую нижнюю оценку

    sum_(k in I)w_k Delta_N(k)^2
      >3D/[4,900,000 ell^2]
      >=3N/[5,017,600,000 ell^2]
      >N/[2,000,000,000 ell^2].                       (17)

Это PAPER-неравенство для каждого N>=10^7, не результат сетки. Большой знаменатель сознательно выбран с запасом.

## 4. Теорема-препятствие: тот же S, но core расходится на всём S

[COFINAL_FAMILY | PAPER.]

Рассмотрим класс ПОКЛЕТОЧНЫХ выводов, в которых действительные tapered коэффициенты характеризуются только следующими данными:

- |c_n|<=1, тот же squarefree support; c_n=mu(n) до D_N из (8);
- равенство b_c(X)=b_mu(X), s_c(X)=s_mu(X) при всех X>=N, с обычным продолжением c_n=mu(n) вне изменённого префикса;
- точный integer-residue словарь, его PSD/Jordan/CRT identities и универсальная хвостовая оценка R8;
- поточечный нулевой предел остатка по N.

Не включены полная свёртка c*1=epsilon, точные значения c_n=mu(n) на остальных индексах и согласованность ОДНОГО ряда c_n между всеми N. Это формальная область запрета, а не утверждение о всяком мыслимом методе.

**Теорема.** Существует явно определённая треугольная система в этом классе с

    H_N^bad > N/[2,000,000,000 log^2 N]
                              для всех N>=10^7.      (18)

Поэтому она не имеет ограниченного core ни на одной неограниченной подсемье настоящего S.

**Построение, включая выбор знака.** На I из (16) два остатка равны R_N и R_N+2eta A_N. Пусть

    m_I=(1/W_I)sum_(k in I)w_k R_N(k).

Если eta*m_I+A_N>=0, выбираем c^(1); иначе выбираем c^(0). В первом случае абсолютное среднее выбранного остатка >=A_N; во втором случае уже |m_I|>A_N. Cauchy–Schwarz на конечном I и (17) дают (18).

Выбор конечен и точен: после умножения на положительные рациональные знаменатели и ell знак eta*m_I+A_N является знаком линейной формы в логарифмах натуральных чисел с целыми коэффициентами. Это сравнение двух целых произведений. В пограничном случае равенства выбирается c^(1); вывод сохраняется. Нули zeta и знак A_m не читаются. Алгоритм не назван практически быстрым.

Все остальные требования класса проверены выше. Для любого фиксированного k при достаточно большом N выполнено k<D_N, поэтому R_N^bad(k)=R_N(k)->0 по R8 (18)–(19). Скалярная последовательность bad-модели на целых совпадает с исходной, следовательно её множество переходов — ровно S. Нельзя спасать утверждение удалением неудобных N из S: (18) верно на каждом позднем N.

Эквивалентный положительный двухканальный Gram и его точный остаток:

    H_N(c^(1))=H_N(mu)+4||Delta_N||_core^2
                         -4<R_N,Delta_N>_core.       (19)

Все величины конечны. Квадрат неотрицателен; смешанный член не отброшен. Выбор по среднему на I — точный способ обеспечить нижний свидетель, а не предположение о знаке этого смешанного члена.

### 4.1. Масштаб препятствия совпадает с масштабом грубой оценки

Для всего описанного класса также

    H_N(c)<=1025 N/ell^2.                             (20)

При k<D истинная head-идентичность и |s_N|<=5/ell, psi(k)<=12k дают |R(k)|<=17k/ell. Её вклад меньше 289D/ell^2. Для остальных k модульная taper-граница даёт |R(k)|<N/ell; сумма весов k>=D равна 1/D. Получаем `289D/ell^2+N^2/(D ell^2)<=1025N/ell^2` по (8). Оценка psi<=12x — прежняя элементарная Chebyshev-граница R8/R6C, не RH-остаток.

Итак, порядок N/log^2N нельзя убрать лишь использованием скаляров и перечисленных generic-ограничений. Константа (18) не оптимизировалась; степень N доказательно существенна в этом классе.

**Строгая отрицательная верхняя огибающая kill.** Для любого B<infinity на всех достаточно больших N in S:

    B-H_N^bad <= B-N/[2,000,000,000 log^2N] <0.       (21)

Это опровергает uniform inference «из данных класса следует bounded core на неограниченной части S». Неоплаченная верхняя оценка не выдается за контрпример. KILL_SCOPE=THEOREM_SHAPE, не ROUTE_FAMILY и не запрет истинной (26).

## 5. Добавление конечного числа endpoint-моментов не ремонтирует метод

[ABSTRACT / COFINAL_FAMILY | PAPER.]

Зафиксируем J>=0. Возьмём 2r различных простых, r=J+2, разделим их на группы p_1,...,p_r и q_1,...,q_r, положим

    A=product p_i q_i, B=product q_i,
    Pi_r(z)=B^(-1)product_i(1-p_i^(-z))
                       product_i(1-q_i^(1-z)).       (22)

Коэффициент при a^(-z), a|A, равен `mu(a)gcd(a,B)/B`; его модуль <=1. Нули Pi_r при 0,1 имеют порядок r. После taper, как в (14), сохраняются все производные порядков 0,...,J в ОБОИХ endpoint. Это более сильные данные, чем (5).

Повторим блоковое построение с squarefree d, взаимно простыми с A, в [D,5D/4), выбрав большинство одного знака mu(d). Для фиксированного A элементарное включение-исключение даёт, при достаточно большом явном D,

    number of such squarefree d >= phi(A)D/(24A),
    majority count >= phi(A)D/(48A).                 (23)

Например, достаточно D>=100 и
`sqrt(D)>=48A(2^omega(A)+1)/phi(A)`. Доказательство: раскрыть mu^2(d)=sum_(l^2|d)mu(l). Подсчёт взаимно простых с A чисел на каждом интервале имеет ошибку <=2^omega(A). Главная сумма >=phi(A)D/(12A), поскольку `product_(p not dividing A)(1-p^-2)>1/3`; хвост и округления стоят не больше `2(2^omega(A)+1)sqrt(D)`. Это доказывает (23) с указанным запасом.

При `D=4 floor(N/(16A))`, для достаточно больших N, имеем N/(8A)<=D<=N/(4A), весь изменённый носитель ниже N, а на том же I только a=1 создаёт плато. Его высота не меньше `phi(A)D/[48AB log N]`, так как log(N/d)>1. Тот же выбор двух кандидатов даёт

    H_N^bad >= [phi(A)^2/(61440 A^3 B^2)]
                       * N/log^2N.                  (24)

Константа положительна и явно зависит только от фиксированного J и выбранных простых. Начальный точно сохранённый блок здесь имеет размер не меньше N/(8A); эта доля зависит от J и не обязана равняться 1/1024 из основной теоремы. Следовательно ни одно ФИКСИРОВАННОЕ конечное число endpoint-jet constraints, вместе с теми же generic-данными, не достаточно для bounded-core inference. Число ограничений, растущее с N, теоремой не покрыто.

## 6. Сильнейшая атака на результат: где точно перестаёт быть mu

[ABSTRACT / FINITE_CELL | PAPER.]

### 6.1. Полная история b действительно содержит арифметику

Для ОДНОГО фиксированного ряда c_n, c_1=1,

    B_c(t)=t b_c(exp t)
       =t+(1/2)sum_(n>=2)c_n(1-1/n)(t-log n)_+,
    B_c''=(1/2)sum_(n>=2)c_n(1-1/n)delta_(log n).      (25)

Поэтому равенство b_c=b_mu на ВСЁМ X>1 принудительно даёт c_n=mu(n) для всех n. Наш свидетель не сохраняет эту полную прошлую историю: сохраняется вся траектория только ПОСЛЕ включения конечного блока, а сам блок меняется с N. Это существенная граница, не техническая оговорка.

Значит неверно было бы заключить «никакая работа с b не может помочь» или «любая автономная динамика запрещена». Динамика, использующая все арифметические скачки (25), уже использует гораздо больше данных, чем значение b в точке перехода.

### 6.2. Первый нарушенный divisor-коэффициент указан явно

Для настоящего источника

    sum_(d|k)mu(d)=1_(k=1),
    sum_(d|k)mu(d)log d=-Lambda(k).                   (26)

У ненулевого изменённого ряда возьмём наименьший индекс n0 с beta_(n0)!=0. Все его собственные делители меньше n0 и неизменны. Поэтому

    sum_(d|n0)c_d^(1)=-2beta_(n0)!=0.                 (27)

Так теряется ПОЛНАЯ истинная head-идентичность при k>=D. Сохраняется только уже названный растущий префикс. На 16-точечном multiplicative cube a|210 настоящий вектор равен `mu(d)(mu(a))_a`; у свидетеля появляется дополнительный множитель `1-2gcd(a,35)/35`. Именно это место отличает настоящую арифметику от контрпримера.

В частности, свидетель не является другой настоящей функцией Мёбиуса, не строит контрпример RH и не опровергает bounded core исходного taper. Он опровергает замену точных связей (26) модульными bounds, несколькими моментами и PSD-геометрией. Оптимальный e_N вообще не изменяется: словарь остаётся тем же, изменён лишь выбранный плохой набор коэффициентов.

## 7. Что остаётся доказать для настоящего источника

[COFINAL_FAMILY | CONDITIONAL для исходной оценки; PAPER для следующих импликаций.]

Для неизменённой mu полный core по-прежнему равен

    H_N=(1/ell^2)sum_(k<=N)
              |psi(k)-k ell s_N|^2/[k(k+1)]
        +sum_(N<k<K_N)|R_N(k)|^2/[k(k+1)].            (28)

Оба блока неотрицательны. На S исчезает большая постоянная мода хвоста, но (28) не сводится к одному b_N. Доказательства ограниченности хотя бы на неограниченной части S не получено. Теорема §§3–5 показывает, какую информацию следующий supplier обязан действительно использовать, но сама не поставляет этот supplier.

**Точная достаточная цепь, без усиления посылки:** при истинной (26) R8 остатки на некоторой последовательности N_j in S ограничены по норме и поточечно стремятся к нулю. Они слабо сходятся к нулю. Выбираем подпоследовательность с `|<R_i,R_j>|<=2^(-i-j)`; тогда

    e_(N_J)<=||(1/J)sum_(j<=J)R_(N_j)||^2
                     <=(B+6)/J+1/J^2 ->0.           (29)

Для исходного словаря из целочисленного деления ТОЧНО

    int_0^1 (Jr_n)(x)x^(z-1)dx
                 =zeta(z)(1/n-n^(-z))/z,
    (Jr_n)(x)={1/(nx)}-(1/n){1/x}.                   (30)

В правом нуле rho=beta+i gamma остаточный Mellin-transform равен 1/rho. Норма этого evaluation functional на L2(0,1) равна (2beta-1)^(-1/2). Поэтому

    e_N >= (2beta-1)/|rho|^2>0                        (31)

для каждого такого нуля, независимо от N. Это противоречит (29); функциональное уравнение исключает и левые нули. Так (26) R8 => RH, но новая арифметическая посылка (26) здесь НЕ доказана. При необходимости прежний R7 finite bridge затем возвращает literal A_m; новый количественный floor для A_m в этой работе не получен.

## 8. Фейки и точный локальный множитель

[ABSTRACT / COFINAL_FAMILY | PAPER с inherited R8/R6 source-controls.]

Контрмодель коэффициентов §§3–4 и фальшивые zeta-миры — разные вещи. Первая остаётся обычным NB-словарём настоящей zeta. Для вторых должен сохраняться собственный полный источник.

**DMV/Берлинг.** Обычная разность r_n(k)-r_n(k-1)=1/n-1_(n|k) и интервалы [1/(k+1),1/k] дают в (30) именно обычную zeta, а не Beurling Z. Разрыв — additive Mellin source-match. Любой корректный L2-null-словарь, зануляющийся в собственном правом нуле DMV, имеет нижнюю оценку (31) с этим нулём. Поэтому source-correct bounded pointwise-zero subsequence не пройдёт. Отсутствующее completion DMV не выдумывается.

**DH.** Сохраняются его собственные коэффициенты, odd-Gamma, conductor 5 и отсутствие полюса. Подстановка D(z) вместо zeta(z) в (30) неверна уже как тождество правой полуплоскости. Корректный ремонт с null-evaluation в правом DH-нуле снова провалит (31). Обычная Lambda не подменяет его полную логарифмическую производную.

**Подсаженный квартет a=1/3.** При стандартной Gamma собственный uncompleted источник равен Q(z-1/2)zeta(z)/Q(1/2). Старый словарь не представляет этот множитель; Q'/Q нельзя удалить из формы Вейля. Для source-correct null-словаря planted rho=5/6+i gamma даёт положительный lower bound (31).

**Самодуальные v_b R6 B.** Арифметическая zeta может оставаться прежней, но Mellin local factor становится Q_b times Gaussian/Gamma. NB-вывод об обычной zeta ничего не утверждает о дополнительных нулях xi_b=Q_b xi. Здесь ломается exact-local-factor link, а не положительность нашего Gram. Для стандартной zeta используется именно

    M[exp(-pi x^2)](z)=(1/2)pi^(-z/2)Gamma(z/2),
    xi(z)=(1/2)z(z-1)pi^(-z/2)Gamma(z/2)zeta(z).

Положительность и самодуальность без этого точного множителя не заменяют данный шаг.

**Кривая над F3.** Для собственного источника с h=log3 имеем автономный положительный выход

    (Per f)(x)=sum_(j in Z)(-1)^j f(x+2hj), 0<=x<2h,
    W_E[f]=2h int_0^(2h)|Per f(x)|^2 dx
          =sum_(j in Z)|fhat((j+1/2)pi/h)|^2>=0.      (32)

Это Parseval на антипериодической ячейке, с конечным числом перекрытий для фиксированного компактного носителя. Буквальные оконные сжатия проходят с нулевым дефектом. Обычный mu-taper не навязывается кривой. Проверка положительного source-return сохранена; завершённый новый RH-сертификат для Q не объявляется.

## 9. Проверки, прогнозы и границы числа

[FINITE_CELL | PAPER для точной алгебры; плавающие проверки — только DIAG.]

Проверены рационально все 16 коэффициентов (6), два скалярных момента и восемь коэффициентов при log 2,log 3,log 5,log 7 в (7). Для D=12,40,84 построены блоки с 16,48,64 ненулевыми коэффициентами. На каждом точно проверены четыре момента, squarefree support, |mu-2beta|<=1 и шесть строк до блока и на плато. Логарифмические равенства проверялись как рациональные векторы показателей простых, не как decimal near-zero.

Дополнительная проверка нормировок при 60 и 90 десятичных знаках для X=N,N+1,2N, N=512D дала максимальные невязки <8.2e-62 и <1.9e-91 соответственно. Это не интервальные сертификаты. Для D=10080 точный подсчёт дал 555 допустимых квадратсвободных d: 264 знака + и 291 знака -. Аналитическая lower bound D/100 выполнена. Рационально проверено

    3/5,017,600,000 - 1/2,000,000,000
                         =307/3,136,000,000,000>0.

Не вычислялась cofinal сетка истинного H_N на S; не искались нули zeta. Доказательство (18) универсально по N и не зависит от удачных малых примеров.

Предсказания freeze: P1 — HIT, с точным (3)–(4); P2 — HIT, сохраняются целые будущие траектории; P3 — HIT, причём сохранена острая граница 1, а не только произвольная константа; P4 — HIT, первый дефект указан в (27); P5 — true-source bound NOT_PROVED, сдан только названный obstruction. Отрицательный результат не записан как доказательство отсутствия всех дальнейших методов.

## 10. K8A и следующий математический ход

**Для kill.** DOWNSTREAM_CONSUMER — bounded actual core, затем (29)–(31). ORIGINAL_REQUESTED_OBJECT — вывод из b,s и generic positivity/modulus/prefix data. ORIGINAL_OBJECT_IS=NOT_NECESSARY: это только предложенный способ контроля, не обязанность любого RH-доказательства. FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для theorem-shape §4 и его фиксированного finite-jet расширения §5. KILL_EVIDENCE_KIND — (18),(21), с полными исходными коэффициентами (6)–(16). REOPEN_TRIGGER — использование информации, НЕ сохранённой свидетелем, или конкретная ошибка в доказательстве.

**Для истинной (26).** FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT. Не доказаны ни boundedness истинного H_N на S, ни её отрицание. Следующая оценка должна удерживать полную мёбиусову свёртку, а не лишь её несколько моментов. Необходимость именно этого taper для RH остаётся UNKNOWN.

Две содержательно различные репрезентации дальнейшей задачи:

1. **Точный multiplicative-cube/source contrast.** Сохранить равенства mu(ad)=mu(a)mu(d) на coprime блоках и совместную аддитивную норму строк. Они различают свидетель (27). Kill-power высокий для moment-only доводов; цена настоящего upper bound высокая. Сама запись факторизации не является оценкой.
2. **Оптимальный rational upper-Gram R8, с проекцией на moment-null блоки.** Для настоящего кандидата направление Delta даёт точно U(theta)=U(0)-2theta g+theta^2 d, d>0; минимум U(0)-g^2/d. Это допустимый finite correction в том же NB-словаре, со всей оплаченной нормой. Kill-power конечного рационального/интервального теста высокий; цена cofinal суммы выигрышей неизвестна. Не утверждается, что такой алгоритм уже сходится.

Discriminator для почти нулевого момента — точный prime-exponent vector; для знака core — строгая interval-граница или (21). Дополнительная precision без разделяющего критерия не заменяет доказательства.

```yaml
iteration:
  target: TRUE_R8_CORE_BOUND_ON_S
  status: OPEN
  cognitive_operator_used: SOURCE_MOMENT_NULLSPACE_AND_ENERGY_AUDIT
  new_gap_name: TRUE_MOBIUS_CORRELATION_BEYOND_ENDPOINT_MOMENTS
  invariant_learned: EVEN_EXACT_FUTURE_b_s_AND_A_LINEAR_SIZE_TRUE_PREFIX_DO_NOT_CONTROL_THE_RELAXED_CORE
  forbidden_future_move: FINITE_ENDPOINT_MOMENTS_OR_GENERIC_PSD_BOUNDS_AS_A_SOURCE_CORE_ESTIMATE
  next_decisive_test: SOURCE_SPECIFIC_JOINT_MOBIUS_BOUND_OR_CERTIFIED_GAIN_FOR_THE_OPTIMAL_UPPER_GRAM
  route_score: 2
```

**Verification handoff.** Созданы только отдельный freeze и этот новый verdict по путям YAML. Старые вердикты и route-state не менялись. Final commit/blob/SHA256 сообщаются после записи и readback: самоссылочный hash внутри файла не имитируется. PAPER, без независимого аналитического аудита, Lean и Arb.

## Приложение. Минимальная воспроизводимая точная проверка

`D` — начало блока; для проверки количественного подсчёта возьми D=10080. Код использует только стандартную библиотеку Python; запуск: `python check_round9.py`. Он проверяет арифметические моменты и envelope, не RH. Для больших теоретических N не требуется вычислять весь core.

```python
from fractions import Fraction as F
from itertools import product
from math import gcd, prod
from functools import lru_cache
from collections import defaultdict

@lru_cache(None)
def factors(n):
    ans = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans

def mu(n):
    f = factors(n)
    return 0 if any(v > 1 for v in f.values()) else (-1)**len(f)

def log_vector(terms):
    out = defaultdict(F)
    for n, c in terms:
        for p, e in factors(n).items():
            out[p] += c*e
    return {p: c for p, c in out.items() if c}

gamma = {}
for flags in product((0, 1), repeat=4):
    a = prod(p for p, f in zip((2, 3, 5, 7), flags) if f)
    gamma[a] = F(mu(a)*gcd(a, 35), 35)

D = 10080
if D % 840 or D < 10080:
    raise ValueError('Use a multiple of 840, at least 10080')
groups = {s: [d for d in range(D, 5*D//4)
              if gcd(d, 210) == 1 and mu(d) == s] for s in (1, -1)}
eta = 1 if len(groups[1]) >= len(groups[-1]) else -1
ds = groups[eta]
beta = {}
for d in ds:
    for a, c in gamma.items():
        assert a*d not in beta
        beta[a*d] = eta*c
for n, c in beta.items():
    assert mu(n) != 0 and abs(mu(n)-2*c) <= 1
for sigma in (0, 1):
    assert sum((c/F(n)**sigma for n, c in beta.items()), F()) == 0
    assert not log_vector((n, c/F(n)**sigma) for n, c in beta.items())
assert len(ds) >= F(D, 100)
assert F(3, 4_900_000*1024) > F(1, 2_000_000_000)
print('PASS exact finite identities; not an RH certificate')
print('D =', D, 'majority sign =', eta, 'count =', len(ds))
```

Последняя логическая строка: **истинная (26) R8 => RH; истинная (26) остаётся недоказанной. Моментная релаксация (26) опровергнута явным арифметическим свидетелем.**
