# STATUS: TRY_ROUND8_RATIONAL_ADDITIVE_GRAM_B

```yaml
STATUS: TRY_ROUND8_RATIONAL_ADDITIVE_GRAM_B
OPERATIVE_CLASS: TRY_ROUND8_RATIONAL_ADDITIVE_GRAM_B
DATE: 2026-11-06
ANSWER: PARTIAL_NEW_FINITE_CERTIFICATE_WITH_PAID_INFINITE_REMAINDER
FULL_REQUEST_ACCEPTANCE: NOT_COMPLETE
REQUEST_COMMIT: 2f75fac798d71500c9445dbeb6a8ee6e99b43f15
REQUEST_BLOB: 3f99134611845b12dfcfada03439e0cba1222bde
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: 6d50c6f9e40f5eb91fa24037adb872f8a0bf2593
SPEC_FREEZE_BLOB: 9bf7acf8e4576919d3c6b02a85138d9d0d688753
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_ROUND8_NEW_MATH_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROVED_STEPS:
  - {id: EXACT_ADDITIVE_FREQUENCY_AND_JORDAN_GRAM, scope: FINITE_CELL, verifier: PAPER}
  - {id: ALL_COEFFICIENT_RATIONAL_UPPER_GRAM_FOR_FULL_NB_NORM, scope: FINITE_CELL, verifier: PAPER}
  - {id: SELBERG_FINITE_CORE_REMAINDER_AT_MOST_5_OVER_LOG_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: ELEMENTARY_POLE_COEFFICIENT_BOUND_5_OVER_LOG, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: UNCONDITIONAL_INFINITE_MEAN_SIGN_CROSSING_SET, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: BOUNDED_SELECTED_CORE_IMPLIES_CAPTURE, scope: COFINAL_FAMILY, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: OPTIMAL_LEADING_CONSTANT_OF_RATIONAL_CERTIFICATE, scope: COFINAL_FAMILY, verifier: CONDITIONAL, premises: RH_PLUS_BCF_H_MINUS_1}
RH_GAP: "No unconditional bound on the finite arithmetic core along an unbounded subset of the proved sign-crossing set; no unconditional convergence of the rational Schur certificates."
MINIMAL_MISSING_IDENTITY: "Exists B<infinity such that {N>=3: b_N*b_(N+1)<=0 and H_N<=B} is unbounded; notation in sections 5-7. This is sufficient, not asserted necessary."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: FINITE_POSITIVE_CERTIFICATE_AND_UNIFORM_INFINITE_TAIL_NOT_GLOBAL_RH_SIGN
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: LITTLE_O_N_SQUARED_UNIVERSAL_RATIONAL_FREQUENCY_DISCREPANCY
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_TWO_FREQUENCY_STRICT_NEGATIVE_UPPER_ENVELOPE
    EVIDENCE: SECTION_9_EQUATION_31
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
DOES_NOT_KILL: [RH, SPECIAL_MOBIUS_CANCELLATION, OPTIMAL_NB_COEFFICIENTS, OTHER_SOURCE_SPECIFIC_BRIDGES]
DISCRIMINATOR: "Exact Mellin source matching and the positive evaluation obstruction (2 beta-1)/|rho|^2; exact Gamma factor required at completion. Finite near-zero diagnostics are not zero certificates."
REOPEN_TRIGGER: "A source-derived bound on the selected finite core, or a proved decay of the explicitly rational upper Schur complement."
K8A:
  DOWNSTREAM_CONSUMER: RH_AND_LITERAL_CCM_FLOOR
  ACTUAL_CONSUMER_REQUIREMENT: CENTERED_NB_CAPTURE_OR_AN_INDEPENDENT_LITERAL_SOURCE_LOWER_BOUND
  ORIGINAL_REQUESTED_OBJECT: NEW_COMPUTABLE_POSITIVE_STRUCTURE_WITH_CONTROLLED_RESIDUAL
  ORIGINAL_OBJECT_IS: UNKNOWN
  KNOWN_WEAKER_INTERFACES: OTHER_TRIANGULAR_NB_APPROXIMANTS_OR_GAUSSIAN_SIGNED_RECEIVER
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: EXPLICIT_RATIONAL_FULL_NORM_UPPER_GRAM_AND_SOURCE_SELECTED_FINITE_CORE
CLOSES: [FULL_INFINITE_TAIL_AT_LOG_SQUARED_SCALE, FINITE_RATIONAL_NB_UPPER_CERTIFICATE, EXISTENCE_OF_MEAN_SMALL_PREFIXES]
OPENS: []
COGNITIVE_OPERATOR: ADDITIVE_SPECTRAL_DECOMPOSITION
ROUTE_SCORE: 3
NUMERICAL_TESTS: DIAGNOSTICS_ONLY
SYMBOLIC_TESTS: EXACT_RATIONAL_COVARIANCES_AND_FINITE_SCHUR_COMPLEMENTS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE
```

Ы. **RH не доказана.** Новый объект — конечная **рациональная положительная матрица**, которая мажорирует ПОЛНУЮ бесконечную NB-норму для любых коэффициентов. Её минимум даёт настоящий конечный верхний сертификат, а не усечённую норму с забытым хвостом.

Для конкретного логарифмического мёбиусова кандидата бесконечность после `ceil(N^(3/2))` оплачена с точной ошибкой не больше `5/log^2 N`, после выделения вычислимой постоянной моды. При RH и точно названной дополнительной гипотезе сертификат имеет оптимальную ведущую константу `2+gamma_E-log(4*pi)`. Безусловная малость конечного арифметического блока не доказана. Поэтому требование §4 брифа о полной нужной оценке остатка не объявляется выполненным: оплачен дальний остаток, не весь RH-трудный блок.

## 1. Источники, freeze и границы импортов

[FINITE_CELL | PAPER: source lock; наследование не означает независимого аудита старых доказательств.]

Бриф и протокол прочитаны через GitHub, blobs совпали. Freeze записан отдельным коммитом до построения и не изменён. Начальная ветка inbox была `8a994500ffc9648f2f3e22561ee74a9d0c2e9eca`. Короткие внутренние пути ниже имеют префикс `docs/routeB_bus/proshka/`.

| Ref | Путь, commit, blob | Использование |
|---|---|---|
| R6C | `PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_C.md`; `0005623ec3a2b476019899562b50c0854a602dfb`; `83004738a32926d80030b52bbae4655ee221dba0` | Остатки, изометрия, Mellin-равенство, source-match |
| L9 | `PROSHKA_VERDICT_ROUND6_LIMIT9_2026-11-06_C.md`; `c09713ede9913599b75e18d94ba36d41f10d5d24`; `5ccfaab6030cd9652aa5f061a2c33654afec4994` | L15-L20, точный head и старый срез N^3; гильбертово усреднение |
| R7B | `PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md`; `8a994500ffc9648f2f3e22561ee74a9d0c2e9eca`; `91cf942a527100c8a0b006377ff963adb23e7b6f` | Центрирование, d_N^2<=e_N, finite-window bound 36000 |
| R6B | `PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_B.md`; `888b808094dcc5d8d53686c466f79487ffb1e05f`; `33de3e38276671101b701d895509e81d09c0f2e5` | §7.2: точный Gaussian/Gamma; собственные self-dual plants; кривая |
| RG | `PROSHKA_VERDICT_PROVE_RH_2026-11-05.md`; `62f782316d2ba4f83d27db82d0b64e1e8361cad2`; `2b5e02a0aa816da34c204f2a56a9033e6ac6b542` | Только inherited source-return/Gaussian receiver, не новая оценка знака |

**T1 — THEOREM, large sieve.** Montgomery–Vaughan, *The large sieve*, Mathematika 20 (1973), 119–134, DOI `10.1112/S0025579300004708`. Точная используемая dual-форма проверена также в авторском тексте Montgomery–Vaughan, *Multiplicative Number Theory II*, Theorem 19.4, (19.7), pp.153–154: для частот, разделённых на окружности расстоянием не меньше delta, сумма квадрата на H последовательных целых не превосходит `(H-1+delta^(-1))*sum|coefficients|^2`. Ниже достаточно более слабого `H+delta^(-1)`. PDF-текст прочитан; screenshot соответствующей страницы вернул cache miss. Положительная нижняя оценка получается ниже из периодического дополнения, а не импортируется без доказательства.

**T2 — CONDITIONAL.** Bettin–Conrey–Farmer, *An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion*, arXiv:1211.5191v1, Theorem 1, p.2. При RH и

    H_-1: exists delta>0: sum_(|Im rho|<=T) 1/|zeta'(rho)|^2 << T^(3/2-delta)

ошибка конкретного `V_N(s)=sum_(n<=N) mu(n)(1-log n/log N)n^(-s)` асимптотически равна `C_zeta/log N`, где `C_zeta=2+gamma_E-log(4*pi)`. H_-1 влечёт простоту нулей; она не известна как следствие RH. Текст и screenshot теоремы проверены. Слово «мягкая» не заменяет гипотезу теоремой.

**T3 — THEOREM.** Burnol, arXiv:math/0103058v2, Theorem 1.3, printed p.4: нижняя граница расстояния с квадратами кратностей. Для discrete-подкласса это даёт `liminf d_N^2 log N >= sum m(rho)^2/|rho|^2` по критическим нулям. Screenshot страницы получен. В журнале: Adv. Math.170 (2002), 56–70. Карточка v2 сообщает о добавленных ссылках без математических изменений.

**T4 — THEOREM, только scope-аудит.** Bettin–Gonek, arXiv:1604.02740v1, Theorems 1–2, pp.1–2. Оценки длинных молифаеров дают zero-free области; для интеграла от 0 до T и длины T^theta в Theorem 1 граница `1/2+1/(2theta)`. Для [T,2T] в Theorem 2 константа другая. Это не доступная оценка нашего конечного core. Текст и screenshot проверены. Упомянутый там результат Conrey для theta<4/7 не переносится на произвольную длину.

Проверка исправлений: просмотрены карточки версий и целевые поиски по авторам/названию + erratum/correction. Отдельных исправлений, меняющих использованные T1–T4 формулы, в этом ограниченном поиске не найдено. Это не утверждение об исчерпывающем поиске литературы. Историческая новизна large sieve, NB-критерия, CRT, Schur complement или слабого гильбертова усреднения НЕ заявляется.

```text
T1 https://www.cambridge.org/core/journals/mathematika/article/abs/large-sieve/2B0269C6D6662EED351C6C06AA8D62ED
   https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf
T2 https://arxiv.org/pdf/1211.5191v1
T3 https://arxiv.org/pdf/math/0103058
T4 https://arxiv.org/pdf/1604.02740v1
```

## 2. Конечные частоты и положительный Jordan-Gram

[ABSTRACT / FINITE_CELL | PAPER.]

Пусть N>=3. Для произвольных комплексных коэффициентов c=(c_0,a_2,...,a_N) определим

    r_n(k)=(k mod n)/n,
    R_c(k)=c_0+sum_(n=2)^N a_n r_n(k),
    E(c)=sum_(k>=1) |R_c(k)|^2/[k(k+1)].                 (1)

Это квадраты норм, не сами нормы. Полный период Q=lcm(2,...,N); R_c(0)=c_0 в периодическом продолжении. Нулевая строка не входит в (1).

Средняя мода и её дополнение:

    b(c)=c_0+sum_(n=2)^N a_n(n-1)/(2n),
    q_c(k)=R_c(k)-b(c),
    nu(c)=(1/Q)sum_(k=0)^(Q-1)|q_c(k)|^2.              (2)

Для сокращённой частоты alpha=a/d, 2<=d<=N, (a,d)=1, положим

    B_d=sum_(j<=N/d) a_(dj)/(dj),
    A_(a/d)=-B_d/[1-exp(-2*pi*i*a/d)].

Точная конечная Fourier-формула для r_n даёт, ПОСЛЕ объединения совпадающих частот,

    q_c(k)=sum_(alpha in Omega_N) A_alpha exp(2*pi*i*k*alpha),
    nu(c)=sum_alpha |A_alpha|^2.                         (3)

Сохраняются все n, не только простые. Следующая запись одновременно вычислима и положительна:

    C_(n,m)=(gcd(n,m)^2-1)/(12*n*m),
    nu(c)=sum_(n,m=2)^N conjugate(a_n) C_(n,m) a_m
         =(1/12)sum_(d=2)^N J_2(d)|sum_(d|n<=N) a_n/n|^2,
    J_2(d)=d^2 product_(p|d)(1-p^(-2))>0.               (4)

**Доказательство covariance.** Пусть d=gcd(n,m). При равномерном k по общему периоду, условно на k mod d, оставшиеся остатки по n/d и m/d независимы по CRT. Условное среднее центрированного r_n равно `[k mod d-(d-1)/2]/n`. Дисперсия равномерного остатка 0,...,d-1 равна `(d^2-1)/12`. Это даёт C. Затем используем `gcd(n,m)^2=sum_(d|n,d|m)J_2(d)`; вычитание 1 удаляет d=1. Последняя сумма квадратов доказывает PSD для любых a. Более того, C положительно определена: если все внутренние суммы нулевые, обратный ход d=N,...,2 даёт все a_d=0. □

Это положительность reference-Gram, не формы Вейля. Автономность буквальная: входы — целочисленное деление, gcd и коэффициенты; ни psi-x, ни нули, ни A_m не читаются.

## 3. Полная бесконечность: точная матрица и явная оценка

[FINITE_CELL | PAPER; единственный неэлементарный вход здесь T1.]

Для K>=1 и частот alpha,beta, включая при необходимости 0, введём

    T_K(alpha,beta)=sum_(k>=K) exp(2*pi*i*k*(beta-alpha))/[k(k+1)].

Это PSD-матрица для любого конечного набора частот. Точно

    T_K(alpha,beta)=z^K int_0^1 x^(K-1)(1-x)/(1-x*z) dx,
    z=exp(2*pi*i*(beta-alpha)),  T_K(alpha,alpha)=1/K.   (5)

Положительность следует из исходной суммы Gram-строк, не из знака интегранда при complex z.

Различные рациональные частоты со знаменателями <=N имеют круговое расстояние >=1/N^2. Для любого интервала I из H последовательных целых T1 даёт

    sum_(k in I)|q_c(k)|^2 <= (H+N^2)nu.

Вложим I в интервал длины jQ. Полная энергия там jQ*nu; применим upper bound к оставшемуся последовательному дополнению. Получаем также lower bound и потому

    |sum_(k in I)(|q_c(k)|^2-nu)| <= N^2 nu.           (6)

Никакой усреднённый знак Мёбиуса здесь не использован.

Для линейного, а не квадратичного остатка геометрическая сумма и Cauchy–Schwarz дают

    |sum_(k in I)q_c(k)|
       <=sqrt(nu)*sqrt(sum_(alpha in Omega_N)csc^2(pi*alpha))
       <=N^(3/2)*sqrt(nu).                             (7)

Последний шаг следует из
`sum_(a=1)^(d-1)csc^2(pi*a/d)=(d^2-1)/3` и суммирования по d<=N; разрешение несокращённых дробей лишь увеличивает сумму.

Пусть `w_k=1/[k(k+1)]`. Abel-суммирование (6),(7), начиная с K, использует ровно `sum_(k>=K)(w_k-w_(k+1))=w_K`. Поэтому

    |sum_(k>=K) w_k |q_c(k)|^2 - nu/K| <= N^2 nu/[K(K+1)],
    |sum_(k>=K) w_k q_c(k)| <= N^(3/2)sqrt(nu)/[K(K+1)]. (8)

Определим конечный core

    H_(N,K)(c)=sum_(1<=k<K)|R_c(k)|^2/[k(k+1)].

Имеем ТОЧНО

    E(c)=H_(N,K)(c)+(|b|^2+nu)/K+D_(N,K)(c),            (9)
    |D_(N,K)(c)| <= [N^2 nu+2|b|N^(3/2)sqrt(nu)]/[K(K+1)].

Здесь D задан равенством, а не неизвестной O-константой. В частотных координатах его quadratic block имеет норму <=N^2/[K(K+1)], а строка связи с нулевой модой — <=N^(3/2)/[K(K+1)]. Именно отдельная оценка этой строки сохраняет нужный масштаб.

## 4. Новый объект: рациональный положительный верхний Gram

[FINITE_CELL | PAPER.]

Young-неравенство

    2|b|N^(3/2)sqrt(nu) <= N|b|^2+N^2nu

превращает (9) в **all-input** сертификат

    E(c) <= U_(N,K)(c),                                (10)
    U_(N,K)(c)=H_(N,K)(c)
       +[1/K+N/(K(K+1))]|b(c)|^2
       +[1/K+2N^2/(K(K+1))]nu(c).

Каждая часть положительна по построению. Более того,

    0<=U_(N,K)(c)-E(c)
       <=2[N|b|^2+2N^2nu]/[K(K+1)].                   (11)

**Явная матрица.** Пусть

    v_k=(1,r_2(k),...,r_N(k))^T,
    vbar=(1,1/4,2/6,...,(N-1)/(2N))^T,
    Ctilde=diag(0,C),
    alpha=1/K+N/[K(K+1)], beta=1/K+2N^2/[K(K+1)].

Тогда

    Gup_(N,K)=sum_(k=1)^(K-1) v_k v_k^T/[k(k+1)]
                         +alpha*vbar*vbar^T+beta*Ctilde. (12)

ВСЕ её элементы рациональны. Это конечная сумма конгруэнций положительных форм; PSD сохраняется для любого входа. Gup строго положительна по (4) и alpha>0. Для настоящего бесконечного Gram Ginf равенство (1) и (10) дают `Ginf <= Gup` в операторном порядке.

Зафиксируем `K_N=ceil(N^(3/2))` и новый рациональный сертификат

    ehat_N=min_(a_2,...,a_N) U_(N,K_N)(1,a_2,...,a_N).

При блочной записи Gup=[[a,b*],[b,B]] он равен точно

    ehat_N=a-b*B^(-1)b>0,      e_N<=ehat_N.             (13)

Это обычный Schur complement положительного РАЦИОНАЛЬНОГО finite input, не корень из неизвестной A_m. Его оптимальные коэффициенты также рациональны. Вычисление не требует интегрирования ζ, знания нулей или контроля psi-x. Размер конечного суммирования — K_N-1, а не полный период lcm(2,...,N).

Не доказана ни монотонность ehat_N, ни его безусловная сходимость. Один малый сертификат не закрывает бесконечный квантор. Новизна результата для проекта — не название Schur complement, а явная мажорирующая матрица (12) с доказанной полной хвостовой ценой (11).

## 5. Мёбиусов taper: оплаченный остаток 5/log^2 N

[COFINAL_FAMILY | PAPER, без RH и без cancellation mu.]

Теперь специализируем коэффициенты из неизменного freeze:

    ell=log N, a_n=mu(n)(1-log n/ell), 1<=n<=N,
    R_N(k)=1+sum_(n=2)^N a_n r_n(k),
    E_N^S=||R_N||^2, H_N=H_(N,K_N)(1,a),
    s_N=sum_(n=1)^N a_n/n, S_N=sum_(n=1)^N a_n,
    b_N=1+(S_N-s_N)/2,
    C_N=H_N+|b_N|^2/K_N.                               (14)

E_N^S — ошибка ОДНОГО кандидата; e_N — оптимальная ошибка; ehat_N — оптимум нашей верхней матрицы. Это три разных числа.

Для всех N>=3:

    |b_N|<=N/ell,               nu_N<=7N/(6ell^2).      (15)

Первая оценка следует из
`sum_(n=2)^N(1-log n/ell) <= (N-1-ell)/ell`.
Для второй в Jordan-сумме (4), при x=N/d,

    |B_d| <= [log x+(log x)^2/2]/(d*ell).

Использованы только |mu|<=1 и сравнение убывающей суммы с интегралом. Поскольку J_2(d)<=d^2,

    12 ell^2 nu_N
       <=sum_(d=2)^N [log(N/d)+log^2(N/d)/2]^2
       <=N int_0^1 [log(1/t)+log^2(1/t)/2]^2 dt=14N.

Подставим (15) в (9)–(11), K_N^2>=N^3. Получаем

    |E_N^S-C_N| <=5/ell^2,                             (16)
    E_N^S<=U_(N,K_N)(1,a)<=C_N+5/ell^2,
    0<=U_(N,K_N)(1,a)-E_N^S<=7/ell^2.                 (17)

Например, для (16) достаточно сложить
`nu/K <=7/(6ell^2)` и
`[N|b|^2+2N^2nu]/[K(K+1)] <=10/(3ell^2)`:
сумма 9/(2ell^2)<5/ell^2. Для (17) удвоенная последняя цена меньше 7/ell^2. Все константы независимы от N.

**Что закрыто:** весь бесконечный signed remainder после конечного core и вычислимой mean-моды стал меньше естественного масштаба 1/log N. Старое L9-отсечение N^3 здесь не требуется. **Что не закрыто:** малость C_N. Нельзя отбросить H_N или b_N^2/K_N, называя их положительными.

## 6. Постоянную моду можно сделать малой на доказанном бесконечном семействе

[COFINAL_FAMILY | PAPER. Это дополнительный аналитический ход P6, зарегистрированный после проверки исходной хвостовой формулы, до данного доказательства.]

### 6.1. Сначала элементарно оплатим pole coefficient

Обозначим m_1(N)=sum_(n<=N)mu(n)/n. Из
`sum_(n<=N)mu(n)floor(N/n)=1` следует |m_1(N)|<=2. Также

    sum_(d<=N) mu(d)/d * H_floor(N/d)=1,
    |H_floor(x)-log x-gamma_E|<=2/x, x>=1.

Первое — точная свёртка на обычных целых; второе следует из оценки гармонических чисел и floor(x). Поэтому

    |ell*s_N|<=1+2 gamma_E+2<5,
    |s_N|<=5/ell.                                      (18)

PNT и RH здесь не нужны. Из L9-идентичности, для 1<=k<=N,

    R_N(k)=k*s_N-psi(k)/ell,                            (19)

следует R_N(k)->0 при каждом фиксированном k. Поточечная сходимость ещё не является сходимостью в норме.

### 6.2. Нулевая мода не ограничена, но имеет бесконечно много доступных переходов

Продолжим b_N на X>1 тем же taper. Новые члены при X=n равны нулю, поэтому b(X) непрерывна. Для t>0:

    F(t)=2t*b(exp t)
      =2t+sum_(n<=exp t) mu(n)(1-1/n)(t-log n).

При Re s>1 почленное Laplace-интегрирование абсолютно законно и даёт

    Laplace(F)(s)=[2+1/zeta(s)-1/zeta(s+1)]/s^2.        (20)

Правая часть мероморфна в Re s>0 и регулярна возле каждой положительной вещественной точки. Здесь используются отсутствие вещественных нулей ζ(s) при s>0 и отсутствие нулей ζ(s+1) при Re s>0. В s=1 обратная ζ имеет нуль, не полюс.

Каждый нетривиальный нуль rho с Re rho>0 создаёт в (20) ненулевой полюс; слагаемое 1/zeta(s+1) его не сокращает. Существование такого нуля безусловно. Если бы b(exp t) была в конце ограничена снизу, прибавление к F линейного положительного члена и компактной поправки сделало бы функцию неотрицательной. Абсцисса её Laplace-сходимости конечна, не меньше Re rho>0, но мероморфное выражение регулярно в соответствующей вещественной точке. Это противоречит лемме Ландау: Taylor-коэффициенты transform неотрицательной функции являются неотрицательными моментами, и аналитичность через конечную абсциссу продолжила бы интеграл левее неё. Аналогично для верхней ограниченности.

Следовательно b(exp t) принимает сколь угодно большие значения обоих знаков. Это верно и при RH: для данного утверждения достаточно критических нулей. Неограниченность периодической mean-функции не означает неограниченность взвешенной нормы E_N^S.

Между целыми

    b'(X)=sum_(n<=X)mu(n)(1-1/n)log n/[2X log^2 X],
    |b'(X)|<=1/(2 log X).

Поэтому |b_(N+1)-b_N|<=1/(2log N). Целая последовательность также принимает оба знака сколь угодно далеко. Множество

    S={N>=3: b_N*b_(N+1)<=0}                            (21)

бесконечно, и для каждого N in S

    |b_N|<=1/(2log N),
    E_N^S<=H_N+6/log^2 N.                              (22)

**Автономная определимость S.** Пусть D=lcm(1,...,N), q_n=D*mu(n)(1-1/n), целые. Тогда

    2D log N*b_N
       =log[N^(2D+sum q_n) product_(n<=N)n^(-q_n)].     (23)

Знак определяется сравнением двух целых после сокращения рационального произведения. Нули ζ нужны для доказательства существования бесконечного S, но НЕ для вычисления его членов. Эффективная верхняя граница времени поиска следующего перехода не доказана; огромные целые в (23) не названы быстрым алгоритмом.

## 7. Попытка закрыть арифметический core и точное место остановки

[COFINAL_FAMILY | PAPER для формул и импликаций; CONDITIONAL для B_core.]

Из (19) конечный положительный блок содержит в точности

    H_N = (1/ell^2)sum_(k=1)^N |psi(k)-k*ell*s_N|^2/[k(k+1)]
          +sum_(N<k<K_N)|R_N(k)|^2/[k(k+1)].           (24)

Во втором блоке сохраняется полная divisor-формула

    R_N(k)=1+k*s_N
      -sum_(n<=min(k,N))mu(n)(1-log n/ell)floor(k/n).

Ни одно proper prime power не удалено. Следовательно положительность Gram не поставляет малость (24); она лишь не даёт отрицательным частям искусственно сократиться в норме.

**Реально полученная безусловная оценка.** Элементарная Chebyshev-граница psi(k)<=12k из R6C и (18) дают |R_N(k)|<=17k/ell на k<=N. На shoulder используем |R_N(k)|<=N/ell из суммы модулей taper. Поэтому

    H_N<=290 N/log^2 N.                               (25)

Это полный upper bound, но он не доказывает следующую нужную строку:

    (B_core) exists B<infinity:
       {N in S: H_N<=B} is unbounded.                  (26)

**(26) не доказано.** Рост правой стороны (25) не доказывает отрицание (26). Ни обычное решето, ни периодическое среднее (4), ни точное зануление отдельных head-строк не дали нового совместного bound на (24).

### Почему достаточно даже bounded core, а не 1/log N

При (26) выберем неограниченную последовательность N_j in S с H_(N_j)<=B. По (22) остатки ограничены в H=ell^2(1/[k(k+1)]) нормой sqrt(B+6), а по (18)–(19) поточечно стремятся к нулю. Значит они сходятся слабо к нулю: сначала проверка на конечной поддержке, затем Cauchy–Schwarz для хвоста произвольного фиксированного вектора.

Выбирая подпоследовательность, обеспечим `|<R_(N_i),R_(N_j)>|<=2^(-i-j)` при i<j. Тогда

    e_(N_J)<=||(1/J)sum_(j=1)^J R_(N_j)||^2
            <=(B+6)/J+1/J^2 ->0.                      (27)

Средние соответствуют допустимым треугольным коэффициентам, не запрещённому фиксированному Möbius-ряду. Это механизм гильбертова усреднения L9; новым здесь является source-defined бесконечное S и независимо оплаченный хвост. Сама арифметическая ограниченность (26) не поставляется усреднением.

Точная Mellin-идентичность R6C:

    int_0^1 (Jr_n)(x)x^(s-1)dx
         =zeta(s)(1/n-n^(-s))/s, Re s>0.              (28)

В любом правом нуле rho=beta+i gamma residual transform равен 1/rho. Отсюда

    e_N >= (2beta-1)/|rho|^2, beta>1/2.                (29)

Таким образом (27) исключает каждый правый нуль, а стандартное функциональное уравнение — левые. Это доказывает `(26)=>RH`, не (26).

Возврат к буквальному A_m также сохранён: при (26) можно выбрать J с `(B+6)/J+1/J^2<=1/m`; R7B даёт

    A_m>=e_(N_J) A_m(1/2)-36000(1+log m)^3 G_m.

Это inherited PAPER-bridge для всех направлений с полными Gamma/полюсами/prime powers. Без (26) он не даёт cofinal floor. Более сильная достаточная строка `C_N<=1/(4log N)` при всех больших N вместе с (16) дала бы R_fast для log N>=20; она тоже не доказана.

## 8. Сертификат не теряет естественную константу — условная теорема

[COFINAL_FAMILY | CONDITIONAL на RH+H_-1 для асимптотики; PAPER для сравнения норм.]

Пусть I_N — классическая нецентрированная ошибка V_N из T2. Mellin–Plancherel реализует её как норму на (0,infinity) остатка `1_(0,1)+sum a_n{1/(nx)}`. Центрированный R_N отличается от него ровно на `s_N{1/x}`; при x>1 центрированный остаток нулевой. Из `||{1/x}||^2=kappa=log(2*pi)-gamma_E<2` и (18):

    |sqrt(E_N^S)-sqrt(I_N)|<=5sqrt(kappa)/log N.        (30)

По T2 при RH+H_-1 имеем I_N~C_zeta/log N. Значит E_N^S имеет ТУ ЖЕ ведущую константу, не kappa*C_zeta. По (17) она сохраняется у U_N(1,a). Burnol даёт противоположную границу для d_N^2; при RH+простоте сумма 1/|rho|^2 равна C_zeta (Hadamard product стандартной xi и её значение log-производной при 1).

Из `d_N^2<=e_N<=ehat_N<=U_N(1,a)` заключаем условно

    d_N^2 ~ e_N ~ ehat_N ~ C_zeta/log N.

Это оптимальность ведущего порядка новой РАЦИОНАЛЬНОЙ finite-модели под названными гипотезами. Нельзя поставить её в начало безусловного доказательства RH.

Без H_-1 известный классический NB capture при RH всё равно даёт ehat_N->0: зафиксировать одно конечное приближение, вложить его в более длинные словари и использовать K_N->infinity, N^2/K_N^2->0 в (12). Обратно e_N<=ehat_N и (29) дают RH. Эта последняя качественная эквивалентность сама по себе НЕ засчитывается как продвижение; содержательное новое утверждение — явная all-input мажоранта (12), её константы и (16)–(17).

## 9. Сильнейшая атака: универсальный частотный остаток действительно имеет масштаб N^2

[FINITE_CELL / COFINAL_FAMILY | PAPER; KILL_SCOPE=THEOREM_SHAPE.]

Возьмём допустимые частоты alpha=1/N, beta=1/(N-1) и
`q(k)=(exp(2*pi*i*k*alpha)+exp(2*pi*i*k*beta))/sqrt(2)`.
Его средняя энергия равна 1. При H=floor(N(N-1)/6), N>=5, для k<=H
cos(2*pi*k/[N(N-1)])>=1/2. Поэтому

    sum_(k=1)^H|q(k)|^2-H >=H/2>=N^2/24.             (31)

Если универсальная поправка r_N=o(N^2) заявлена вместо масштаба N^2, то её claimed upper envelope минус фактическая сумма <=r_N-N^2/24<0 для всех поздних N. Это строгий отрицательный upper witness.

Убит только all-coefficient класс произвольных рациональных частот. У реального Möbius-кандидата A_(a/d) связаны общими B_d; (31) не доказывает такого же насыщения в его подклассе. Не убиты специальная арифметическая отмена, другие веса или RH. Точно так же из того, что большой периодический variance существует, нельзя заключать большую NB-норму у цели.

Дополнительная проверенная граница для самого taper: при N>=4096,

    N/(9216log^2 N)<=nu_N<=7N/(6log^2 N).

Для lower bound берём squarefree d in (N/2,3N/4]. Их не меньше N/24: исключение кратных квадратам стоит <=N/4*(zeta(2)-1)+sqrt N, плюс конечная плата за концы. При N>=4096 достаточно zeta(2)<5/3. Для такого d сумма B_d содержит один член, J_2(d)/d^2>=1/zeta(2)>1/2 и log(N/d)>=log(4/3)>1/4. Каждый квадрат в (4) даёт >=1/(384log^2 N). Это количественно объясняет, почему positive variance оплачивается как tail, а не объявляется самим малым NB-остатком.

## 10. Арифметика Q, точный local factor и ложные миры

[ABSTRACT / COFINAL_FAMILY | PAPER с указанными inherited source-фактами.]

**Где входит Q.** CRT в (4), рациональные частоты и separation в (6), соседние клетки `(1/(k+1),1/k]` в изометрии J и обе Möbius-свёртки (18),(19) используют ОДНОВРЕМЕННО обычное сложение и делимость целых. Полный source-match — (28), не просто PSD матрицы делимости.

**Где входит exact Gamma.** Сама upper NB-матрица не содержит Gamma. Завершение прямой стрелки использует именно

    xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2,
    M[exp(-pi*x^2)](s)=pi^(-s/2)Gamma(s/2)/2.

Этот archimedean фактор не имеет нулей в критической полосе и даёт нужную функциональную симметрию. При возврате в A_m он также фиксирует полный Gamma-источник. Положительность произвольного self-dual seed не заменяет это равенство.

**DMV.** Абстрактная делимость и положительные Gram могут существовать. Но соседние ОБЫЧНЫЕ целые и (28) представляют ζ, а не его generalized-integer counting measure. Это точное место разрыва. Для любого возможного source-correct L2-словаря, чьи Mellin-образы исчезают в одном правом DMV-нуле, сохраняется evaluation lower bound вида (29). Поэтому source-correct capture там невозможно. Не предполагается несуществующее zeta-подобное completion DMV.

**DH.** Его Dirichlet coefficients, в том числе смешанные n=6, собственная odd-Gamma, conductor 5 и отсутствие pole не совпадают с нашим источником. Подстановка D(s) вместо ζ в (28) уже неверна. Корректный ремонт с Mellin-null в известном правом DH-нуле также не может иметь capture. Никакой положительный обычный Gram не объявляется формой DH.

**Подсаженный квартет a=1/3.** При стандартной Gamma собственный uncompleted factor равен `Q(s-1/2)zeta(s)/Q(1/2)`. Старые r_n представляют ζ, не этот фактор; link (28) ломается. Нельзя удалить Q'/Q из полного источника. Если построить новый правильный null-словарь, planted rho даёт строго положительный нижний остаток (29).

**Самодуальные v_b из R6B.** Здесь арифметическая ζ может оставаться прежней, но Mellin local factor меняется на Q_b times Gaussian/Gamma. Наш вывод о ζ не утверждает, что xi_b=Q_b xi имеет все нули на линии. Ломается именно exact-local-factor link выше, а не PSD upper Gram. Это сохраняет отрицательный контроль R6B, вместо его обхода переименованием.

**Кривая E/F3 проходит собственный положительный выход.** Пусть h=log3 и `(Per f)(x)=sum_(j in Z)(-1)^j f(x+2hj)`, 0<=x<2h. Для компактного f сумма конечна и Parseval даёт

    A_m^E[f]=2h int_0^(2h)|Per f(x)|^2dx
            =sum_(j in Z)|fhat((j+1/2)pi/h)|^2>=0.

Это identity -> congruence, с нулевым дефектом и её собственным источником. Нельзя навязать кривой обычный ζ-residue dictionary. Тем самым positive primitive/source-return контроль выполнен; законченного нового RH-сертификата для Q нет, и полная приёмка раунда не заявляется.

## 11. Проведённые проверки, предсказания и граница чисел

[FINITE_CELL | PAPER для точной рациональной алгебры; DIAG для плавающей арифметики. DIAG не является новым verifier-тегом для cofinal утверждения.]

1. Covariance (4): все 121 пары 2<=n,m<=12 проверены точными рациональными суммами по lcm(n,m). Совпадение точное. Young-константы и целочисленные конструкции проверены отдельно.
2. N=3,...,10: E_N^S вычислена через полный период с digamma-весами при 80 и 120 десятичных знаках. Формула для каждого периода:

       sum_(j>=0)1/[(k+jQ)(k+jQ+1)]
         =[digamma((k+1)/Q)-digamma(k/Q)]/Q.

   Проверены (9), (16), Fourier/Jordan variance. Разница точностей <5.4e-81; это проверка нормировки, НЕ интервальный сертификат.
3. Верхний Gram N=3,...,8 построен рационально; Schur minima точные. Сравнение с полным periodized Gram при 80/120 знаках дало положительные eigenvalues разности, с расхождением <1.9e-80. Теорема порядка Ginf<=Gup доказана (10), не этими eigenvalues.

| N | ehat_N, округлено из точной дроби | e_N, DIAG |
|---:|---:|---:|
| 3 | 0.180379850019 | 0.095747783928 |
| 4 | 0.153233234776 | 0.065951694216 |
| 5 | 0.087102727870 | 0.036319017938 |
| 6 | 0.084779259082 | 0.036208034637 |
| 7 | 0.062451658544 | 0.024388367885 |
| 8 | 0.059004116762 | 0.024244525307 |

Например, ehat_3=2080069/11531604 точно.

4. Frozen grid N=8,16,...,4096: совместный finite-core вычислялся divisor-свёрткой, без таблицы нулей. Сравнены float64 и longdouble; max discrepancy C_N <3.4e-15. Head identity residual <3.1e-16.

| N | log N*C_N | head contribution | shoulder contribution | mean contribution |
|---:|---:|---:|---:|---:|
| 8 | 0.648428113 | 0.552122111 | 0.062019160 | 0.034286842 |
| 64 | 0.358680649 | 0.344020829 | 0.013801707 | 0.000858112 |
| 512 | 0.252861744 | 0.246154436 | 0.006688408 | 0.000018900 |
| 4096 | 0.202671594 | 0.198918145 | 0.003752579 | 0.000000870 |

Эта сетка не доказывает eventual C_N<=1/(4log N), bounded core на S или сходимость ehat_N. Никакой cofinal PASS из неё не сделан.

**Судьба предсказаний.** P1 — HIT, с константой 7/6 вместо 2. P2 — HIT, 5 вместо 10. P3 — HIT как локализация неоплаченного core; искомая его оценка NOT_PROVED. P4 — HIT только в точно названном unrestricted-frequency классе. P5 — source-match границы сохранены. Дополнительно P6 (mean-crossings) — HIT аналитически; P7 (rational upper Gram, N=3..8) — точная finite construction и успешный DIAG; P8 (lower variance) — HIT. P6–P8 зарегистрированы после раннего grid и до соответствующих новых проверок; они не выдаются за слепые предсказания исходного freeze.

Discriminator для почти нулевого значения: exact rational Schur/identity, либо строгая interval-граница; два совпавших decimal прогона не доказывают точный нуль. Численный поиск нулей, Lean, Arb и независимый аналитический аудит не выполнялись.

## 12. K8A, сильнейшая граница и следующий проверяемый шаг

[ABSTRACT / COFINAL_FAMILY | PAPER для ограничений; CONDITIONAL для core-bound.]

**Главная атака на результат:** можно построить хороший положительный reference-object и всё равно не приблизиться к нужному знаку источника. Здесь она не скрыта: E(c)<=U(c) — доказано, малость U — нет. При фальшивом source-match положительная рациональная матрица продолжит существовать, но не будет контролировать чужой Weil-functional. Именно поэтому итог не называется доказательством RH.

Для незакрытой (26): DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=NB capture или независимый signed receiver; ORIGINAL_REQUESTED_OBJECT=полная критическая оценка нового объекта; ORIGINAL_OBJECT_IS=UNKNOWN как необходимый для конкретного taper; KNOWN_WEAKER_INTERFACES=оптимальные moving coefficients с e_N->0; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=конечный rational domination плюс оплаченный infinite tail и доказанное source-selected S. REOPEN_TRIGGER=новая совместная оценка (24), не улучшение константы 5.

Для узкого kill (31): DOWNSTREAM_CONSUMER=uniform tail certificate; ORIGINAL_OBJECT=замена N^2 на o(N^2) для ВСЕХ separated rational frequency inputs; ORIGINAL_OBJECT_IS=NOT_NECESSARY для RH; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для этого theorem-shape; KILL_SCOPE=THEOREM_SHAPE; EVIDENCE=(31), точный двухчастотный upper witness. REOPEN_TRIGGER=использование доказанных связей Möbius-коэффициентов или другого ограниченного конуса, не повтор universal large-sieve bound.

Две дальнейшие репрезентации остаются различными, а не двумя именами одной нормы:

- **Оптимизированная рациональная мажоранта (12)–(13).** Менять все коэффициенты, анализировать Schur-minimum/source-specific recurrence. Kill-power высокий: конечный рациональный witness проверяем; аналитическая цена cofinal оценки высокая. Не нужно привязываться к одному taper или inverse-zeta-derivative гипотезе.
- **Selberg-core на доказанном S.** Достаточна лишь boundedness (26), затем sparse averaging. Kill-power высокий для данного кандидата; цена — новая совместная оценка двух положительных блоков (24). Огромная upper bound или unbounded mean вне S не опровергают этот путь.

Не следует снова доказывать PSD reference-Gram ради вывода малости, оценивать psi и k*ell*s_N отдельно с надеждой получить критический масштаб, считать finite-grid decay cofinal законом или подменять стандартную Gamma generic self-duality. R4–R4–R5 потоки здесь не используются; ни heat flow, ни свободный path, ни full exact-head convergence не возрождены.

```yaml
iteration:
  target: SOURCE_MATCHED_CRITICAL_NB_CONTROL
  status: PROGRESS
  cognitive_operator_used: ADDITIVE_SPECTRAL_DECOMPOSITION
  new_gap_name: BOUNDED_FINITE_CORE_ON_UNCONDITIONAL_MEAN_CROSSING_SET
  invariant_learned: FULL_NB_NORM_HAS_A_FINITE_RATIONAL_PSD_UPPER_GRAM_WITH_PAID_TAIL
  forbidden_future_move: TAIL_CERTIFICATE_OR_GRAM_POSITIVITY_AS_PROOF_OF_CORE_SMALLNESS
  next_decisive_test: DERIVE_A_SOURCE_BOUND_FOR_THE_FINITE_SCHUR_MINIMUM_OR_SELECTED_CORE
  route_score: 3
```

**Verification handoff.** Записаны только отдельный freeze и этот новый verdict; старые результаты и route-state не менялись. Freeze commit/blob и все пути находятся в YAML. Final commit/blob/SHA256 сообщаются после записи и readback: самоссылочный commit hash внутри файла не имитируется. Уровень результата PAPER; conditional asymptotic отмечена отдельно. RH_PROVED=false.

## Приложение: воспроизводимая точная рациональная конструкция

Код не проверяет RH. Он строит (12), вычисляет точный Schur complement и проверяет 121 covariance. `N` — длина словаря; `K` — первый индекс бесконечного хвоста. Для воспроизведения малой проверки достаточно сохранить блок как `check_round8.py` и выполнить `uv run --with sympy python check_round8.py`.

```python
from math import gcd, isqrt, lcm
import sympy as sp


def upper_gram(N: int) -> tuple[sp.Matrix, sp.Rational]:
    if N < 3:
        raise ValueError("N must be at least 3")
    K = isqrt(N**3)
    K += int(K*K < N**3)
    mean = sp.Matrix([1] + [sp.Rational(n-1, 2*n) for n in range(2, N+1)])
    G = sp.zeros(N)
    for k in range(1, K):
        v = sp.Matrix([1] + [sp.Rational(k % n, n) for n in range(2, N+1)])
        G += v*v.T / sp.Integer(k*(k+1))
    C = sp.zeros(N)
    for i, n in enumerate(range(2, N+1), 1):
        for j, m in enumerate(range(2, N+1), 1):
            C[i, j] = sp.Rational(gcd(n, m)**2-1, 12*n*m)
    G += (sp.Rational(1, K) + sp.Rational(N, K*(K+1))) * mean*mean.T
    G += (sp.Rational(1, K) + sp.Rational(2*N*N, K*(K+1))) * C
    b, B = G[1:, 0], G[1:, 1:]
    ehat = sp.factor(G[0, 0] - (b.T * B.inv() * b)[0])
    assert ehat > 0
    return G, ehat


def covariance_check() -> None:
    for n in range(2, 13):
        for m in range(2, 13):
            Q = lcm(n, m)
            got = sum(
                (sp.Rational(k % n, n)-sp.Rational(n-1, 2*n)) *
                (sp.Rational(k % m, m)-sp.Rational(m-1, 2*m))
                for k in range(Q)
            ) / Q
            assert got == sp.Rational(gcd(n, m)**2-1, 12*n*m)


if __name__ == "__main__":
    covariance_check()
    for N in range(3, 9):
        _, ehat = upper_gram(N)
        print(f"N={N}: exact={ehat}; decimal={sp.N(ehat, 18)}")
```

Последняя логическая строка работы: **(26) ⇒ capture ⇒ RH; (26) остаётся недоказанной.**
