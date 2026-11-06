# STATUS: KILL_BLOCK_B_FIXED_WIDTH_POSITIVE_GREEN_MAJORANTS_B

```yaml
STATUS: KILL_BLOCK_B_FIXED_WIDTH_POSITIVE_GREEN_MAJORANTS_B
OPERATIVE_CLASS: KILL_BLOCK_B_FIXED_WIDTH_POSITIVE_GREEN_MAJORANTS_B
DATE: 2026-11-06
ANSWER: C_FOR_THE_FROZEN_FIXED_WIDTH_ALL_INPUT_CLASS
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
TRUE_ENDPOINT_BOUND: NOT_PROVED_AND_NOT_REFUTED
REQUEST_COMMIT: caeaac024b05054e6a625bdea8b3f929ee665ac8
REQUEST_BLOB: ea960a415d74beb2c332d6851b43e18cb93716d0
DICTIONARY_REF: 089f59e5
DICTIONARY_BLOB: 8462d827e01dd83fef22f750936f3d84ad238e1d
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_COMMIT: b227cf636cbf33e482177b05d4e151b02b5a6cd8
INPUT_BLOB: ebb4994e7adb3aff745c5e9feb7c8dda71ea0842
SPEC_FREEZE_COMMIT: c3f9b6f7c6ac0b5e57ce0a3a51a333c563ef0231
SPEC_FREEZE_BLOB: 4c7c96cee0b7b1a833b78ed7ea5d71ce3524a270
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_BLOCK_B_SHIFT_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_BLOCK_B_SHIFT_2026-11-06_B.md
SOURCE_MOBIUS_CHANGED: false
FULL_DIVISOR_CONVOLUTION_PRESERVED: true
CROSS_PREFIX_SOURCE_COHERENCE_PRESERVED: true
PROVED_STEPS:
  - {id: WEIGHTED_TAIL_TRANSFORM_IS_UNITARY, scope: ABSTRACT, verifier: PAPER}
  - {id: EXACT_UNIT_SHIFT_CURRENT_AND_HARMONIC_NB_RETURN, scope: FINITE_CELL, verifier: PAPER}
  - {id: POSITIVE_FINITE_HARMONIC_CORE_AND_TAIL_AT_MOST_Q_SQUARED_OVER_K, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_CRT_SHIFT_COVARIANCE_AND_RAMANUJAN_DECOMPOSITION, scope: FINITE_CELL, verifier: PAPER}
  - {id: LOGARITHMIC_FIXED_WIDTH_BLOCK_PRICE_ON_TRUE_MOBIUS, scope: COFINAL_FAMILY, verifier: PAPER, quantifier: FREQUENCY_CUTOFF_AT_FIXED_N}
  - {id: LARGE_PRIMES_DIVISIBILITY_NECESSARY_FOR_FINITE_BLOCK_PRICE, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXPONENTIAL_NECESSARY_BLOCK_WIDTH_IN_THE_TESTED_CLASS, scope: COFINAL_FAMILY, verifier: PAPER, dependency: CLASSICAL_PNT_FOR_SCALE_ONLY}
RH_GAP: SIGNED_ALL_SCALE_INVERSE_SHIFT_ENERGY_FOR_THE_TRUE_SOURCE_ON_S
MINIMAL_MISSING_IDENTITY: "Exists C<infinity such that {N in S: sum_(j>=1)|y_(N,j)|^2<=C} is unbounded; y is exactly (7). Equivalent to the previous endpoint obligation, not proved here."
PROGRESS_CLASS: FALSIFICATION_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: FIXED_WIDTH_BLOCK_DIAGONAL_ALL_INPUT_GREEN_UPPER_CERTIFICATE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_ENVELOPE_ON_THE_UNMODIFIED_SOURCE_CURRENT
    EVIDENCE: SECTIONS_5_6_EQUATIONS_19_22_24
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_WITHIN_THE_STATED_CLASS
DOES_NOT_KILL:
  - RH
  - TRUE_J_N_BOUND_ON_S
  - SIGNED_INTERBLOCK_ESTIMATES
  - BLOCK_WIDTHS_GROWING_WITH_THE_FREQUENCY_INDEX
  - EXACT_TAIL_RESUMMATION
  - STATE_SPECIFIC_BOUNDS_WITHOUT_ALL_INPUT_MAJORANT
  - FULL_R8_GRAM
  - OPTIMAL_NB_COEFFICIENTS
  - NORMALIZED_SMOOTH_PROFILE_AVERAGING
DISCRIMINATOR: EXACT_INTEGER_CRT_VARIANCE_AND_THE_STANDARD_SOURCE_MELLIN_MATCH
REOPEN_TRIGGER: A source-specific signed inverse-shift estimate, or a defect in the fixed-width necessary-price proof.
K8A:
  DOWNSTREAM_CONSUMER: SOURCE_CORRECT_NB_CAPTURE_THEN_RH
  ACTUAL_CONSUMER_REQUIREMENT: A_BOUNDED_POINTWISE_ZERO_TRUE_RESIDUAL_SUBSEQUENCE
  ORIGINAL_REQUESTED_OBJECT: RH_OR_A_NAMED_OBSTRUCTION
  ORIGINAL_OBJECT_IS: UNKNOWN_FOR_THE_PARTICULAR_ENDPOINT_SUPPLIER
  TESTED_BLOCK_SEPARABLE_INTERFACE_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES: SIGNED_COUPLING_EXACT_TAIL_OR_ANOTHER_SOURCE_CORRECT_RECEIVER
  FAILURE_TYPE: COUNTEREXAMPLE_FOR_LOCAL_CERTIFICATE_NO_DERIVATION_FOR_TRUE_J
  EPISTEMIC_STATUS: RESEARCH_DEBT_FOR_RH
  NOVELTY_AXIS: UNIT_SHIFT_GREEN_RETURN_AND_EXACT_LOCAL_RESIDUE_PRICE_ON_TRUE_MOBIUS
CLOSES: [ELEMENTARY_DISCRETE_NORM_RETURN, FIXED_WIDTH_LOCAL_POSITIVE_PAYMENT_SHORTCUT]
OPENS: []
COGNITIVE_OPERATOR: DISCRETE_GREEN_FUNCTION_AND_SOURCE_COHERENT_BLOCK_TEST
ROUTE_SCORE: 2
NUMERICAL_TESTS: DIAGNOSTIC_ONLY_40_AND_70_DIGITS
EXACT_TESTS: RATIONAL_LOG_VECTORS_CRT_AND_WEIGHTED_TAIL_COLUMNS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE
```

Ы. **RH не доказана.** Получен точный дискретный возврат NB-нормы через обратный сдвиг на единицу и узкая теорема-препятствие для заранее замороженного класса локальных положительных мажорант. Свидетель — настоящие согласованные мёбиусовы коэффициенты, без подсадки.

Основной вывод: если при фиксированном N разбить Fourier-индексы на последовательные блоки одной ширины h и оплачивать блоки раздельной квадратичной мажорантой, действующей для всех входов, то пропущенный простой p из (N/2,N), не делящий h, заставляет цену расходиться при снятии частотного среза. При этом полная подписанная энергия сходится к конечной E_N. Блок B действительно входит в доказательство — через точную совместимость вычетов и подсчёт кратных на соседних целых, — но положительная раздельная оплата теряет необходимое межблочное сокращение.

Это **не** нижняя оценка J_N или E_N при N→∞ и **не** запрет всех методов, использующих аддитивные сдвиги. Два предела N→∞ и частотный срез T→∞ ниже строго различаются.

## 1. Source lock и условия литературных мостов

[FINITE_CELL | PAPER: проверка pins, не независимый аудит прежних теорем.]

Бриф и словарь прочитаны по указанным refs, blobs совпали. Bootstrap прочитан на rh_clean; содержимое — v3. Полная локальная копия входа b227cf63 имеет 47895 байт и Git blob ebb4994e7adb3aff745c5e9feb7c8dda71ea0842. Используются его определения, положительная изометрия и оплаченный complement, а не недоказанный bound слоя. Freeze создан отдельным коммитом до завершённых доказательств и тестов, затем прочитан обратно; не изменён.

Внутренние источники:

- R: `docs/routeB_bus/proshka/PROSHKA_VERDICT_SMOOTH_PROFILE_HARDY_RETURN_2026-11-06_B.md`, b227cf636cbf33e482177b05d4e151b02b5a6cd8; §§2,5,8–9.
- R8: `PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md`, 70c4e6b097bc714689fb9226aeaea12a46127c95, blob e0c22e09de31ce8c3ee37e8c53343477168b2063; определения S и bounded-subsequence receiver.
- R9: `PROSHKA_VERDICT_ROUND9_2026-11-06_B.md`, b5fc098b7727bded490c4e46969d6379afa90307, blob bc15928e8da77401e6fc15514cb6fc6f2c1932ee; §6, первая нарушенная divisor-идентичность.

Последние два коротких пути имеют префикс `docs/routeB_bus/proshka/`. Проверка bytes и использование inherited PAPER не названы Lean-проверкой.

**T1 — THEOREM / CONDITIONAL.** D. A. Goldston, *Notes on Pair Correlation of Zeros and Prime Numbers*, arXiv:math/0412313v1, §9, Theorem 7, печатные pp.18–19: теорема об эквивалентности форм парной корреляции и дисперсии простых начинается с предположения RH. Эти страницы прочитаны и проверены web-screenshot. Существенная оговорка: footnote 6 отдельно говорит, что достаточно сильная равномерная prime-variance формула (9.3) сама влечёт RH. Поэтому нельзя ни использовать условную теорему как безусловный supplier, ни объявлять всякую работу с prime variance бесполезной. Такой новой variance-оценки здесь нет.

**T2 — CONJECTURE / HEURISTIC.** Bogomolny–Keating, *Random matrix theory and the Riemann zeros I*, Nonlinearity 8 (1995), DOI 10.1088/0951-7715/8/6/013: проверен издательский abstract, прямо указывающий использование гипотезы Харди–Литтлвуда. Это не импорт безусловной оценки нашего остатка. Технические формулы из недоступного полного текста не используются.

**T3 — THEOREM, контекст.** Broucke–Debruyne–Vindas, arXiv:2004.11501, Theorem 1.1: построена Beurling-система с RH и сильными осцилляциями counting function целых. Прочитан авторский текст и карточка опубликованной работы Adv. Math.370 (2020), 107240. Не каждая Beurling-система является отрицательным контролем. Факт существования обычной числовой операции сложения также нельзя путать с source-correct единичной решёткой её counting measure.

**T4 — THEOREM.** Классическая PNT используется только для интерпретации размера произведения простых в §6. Источник: T1, (2.5). Основная отрицательная огибающая элементарна и PNT не требует.

Целевой поиск correction/erratum по этим названиям не выявил отдельного исправления используемых формулировок; это ограниченная проверка, не заявление об исчерпывающей библиографии. Никакие GUE/HL-посылки ниже не приняты.

```text
https://arxiv.org/pdf/math/0412313
https://websites.umich.edu/~hlm/pc.html
https://doi.org/10.1088/0951-7715/8/6/013
https://arxiv.org/abs/2004.11501
https://doi.org/10.1016/j.aim.2020.107240
```

## 2. Элементарная унитарная версия сдвига

[ABSTRACT | PAPER.]

Пусть w_k=1/[k(k+1)] и H=ell²(N,w). Для R∈H определим

    (U R)_1 = sum_(k>=1) w_k R(k),
    (U R)_j = sum_(k>=j) w_k R(k) - R(j-1)/j,  j>=2.       (1)

Хвостовые линейные функционалы существуют по Cauchy–Schwarz, поскольку sum_(k>=j)w_k=1/j.

**Теорема 1. U — унитарный оператор H→ell²(N).** В частности,

    sum_(k>=1) w_k |R(k)|² = sum_(j>=1) |(UR)_j|².         (2)

Его обратный оператор покоординатно равен

    R(k)=sum_(j=1)^k y_j-k y_(k+1),  y=UR.                (3)

**Доказательство.** Образ δ_k имеет первые k координат w_k, координату k+1, равную −1/(k+1), и далее нули. Его квадрат нормы равен w_k. При k<l скалярное произведение образов равно

    k w_k w_l - w_l/(k+1)=0.

Поэтому нормированные образы дают ортонормированную систему. Если y ортогонален всем этим образам, то y_(k+1)=(y_1+...+y_k)/k; индукцией все y_j одинаковы. Постоянная последовательность принадлежит ell² только при нулевом значении. Следовательно система полна, U унитарен. Формула (3) — его сопряжённый оператор с учётом исходного веса. □

Это независимое элементарное доказательство дискретного возврата; Vasyunin/reciprocity и гипотезы о ζ здесь не нужны. Историческая новизна общей ортогонализации вложенных хвостов не заявляется.

### 2.1. Настоящий источник и граничная единица

[FINITE_CELL | PAPER.]

Для N≥3, L=log N сохраняем

    a_1=1, a_n=mu(n) log(N/n)/L  (2<=n<=N),
    R_N(k)=1+sum_(n=2)^N a_n (k mod n)/n,
    s=sum_(n=1)^N a_n/n, u=sum_(n=1)^N a_n log(n)/n,
    q_1=1-s, q_n=a_n (n>=2), Q=sum_(n=1)^N |q_n|.

Точно sum q_n/n=0. Положим

    A(l)=sum_(n|l,n<=N) q_n,
    d_l=[1_(l=1)-A(l)]/l.                               (4)

В буквальной формуле R_N(0)=1. Целочисленное деление даёт

    R_N(k)-R_N(k-1)=-A(k), k>=1.                        (5)

Чтобы применить стандартный обратный сдвиг, у его входной последовательности положено R(0)=0. Поэтому при k=1 требуется ровно добавка 1_(k=1) в (4). Граничная единица не удалена.

Полная мёбиусова свёртка даёт

    A(l)=1_(l=1)+Lambda(l)/L-s, 1<=l<=N.               (6)

Здесь Lambda(p^r)=log p для всех r≥1. Это не замена простых степеней простыми.

Пусть h_j=sum_(k=1)^j 1/k, h_0=0. Тогда вычислимый без нулей ζ образ y=UR_N равен

    y_j=sum_(l>=j)d_l
       =u+1_(j=1)+sum_(n=1)^N (q_n/n) h_floor((j-1)/n). (7)

Именно (7), а не её отдельные модули, используется ниже.

Для вывода суммы в (7) заметим:

    sum_(l<=T)d_l=1-sum_n (q_n/n)h_floor(T/n) -> 1+u.

Логарифмическая и постоянная части гармонических чисел сокращаются благодаря sum q_n/n=0. Вычитание конечного префикса даёт (7). Альтернативно (5) и дискретное интегрирование по частям прямо возвращают (1).

Проверки нормировки: при a_n=0, n≥2, имеем y=(1,0,...) и E=1. Для одного a_2=t имеем E=1+t log2+(t²/4)log2. Никакого дополнительного вычитания полюса в (2) нет.

### 2.2. Положительный конечный объект и точный остаток

[FINITE_CELL | PAPER.]

Для любых целых v≥r≥1:

    |sum_(l=r)^v A(l)|
     =|sum_n q_n({(r-1)/n}-{v/n})| <= Q.

Следовательно |y_j|≤Q/j при j≥2, по суммированию по частям. Для каждого K≥1 получаем ТОЧНО

    E_N=Y_(N,K)+T_(N,K),
    Y_(N,K)=sum_(j=1)^K |y_j|² >=0,
    T_(N,K)=sum_(j>K)|y_j|²,
    0<=T_(N,K)<=Q²/K.                                  (8)

Все y_j в конечной части явно даны (7). Это положительный Gram линейных функций коэффициентов, а хвост оплачен без RH. Но Q зависит от N: (8) не является cofinal bound.

Для сравнения с входным J_N: Fourier-ряд прежней F_N равен

    F_N(x)=(1/pi) sum_(l>=1) d_l sin(2pi l x).           (9)

У конечной суммы F_T используется тождество

    sin(2pi l x)/sin(pi x)=2 sum_(j=1)^l cos((2j-1)pi x).

По ортогональности, если y_j^(T)=sum_(l=j)^T d_l при j≤T и 0 далее,

    (pi²/2) integral_0^1 |F_T(x)|²/sin²(pi x) dx
                     =sum_j |y_j^(T)|²,
    ||y-y^(T)||²<=2Q²/T.                               (10)

Вторая оценка следует из y_j−y_j^(T)=y_(T+1) для j≤T и из (8). Поэтому предел F_T в sine-взвешенной норме существует, а в обычной L²-норме совпадает с F_N из конечной суммы Bernoulli-функций. Так (2) независимо возвращает изометрию b227cf63, включая комплексную поляризацию.

## 3. Где именно работает «n+1»: CRT, а не аналогия

[FINITE_CELL | PAPER.]

A(l) периодична; допустимый общий период P=lcm(1,...,N). Её среднее равно sum q_n/n=0. Для целого t рассмотрим точную периодическую ковариацию

    C_A(t)=(1/P)sum_(l=1)^P A(l) conjugate(A(l+t)).

Китайская теорема об остатках даёт

    C_A(t)=sum_(n,m<=N) q_n conjugate(q_m)
               gcd(n,m)/(nm) * 1_(gcd(n,m) divides t).   (11)

Условия n|l и m|l+t совместимы ровно при gcd(n,m)|t; тогда плотность решений 1/lcm(n,m). В частности,

    C_A(1)=sum_(gcd(n,m)=1) q_n conjugate(q_m)/(nm).      (12)

Это точное количественное использование того, что соседние целые взаимно просты. Оно не говорит, что каждый оставшийся член имеет полезный знак.

Можно также записать

    C_A(t)=sum_(d<=N) c_d(t) |sum_(d|n,n<=N)q_n/n|²,    (13)

где c_d(t)=sum_(1<=a<=d,(a,d)=1) exp(2pi i a t/d) — сумма Рамануджана. Доказательство: sum_(d|g)c_d(t)=g*1_(g|t), после группировки корней единицы. Поэтому c_d(0)=phi(d), c_d(1)=mu(d). При t=0 имеем положительную энергию, при t=1 — подписанную сумму квадратов. Положительность ковариационной матрицы всех сдвигов сохранена, но (12)–(13) сами не оценивают энергию обратного сдвига.

## 4. Точный Green-Gram и замороженный класс методов

[FINITE_CELL | PAPER.]

Пусть v_l=(1,...,1,0,...) — индикатор первых l целых координат. Тогда

    G_T(l,k)=<v_l,v_k>=min(l,k),  1<=l,k<=T,
    E_T=||sum_(l=1)^T d_l v_l||²=d*G_T d -> E_N.       (14)

Это положительный Green-Gram обратного единичного сдвига. Конечные E_T не объявляются монотонными.

Фиксируем N и целую ширину h≥1, НЕ зависящую от T. Берём T=B h и блоки I_b={bh+1,...,(b+1)h}, 0≤b<B. Разрешена любая эрмитова block-diagonal матрица W=diag(W_0,...,W_(B-1)), удовлетворяющая

    W-G_T >=0                                          (15)

для всех входных амплитуд. Внутри W_b разрешены все смешанные члены, произвольные веса и зависимость от настоящей mu, N, h, B. Класс непуст, например W=T² I удовлетворяет (15).

Цена на ИСХОДНОМ векторе d равна M_(N,h,B)=d*W d. Компрессия (15) на один блок даёт неизбежную нижнюю цену

    M_(N,h,B)>=D_(N,h,B),
    D_(N,h,B)=sum_(b=0)^(B-1)||sum_(l in I_b)d_l v_l||². (16)

При этом ТОЧНО

    E_T=D_(N,h,B)+X_(N,h,B),
    X=2 Re sum_(b<c)<sum_(l in I_b)d_l v_l,
                         sum_(k in I_c)d_k v_k>.       (17)

D≥0, X подписан. Ни (16), ни положительность G_T не разрешают удалить X из истинной энергии.

## 5. Цена фиксированной ширины: строгая огибающая

[COFINAL_FAMILY | PAPER; здесь предел B→∞ при ФИКСИРОВАННЫХ N,h.]

Обозначим

    C_b=sum_(r=1)^h A(bh+r),
    M=P/gcd(P,h),
    v=(1/M)sum_(b=0)^(M-1)|C_b|² >=0.

C_b имеет период M. Для b≥1 из (4) и |A|≤Q:

    sum_(l in I_b)d_l = -C_b/(bh)+epsilon_b,
    |epsilon_b|<=Q/b².

Первые bh координат блока одинаковы; на оставшихся h координатах стоят его хвостовые суммы. Отсюда

    | ||sum_(l in I_b)d_l v_l||² - |C_b|²/(bh) |
                                    <=4hQ²/b².

Первый блок оставляем точным. Получаем

    |D_(N,h,B)-D_(N,h,1)-(1/h)sum_(b=1)^(B-1)|C_b|²/b|
                                    <=8hQ².           (18)

Все константы явные. Поскольку суммы |C_b|² по каждому полному периоду равны Mv, группировка по периодам даёт для всех B≥1

    D_(N,h,B)>=(v/h)log_+(B/M)-8hQ²,                  (19)

где log_+(x)=max(0,log x). Например, q=floor((B-1)/M) полных периодов дают не меньше v h_q; h_q≥log(q+1), а q+1≥B/M. Периодическое суммирование также показывает

    D_(N,h,B)=(v/h)log B+O_(N,h)(1).                  (20)

Последняя O-константа не используется как неоплаченная часть строгой огибающей (19).

### 5.1. Локальные вычеты большого простого дают положительную v

[FINITE_CELL | PAPER.]

Пусть N/2<p<N — простой, N≥4. Среди индексов n≤N единственный кратный p индекс — p. Поэтому

    A(l)=a_p(1_(p|l)-1/p)+A_rest(l),
    a_p=-log(N/p)/L !=0,

где A_rest имеет среднее ноль и период, взаимно простой с p. Если p не делит h, то bh пробегает все классы modulo p. Запишем h=kp+r_p, 0≤r_p<p. Число кратных p в h последовательных целых равно k или k+1; обе частоты известны точно. Отсюда дисперсия p-компоненты C_b равна

    a_p² r_p(p-r_p)/p².

CRT делает эту компоненту ортогональной остальным: их период по b взаимно прост с p. То же верно одновременно для различных простых из (N/2,N). Таким образом

    v >= V_(N,h),
    V_(N,h)=sum_(N/2<p<N) [log(N/p)/L]²
                            (h mod p)(p-(h mod p))/p². (21)

Это конечная явно вычислимая величина. Она строго положительна, если хотя бы один такой p не делит h. В доказательстве не использованы ни RH, ни PNT, ни распределение знаков mu, ни смена коэффициентов. Граничный индекс p=N исключён, потому что его taper равен нулю.

Сложение (16), (19), (21) даёт конечную нижнюю огибающую

    M_(N,h,B)>=[V_(N,h)/h]log_+(B/M)-8hQ².             (22)

### 5.2. Почему это действительно препятствие, а не большая грубая оценка

При V_(N,h)>0 для любой предполагаемой конечной цены C и любого допустимого W:

    C-M_(N,h,B)<=C+8hQ²-[V_(N,h)/h]log(B/M)<0          (23)

как только

    B>M exp(h(C+8hQ²)/V_(N,h)).

Это строгая отрицательная ВЕРХНЯЯ огибающая margin. Между тем E_T→E_N<∞ по (10). Поэтому действительная подписанная сумма не расходится; расходится цена её разъединения.

В частности (17),(20) показывают X=−(v/h)log B+O_(N,h)(1): бесконечные положительные блоковые энергии действительно сокращаются межблочными членами. Это отмена по вспомогательному cutoff при фиксированном N, НЕ требуемая RH-отмена при N→∞.

## 6. Теорема-препятствие и точная область запрета

[COFINAL_FAMILY | PAPER.]

**Теорема 2.** Чтобы замороженный fixed-width all-input метод мог дать хотя бы конечную цену полной E_N после B→∞, необходимо

    product_(N/2<p<N) p divides h.                     (24)

Если это условие нарушено, (23) исключает любую конечную цену, в том числе цену, произвольно зависящую от данного N.

По PNT только для интерпретации масштаба,

    log product_(N/2<p<N)p=(1/2+o(1))N.                (25)

Следовательно методы этого класса с h(N)=exp(o(N)), включая любую фиксированную степень N, проваливаются при каждом достаточно большом N, а значит и на настоящем неограниченном S. Условие (24) необходимое, не достаточное. Если h кратно полному периоду P, то C_b=0 и v=0: наш механизм расходящегося lower bound исчезает. Это не доказательство эффективности оставшихся мажорант.

**Границы.** Не запрещены:
- сохранение signed межблочных членов;
- блоки, увеличивающиеся с Fourier-индексом, а не одной ширины h;
- точное суммирование хвоста (7)–(8), конечный frequency cutoff с отдельно оплаченным remainder;
- оценки только на связанном настоящем векторе без требования (15) для всех входов;
- общий неблочный положительный Gram, включая R8, и другие source-correct представления.

Экспоненциальная ширина (25) НЕ является сложностью вычисления E_N или универсальной ценой RH-доказательства. Формула (7) вычисляет каждую координату без перебора периода P.

**Сильнейшая атака на вывод.** Для G_2=[[1,1],[1,2]] и d=(1,−1) истинная энергия равна 1, сумма двух отдельных энергий равна 3. Следовательно D не обязана мажорировать E_T. Доказано только M≥D для all-input мажорант. Превратить большой D или M в нижний bound E_N было бы фундаментальной ошибкой. KILL_SCOPE=THEOREM_SHAPE, не ROUTE_FAMILY.

## 7. Прямая попытка оценить настоящее J_N и остановка

[FINITE_CELL | PAPER для формул; COFINAL_FAMILY | CONDITIONAL для нужного bound.]

На начальном участке j≤N+1 формула (6) даёт

    y_j=1+u-s h_(j-1)+(1/L)sum_(2<=l<j)Lambda(l)/l.     (26)

Таким образом сдвиг на единицу не теряет арифметику: его точный примитив содержит совместно pole-normalization, мёбиусов s,u и гармонически взвешенную сумму всех prime powers. Оценивать эти три части независимо нельзя. После j>N+1 остаётся полная усечённая divisor-свёртка A(l), а не одна Lambda.

Сохранение (11)–(13), точные формулы (7),(26), переход к периодам и signed Green-равенство (17) не дали нового равномерного верхнего bound на sum |y_j|² при N→∞ на S. Хвост (8) позволяет оплачивать бесконечность при каждом фиксированном N, но не малость растущего конечного блока. Прежний bound на S остаётся только

    E_N<= (290N+6)/L².

Он слишком велик; его рост не является опровержением ограниченной подпоследовательности.

Незакрытая строка:

    exists C<infinity:
       {N in S: sum_(j>=1)|y_(N,j)|²<=C} is unbounded.  (27)

По точному равенству (2) и входному J_N≤E_N≤J_N+63 на S это прежняя задача (25), а не новая более слабая гипотеза. **(27) здесь не доказано.** Новая теорема — запрет конкретной раздельной оплаты при полном сохранении настоящей mu и явное место CRT, а не положительность исходного Weil-оператора.

При (27) прежний receiver остаётся законным: R_N(k)=k s_N−psi(k)/L→0 для каждого фиксированного k, а полные нормы ограничены. Поэтому остатки слабо стремятся к нулю вдоль выбранной подпоследовательности. Из неё выбирается разреженная последовательность с попарными скалярными произведениями ≤2^(−i−j). Норма среднего J остатков не больше C/J+1/J² в квадрате, откуда e_N→0.

Точный source-match обычных целых:

    integral_0^1 Jr_n(x)x^(s-1)dx=zeta(s)(1/n-n^(-s))/s,
    Jr_n(x)={1/(nx)}-{1/x}/n.

В правом нуле rho=beta+i gamma он даёт e_N≥(2beta−1)/|rho|²>0, что противоречило бы capture. Стандартное функциональное уравнение исключает левую половину. Значит (27)⇒RH, но посылка не установлена. Это не новая RH-эквивалентность, выдаваемая за оценку.

## 8. Контрконтроли и точный Gamma-фактор

[ABSTRACT / COFINAL_FAMILY | PAPER; прежние source-controls наследуются, новые нули не локализовались.]

Универсальные линейные тождества (1)–(3) и PSD Green-Gram не обязаны ломаться в ложном мире. Ломается соединение с ЕГО полным источником; нельзя требовать, чтобы общая положительная карта перестала быть положительной.

**DMV/Берлинг.** (5),(11) используют буквально кратные обычных целых и CRT на Z. Их Mellin-словарь представляет ζ, а не собственную Beurling zeta с её counting measure. У обобщённого моноида может быть divisor-идентичность с его counting function, но не это тождество с соседними единичными клетками. Отказ — additive source-match, не утверждение, что у вещественных чисел вообще нет операции сложения. Для source-correct L²-null-словаря собственный правый нуль снова даёт положительную evaluation-преграду. Completion DMV не выдумывается.

**DH.** Должны сохраняться все собственные Dirichlet-коэффициенты, odd-Gamma, conductor 5 и отсутствие полюса. Подстановка DH-функции вместо ζ в написанное Mellin-равенство неверна. Препятствие находится в exact source-match; обычная mu не подменяет его арифметику.

**Подсаженный квартет a=1/3.** При стандартном Gamma собственный uncompleted источник содержит дополнительный Q(s−1/2). Старый integer-словарь вычисляет ζ, не Qζ. Рациональную добавку Q'/Q в полной Weil-форме нельзя отбрасывать. Source-correct null-evaluation в rho=5/6+i gamma запрещает capture.

**Самодуальные v_b.** Здесь обычные простые, mu, (5), (11) и все их аддитивные свойства могут остаться теми же! Меняется Mellin local factor. Поэтому один блок B не различает такую подсадку без exact-local-factor условия:

    integral_0^infinity exp(-pi x²)x^(s-1)dx
                         =(1/2)pi^(-s/2)Gamma(s/2), Re s>0,
    xi(s)=(1/2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s).

У v_b вместо него Q_b(s−1/2) times этот фактор. Вывод об обычной ζ не утверждает отсутствие дополнительных нулей Q_b xi. Это точная граница гипотезы, будто одних аддитивных свойств всегда достаточно.

**R9-контрмассив.** У первой изменённой квадратсвободной координаты n0 полная свёртка c*1 уже не равна epsilon. Его taper с n0<N поэтому не удовлетворяет (6). Наше построение использует действительные mu и mu*log во всём префиксе, а не только b,s или несколько моментов. Общая унитарность (2) для плохого массива остаётся верной; source-specific prime-формула — нет.

**Кривая над F3.** Для её собственного источника h0=log3, Per f(x)=sum_(k in Z)(−1)^k f(x+2h0 k) на [0,2h0). Компактная поддержка даёт конечное число перекрытий, и Parseval даёт

    W_E[f]=2h0 integral_0^(2h0)|Per f(x)|²dx
          =sum_(j in Z)|fhat((j+1/2)pi/h0)|² >=0.

Это источник-определённая прямая конгруэнция, с нулевым дефектом в буквальных сжатиях. Обычный mu-словарь кривой не навязывается. Положительный контроль source-return проходит; нового законченного RH-сертификата для Q здесь нет.

## 9. Проверки и судьба предсказаний

[FINITE_CELL | PAPER для точной рациональной алгебры; численные значения ниже — DIAG.]

Точные проверки выполнены для 16 столбцов (1), для source-convolution при N=4,8,12, для CRT-ковариаций t=0,1,2, а также block-sums при h=1,2,3,5 и h, кратной полному периоду. Логарифмы представлялись рациональными векторами показателей простых: это exact algebra, не сравнение близких десятичных чисел. Период может быть неминимальным; это не меняет средние и доказательства.

При 40 и 70 десятичных знаках независимо сравнены:
- E_N через полный период остатка и точную digamma-сумму весов;
- конечная гармоническая энергия (7) при K=2000 с положительным tail cap Q²/K;
- формула одной свободной координаты a_2 и sine-взвешенный интеграл;
- нижняя CRT-цена (21).

Максимальные невязки гармонического тождества меньше 1.6e−41 и 1.9e−71 соответственно. Это нормировочные DIAG, не интервальные сертификаты.

Отдельный native-DIAG сравнил B=1000 и 100000:

| N,h | v/h | измеренный наклон D по log B |
|---|---:|---:|
| 4,1 | 0.07206978477 | 0.07207690207 |
| 4,2 | 0.00478489238 | 0.00478773490 |
| 8,5 | 0.02683567355 | 0.02683888126 |

При N=4,h=6 периодическая дисперсия равна нулю ТОЧНО; малое float-значение порядка 10^−34 не названо доказательством нуля. Discriminator — exact сумма log-векторов за период. Никаких больших N или cofinal сеток J_N на S не вычислялось.

Скорборд freeze: P1 HIT — (2),(7),(10), без дополнительного вычитания; P2 HIT — (5),(6); P3 HIT — (18)–(23); P4 HIT в точном необходимом scope — (24), с PNT только для (25); P5 HIT с оговоркой footnote 6 Goldston: сильная prime-variance оценка могла бы сама быть supplier, но она здесь не доказана. Прямая задача о bound J_N осталась OPEN. Унитарность на всём H и Ramanujan-формула получены в ходе доказательства, не записываются задним числом как отдельные заранее предсказанные открытия.

### Короткий воспроизводимый точный судья

Python 3, только стандартная библиотека. Vectors кодируют log p; проверяются identities, не положительность больших численных матриц.

```python
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce

def factor(n):
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out

def mu(n):
    f = factor(n)
    return 0 if any(v > 1 for v in f.values()) else (-1)**len(f)

def add(a, b, scale=F(1)):
    out = dict(a)
    for p, x in b.items():
        out[p] = out.get(p, F(0)) + scale*x
        if out[p] == 0: del out[p]
    return out

def lv(n):
    return {p: F(v) for p, v in factor(n).items()}

def outeradd(out, a, b, scale):
    for p, x in a.items():
        for q, y in b.items():
            key = tuple(sorted((p, q)))
            out[key] = out.get(key, F(0)) + scale*x*y
            if out[key] == 0: del out[key]

for N in (4, 8, 12):
    # a and q store L times their mathematical counterparts.
    a = {n: {p: mu(n)*v for p, v in add(lv(N), lv(n), -1).items()
             if mu(n)*v} for n in range(1, N+1)}
    s = {}
    for n in a: s = add(s, a[n], F(1, n))
    q = dict(a); q[1] = add(a[1], s, -1)
    mean = {}
    for n in q: mean = add(mean, q[n], F(1, n))
    assert not mean
    P = reduce(lcm, [n for n in a if a[n]], 1)
    A = []
    for k in range(1, P+1):
        v = {}
        for n in q:
            if k % n == 0: v = add(v, q[n])
        A.append(v)
        if k <= N:
            want = add(lv(N) if k == 1 else {}, s, -1)
            f = factor(k)
            if len(f) == 1: want = add(want, {next(iter(f)): F(1)})
            assert v == want
    for t in (0, 1, 2):
        left, right = {}, {}
        for k in range(P): outeradd(left, A[k], A[(k+t) % P], F(1, P))
        for n in q:
            for m in q:
                if t % gcd(n, m) == 0:
                    outeradd(right, q[n], q[m], F(gcd(n, m), n*m))
        assert left == right
    total = {}
    for v in A: total = add(total, v)
    assert not total
    print(f'N={N}: convolution, CRT and whole-period cancellation PASS')

cols = [[F(1, k*(k+1)) if j <= k else -F(1, k+1)
         if j == k+1 else F(0) for j in range(1, 18)] for k in range(1, 17)]
for k in range(1, 17):
    for l in range(1, 17):
        value = sum(x*y for x, y in zip(cols[k-1], cols[l-1]))
        assert value == (F(1, k*(k+1)) if k == l else 0)
print('16 weighted-tail columns: exact orthogonality PASS')
```

## 10. Closeout, K8A и доставка

Для kill: DOWNSTREAM_CONSUMER — истинный bounded residual на S. ORIGINAL_REQUESTED_OBJECT — локальная положительная оплата обратного сдвига. ORIGINAL_OBJECT_IS=NOT_NECESSARY: это один способ оценки. FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для (15) при V_(N,h)>0 и снятии cutoff с фиксированной h. Свидетель и строгая верхняя огибающая — (21)–(23). Разрешение всем весам читать полную настоящую арифметику не спасает all-input block-diagonal class.

Для RH: FAILURE_TYPE=NO_DERIVATION, EPISTEMIC_STATUS=RESEARCH_DEBT. Истинная оценка (27) не опровергнута. Новизна для проекта — точный унитарный discrete return и необходимая residue-цена локальной оплаты; не новая zero-free region.

Две оставшиеся репрезентации:

1. **Signed multiscale Green-coupling.** Сохранять X в (17), либо использовать растущие блоки и точный хвост (7). Kill-power высокий: настоящее E_N вычисляется точно; аналитическая стоимость высокая, потому что нужен uniform по N bound, а не конечность при fixed N.
2. **Общий рациональный Gram R8 / нормированные профили.** Сохраняет межблочные связи и не принадлежит (15). Kill-power конечного сертификата высокий, вычислительная стоимость растёт с N; cofinal control не следует из finite diagnostics. Дискриминатор малой численной нормы — строгий upper certificate плюс отдельная теорема по N, не добавление разрядности.

```yaml
iteration:
  target: TRUE_ENDPOINT_LAYER_BOUND_USING_ADDITIVE_STRUCTURE
  status: OPEN
  cognitive_operator_used: DISCRETE_GREEN_FUNCTION_AND_SOURCE_COHERENT_BLOCK_TEST
  new_gap_name: TRUE_SIGNED_ALL_SCALE_INVERSE_SHIFT_ENERGY_ON_S
  invariant_learned: EXACT_CRT_RESIDUES_FORCE_LOCAL_CERTIFICATE_COST_BUT_NOT_TRUE_ENERGY_GROWTH
  forbidden_future_move: LARGE_SEPARATED_PRICE_AS_A_LOWER_BOUND_FOR_THE_SIGNED_SUM
  next_decisive_test: A_SOURCE_SPECIFIC_SIGNED_BOUND_NOT_A_FIXED_WIDTH_ALL_INPUT_MAJORANT
  route_score: 2
```

Записаны только отдельный freeze и этот новый verdict под docs/routeB_bus/proshka/ на proshka_inbox_2026-10-31. Freeze: c3f9b6f7c6ac0b5e57ce0a3a51a333c563ef0231, blob 4c7c96cee0b7b1a833b78ed7ea5d71ce3524a270. Финальные commit/blob этого файла сообщаются в квитанции после записи и readback: самоссылочный hash не придумывается. Предыдущие вердикты и route-state не редактировались. Lean, Arb и независимый аналитический аудит не выполнены.

**RH_PROVED: false.** Обратный сдвиг построен точно; нужная source-specific верхняя оценка его полной энергии остаётся недоказанной.
