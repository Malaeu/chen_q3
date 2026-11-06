# STATUS: TRY_SQRT_PHASE_VARIANCE_WITH_OPEN_FIXED_WINDOW_F

```yaml
STATUS: TRY_SQRT_PHASE_VARIANCE_WITH_OPEN_FIXED_WINDOW_F
OPERATIVE_CLASS: TRY_SQRT_PHASE_VARIANCE_WITH_OPEN_FIXED_WINDOW_F
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_SQRT_CANCELLATION_ON_N_HALF_TO_TWO_N
ANSWER: PROVED_TRANSLATE_MEAN_SQUARE_AND_EXACT_CROSS_BRIDGE_NOT_THE_FIXED_WINDOW_BOUND
REQUESTED_FIXED_WINDOW_BOUND: NOT_PROVED_AND_NOT_REFUTED
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_COMMIT: 6602052985df5a1b2e3ab876e6a459e6f92a18cd
INPUT_BLOB: e7d45ebbd49e8d060cc5368352e7b3f17b837e13
SPEC_FREEZE_COMMIT: b37dc0aeea924b00d825905b3613b877fcb60beb
SPEC_FREEZE_BLOB: fd34760b70ea70b4f7eaf6ffd89cbe6938d4033c
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_SQRT_WINDOW_BALANCE_2026-11-06_F.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SQRT_WINDOW_BALANCE_2026-11-06_F.md
PROVED_STEPS:
  - {id: SOURCE_EXACT_SIGNED_WINDOW_BALANCE_AND_PRIME_POWER_EXCEPTION, scope: FINITE_CELL, verifier: PAPER}
  - {id: PROPER_PRIME_POWER_WINDOW_MASS_LE_25_SQRT_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: RAW_CURRENT_TRANSLATE_MEAN_SQUARE_LE_7N_OVER_2_FOR_EVERY_BLOCK_LENGTH, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_SHIFTED_HEAD_TAIL_INTEGRAL_NO_LATTICE_REMAINDER, scope: FINITE_CELL, verifier: PAPER}
  - {id: CROSS_LE_2AB_OVER_N_FROM_FIXED_SOURCE_PARTIAL_SUMS, scope: FINITE_CELL, verifier: PAPER}
  - {id: FIXED_SOURCE_INTEGRATED_PREFIX_PRODUCT_INTERFACE, scope: FINITE_CELL, verifier: PAPER, type: IMPLICATION_ONLY}
  - {id: GENERIC_MEAN_TO_FIXED_PHASE_SHORTCUT_COUNTEREXAMPLE, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: NO_SOURCE_SPECIFIC_FIXED_ORIGIN_OR_FULL_BALANCED_ENERGY_UPPER_BOUND
MINIMAL_MISSING_IDENTITY: "For the full unchanged Z_N, exists C<infinity such that {N in S: Z_N<=C} is unbounded. The local sqrt prefix bounds of (19) would control only X_N, not all of Z_N."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: UNIFORM_TRANSLATE_VARIANCE_AND_EXACT_FINITE_CROSS_ESTIMATE_ONLY
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: GENERIC_TRANSLATE_MEAN_TO_FIXED_WINDOW_SQRT_INFERENCE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_CENTERED_DIVISOR_TAPER_WITH_LINEAR_FIXED_WINDOW_SUM
    EVIDENCE: SECTION_5_EQUATIONS_13_14
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_GENERIC_INFERENCE_ONLY
DOES_NOT_KILL: [RH, ACTUAL_MOBIUS_FIXED_WINDOW_ESTIMATE, TRUE_S_SUBSEQUENCE, JOINT_SIGNED_CORRELATION, SOURCE_SPECIFIC_PHASE_CONTROL, FULL_BALANCED_GREEN_METHOD]
DISCRIMINATOR: "All-phase mean is not the prescribed phase. Exact log-coefficient identities test normalization; only a fixed-source upper envelope tests the requested bound."
REOPEN_TRIGGER: "A source-derived bound for the actual partial sums or their integrated product, with all windows required by the full-energy receiver accounted for."
COGNITIVE_OPERATOR: FIXED_PHASE_VERSUS_EXACT_CRT_VARIANCE
ROUTE_SCORE: 3
CLOSES: [EXPLICIT_SQRT_TRANSLATE_VARIANCE, PROPER_POWER_COST_AT_SQRT_SCALE, CROSS_BOUND_WITHOUT_288_LATTICE_REMAINDER]
OPENS: []
NUMERICAL_TESTS: DIAG_ONLY_50_AND_80_DIGITS
EXACT_TESTS: RATIONAL_PRIME_LOG_COEFFICIENT_MATRICES
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **Квадратнокорневое сокращение на требуемом фиксированном окне не доказано.** Доказана близкая, но другая оценка для ТОГО ЖЕ усечённого мёбиусова тока: при любом N и любой длине блока его средний квадрат по всем целочисленным сдвигам не больше 7N/2 в сырой нормировке. Это не случайная модель. Однако от среднего по фазам до фазы, заданной настоящим окном, остаётся неоплаченный переход.

Второй результат относится непосредственно к нужному фиксированному cross: получено точное представление со сдвинутыми границами и оценка |X_N|<=2 A_N^sharp B_N^sharp/N **без** добавки 288/log²N. Поэтому заявленный масштаб sqrt N у нормированных partial sums действительно достаточен для O(1) cross. Сами эти partial-sum bounds не получены. Малый cross также не заменяет контроль полной положительной Z_N.

## 1. Источники, нормы и кванторы

[FINITE_CELL | PAPER для source lock; импорт — inherited PAPER, не независимый аудит всей цепочки.]

E — `docs/routeB_bus/proshka/PROSHKA_VERDICT_RAMANUJAN_HEAD_TAIL_2026-11-06_E.md`, commit `6602052985df5a1b2e3ab876e6a459e6f92a18cd`, blob `e7d45ebbd49e8d060cc5368352e7b3f17b837e13`. Полная локальная копия: 35050 bytes, SHA256 `36230f08ab4cd8ab6f6974d230480f0ccda07703647c21697a9dae71ed051d2c`; Git blob пересчитан и совпал. Нужные §§1–6 прочитаны через GitHub. Авторитетны исправленные коэффициенты E, не отозванные формулы D.

R8 — `PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md`, `70c4e6b0`, blob `e0c22e09de31ce8c3ee37e8c53343477168b2063`: определения S и периодической дисперсии. Уже R8 содержит родственную оценку nu_N<=7N/(6L²). Следствие E_t|R(t+H)-R(t)|²<=4nu_N даёт масштаб N/L². Поэтому общий механизм square-root cancellation **в периодическом среднем** не объявляется впервые открытым: ниже дан непосредственный Ramanujan-вывод для любого H с меньшей явной константой 7/2 вместо 14/3, и закрыта конкретная нормировка нового запроса.

G — `PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md`, `a337b335777c3912694fb058a68a019c47061ffe`, blob `692b10822320c76a8d2c9a82168bb5c35f124d4b`: полная Z_N и достаточный finite-to-global receiver. Короткие пути R8/G имеют префикс `docs/routeB_bus/proshka/`.

**THEOREM, проверенный внешний нормировочный факт:** Laporta, *On Ramanujan expansions and primes in arithmetic progressions*, Abh. Math. Semin. Univ. Hambg. 94 (2024), 209–224, §1, (4)–(6). Издательский HTML содержит конечную формулу с весом 1/d. Ни Delange-condition из основной теоремы статьи, ни conjectural twin-prime conclusion не используются. Конечные тождества здесь доказываются самостоятельно. Целевой поиск erratum/correction не выявил отдельной поправки к этим формулам; это ограниченная проверка.

**THEOREM, только контекст силы цели:** NIST DLMF 25.16.1–25.16.4: определение psi, PNT и эквивалентность RH оценке psi(x)=x+O_epsilon(x^(1/2+epsilon)) для каждого epsilon>0. Это не разрешение импортировать RH-остаток. На просмотренной странице пометка erratum относится к harmonic-number notation в §25.16(ii), не к используемым строкам. Никакой условной оценки простых ниже нет.

```text
https://link.springer.com/article/10.1007/s12188-024-00282-4
https://dlmf.nist.gov/25.16
```

Пусть N>=3 — целое, L=log N, h=floor(N/2). Сохраняем

    a_n=mu(n) log(N/n)/L, 1<=n<=N; a_1=1;
    s_N=sum_(n<=N) a_n/n; c_N=L*s_N;
    q_1=1-s_N; q_n=a_n, n>=2;
    A_N(k)=sum_(n|k,n<=N)q_n;
    j_N(k)=1_(k=1)-A_N(k).

Всегда sum q_n/n=0. На рабочей полосе k>h, k>=2, **сырой ток** f_N(k)=L*j_N(k)=-L*A_N(k). Утверждение о sqrt N для f_N сильнее такого же утверждения о j_N в L раз. Эти нормы ниже не смешиваются.

Используется точное соглашение h<k<=2N из E. Для буквально замкнутого [N/2,2N] при чётном N нужно добавить один атом f_N(N/2)=c_N-Lambda(N/2). Его модуль <=5+L; в нормировке j_N цена <=1+5/L. Это не потерянная граница, и она не меняет квадратнокорневый масштаб.

## 2. Что именно должно сократиться в настоящем окне

[FINITE_CELL | PAPER; прямое следствие полной mu*1 и mu*log, с сохранением всех степеней.]

На всей полосе:

    f_N(k)=c_N-Lambda(k),                    h<k<=N;
    f_N(k)=c_N-Lambda(k)-mu(k)log(k/N),       N<k<=2N.       (1)

После N только один делитель, само k, превышает N. Это и доказывает вторую строку, а не приблизительная оценка divisor-tail.

Следовательно, для любых целых h<=a<b<=2N,

    D_N(a,b):=sum_(a<k<=b) f_N(k)
     =c_N(b-a)-[psi(b)-psi(a)]
       -sum_(max(a,N)<k<=b) mu(k)log(k/N).                    (2)

Если верхний предел последней суммы не превосходит нижнего, сумма нулевая. В частности,

    D_N(h,2N)=(2N-h)c_N-psi(2N)+psi(h)
                    -sum_(N<k<=2N)mu(k)log(k/N).              (3)

Это точная величина, а не произвольная разность числа составных и числа простых.

**Знаки.** При k<=N непростое, не являющееся степенью простого, даёт c_N; простой p и proper power p^r дают c_N-log p. При N<p<=2N простой даёт c_N-L, поскольку mu(p)=-1. Squarefree composite после N даёт c_N-mu(k)log(k/N); non-squarefree composite, не являющееся prime power, даёт c_N. Поэтому «все непростые положительны» неверно без оговорок, а минус простого весит логарифм, не единицу. Никакая предполагаемая положительность c_N в доказательстве не используется.

Для контроля констант |c_N|<5 следует элементарно: |sum_(n<=x)mu(n)/n|<=2 из sum mu(n)floor(x/n)=1; затем sum_(n<=N)mu(n)H_floor(N/n)/n=1 и |H_floor(x)-log x-gamma_E|<=2/x дают |c_N|<=1+2gamma_E+2<5.

### Теорема 1: proper powers уже укладываются в sqrt N

[COFINAL_FAMILY | PAPER; для каждого N>=3, без RH/PNT.]

    0<=sum_(h<k<=2N, k=p^r, r>=2) Lambda(k)<=25 sqrt N.      (4)

Доказательство. Для целого m центральный binomial даёт

    psi(2m)-psi(m)<=log binom(2m,m)<=2m log2.

Каждый p^r в (m,2m] вносит log p в соответствующее неотрицательное p-adic valuation. Dyadic-суммирование до верхней степени 2 даёт psi(x)<3x при x>=1, следовательно theta(x)<3x. Теперь

    psi(x)-theta(x)=sum_(r>=2)theta(x^(1/r))
      <=3 sqrt x+3 x^(1/3) log(x)/log2.

Максимум t exp(-t/6), t>=0, равен 6/e<3; log2>2/3. Поэтому правая часть меньше (33/2)sqrt x<17sqrt x. При x=2N получаем 17sqrt(2N)<25sqrt N. Ограничение на окно может только уменьшить положительную сумму. QED.

Таким образом замена Lambda первыми степенями простых в линейной сумме имеет оплаченный raw-бюджет 25sqrt N. Это НЕ оценка самой суммы (2), NOT вывод о c_N-1 и NOT оплата мёбиусова tail-term.

## 3. Доказанное квадратнокорневое сокращение: точное среднее по сдвигу

[FINITE_CELL / COFINAL_FAMILY | PAPER; все N>=3 и все целые H>=1.]

Для определения периодического тока положим f_N(k)=-L*A_N(k) на всех целых. На положительных k>=2 он совпадает с исходным L*j_N(k); только boundary unit при k=1 отличается. В среднем ниже t начинается с 1, поэтому все t+r>=2 и эта единица вообще не входит.

Пусть P_N=lcm(1,...,N) и

    S_(N,H)(t)=sum_(r=1)^H f_N(t+r),
    V_(N,H)=(1/P_N)sum_(t=1)^P_N |S_(N,H)(t)|².

### Теорема 2

    V_(N,H)<=7N/2,
    (1/P_N)sum_(t=1)^P_N |sum_(r=1)^H j_N(t+r)|²
                   <=7N/(2L²).                               (5)

Оценка одновременна по H. Она работает, в частности, при H=2N-h — длине нужного окна. Но нужное начало t=h — ОДНА фаза; (5) не утверждает bound для этой фазы.

**Доказательство с точными коэффициентами.** По исправленной конечной формуле

    beta_N(q)=sum_(n<=N,q|n)q_n/n, beta_N(1)=0,
    A_N(k)=sum_(q=2)^N beta_N(q)c_q(k).

Разные приведённые дроби a/q задают разные частоты modulo 1. Конечная ортогональность на P_N даёт ровно

    V_(N,H)=L² sum_(q=2)^N |beta_N(q)|² K_q(H),
    K_q(H)=sum_(1<=a<=q, gcd(a,q)=1)
                         |sum_(r=1)^H exp(2pi i a r/q)|².      (6)

Это конечная сумма неотрицательных квадратов с настоящими beta_N. Никаких случайных знаков или гипотез о распределении mu нет.

Пусть r_q=H mod q. Полные q-блоки в внутренней сумме исчезают. Расширение суммы по a на все ненулевые классы даёт

    0<=K_q(H)<=sum_(a=1)^(q-1)|sum_(r=1)^r_q exp(2pi i a r/q)|²
                =r_q(q-r_q)<=q²/4.                           (7)

Последнее равенство — обычный конечный Parseval: сумма с a=0 равна q*r_q, вклад a=0 равен r_q².

Для x=N/q>=1, по |mu|<=1 и монотонности log(x/v)/v,

    L|beta_N(q)|<= (1/q)sum_(v<=x)log(x/v)/v
                   <=[log x+(log x)²/2]/q.                    (8)

Обозначив g(x)=[log x+(log x)²/2]², получаем

    V_(N,H)<=1/4 sum_(q=2)^N g(N/q)
       <=(N/4) integral_0^1 [log(1/t)+log²(1/t)/2]² dt
       =(N/4)(2!+3!+4!/4)=7N/2.                              (9)

В сравнении суммы с интегралом функция g(N/x) неотрицательна и убывает; интервалы [q-1,q] дают требуемое направление. Это завершает доказательство. QED.

**Дополнительная точная реализация.** K_q(H)=sum_(u,v=1)^H c_q(u-v) — целое число. Поэтому после представления L*beta_N(q) рациональными векторами при log простых равенство (6) проверяется как равенство рациональных матриц, без decimal near-zero.

Например, из (5) следует

    #{1<=t<=P_N: |S_(N,H)(t)|>lambda sqrt N}/P_N
                      <=7/(2lambda²).                        (10)

Это доля фаз при каждом fixed N,H. Она не является утверждением, что N in S выбирает хорошую фазу. И для t за пределами рабочей полосы усечённый ток не обязан иметь короткую prime-tail формулу (1).

## 4. Где находится недоказанный переход

[FINITE_CELL | PAPER для точного разложения; необходимая оценка остатка CONDITIONAL.]

Для prescribed t0=h и H=2N-h определим

    Rphase_(N,H)(t0)=|S_(N,H)(t0)|²-V_(N,H).

Точно

    |D_N(h,2N)|²=V_(N,2N-h)+Rphase_(N,2N-h)(h).              (11)

Первая часть конечна, положительна и полностью оплачена (5). Последний член имеет любой знак. Условие Rphase(h)<=C*N, например, дало бы raw sqrt-оценку общей суммы; для нужных partial sums потребовался бы контроль соответствующих длин и начал. **Такого fixed-source phase-bound не получено.**

Сама (11) не считается новым доказательством или более лёгкой RH-эквивалентностью. Её роль — точно назвать операцию, которую нельзя делать бесплатно. В частности, (6) зануляет межчастотные члены после полного фазового среднего. На t=h они не исчезают: это именно запрошенное signed coupling с истинными коэффициентами.

## 5. Строгий судья: из (5) одной фиксированной фазе нельзя приписать sqrt N

[COFINAL_FAMILY | PAPER; counterexample касается generic-интерфейса, НЕ настоящей mu.]

Пусть N кратно 30. Возьмём в том же divisor dictionary

    a_n^+=log(N/n)/L, если 4N/5<=n<5N/6;
    a_n^+=0 для остальных n>=2; raw a_1=1,
    q_1^+=-sum_(n>=2)a_n^+/n, q_n^+=a_n^+.

Центрирование точно. Envelope |a_n^+|<=log(N/n)/L сохранён, поэтому ВСЁ доказательство (5) остаётся верным для этого массива.

На том же фиксированном окне (N/2,2N] число кратных каждому поддержанному n равно 2. При H=3N/2:

    sum_(N/2<k<=2N) f_N^+(k)
       =-sum_(4N/5<=n<5N/6) log(N/n)*(2-3N/(2n)).             (12)

Здесь 2-3N/(2n)>=1/8, log(N/n)>=log(6/5), а индексов ровно N/30. Значит

    sum_(N/2<k<=2N) f_N^+(k)
                    <=-[log(6/5)/240]*N.                     (13)

Для любой предлагаемой универсальной fixed-phase константы C:

    C sqrt N-|sum f_N^+(k)|
                 <=C sqrt N-[log(6/5)/240]N<0               (14)

при всех достаточно больших N из этой последовательности. Это строгая отрицательная верхняя огибающая.

У свидетеля нет настоящих mu и полной mu*1=epsilon. Поэтому он **не опровергает** source-specific оценку пользователя. Он лишь запрещает выводить её из envelope, centering и mean-square результата (5). Нужна информация, потерянная при переходе к фазовому среднему. KILL_SCOPE=THEOREM_SHAPE, не ROUTE_FAMILY.

## 6. Точный мост от sqrt partial sums к cross — без остатка 288/L²

[FINITE_CELL | PAPER; все N>=3, исходные вещественные коэффициенты.]

Определим на fixed source

    U_N(t)=sum_(t/2<l<=N)j_N(l),                  N<=t<=2N;
    V_N(y)=sum_(N<k<=min(y,2N))j_N(k),            y>=N;
    W_N(y)=sum_(N<k<=min(y,2N))j_N(k)/k.

После 2N обе последние функции постоянны. Тогда полный исходный cross из E имеет ТОЧНОЕ представление

    X_N=(2/log2) integral_N^(2N) U_N(t) W_N(t+1) dt/(t+2).    (15)

**Доказательство границ.** В исходной паре N<k<=2l используем

    log(2(l+1)/(k+1))=integral_(k-1)^(2l) dt/(t+2).

Перестановка конечных сумм законна. При фиксированном t условия равны l>t/2 и k<=t+1, с исходными ограничениями l<=N, k>N. Точки равенства имеют нулевую меру. Получаем (15), включая k=2l и первую tail-строку k=N+1. QED.

Эквивалентная точная step-формула:

    X_N=(2/log2) sum_(t=N)^(2N-1) log((t+3)/(t+2))
          [sum_(l=floor(t/2)+1)^N j_N(l)]
          [sum_(k=N+1)^(t+1)j_N(k)/k].                        (16)

Здесь не выполнялась замена shifted-ядра однородным. Поэтому lattice-remainder вообще не нужен.

Пусть

    A_N^sharp=max_(h<=r<=N)|sum_(r<l<=N)j_N(l)|,
    B_N^sharp=max_(N<=r<=2N)|sum_(N<k<=r)j_N(k)|.

Abel summation, V_N(N)=0, даёт для N<=y<=2N+1

    W_N(y)=V_N(y)/y+integral_N^y V_N(v)dv/v²,
    |W_N(y)|<=B_N^sharp/N.

Из (15):

    |X_N|<= [2 A_N^sharp B_N^sharp/(N log2)]
                           *log((2N+2)/(N+2))
            <=2 A_N^sharp B_N^sharp/N.                        (17)

Это универсальный конечный bound, не предположение о mu. Он улучшает для этих входных норм способ оплаты cross: отдельного +288/L² больше нет.

В частности,

    A_N^sharp<=A sqrt N, B_N^sharp<=B sqrt N
                         ==> |X_N|<=2AB.                     (18)

Для raw partial sums f_N=L*j_N условие <=A sqrt N, <=B sqrt N сильнее и даёт |X_N|<=2AB/L².

**Целевая неоплаченная строка этой попытки:**

    exists A,B<infinity and an unbounded S0 subset S:
       A_N^sharp<=A sqrt N and B_N^sharp<=B sqrt N
                                  for every N in S0.         (19)

(19) не доказано. Одна малая сумма D_N(h,2N) не обеспечивает (19): она не контролирует противоположные excursions внутри окна.

### Более слабый интегральный sufficient interface для cross

На том же fixed source положим

    Ucal_N=(1/N) integral_N^(2N) |U_N(t)|² dt/(t+2),
    Wcal_N=N integral_N^(2N) |W_N(t+1)|² dt/(t+2).

Обе формы положительны и вычислимы конечными step-суммами. Cauchy–Schwarz в (15) даёт

    |X_N|<=(2/log2) sqrt(Ucal_N Wcal_N).                       (20)

Поэтому для cross достаточно ограниченности их произведения, без pointwise sqrt-bound на каждом partial sum. **Оценка этого произведения из настоящего источника также не получена.** (20) — proved implication, не доказанная более слабая арифметическая посылка брифа.

## 7. Прямая арифметическая попытка и остановка

[FINITE_CELL | PAPER для тождеств и грубых границ; COFINAL_FAMILY | CONDITIONAL для требуемого улучшения.]

Для головных suffix sums из (2) точно

    L*sum_(r<k<=N)j_N(k)=c_N(N-r)-psi(N)+psi(r), h<=r<=N.

Для хвостовых prefix sums:

    L*sum_(N<k<=r)j_N(k)=c_N(r-N)-psi(r)+psi(N)
                       -sum_(N<k<=r)mu(k)log(k/N).             (21)

Совместное CRT-разложение сохраняет точность, но не превращает эти выражения в положительные/малые по модулю. Из |c_N|<5, psi(x)<3x, |mu|<=1 и log2<1 следует только

    A_N^sharp<=8N/L, B_N^sharp<=12N/L,
    |X_N|<=192N/L².                                          (22)

Последняя цена согласуется с E, а не является новым RH-выигрышем. В (5) square-root получается после взаимного уничтожения РАЗНЫХ частот полным фазовым средним. На фиксированном начале такую ортогональность применять нельзя. Никакая новая estimate для joint true-Mobius residue в (21) здесь не выведена.

Полная форма остаётся

    Z_N=Hcal_N+Tcal_N+X_N, Hcal_N,Tcal_N>=0.

Даже (19) контролировало бы только X_N. Если positive blocks не ограничены отдельно или совместно, это не доказательство bounded Z_N. Положительные окна, целиком лежащие в голове или хвосте, не отменяются cross другого окна. Рост этих блоков для настоящего источника не утверждается.

Для RH всё ещё нужна source-correct ограниченность полной Z_N на неограниченной части S, либо другой независимый поставщик. Тогда pinned E_N<=14Z_N+9/L², pointwise-zero остатки и гильбертово усреднение дают e_N->0; Mellin-evaluation в любом правом нуле даёт e_N>=(2Re rho-1)/|rho|²>0 — противоречие. Это CONDITIONAL receiver, не новое доказательство его посылки.

## 8. Отрицательные миры и область настоящего результата

[ABSTRACT | PAPER для алгебры; zero/source-контроли — inherited PAPER из E и его пинов.]

**DMV/Берлинг.** Точное среднее (6) использует период lcm обычных целых и ортогональность e(at/q) на обычных единичных ячейках. Generalized-integer counting measure не заменяет этот source. Не утверждается, что у вещественных generalized primes отсутствует обычная операция сложения; отсутствует доказанное совпадение с данным словарём и Mellin-источником ζ.

**DH.** Его inverse Dirichlet coefficients не равны µ. Подстановка их полного источника, включая odd-Gamma и отсутствие zeta-pole, не сохраняет (1). Универсальная ортогональность сама не является судьёй RH; нужно source-match.

**Квартет и self-dual plants.** При uncompleted source Qζ прежние µ не являются обратными коэффициентами нового источника. При неизменной ζ и изменённом local factor Q times Gaussian/Gamma наш конечный ток и (5) не меняются, но дополнительные нули Q и Q'/Q в полной форме остаются. Поэтому (5) не различает эти completion и не претендует на такое различение. Точный стандартный Γ-фактор обязателен для заключения о настоящей RH.

**Контрмассив R9.** Его envelope тоже допускает mean-square bound типа (5); это не означает малости его core. Source-collapse (1) ломается на первой нарушенной mu*1. Этот контроль подтверждает, что периодическое среднее — недостаточный положительный supplier, а не тайное доказательство RH.

**Кривая над F3.** На собственном источнике сохраняется native exact square 2h integral_0^(2h)|sum_j(-1)^j f(x+2hj)|²dx, h=log3. Она проходит свой source-return без zeta-µ и без навязывания нашего периода P_N. Здесь не построен новый универсальный сертификат, который одинаковой заменой обозначений доказывает все эти задачи.

## 9. Проверки, predictions и честная граница новизны

[FINITE_CELL | PAPER для exact algebra; decimal output — только DIAG.]

Freeze создан отдельно до тестов и не редактировался. Выполнены **47 точных строк** source-формулы (1), для N=3,4,5,6,8 и 2<=k<=2N; **24 точных quadratic identities** полного периодического среднего, для тех же N и разных H из {1,floor(N/2),N,2N,2N-floor(N/2)}. Все log простых представлены формальными переменными с rational coefficients (алгебраическая независимость реальных логарифмов не предполагается); квадратные формы сравнивались как рациональные матрицы. Это сильнее совпадения decimal near-zero, но не заменяет PAPER-квантор.

Для N=30,60,120,240 точно проверены диапазон и рациональные floor/margin условия witness (12). Аналитическое доказательство даёт все N, кратные 30.

На N=3,4,5,6,8, при 50 и 80 decimal digits сверены прямой shifted cross и новая step-формула (16). Максимальные невязки меньше 1.3e-52 и 1.6e-82 соответственно; (17) выполнено на этой сетке. Это не Arb-сертификаты. Большого вычисления на S не было и не требуется для доказанных универсальных lemmas.

P1 — HIT: prime-power exception и tail term сохранены. P2 — HIT: (4) с явной константой 25. P3 — HIT для полного фазового среднего (5), NOT_PROVED для prescribed phase. P4 — HIT для точного bridge (17)/(20), source premise (19) NOT_PROVED. P5 — HIT: (12)–(14) запрещают generic mean-to-pointwise перенос. Ни один из этих scores не означает, что запрошенный fixed-window bound доказан.

Общий периодический variance mechanism уже присутствовал в R8/CRT. Новое для данного шага — одновременная по H нормировка 7N/2, явный fixed-band witness для границы интерфейса и exact shifted cross estimate без lattice-error. Историческая новизна Fourier-ортогональности, Chebyshev-bound или Abel summation не заявляется.

## 10. K8A и следующий решающий вход

Для fixed-source цели: DOWNSTREAM_CONSUMER=полная NB-energy, затем RH; ACTUAL_CONSUMER_REQUIREMENT=bounded pointwise-zero source-correct subsequence; ORIGINAL_REQUESTED_OBJECT=sqrt-cancellation на [N/2,2N]; ORIGINAL_OBJECT_IS=UNKNOWN как необходимый механизм; KNOWN_WEAKER_INTERFACES=интегральная signed-корреляция или полный Gram bound; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; REOPEN_TRIGGER=количественный источник для (19)/(20), с контролем остальных положительных окон.

Для generic kill: ORIGINAL_OBJECT_IS=NOT_NECESSARY; KILL_SCOPE=THEOREM_SHAPE; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для mean-to-fixed inference на taper-envelope class; evidence (12)–(14). Он не распространяется на exact-µ методы.

Две допустимые репрезентации: **A**, фиксированная рационально-частотная форма с полными межчастотными фазами, которые исчезли из (6); различающая сила высокая, аналитическая цена высокая. **B**, положительные fixed-origin prefix energies в (20) и source-specific bound их произведения; различающая сила высокая для cross, аналитическая цена высокая, а для RH остаётся обязательство полной Z_N. DISCRIMINATOR при zero-consistent тесте — exact log-coefficient identity для нормировки и строгая верхняя огибающая для настоящих partial sums; конечная близость к нулю не закрывает cofinal bound.

```yaml
iteration:
  target: FIXED_SOURCE_SQRT_CANCELLATION_ON_N_HALF_TO_TWO_N
  status: OPEN
  cognitive_operator_used: FIXED_PHASE_VERSUS_EXACT_CRT_VARIANCE
  new_gap_name: ACTUAL_PHASE_CONTROL_AFTER_PROVED_SQRT_TRANSLATE_MEAN
  invariant_learned: ROOT_MEAN_SQUARE_OVER_SHIFTS_IS_NOT_THE_FIXED_WINDOW
  forbidden_future_move: REPLACE_PRESCRIBED_SOURCE_PHASE_BY_PERIODIC_ORTHOGONALITY
  next_decisive_test: DERIVE_FIXED_SOURCE_BOUND_FOR_PREFIX_PRODUCT_WITH_ALL_PHASES_RETAINED
  route_score: 3
```

## 11. Проверяемость и доставка

Написаны только отдельный freeze и этот новый Markdown в `docs/routeB_bus/proshka/` на `proshka_inbox_2026-10-31`. Старые verdicts и state files не менялись. Коммит этого файла и remote blob сообщаются в квитанции после записи; их нельзя включить в собственные bytes без изменения hash. Уровень — PAPER с exact finite checks. Lean/Arb и независимый аналитический аудит не выполнены. **Запрошенное сокращение на фиксированном окне и RH остаются недоказанными.**

## Приложение: воспроизводимый exact judge

Код ниже использует только стандартную библиотеку Python. N — длина исходного словаря, H — длина сдвигаемого блока, period — полный период только малых тестов. Перебирать его для больших N не предлагается. `Fraction` хранит точные рациональные коэффициенты при log простых; сравниваются целые матрицы коэффициентов, не floating-point значения логарифмов.

```python
from fractions import Fraction as F
from math import gcd, lcm
import json


def factors(n):
    ans={}; p=2
    while p*p<=n:
        while n%p==0:
            ans[p]=ans.get(p,0)+1; n//=p
        p+=1
    if n>1: ans[n]=ans.get(n,0)+1
    return ans

def mob(n):
    fs=factors(n)
    return 0 if any(k>1 for k in fs.values()) else (-1)**len(fs)

def primes_to(n):
    return [i for i in range(2,n+1) if len(factors(i))==1 and next(iter(factors(i).values()))==1]

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(a,t): return tuple(t*x for x in a)
def outer(a): return [[x*y for y in a] for x in a]
def madd(A,B,t=F(1)):
    for i in range(len(A)):
        for j in range(len(A)):
            A[i][j]+=t*B[i][j]

def ram(q,k):
    return sum(d*mob(q//d) for d in range(1,q+1) if q%d==0 and k%d==0)

cases=[]; source_rows=0
for N in (3,4,5,6,8):
    ps=primes_to(2*N); dim=len(ps); z=(F(0),)*dim
    def logvec(n):
        fs=factors(n); return tuple(F(fs.get(p,0)) for p in ps)
    Lv=logvec(N)
    raw=[z]*(N+1)
    for n in range(2,N+1): raw[n]=scale(add(Lv,scale(logvec(n),-1)),mob(n))
    raw[1]=z
    for n in range(2,N+1): raw[1]=add(raw[1],scale(raw[n],F(-1,n)))
    c=add(Lv,scale(raw[1],-1))
    # Centering and finite Ramanujan coefficients, as exact log vectors.
    beta=[z]*(N+1)
    for q in range(1,N+1):
        for n in range(q,N+1,q): beta[q]=add(beta[q],scale(raw[n],F(1,n)))
    assert beta[1]==z
    P=lcm(*range(1,N+1))
    vals=[]
    for k in range(P):
        v=z
        for n in range(1,N+1):
            if k%n==0: v=add(v,scale(raw[n],-1))
        vals.append(v)
    for k in range(2,2*N+1):
        fs=factors(k)
        Lambda=logvec(next(iter(fs))) if len(fs)==1 else z
        expected=add(c,scale(Lambda,-1))
        if k>N:
            expected=add(expected,scale(add(logvec(k),scale(Lv,-1)),-mob(k)))
        assert vals[k%P]==expected, (N,k,vals[k%P],expected)
        source_rows+=1
    for H in sorted(set((1,N//2,N,2*N,2*N-N//2))):
        direct=[[F(0) for j in range(dim)] for i in range(dim)]
        for t in range(P):
            block=z
            for r in range(1,H+1): block=add(block,vals[(t+r)%P])
            madd(direct,outer(block),F(1,P))
        spectral=[[F(0) for j in range(dim)] for i in range(dim)]
        for q in range(2,N+1):
            integer_energy=sum(ram(q,i-j) for i in range(1,H+1) for j in range(1,H+1))
            r=H%q
            assert 0<=integer_energy<=r*(q-r)
            madd(spectral,outer(beta[q]),F(integer_energy))
        assert direct==spectral, (N,H)
        cases.append({'N':N,'H':H,'period':P,'log_variables':ps,'exact_matrix_identity':True})
# Rational constants for powers bound and fixed-phase obstruction.
assert F(33,2)<17 and 17**2*2<25**2
for N in (30,60,120,240):
    lo,hi=4*N//5,5*N//6
    assert hi-lo==N//30
    for n in range(lo,hi):
        assert (2*N)//n-(N//2)//n==2
        assert F(2)-F(3*N,2*n)>=F(1,8)
res={'source_rows':source_rows,'periodic_quadratic_cases':len(cases),'cases':cases,
     'proper_power_constant_squared_checks':'PASS','fixed_phase_counts_N':[30,60,120,240],
     'all_tests':'PASS','arithmetic':'fractions.Fraction; formal prime-log coefficient matrices'}
print(json.dumps({k:v for k,v in res.items() if k!='cases'},indent=2))
```

Сохрани код как `check_sqrt_window.py` и запусти `python3 check_sqrt_window.py`. Пакеты и сетевой доступ не нужны. Проверка полного набора кванторов остаётся PAPER-доказательством выше, а не результатом этих малых тестов.
