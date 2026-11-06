# STATUS: TRY_RAMANUJAN_HEAD_TAIL_WITH_PAID_LATTICE_DEFECT_E

```yaml
STATUS: TRY_RAMANUJAN_HEAD_TAIL_WITH_PAID_LATTICE_DEFECT_E
OPERATIVE_CLASS: TRY_RAMANUJAN_HEAD_TAIL_WITH_PAID_LATTICE_DEFECT_E
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_GO_JOINT_RAMANUJAN_HEAD_TAIL_CANCELLATION
ANSWER: EXACT_FULL_CROSS_RETURN_AND_PAID_DISCRETE_BOUNDARY_NOT_THE_REQUIRED_O_ONE_BOUND
FULL_RH_ACCEPTANCE: NOT_COMPLETE
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
INPUT_D_COMMIT: 2bac098143d9e8968d4a0f16d700a3646906056e
INPUT_D_BLOB: 18e8cbeb850ec0b6fe5789eb96f2334b689dcd76
INPUT_GREEN_COMMIT: a337b335777c3912694fb058a68a019c47061ffe
INPUT_GREEN_BLOB: 692b10822320c76a8d2c9a82168bb5c35f124d4b
SPEC_FREEZE_COMMIT: 8afbad3a2e4f756f4cf3a661ce54aede50fb5ddf
SPEC_FREEZE_BLOB: 2771af8192a3c1338a6a4b00b732cdf265478966
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_RAMANUJAN_HEAD_TAIL_2026-11-06_E.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_RAMANUJAN_HEAD_TAIL_2026-11-06_E.md
PROVED_STEPS:
  - {id: TWO_EXACT_COUNTEREXAMPLES_TO_PREVIOUS_D_NORMALIZATIONS, scope: FINITE_CELL, verifier: PAPER}
  - {id: CORRECT_FINITE_RAMANUJAN_EXPANSION_OF_THE_FULL_CENTERED_CURRENT, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_TRIANGULAR_HEAD_TAIL_SUPPORT, scope: FINITE_CELL, verifier: PAPER}
  - {id: SINGLE_OMITTED_DIVISOR_COLLAPSE_ON_THE_ENTIRE_CROSS_STRIP, scope: FINITE_CELL, verifier: PAPER}
  - {id: FULL_SIGNED_RAMANUJAN_BILINEAR_AND_CRT_BOUNDARY_RETURN, scope: FINITE_CELL, verifier: PAPER}
  - {id: LATTICE_SHIFT_DEFECT_AT_MOST_288_OVER_LOG_SQUARED, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_ONE_DIMENSIONAL_PRIME_MOBIUS_CROSS_CORRELATION, scope: FINITE_CELL, verifier: PAPER}
RH_GAP: NO_SOURCE_BOUND_FOR_THE_JOINT_HEAD_TAIL_ENERGY_ON_AN_UNBOUNDED_SUBSET_OF_S
MINIMAL_MISSING_IDENTITY: "Exists C<infinity such that {N in S: Hcal_N+Tcal_N+2 I_N/(log(N)^2 log(2))<=C} is unbounded; definitions (2),(15). This is the old full-energy obligation with a paid lattice defect, not a proved arithmetic bound."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: SOURCE_REPAIR_EXACT_BOUNDARY_AND_UNIFORM_DISCRETIZATION_ERROR
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: D_EQUATION_1_WRONG_RAMANUJAN_COEFFICIENT
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_N2_L1_NONZERO_LOG_COEFFICIENT
    EVIDENCE: SECTION_0_A
  - id: D_EQUATION_2_DOUBLE_DIVISION_BY_INDICES
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_SINGLE_COORDINATE_AND_ACTUAL_N3_COUNTEREXAMPLES
    EVIDENCE: SECTION_0_B
DOES_NOT_KILL: [RH, ACTUAL_BALANCED_GREEN_FORM, JOINT_RAMANUJAN_CANCELLATION, GAUSSIAN_MELLIN_FINITE_IDENTITY, SOURCE_SPECIFIC_SIGNED_ESTIMATES]
DISCRIMINATOR: EXACT_DIVISOR_SOURCE_MATCH_AND_STANDARD_GAMMA_FACTOR_NOT_SMALL_FLOATING_RESIDUALS
REOPEN_TRIGGER: A joint source-derived bound for (22), or an error in the corrected source identities or boundary estimate.
COGNITIVE_OPERATOR: EXACT_BOUNDARY_DIVISOR_COLLAPSE_AND_RAMANUJAN_BILINEAR_RETURN
ROUTE_SCORE: 3
CLOSES: [FULL_HEAD_TAIL_RAMANUJAN_RETURN, ONE_OMITTED_DIVISOR_BOUNDARY, DISCRETE_PLUS_ONE_PRICE]
OPENS: []
NUMERICAL_TESTS: DIAG_ONLY_50_AND_80_DIGITS
EXACT_TESTS: RATIONAL_PRIME_LOG_COEFFICIENTS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_READBACK
```

Ы. **Полный перекрёстный член разложен с обоими настоящими Ramanujan-весами и точной границей. Получена новая равномерная оценка дискретной поправки: 288/log²N. Главная подписанная корреляция не оценена величиной O(1); RH не доказана.** Перед построением обнаружены и исправлены в этом новом файле две ошибки моего предыдущего вердикта D. Старые файлы и freeze не редактировались.

## 0. Исправления входа D: два независимых дефекта

[FINITE_CELL | PAPER.]

**A. Коэффициент в (1) D неверен.** Для divisor-свёртки

    f_[N](l)=sum_(d|l,d<=N) f(d)

правильно

    fhat_N(q)=sum_(d<=N,q|d) f(d)/d,
    f_[N](l)=sum_(q<=N) fhat_N(q)c_q(l).                 (0.1)

Нельзя заменять знаменатель d внутри суммы на q. Для f(d)=-mu(d)log d, N=2, l=1 формула D даёт **log(2)/2**, тогда как Lambda_[2](1)=0. Это точный ненулевой коэффициент при log 2, не численная невязка.

Доказательство (0.1): сумма по q|d от c_q(l) равна d при d|l и нулю иначе. Поэтому sum_d f(d)/d sum_(q|d)c_q(l)=f_[N](l). Перестановка конечна. В частности,

    h_N(q)=-sum_(d<=N,q|d) mu(d)log(d)/d.                (0.2)

**B. В (2) D индексы поделены дважды.** Если v_l=L*d_l, то правильное ядро для v — min(l,k)*kappa(l,k)/L², а не kappa(l,k)/(L² max(l,k)). Последнее допустимо для числителя j_l=l*d_l, но не для d_l. На координате d_2=1 истинная энергия равна 2, ошибочная — 1/2.

Дефект не исчезает и на настоящем источнике. После отдельного исправления h возьмём N=3, t=log(3/2)/log3 и s=1-t/2. Тогда j=(s,t/2,-t/2). Пусть W_lk=kappa(l,k)/max(l,k). Разность правильной головы и ошибочной формулы с дополнительным делением на lk равна

    s*t*W_12/2 + t²*(3/32+2/27-5*W_23/12)
      > (25/864)t² > 0,

поскольку W_12>0 и W_23<=1/3. Это второй source-level контрпример.

**Последствие для ledger.** Утверждения D о точном конечном Ramanujan-разложении с его выписанными коэффициентами и точной голове с его ядром недействительны. Конечное Gaussian–Mellin тождество D этим не опровергается. Положительная Green-теорема a337b335 не затронута. Ниже используются заново доказанные нормировки.

## 1. Источники и неизменный объект

[FINITE_CELL | PAPER для сверки и определений; импортированные теоремы остаются inherited PAPER.]

D — `PROSHKA_VERDICT_RAMANUJAN_GAUSSIAN_2026-11-06_D.md`, commit/blob в YAML; прочитан полностью через GitHub. G — `PROSHKA_VERDICT_BLOCK_B_MULTISCALE_2026-11-06_C.md`, commit/blob в YAML; полная локальная копия имеет 45426 байт и совпадающий Git blob. Короткие пути здесь имеют префикс `docs/routeB_bus/proshka/`.

G §§2–5 фиксирует источник и доказывает E_N<=14 Z_N+9/L² при N>=8. Его исходная матрица, а не ошибочная запись D, является авторитетным объектом. Для множества S и receiver используются закреплённые там R8 (`70c4e6b0`, blob `e0c22e09de31ce8c3ee37e8c53343477168b2063`) и unit-shift (`2cb30501`, blob `9eccae44e4e1a69e8b6eaa2343c2493784f17ecd`). Независимый аудит всей прежней цепочки не заявляется.

**THEOREM, классический конечный факт:** Laporta, *On Ramanujan expansions and primes in arithmetic progressions*, Abh. Math. Semin. Univ. Hambg. 94 (2024), 209–224, §1, (4)–(6). Издательский HTML проверен: в (5) стоит именно mu(d)log(d)/d; в (6) после d=qv остаётся дополнительный знаменатель v. Используется только конечная идентичность, самостоятельно доказанная выше, не условная оценка корреляций из статьи. Целевой поиск erratum/correction не выявил отдельного исправления этих формул; это ограниченная проверка. PDF не использовался.

```text
https://link.springer.com/article/10.1007/s12188-024-00282-4
https://arxiv.org/abs/2204.01581
```

Пусть N>=3, L=log N. Всюду сохраняются

    a_n=mu(n)log(N/n)/L, 1<=n<=N; a_1=1;
    s_N=sum_(n<=N)a_n/n;
    q_1=1-s_N, q_n=a_n (n>=2);
    A_N(l)=sum_(n|l,n<=N)q_n;
    j_N(l)=1_(l=1)-A_N(l), d_N(l)=j_N(l)/l;
    kappa(l,k)=(1-|log((l+1)/(k+1))|/log2)_+;
    W(l,k)=kappa(l,k)/max(l,k).

Тогда исходная полная форма с T=N² есть

    Z_N=sum_(l,k<=N²) j_N(l)j_N(k)W(l,k).              (1)

Все коэффициенты здесь вещественны. Комплексный вариант требует сопряжения первого множителя; source-специализация его не использует.

Разделим, НЕ меняя форму:

    Z_N=Hcal_N+Tcal_N+X_N,                             (2)
    Hcal_N=sum_(l,k<=N)j_N(l)j_N(k)W(l,k)>=0,
    Tcal_N=sum_(N<l,k<=N²)j_N(l)j_N(k)W(l,k)>=0,
    X_N=2 sum_(l<=N<k<=N²)j_N(l)j_N(k)W(l,k).

Hcal_N — голова Green-формы, НЕ старое H_N из остаточного пространства R8. Положительность двух главных блоков — положительность главных подматриц G. X_N подписан.

## 2. Конечное разложение ПОЛНОГО центрированного тока

[FINITE_CELL | PAPER.]

Определим настоящие коэффициенты

    beta_N(q)=sum_(n<=N,q|n)q_n/n, 1<=q<=N.           (3)

Центрирование даёт beta_N(1)=0 ТОЧНО. Из (0.1), для каждого l>=1,

    A_N(l)=sum_(q=2)^N beta_N(q)c_q(l).                (4)

При q>=2 это не коэффициент одной усечённой Lambda:

    beta_N(q)=sum_(n<=N,q|n) mu(n)log(N/n)/(L*n)
      =mu(q)/(q*L) sum_(v<=N/q,(v,q)=1)
                            mu(v)log(N/(qv))/v.       (5)

Если mu(q)=0, обе стороны равны нулю. Коэффициенты по разным q связаны одним настоящим рядом mu, а не выбираются независимо.

Для сравнения: пусть mhat_N(q)=sum_(n<=N,q|n)mu(n)/n, а h_N — (0.2). Тогда

    beta_N(q)=mhat_N(q)+h_N(q)/L-s_N*1_(q=1).          (6)

Пропуск mhat_N особенно опасен в хвосте: там полная свёртка mu*1 уже не совпадает со своей усечённой версией.

## 3. Точная граница: взаимодействует только полоса (N/2,2N]

[FINITE_CELL | PAPER.]

При l<=N<k вес положителен ровно тогда, когда k+1<2(l+1), то есть **k<=2l**. Поэтому

    l0=floor(N/2)+1,
    X_N=(2/log2) sum_(l=l0)^N sum_(k=N+1)^(2l)
          j_N(l)j_N(k)/k * log(2(l+1)/(k+1)).          (7)

Граница k=2l включена и имеет ненулевой shifted-вес. На k=2l+1 вес ровно нулевой. После k=2N связи с головой нет. Так как N²>=2N, частотный срез не отрезает никакой член (7).

**Вся арифметика полосы сворачивается точно.** Для l<=N имеем

    j_N(l)=s_N-Lambda(l)/L.

Для N<k<=2N единственный делитель k, превышающий N, — само k. Даже при k=2N собственный делитель N остаётся включён. Полные тождества

    sum_(d|k)mu(d)=0,
    -sum_(d|k)mu(d)log d=Lambda(k), k>1

дают

    j_N(k)=s_N-Lambda(k)/L-mu(k)log(k/N)/L.             (8)

В (8) нет неопределённого divisor-tail. Все proper prime powers включены в Lambda. Настоящая mu и согласованность префиксов не изменены.

## 4. Запрошенный полный c_q(l)c_r(k)-cross

[FINITE_CELL | PAPER.]

Все l в (7) не меньше 2, поэтому граничная единица 1_(l=1) здесь отсутствует законно. Подстановка (4) в оба множителя даёт

    X_N=2 sum_(q,r=2)^N beta_N(q)beta_N(r) B_N(q,r),    (9)

где

    B_N(q,r)=(1/log2) sum_(l=l0)^N sum_(k=N+1)^(2l)
         c_q(l)c_r(k)/k * log(2(l+1)/(k+1)).           (10)

Матрица B_N не обязана быть симметричной; в (9) автоматически используется её симметричная часть. Все q!=r и оба настоящих веса сохранены. Внешнего усреднения по вычетам нет.

### 4.1. Вычислимая точная граница без двойного обхода строк

Для N<=m<=2N положим

    C_r(m)=sum_(N<k<=m)c_r(k)/k,
    D_r(m)=sum_(N<k<=m)c_r(k)log(k+1)/k.

Тогда

    B_N(q,r)=(1/log2)sum_(l=l0)^N c_q(l)
              [log(2(l+1))*C_r(2l)-D_r(2l)].          (11)

Через c_r(k)=sum_(d|r,d|k)d*mu(r/d) получаем

    C_r(m)=sum_(d|r)mu(r/d)
                 [H_floor(m/d)-H_floor(N/d)],
    D_r(m)=sum_(d|r)mu(r/d)
             sum_(j=floor(N/d)+1)^floor(m/d)log(dj+1)/j.

Здесь H_j — гармоническое число, H_0=0. Никакой boundary term не заменён O-символом. После свёртки по q,r формула (11) вычисляет настоящий X_N за O(N) арифметических операций после подготовки j_N на [1,2N]. Это не оценка битовой сложности и не заявление об устойчивости floating-point вычитаний.

### 4.2. Совместные вычеты и сдвиг: где работает обычная решётка

Положим h=k-l. Тогда в (10)

    1<=h<=N, max(h,N+1-h)<=l<=N.                     (12)

После раскрытия двух Ramanujan-сумм остаются условия d|l, e|l+h. Они совместимы **ровно при gcd(d,e)|h**. Если совместимы, l лежит в одном классе modulo lcm(d,e). Поэтому (10) равно

    sum_(h=1)^N sum_(d|q,e|r,gcd(d,e)|h)
       d*e*mu(q/d)*mu(r/e)
       sum_(max(h,N+1-h)<=l<=N,
            l congruent r_(d,e,h) mod lcm(d,e))
         log(2(l+1)/(l+h+1))/((l+h)*log2).             (13)

r_(d,e,h) — любое решение двух указанных congruences. Нижний и верхний концы сохранены буквально. Это CRT-использование сцепки сложения и делимости, не замена фиксированной формы средним по периоду. Когда lcm(d,e) сопоставим с N или больше N, короткий интервал может содержать ноль или одно решение: плотность 1/lcm сама не равна последней сумме.

## 5. Новый количественный шаг: дискретный +1 стоит не больше 288/L²

[COFINAL_FAMILY | PAPER, для каждого целого N>=3, без RH/PNT.]

Определим однородный cross теми же настоящими токами:

    X_N^0=(2/log2)sum_(l=l0)^N sum_(k=N+1)^(2l)
                    j_N(l)j_N(k)log(2l/k)/k.

На k=2l его вес равен нулю. Тогда

    X_N=X_N^0+Rlat_N,
    |Rlat_N|<=288/L².                                 (14)

**Независимые арифметические константы.** Имеем |L*s_N|<5. Действительно, divisor-тождество sum mu(n)floor(x/n)=1 даёт |sum_(n<=x)mu(n)/n|<=2. Кроме того,

    sum_(n<=N)mu(n)H_floor(N/n)/n=1,
    |H_floor(x)-log x-gamma_E|<=2/x, x>=1.

Следовательно |L*s_N|<=1+2 gamma_E+2<5.

Также psi(m)<3m для каждого целого m>=1. Для целого v центральный binomial даёт psi(2v)-psi(v)<=log binom(2v,v)<=2v log2: каждое prime power в (v,2v] даёт соответствующий неотрицательный член в p-adic valuation. Суммирование по степеням 2 и увеличение m до ближайшей верхней степени 2 дают psi(m)<4m log2<3m. Это элементарная Chebyshev-оценка, не RH-остаток.

По (8), |mu|<=1 и log2<1,

    sum_(l=l0)^N |j_N(l)| <=8N/L,
    sum_(k=N+1)^(2N)|j_N(k)| <=12N/L.

На каждой паре N<k<=2l:

    0<=log(2(l+1)/(k+1))-log(2l/k)
       =log(1+1/l)-log(1+1/k)<=1/l-1/k,
    (1/l-1/k)/k=(k-l)/(l*k²)<=1/(4l²)<1/N².

Разность (14) поэтому не больше

    2/(N² log2) * (8N/L)*(12N/L)
       =192/(L² log2)<288/L²,

где log2>2/3. Это доказывает (14) со всеми дискретными концами. Rlat_N может иметь любой знак: положительность разности ядер не означает положительность её значения на подписанных токах.

### 5.1. Одна точная арифметическая корреляция вместо четырёх сумм

Положим c_N=L*s_N. Для N<=u<=2N определим

    P_N(u)=sum_(u/2<l<=N)[c_N-Lambda(l)],
    Q_N(u)=sum_(N<k<=u)[c_N-Lambda(k)-mu(k)log(k/N)]/k,
    I_N=int_N^(2N) P_N(u)Q_N(u) du/u.                 (15)

Конечные скачки интеграла не меняют. Из log(2l/k)=int_k^(2l)du/u и (8) следует ТОЧНО

    X_N^0=2 I_N/(L² log2),
    Z_N=Hcal_N+Tcal_N+2 I_N/(L² log2)+Rlat_N.          (16)

Вот три требуемые части: явно вычислимые положительные главные блоки Hcal_N,Tcal_N; точная подписанная корреляция I_N; полностью оплаченный остаток Rlat_N. Новая оценка (14) относится **только к последнему**, не к I_N.

Для прямого расчёта I_N достаточно суммы по t=N,...,2N-1:

    I_N=sum_t log((t+1)/t)
       [sum_(l=floor(t/2)+1)^N (c_N-Lambda(l))]
       [sum_(k=N+1)^t (c_N-Lambda(k)-mu(k)log(k/N))/k]. (17)

Это точная step-интеграция, не quadrature.

## 6. Попытка оценить главный совместный член

[FINITE_CELL | PAPER для следующих неравенств; нужный cofinal bound НЕ ДОКАЗАН.]

Формулы (9) и (13) сохраняют все взаимодействия, но обычная ортогональность Ramanujan-сумм не диагонализует эту треугольную, взвешенную, фиксированную область. Замена её полным периодом была бы новой неоплаченной операцией.

Чтобы явно увидеть цену модульной оплаты после настоящей свёртки, положим

    eta_N=|L*s_N-1|,
    Delta_N=max_(floor(N/2)<=m<=2N)|psi(m)-m|,
    Mcal_N=max_(N<=m<=2N)|M(m)-M(N)|,
    M(m)=sum_(n<=m)mu(n).

Все максимумы по целым. По точным частичным суммам

    |P_N(u)|<=N*eta_N+2Delta_N,
    |Q_N(u)|<=eta_N log2+2Delta_N/N+Mcal_N log2/N.      (18)

Для Lambda-части второе неравенство — Abel summation с частичными суммами (psi(m)-m)-(psi(N)-N). Для mu-части функция log(x/N)/x возрастает на [N,2N]; её двойная вариационная цена не больше log2/N. Поэтому

    |X_N| <= 2/L² * (N*eta_N+2Delta_N)
              *[eta_N log2+(2Delta_N+Mcal_N log2)/N]
              +288/L².                               (19)

(19) — честное конечное неравенство, но не O(1): нужные square-root-scale цены в его правой части не доказаны. Например, eta_N=O(L/sqrt(N)) и Delta_N,Mcal_N=O(sqrt(N)*L) были бы достаточны для O(1) cross; они не принимаются как посылки. Совместная I_N может допускать более слабые оценки, поэтому (19) не объявляется необходимой обязанностью RH.

Прямая элементарная оплата (7) даёт лишь

    |X_N|<=192N/L².                                   (20)

Это не новый RH-выигрыш и не опровержение bounded cross. Получить I_N=O(L²) либо нужную компенсацию в (16) настоящими весами здесь не удалось. Нового безусловного bounded-core, NB-rate или Weil-floor нет.

## 7. Что должен сокращать cross — и чего он не видит

[ABSTRACT / FINITE_CELL | PAPER; source-specific ограниченность остаётся CONDITIONAL.]

**O(1) нужен всей Z_N.** Если Hcal_N+Tcal_N на некоторой семье растёт, недостаточно показать X_N=O(1): тогда необходима компенсация

    X_N=-(Hcal_N+Tcal_N)+O(1).

Рост этих двух блоков для настоящей mu здесь НЕ утверждается. Это логическая граница достаточности отдельной оценки cross, не новый факт о ζ.

Есть более точная геометрия. Положительное представление G имеет вид

    Z_T(d)=(1/log2)sum_(m=1)^T
       [log((2m+1)/(2m))*B_(m,2m)(d)
        +log((2m+2)/(2m+1))*B_(m,2m+1)(d)],
    B_(m,M)(d)=m|sum_(l=m)^(M-1)d_l|²
                 +sum_(j=m+1)^(M-1)|sum_(l=j)^(M-1)d_l|²>=0,

с нулевым продолжением d после T. Разделим окна на M-1<=N, m<=N<M-1 и m>N. Это точная сумма трёх НЕОТРИЦАТЕЛЬНЫХ частей. Только средняя группа содержит head-tail cross. Положительные вклады окон, полностью лежащих в голове или хвосте, cross другого окна не отменяет.

Следовательно оценка одной границы не заменяет контроля всех масштабов. Простой all-input судья: ток, поддержанный на l=1, имеет X_N=0, но произвольно большую Z_N после масштабирования. Это не настоящий mu-свидетель и не KILL source-specific метода; он лишь исключает автоматическую стрелку «малый cross ⇒ малая вся форма».

### Сохранённая стрелка к RH и точная остановка

Нужная строка для (16):

    exists C<infinity:
      {N in S: Hcal_N+Tcal_N+2 I_N/(L² log2)<=C}
      is unbounded.                                  (22)

Благодаря (14), (22) эквивалентно bounded Z_N на неограниченной части S. Это прежняя трудность с оплаченной дискретной поправкой, а не новое доказанное более слабое условие.

При (22) pinned receiver G даёт E_N<=14Z_N+9/L² на выбранной последовательности. Истинный остаток R_N(k)=k s_N-psi(k)/L при N>=k поточечно стремится к нулю. Ограниченная по норме последовательность таких остатков слабо стремится к нулю в ell²(1/[k(k+1)]). Выбор разреженной подпоследовательности с попарными inner products <=2^(-i-j) даёт средние с квадратом нормы <=B/J+1/J². Значит оптимальные NB-ошибки стремятся к нулю.

Обычный integer-cell Mellin-match даёт в каждом правом нуле rho=beta+i gamma нижнюю границу e_N>=(2beta-1)/|rho|². Она противоречит такому пределу; стандартное функциональное уравнение исключает левые нули. Это доказывает условную стрелку (22)⇒RH, **не (22)**.

## 8. Собственные источники отрицательных контролей

[ABSTRACT | PAPER для алгебраических разрывов; zero/source-контроли прежних вердиктов — inherited PAPER.]

**DMV/Берлинг.** Связь (13) использует кратность обычных целых и обычный класс l mod lcm(d,e). В NB-source единичные ячейки дают именно обычную ζ. Подстановка generalized integers не сохраняет эту меру счёта и этот Mellin-match. Это не утверждение, что у вещественных чисел нет операции сложения; не сохраняется данная арифметическая решётка. Корректный другой null-словарь, исчезающий в собственном правом нуле, всё равно имеет положительную Mellin-evaluation нижнюю границу и не может дать capture.

**DH.** Его собственные Dirichlet-коэффициенты и odd-Gamma не совпадают с нашим mu/divisor-source. Обычная mu не может быть переименована в inverse DH-coefficients; (8) тогда не является его формулой. Никакое DH completion не подменяется стандартной ξ.

**Квартет и самодуальные подсадки R6 B.** При изменении uncompleted источника на Q(s-1/2)ζ(s) прежняя mu-формула не представляет весь источник. При сохранении ζ и изменении local factor на Q times Gaussian/Gamma NB-критерий относится лишь к ζ, не к добавочным нулям Q. Член Q'/Q в полной форме Вейля нельзя удалить. Стандартный точный Gamma-фактор остаётся обязательным в финальном source-return; (9) сам его не заменяет.

**Контрмассив R9.** Универсальное конечное разложение (0.1) остаётся верным для любых коэффициентов. Но сокращение (8) использует полную настоящую mu*1=epsilon и mu*log; у R9 они нарушены в первом изменённом индексе. Поэтому его нельзя пропустить через наш source-specific collapse. Положительность Gram не является здесь различающим тестом.

**Кривая над F3.** На своём источнике с h=log3 сохраняется точная положительная периодизация

    W_E[f]=2h int_0^(2h)|sum_(j in Z)(-1)^j f(x+2hj)|²dx>=0.

Это native positive control из закреплённых R6/G, не заявление, что ordinary mu/Ramanujan-source после переименования вычисляет форму кривой. Законченного нового universal RH-сертификата в данной работе нет.

## 9. Проверки, судьба прогнозов и границы вывода

[FINITE_CELL | PAPER для точной алгебры; десятичные сравнения — DIAG.]

После отдельного freeze выполнены проверки с рациональными коэффициентами при log простых для N=2,3,4,8,16,32 и всех l<=2N: **130 строк**. Проверены центрирование beta_N(1)=0, полное Ramanujan-представление A_N, corrected Lambda expansion и обе части boundary-формулы (8). Логарифмы проверялись как формальные векторы рациональных коэффициентов, не через близость decimal к нулю.

На сетке N=8,16,32,64,128,256 при 50 и 80 десятичных знаках сверены прямой cross, независимая prefix-формула и точная step-интеграция. Для N<=32 дополнительно суммировалась полная матрица B_N(q,r) с обоими beta-весами. Невязки меньше 10^-50 и 10^-79 соответственно. Это не интервальные сертификаты.

| N | X_N, DIAG | X_N^0, DIAG |
|---:|---:|---:|
| 8 | 0.001219888860565718 | 0.000593936216346951 |
| 16 | -0.02182738539694161 | -0.02107230554698613 |
| 32 | -0.01828664508764948 | -0.01824361260148668 |
| 64 | 0.000928798525935963 | 0.000709034787414566 |
| 128 | 0.000688359974059656 | 0.000684547183124673 |
| 256 | -0.002855771454894285 | -0.002844468456115808 |

На этой сетке |X-X^0|L²<0.006; это не доказательство (14), которое выведено аналитически для каждого N. Гомогенное следствие (14) было получено после основного freeze и до его отдельной диагностической проверки; оно не записано задним числом как прогноз freeze. Сетка не доказывает boundedness на S; cofinal-прогона не было.

P1 — HIT: два дефекта D подтверждены, старые файлы не исправлялись молча. P2 — HIT: точная полоса и единственный пропущенный делитель. P3 — HIT: полный cross с коэффициентами beta_N, а не с неверным h_N. P4 — целевой O(1) NOT_PROVED; доказана только новая цена дискретной границы и точное сведение. P5 — общая достаточность одного cross неверна; source-specific невозможность не утверждается.

**Сильнейшая атака:** (14) легко принять за оценку самого X_N. Это неверно: она оценивает лишь X_N-X_N^0. Аналогично (22) не следует из PSD или конечности матрицы B_N. Обе границы сохранены явно.

## 10. K8A, оставшиеся представления и передача

Для двух исправлений D: KILL_SCOPE=THEOREM_SHAPE; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для буквально выписанных формул D; точные свидетели — §0 и pinned INPUT_D. Reopen trigger: исправленные формулы (0.1),(1), а не попытка доказать неверную нормировку.

Для цели: DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=истинная source-correct bounded NB subsequence или независимый Weil supplier; ORIGINAL_REQUESTED_OBJECT=joint Ramanujan head-tail cancellation; ORIGINAL_OBJECT_IS=UNKNOWN как необходимый механизм; KNOWN_WEAKER_INTERFACES=полный Gram/optimal NB/direct prime-only receiver; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=полный source-exact cross и равномерная O(log^-2 N) lattice-поправка, не новая RH-эквивалентность.

Два оставшихся представления: **A**, совместная weighted CRT-сумма (13) с настоящими beta_N — высокая различающая сила, высокая аналитическая стоимость; **B**, положительные окна §7 и локальная корреляция (15), с отдельным учётом окон вне границы — высокая различающая сила, высокая аналитическая стоимость. Ни одно не имеет доказанного cofinal O(1). DISCRIMINATOR для near-zero результата — точные divisor/log-коэффициенты и строгая односторонняя огибающая на всей требуемой семье; конечная floating-point близость не занимает квантор.

```yaml
iteration:
  target: TRUE_RAMANUJAN_HEAD_TAIL_CANCELLATION
  status: OPEN
  cognitive_operator_used: EXACT_BOUNDARY_DIVISOR_COLLAPSE_AND_RAMANUJAN_BILINEAR_RETURN
  new_gap_name: FULL_SIGNED_CORRELATION_AFTER_PAID_LATTICE_SHIFT
  invariant_learned: THE_CROSS_IS_ONLY_A_BOUNDARY_STRIP_AND_NEEDS_THE_FULL_CENTERED_CURRENT
  forbidden_future_move: OMIT_ONE_OVER_DIVISOR_OR_DOUBLE_DIVIDE_THE_GREEN_SOURCE
  next_decisive_test: SOURCE_ESTIMATE_FOR_THE_JOINT_EXPRESSION_22_NOT_FOR_THE_DISCRETIZATION_ERROR_ALONE
  route_score: 3
```

Записаны только новый freeze и этот новый вердикт в `docs/routeB_bus/proshka/` на заданной ветке. Commit и remote blob — в квитанции после записи. Freeze неизменён; чужие вердикты, Lean и route-state не изменены. Проверка доставки не является доказательством. Уровень: PAPER, без Lean, Arb и независимого аналитического аудита.

**Итог: требуемое разложение выполнено и дискретная граница оплачена. Главный O(1) bound и RH не доказаны.**
