# STATUS: TRY_MOBIUS_RECIPROCITY_WITH_OPEN_ARITHMETIC_TRACE_B

```yaml
STATUS: TRY_MOBIUS_RECIPROCITY_WITH_OPEN_ARITHMETIC_TRACE_B
OPERATIVE_CLASS: TRY_MOBIUS_RECIPROCITY_WITH_OPEN_ARITHMETIC_TRACE_B
DATE: 2026-11-06
AUTHORITY: DIRECT_OWNER_PROVE_RH_REQUEST_AFTER_R10
ANSWER: PARTIAL_SIGNED_FOURIER_ESTIMATE_AND_EXACT_UNPAID_RETURN
FULL_RH_ACCEPTANCE: NOT_COMPLETE
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: e40f93ceb81f76a51b504d7709eea7439c221bcd
SPEC_FREEZE_BLOB: 881ef00d511e5c816331719e76e8ecb50221d87e
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_MOBIUS_RECIPROCITY_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_MOBIUS_RECIPROCITY_2026-11-06_B.md
PROVED_STEPS:
  - {id: EXACT_CENTERED_GCD_VASYUNIN_RETURN, scope: FINITE_CELL, verifier: PAPER}
  - {id: TRUE_MOBIUS_BOUNDARY_COEFFICIENT_AT_MOST_30, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: FULL_SIGNED_ADDITIVE_FOURIER_ERROR_AT_MOST_7_OVER_LOG_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: EXACT_RATIONAL_COTANGENT_TRACE_TO_FULL_NB_NORM, scope: FINITE_CELL, verifier: PAPER}
  - {id: ARITHMETIC_BOUNDARY_ON_S_AT_MOST_36_OVER_LOG_N, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: UNBOUNDED_L2_SAMPLING_ON_THE_ACTUAL_MOBIUS_CROSSING_SET, scope: ABSTRACT, verifier: PAPER}
RH_GAP: SOURCE_SPECIFIC_LOWER_BOUND_FOR_THE_RATIONAL_TRACE_OF_THE_ACTUAL_FOURIER_ERROR
MINIMAL_MISSING_IDENTITY: "Exists C>=0 such that {N in S: L_N(F_N)>=-C} is unbounded; L_N and F_N are exactly (14)-(15). This is equivalent to the old bounded-core obligation, not newly proved."
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: COMPLETE_ADDITIVE_NORM_ESTIMATE_NOT_A_NEW_NB_OR_WEIL_SIGN_BOUND
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: GENERIC_L2_TO_RATIONAL_TRACE_LOWER_BOUND
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_INTEGER_FREQUENCY_ALIASING_WITH_STRICT_NEGATIVE_UPPER_ENVELOPE
    EVIDENCE: SECTION_6_EQUATIONS_20_21
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_OPERATOR_BOUND_ONLY
DOES_NOT_KILL: [RH, TRUE_R8_CONDITION_26, SOURCE_SPECIFIC_TRACE_BOUNDS, EXACT_RECIPROCITY_METHODS, FULL_R8_GRAM, OPTIMAL_NB_COEFFICIENTS]
DISCRIMINATOR: EXACT_MOBIUS_DIVISOR_CONVOLUTION_AND_SOURCE_MATCH_PLUS_THE_STANDARD_GAMMA_FACTOR
REOPEN_TRIGGER: A joint lower bound for L_N(F_N) using the actual Fourier coefficients, or an error in the exact return or aliasing witness.
K8A:
  DOWNSTREAM_CONSUMER: RH_VIA_SOURCE_CORRECT_NB_CAPTURE
  ACTUAL_CONSUMER_REQUIREMENT: BOUNDED_POINTWISE_ZERO_RESIDUAL_SUBSEQUENCE
  ORIGINAL_REQUESTED_OBJECT: RH_PROOF
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_THE_STATED_GOAL
  TESTED_L2_INTERFACE_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES: OPTIMAL_NB_CAPTURE_OR_DIRECT_LITERAL_WEIL_LOWER_BOUND
  FAILURE_TYPE: NO_DERIVATION_FOR_THE_ACTUAL_SIGNED_TRACE
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: PROJECT_SPECIFIC_QUANTITATIVE_FOURIER_TO_RECIPROCITY_RETURN_NOT_HISTORICAL_NOVELTY_OF_DAVENPORT_OR_VASYUNIN
CLOSES: [FULL_ADDITIVE_ERROR_NORM, ELEMENTARY_BOUNDARY_PRICE, NORM_ONLY_TRACE_SHORTCUT]
OPENS: []
COGNITIVE_OPERATOR: EXACT_RECIPROCITY_AND_ADDITIVE_FOURIER_DUALITY
ROUTE_SCORE: 3
NUMERICAL_TESTS: FINITE_NORMALIZATION_DIAGNOSTICS_ONLY
EXACT_TESTS: DIVISOR_IDENTITIES_INTEGER_ALIASING_AND_RATIONAL_CONSTANT_INEQUALITIES
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT_AFTER_REMOTE_WRITE_AND_READBACK
```

Ы. **RH не доказана.** Получена безусловная оценка полного нового положительного объекта, а не только его дальнего хвоста: явно заданный аддитивный Fourier-остаток имеет норму не больше `7/log N`. Но это норма на окружности, не исходная NB-норма. Точный возврат требует подписанного функционала значений в рациональных точках. Его нужная нижняя оценка на настоящем остатке не доказана.

Одновременно доказано, почему одной малой L2-нормы недостаточно: для настоящих мёбиусовых коэффициентов и настоящего S соответствующий функционал не имеет никакого ограниченного продолжения на L2. Это узкий запрет общей операторной оценки, не запрет source-specific компенсации. Истинная (26) R8 остаётся открытой.

## 1. Источники и границы импорта

[FINITE_CELL | PAPER: source lock, не независимый аудит прежних теорем.]

Внутренние короткие пути имеют префикс `docs/routeB_bus/proshka/`.

| Ref | Pin | Используется |
|---|---|---|
| R8 | `PROSHKA_VERDICT_ROUND8_NEW_MATH_2026-11-06_B.md`; 70c4e6b097bc714689fb9226aeaea12a46127c95; blob e0c22e09de31ce8c3ee37e8c53343477168b2063 | Исходные R_N, E_N, H_N, S, хвост и bounded-subsequence receiver |
| R9 | `PROSHKA_VERDICT_ROUND9_2026-11-06_B.md`; b5fc098b7727bded490c4e46969d6379afa90307; blob bc15928e8da77401e6fc15514cb6fc6f2c1932ee | Точная граница counterarray и source-controls |
| R10 | `PROSHKA_VERDICT_ROUND10_2026-11-06_B.md`; 4a496c5c5984ee47e01746ef84c7971a6d11cd0f; blob c6d3c4da9cda6b3ef98d08d5f58f6f35cc038c29 | Не разъединять подписанные пакеты |
| Summary | rh_clean 1c870b51; `docs/routeB_bus/mythos/ROUTE_B_ROUNDS_4_9_SUMMARY_2026-11-06.md`; blob df730a5d44e5aee76b02e9c1532e4970d593f942 | Контекст, не самостоятельный поставщик оценок |
| Lit | rh_clean 15398196; `docs/routeB_bus/litreview/LIT_MOBIUS_SIGNED_CANCELLATION_2026-11-06.md`; blob 3c69a4d7f54507c4aeee385d1879f1457214ee8d | Указатели на первичные работы; ASSESSMENT не импортируется как THEOREM |

Bootstrap получен заново с rh_clean. Полные локальные R8/R9 совпали с pins. Локальная R10 соответствует исправлению 0ee656bb, blob 88379ce92680f08dd826cef28eadecf344976894. Diff этого исправления отдельно прочитан: исправлены обозначение, номера локаторов и область Gamma-integral, а не price-теорема. Freeze записан отдельным коммитом и не изменён.

**T1 — THEOREM.** Bettin–Conrey, *Period functions and cotangent sums*, arXiv:1111.0931v2, формулы (13), (14), Theorem 4; Algebra & Number Theory 7 (2013), 215–242. Используются точная Vasyunin-формула и reciprocity, не оценка нашей мёбиусовой суммы. Прочитаны arXiv и издательская версия, screenshots arXiv pp.12–13. Целевой поиск correction/erratum отдельного исправления используемых формул не выявил; это ограниченная проверка.

**T2 — NOT_IMPORTED_AS_A_QUANTITATIVE_BOUND.** Maier–Rassias, arXiv:1806.05070, просмотренные pp.2–3. В буквальных нормировках этой копии имеются проблемы, разобранные в §9. Ни численный показатель экономии, ни theorem-to-balanced-range перенос отсюда не используются. Это не утверждение, что намеренный результат авторов опровергнут.

Mellin–Plancherel, Fourier–Parseval и функциональное уравнение стандартной ζ — THEOREM. Прямые арифметические оценки ниже доказаны самостоятельно; RH, простота нулей и отрицательные моменты ζ' не предполагаются. Fourier–Möbius механизм классический; мировая новизна его идеи не заявляется.

```text
T1 https://arxiv.org/pdf/1111.0931v2
   https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf
T2 https://arxiv.org/pdf/1806.05070
```

## 2. Неизменный источник и два оплаченных коэффициента

[COFINAL_FAMILY | PAPER.]

Для N>=3 положим L=log N и

    a_n=mu(n)log(N/n)/L, 1<=n<=N,
    r_n(k)=(k mod n)/n,
    R_N(k)=1+sum_(n=2)^N a_n r_n(k),
    E_N=sum_(k>=1) R_N(k)^2/[k(k+1)],
    s_N=sum a_n/n, S_N=sum a_n, b_N=1+(S_N-s_N)/2,
    u_N=sum a_n log(n)/n,
    q_1=1-s_N, q_n=a_n (n>=2).                         (1)

Все суммы без границ в (1) идут по 1<=n<=N. В частности,

    sum q_n/n=0, sum q_n=2b_N-2.

Используется обычная неизменная mu во всех префиксах. E_N — ошибка одного заданного taper, НЕ оптимальный e_N.

### Лемма 1

Для каждого N>=3:

    |s_N|<=5/L, |u_N|<=30.                             (2)

**Доказательство.** Обозначим m_1(x)=sum_(n<=x)mu(n)/n. Из `sum mu(n)floor(x/n)=1` и |mu|<=1 следует |m_1(x)|<=2 при x>=1. Пусть h_j=sum_(v=1)^j 1/v. Для x>=1:

    |h_floor(x)-log x-gamma_E|<=2/x.

Точная свёртка даёт `sum_(n<=N)mu(n)h_floor(N/n)/n=1`. После подстановки harmonic approximation получаем

    L s_N + gamma_E m_1(N) + error =1, |error|<=2.

Это доказывает первую оценку (2), так как 0<gamma_E<1.

Для второй используем ПОЛНУЮ свёртку

    sum_(d|j)mu(d)log d=-Lambda(j).

Она даёт

    sum_(n<=N)mu(n)log(n)h_floor(N/n)/n
       =-sum_(j<=N)Lambda(j)/j.

Левая часть равна `L u_N+gamma_E v_N+error`, где
`v_N=sum mu(n)log(n)/n`, |v_N|<=4L по частичному суммированию m_1, и |error|<=2L. Элементарно theta(x)<=4x: использовать делимость центрального биномиального коэффициента простыми n<p<=2n и dyadic-суммирование. Далее
`psi(x)<=4x+4sqrt(x)log_2 x<=12x`, с сохранением всех простых степеней. Поэтому

    sum_(j<=N)Lambda(j)/j<=12(1+L).

Получаем `|u_N|<=12(1+L)/L+4+2<=30`, поскольку L>1. □

Из R8 наследуются бесконечность S и

    S={N>=3:b_N b_(N+1)<=0},
    |b_N|<=1/(2L), 0<=E_N-H_N<=6/L^2 on S.           (3)

Верхняя оценка хвоста в (3) не является оценкой H_N. Новые (2) не предполагают такого bounds.

## 3. Полная подписанная Vasyunin-форма: главный элементарный член сокращён

[FINITE_CELL | PAPER, T1 для точного Gram.]

Фиксируем соглашения, включая точки разрыва только там, где они понадобятся далее:

    V(a/b)=sum_(r=1)^(b-1) {ra/b}cot(pi r/b), (a,b)=1,
    V(a/1)=0,
    c0(a/b)=-sum_(r=1)^(b-1)(r/b)cot(pi r a/b).

Тогда V(a/b)=-c0(abar/b), где a*abar=1 mod b. При h,k>=1 положим d=(h,k), a=h/d, b=k/d. Для rho_h(x)={1/(hx)} на (0,infinity) формула T1 и масштабирование дают

    J(h,k)=<rho_h,rho_k>
      =C0(1/h+1/k)/2+(k-h)log(h/k)/(2hk)
       -pi*d[V(a/b)+V(b/a)]/(2hk),
    C0=log(2*pi)-gamma_E.                             (4)

Множитель d НЕ опускается. Он следует из J(da,db)=J(a,b)/d. На диагонали J(h,h)=C0/h.

Функция g_N=sum q_n rho_n равна sum_(n>=2)a_n Jr_n на (0,1) и точно равна нулю при x>1, поскольку sum q_n/n=0. Здесь J в Jr_n означает step-изометрию R8, не ядро J(h,k). Кроме того, `<1,g_N>_(0,1)=u_N` по `<1,Jr_n>=log n/n`.

Определим ПОЛНУЮ, не модульную сумму

    T_N=sum_(h,k<=N) q_h q_k * (h,k)/(hk)
                         * V((h/(h,k))/(k/(h,k))).    (5)

При сложении (4) член C0 исчезает по sum q_n/n=0. Логарифмический член равен `(sum q_n)u_N`; два линейных члена цели дают ещё 2u_N. Итак,

    E_N=1+2b_N u_N-pi T_N.                            (6)

Это равенство для каждого N, без отсечения бесконечной NB-нормы. На S:

    |E_N-(1-pi T_N)|<=30/L.                           (7)

Результат (7) действительно оплачивает весь элементарный остаток. Но он НЕ доказывает нижней границы T_N. Из E_N>=0 получается лишь верхняя граница `pi T_N<=1+30/L` — противоположное нужному направление.

### Точная gcd-перегруппировка, без потери общей арифметики

Для взаимно простых a,b положим

    W_N(a,b)=sum_(d<=N/max(a,b),(d,ab)=1)
      mu(d)^2/d * log(N/(ad))log(N/(bd))/L^2 >=0.

Если в (5) использовать сначала a_h вместо q_h, то

    T_N^raw=sum_((a,b)=1,a,b<=N)
               mu(a)mu(b) W_N(a,b)V(a/b)/(ab).

Полное центрирование возвращается точно:

    T_N=T_N^raw-s_N sum_(n<=N)a_n V(1/n)/n.            (8)

Члена s_N^2 нет, поскольку V(1/1)=0; вторая ориентация при индексе 1 также нулевая. Формула (8) сохраняет общий делитель, оба taper и всю историю mu. Положительность W_N(a,b) не делает подписанную сумму положительной.

Reciprocity T1 даёт, с аналитической period function B(x)=i psi_0(x)/2,

    c0(a/b)=B(a/b)+1/(pi a)-(b/a)c0((b mod a)/a).       (9)

Если r_0=b,r_1=a,r_(j+1)=r_(j-1) mod r_j, r_ell=1, то точная конечная итерация равна

    c0(a/b)=sum_(j=1)^ell (-1)^(j-1) b/r_(j-1)
                   [B(r_j/r_(j-1))+1/(pi r_j)].

Ни положительность, ни исчезновение подписанных весов из этого не следуют. Уже B(1/2)=-1/pi, B(1/4)=1/2-1/pi имеют разные знаки. И modular inversion НЕ сохраняет mu: обратное к 2 modulo 7 равно 4, но mu(2)=-1, mu(4)=0. Перестановка допустима только вместе с переносом весов; заменить их обратно на старые нельзя. Нужной общей оценки суммы (8) этот расчёт не дал.

## 4. Новый полностью оценённый положительный объект

[COFINAL_FAMILY | PAPER, без RH и без PNT.]

Пусть B_1(x)={x}-1/2 вне целых и B_1(x)=0 на целых, с периодом 1. Это midpoint-представитель sawtooth. Его Fourier-ряд в L2 и в средних значениях в точках разрыва:

    B_1(x)=-sum_(r>=1)sin(2*pi*r*x)/(pi*r).

Построим на окружности

    Z_N(x)=sum_(n<=N)(a_n/n) B_1(nx)+sin(2*pi*x)/pi,
    F_N(x)=sum_(n<=N)(q_n/n) B_1(nx)+sin(2*pi*x)/pi
          =Z_N(x)-s_N B_1(x).                        (10)

F_N здесь — аддитивный Fourier-остаток, не Gaussian-transform прежних раундов.

**Положительная вычислимая структура.** Это Gram функций `sin(2*pi*x)/pi` и `B_1(nx)/n` в L2(0,1). Его элементы:

    G_00=1/(2*pi^2), G_0n=-1_(n=1)/(2*pi^2),
    G_hk=(h,k)^2/(12*h^2*k^2), h,k>=1.

Он PSD для всех входных коэффициентов. В частности,

    ||F_N||_2^2=sum_(h,k<=N)q_h q_k (h,k)^2/(12h^2k^2)
                            +(1/2-q_1)/pi^2 >=0.

Последняя запись не названа рациональной матрицей: здесь присутствует pi. Положительность следует из Gram, а не из знака каждого выписанного слагаемого.

Пусть `A_N(r)=sum_(n|r,n<=N)a_n`. Для ВСЕХ r<=N полная свёртка mu даёт

    A_N(r)=1_(r=1)+Lambda(r)/L.                       (11)

Следовательно Parseval даёт ТОЧНО

    ||Z_N||_2^2 = [1/(2*pi^2*L^2)]sum_(r=2)^N Lambda(r)^2/r^2
                   + Q_N,
    Q_N=[1/(2*pi^2)]sum_(r>N) A_N(r)^2/r^2 >=0.       (12)

Здесь есть все три части: явно вычислимый положительный конечный член, положительный Gram по построению и точный бесконечный остаток Q_N.

### Теорема 1: весь остаток, а не один хвост, мал

Для каждого целого N>=3:

    0<=Q_N<=[L^3+6L^2+15L+16]/(pi^2 N),
    ||Z_N||_2^2<=30/L^2,
    ||F_N||_2<=7/L.                                  (13)

**Доказательство.** |a_n|<=1, поэтому |A_N(r)|<=d(r). На простых степенях `(j+1)^2<=binom(j+3,3)`, следовательно d(r)^2<=d_4(r). Число упорядоченных четвёрок с произведением <=x ограничено `x(1+log x)^3`: просуммировать floor(x/(abc)) и увеличить область тройной гармонической суммы. Частичное суммирование даёт

    sum_(r>N)d_4(r)/r^2
       <=2 integral_N^infinity (1+log x)^3/x^2 dx
       =2[L^3+6L^2+15L+16]/N.

Это доказывает bound на Q_N. Также
`sum_(r>=2)(log r)^2/r^2<4`, например сравнением на [r-1,r] с log^2(x+1)/x^2 и интегралом `(log2+log x)^2/x^2`. Поэтому (12) не больше

    2/(pi^2 L^2)+(L^3+6L^2+15L+16)/(pi^2 e^L).

Для каждого x>=0, x^j e^(-x)<=(j/e)^j<(j/2)^j. Отсюда

    e^(-L)(L^5+6L^4+15L^3+16L^2)<261,
    (2+261)/pi^2<30.

Наконец ||B_1||_2=1/sqrt(12), (2) и triangle inequality дают
`||F_N||_2< (sqrt(30)+5/sqrt(12))/L<7/L`. □

Это настоящая безусловная подписанная компенсация: равенство (11) использует точные mu*1 и mu*log, а не сумму модулей mu. Но нормы (13) — аддитивные L2-нормы, НЕ E_N и НЕ H_N. Такое различие нельзя убрать словом «изометрия».

## 5. Точный возврат: рациональный котангенсный функционал

[FINITE_CELL | PAPER.]

Для функций с заданными значениями в рациональных точках определим

    L_N(f)=sum_(k=2)^N (q_k/k)
                  sum_(r=1)^(k-1) cot(pi*r/k) f(r/k). (14)

Это конечный signed functional; обозначение L_N не означает интеграл Лебега или ограниченный оператор на L2. Для F_N из (10) значения фиксируются midpoint-конвенцией.

Утверждение для всех N>=3:

    E_N = B_N - pi L_N(F_N),
    B_N=2b_N(1+u_N)-s_N.                             (15)

На S имеем независимую оценку

    |B_N|<=36/L.                                     (16)

**Доказательство (15).** Для общих h,k конечная сумма с неприведённым отношением удовлетворяет

    sum_(r=1)^(k-1){rh/k}cot(pi*r/k)
                       =(h,k)V((h/(h,k))/(k/(h,k))).

Это cotangent multiplication identity после группировки r по приведённому знаменателю. Заменить fractional part на B_1 можно внутри полной cotangent-суммы: постоянная часть и поправки в целых точках взаимно уничтожаются при r <-> k-r.

Кроме того, для k>=2

    sum_(r=1)^(k-1)cot(pi*r/k)sin(2*pi*r/k)=k-2.

Поэтому из (5),(10),(14)

    L_N(F_N)=T_N+(sum_(k=2)^N q_k-2sum_(k=2)^N q_k/k)/pi
            =T_N+(2b_N-1-s_N)/pi.

Подстановка в (6) даёт (15). Оценка (16) следует из (2),(3): `2|b|(1+|u|)+|s|<=36/L`. □

**Граница результата.** (13) оценивает всю положительную Fourier-энергию, (15) возвращает весь исходный объект. Но для завершения нужна оценка L_N именно на F_N. Она не следует из (13).

## 6. Строгий судья попытки оплатить возврат одной L2-нормой

[ABSTRACT / COFINAL_FAMILY | PAPER.]

Положим R_N(0)=1, в согласии с буквальной формулой (1). Для целого ell>=1 стандартная конечная cotangent-идентичность равна

    sum_(r=1)^(k-1)cot(pi*r/k)sin(2*pi*ell*r/k)
       = k-2(ell mod k), если k не делит ell;
       = 0, если k делит ell.

Через исходные остатки она даёт

    L_N(sin(2*pi*ell*x))=2b_N-R_N(ell)-R_N(ell-1).     (17)

Например, `R_N(1)=s_N`, так что

    L_N(sin(2*pi*x))=2b_N-1-s_N.                      (18)

У самого F_N sine-коэффициент номера ell равен

    [1_(ell=1)-sum_(n|ell,n<=N)q_n]/(pi*ell).          (19)

Таким образом signed sampling возвращает не независимый случайный шум, а полные исходные остатки. Подмена (19) одними их модулями теряет нужную арифметику.

### Теорема 2: точное aliasing-препятствие на настоящем S

Зафиксируем N in S с log N>=12 и Q=lcm(1,...,N). Для любого J>=1 положим

    f_(N,J)(x)=sqrt(2/J)sum_(j=0)^(J-1)
                              sin(2*pi*(1+jQ)*x).

Все частоты — обычные целые. По ортогональности ||f_(N,J)||_2=1. В КАЖДОЙ рациональной точке r/k, k<=N, все слагаемые совпадают, поэтому

    L_N(f_(N,J))=sqrt(2J)(2b_N-1-s_N)
                <=-sqrt(J/2).                       (20)

Последнее использует `2b_N-1-s_N<=-1+6/L<=-1/2` из (2),(3).

Следовательно не существует даже конечной, зависящей от этого N константы C_N, для которой `L_N(f)>=-C_N||f||_2` для всех тригонометрических полиномов. Для предполагаемой C_N строгая верхняя огибающая margin равна

    C_N||f_(N,J)||_2+L_N(f_(N,J))
                            <=C_N-sqrt(J/2)<0         (21)

при достаточно большом J. Масштабирование на 7/L сохраняет тот же counterexample с norm <=7/L. □

Свидетель НЕ меняет mu, q_N, свёртку, S или исходный источник. Он меняет только пробную функцию в проверяемой all-input операторной оценке. Он **не равен настоящему F_N**. Поэтому KILL_SCOPE — THEOREM_SHAPE общей L2-оценки (14), не запрет bound на L_N(F_N). Формула (20) также объясняет, почему малая Fourier-норма не оплачивает автоматически значения на возрастающей рациональной сетке.

## 7. Попытка закончить знак и точная остановка

[COFINAL_FAMILY | CONDITIONAL для missing bound; PAPER для стрелок.]

Единственная неоценённая величина в (15) — signed trace настоящего F_N. Требуется

    exists C>=0:
      {N in S : L_N(F_N)>=-C} is unbounded.            (22)

Это не объявляется новым более слабым условием. По (3),(15),(16) оно эквивалентно прежней bounded-core посылке R8 на S. Если (22) выполнено, `E_N<=pi C+36` на выбранной последовательности. Обратно, из H_N<=B на S следует
`L_N(F_N)>=-(B+42)/pi`.

Проверенные подходы к (22): полная gcd-перегруппировка (8), конечная reciprocity (9), совместная Fourier-конволюция (11) и точный sampling-return (17)-(19). Они не дали source-specific нижнего bound в (22). Отдельные оценки модулей и (13) его не дают; §6 исключает именно последний общий shortcut. Точный ряд (19), напротив, не запрещён и остаётся доступным для совместной оценки.

Безусловный старый bound `H_N<=290N/L^2` R8 на S вместе с (3) даёт лишь

    L_N(F_N)>=-[36/L+(290N+6)/L^2]/pi,

а не константу. Это верхняя цена возможного ущерба, не доказательство ложности (22). **Нового unconditional NB-rate, bounded core или signed Weil floor здесь нет.**

### Полный conditional receiver к RH

Для фиксированного k и N>=k исходная свёртка даёт

    R_N(k)=k s_N-psi(k)/L ->0.

При (22) остатки ограничены по норме и сходятся поточечно к нулю в H=ell^2(1/[k(k+1)]), значит слабо сходятся к нулю. Выбираем подпоследовательность с попарными inner products по модулю <=2^(-i-j). Если B=pi C+36, её J-членное среднее имеет норму в квадрате <=B/J+1/J^2. Оно остаётся допустимым NB-приближением, следовательно e_N->0.

Точная изометрия на интервалы (1/(k+1),1/k] и Mellin-формула обычных остатков дают

    int_0^1 Jr_n(x)x^(s-1)dx=zeta(s)(1/n-n^(-s))/s.

В любом правом нуле rho=beta+i gamma получаем

    e_N >= (2beta-1)/|rho|^2 >0,

по Cauchy–Schwarz в L2(0,1). Это противоречит e_N->0. Функциональное уравнение исключает левые нули. Поэтому (22) => RH, но **(22) не доказано**. Дополнительные гипотезы о простоте нулей здесь не нужны.

Возврат к буквальному A_m не меняется: после capture можно достигнуть e_N<=1/m и применить R7-bridge с дефектом 36000(1+log m)^3G_m; либо использовать полную Weil-формулу после RH. Это глобальные conditional стрелки, не вывод из одной конечной проверки.

## 8. Собственные источники отрицательных миров и положительный контроль

[ABSTRACT | PAPER с inherited source-controls R8/R9.]

**R9 counterarray.** В первом изменённом индексе нарушается `sum_(d|n)mu(d)=1_(n=1)`. Поэтому (11) с настоящей Lambda уже неверно. Это именованный разрыв точной арифметики, а НЕ утверждение, что всякий такой counterarray обязан нарушать численный bound 7/L: слабая аддитивная норма может пропустить некоторые изменённые массивы.

**DMV.** Свободный мультипликативный моноид не даёт обычные integer harmonics B_1(nx), обычные интервалы (1/(k+1),1/k] и то же Mellin-равенство. Подстановка generalized primes в этот словарь не представляет его Z_B. Разрыв — additive source-match. Любой source-correct null-Mellin repair имеет положительный evaluation lower bound в собственном правом нуле, поэтому не может одновременно иметь bounded pointwise-zero capture. Completion DMV не выдумывается.

**DH.** Полный источник сохраняет его коэффициенты, odd-Gamma, conductor 5 и отсутствие полюса. Обычная mu не является Dirichlet inverse DH; (11) с обычной Lambda и NB source-match относятся к другой функции. Его собственный правый нуль препятствует source-correct capture той же evaluation-оценкой.

**Квартет a=1/3.** При стандартной Gamma изменённый uncompleted фактор Q(s-1/2)zeta(s)/Q(1/2) не имеет старого Mellin-словаря. Его Q'/Q нельзя удалить из Weil-source. Source-correct null-словарь чувствует planted rho=5/6+i gamma и имеет положительный остаток.

**Самодуальные v_b R6 B.** Здесь обычная zeta и mu могут остаться прежними. Тогда (4)-(22), включая reciprocity и маленькую Fourier-норму, действительно могут остаться теми же. Нельзя выдумывать отказ самой reciprocity. Ломается последний completion link: требуется точно

    Mellin[exp(-pi x^2)](s)=Gamma(s/2)pi^(-s/2)/2,
    xi(s)=s(s-1)Gamma(s/2)pi^(-s/2)zeta(s)/2.

У v_b Mellin-фактор умножен на Q_b; дополнительные нули принадлежат ему, а не обычной zeta. Generic Poisson/self-duality их не удаляет.

**Кривая над F3.** Для её собственного h=log3 и antiperiodization

    (Per f)(x)=sum_(j in Z)(-1)^j f(x+2hj), 0<=x<2h,
    W_E[f]=2h int_0^(2h)|Per f(x)|^2 dx
          =sum_(j in Z)|fhat((j+1/2)pi/h)|^2>=0.

Это точный source-return с нулевым дефектом, по Parseval; на каждом компактном окне число перекрытий конечно. Обычный mu-словарь кривой не приписывается. Этот положительный контроль не выдаётся за завершённое доказательство (22) для Q.

## 9. Проверка нормировок в литературе

[ABSTRACT | PAPER для следующих элементарных тестов.]

1. В T1 используется `V(a/b)=sum {ra/b}cot(pi r/b)`. В просмотренной T2 p.2 напечатано cot(pi*r*a/b) при том же fractional part. Для coprime a,b последнее выражение после перестановки r не зависит от a. При b=3 правильные V(1/3)=-1/(3sqrt3), V(2/3)=+1/(3sqrt3); выражение с обоими a даёт одно значение. Поэтому оно не подставлялось в (4). Это literal normalization issue данной копии, не опровержение намеренной теоремы авторов.

2. При обычной fractional part буквальный ряд `sum_(l>=1)(1-2{l a/b})/l` расходится для rational a/b. Сумма числителей за период b равна 1; следовательно частичная сумма равна `(log M)/b+O_b(1)`. Fourier/midpoint convention или finite part должны задаваться отдельно. В нашей работе используются конечная V и явно определённая B_1; неформальное g(h/k) не импортируется.

3. У напечатанного определения C в T2 Theorem 2.1 одновременно стоят `C>=phi=(1+sqrt5)/2` и `2C-log C-1-(5/2)log2=0`. Эти literal условия несовместимы. Функция слева строго возрастает при C>=phi. Из phi>809/500, log phi<241/500 и log2<347/500 следует её значение в phi>19/1000. Логарифмические bounds проверяются рациональными нижними Taylor-суммами exp, а bounds на phi — возведением в квадрат. Поэтому конкретный numerical saving exponent из этого дисплея не используется.

Целевой поиск не дал исправления, которое разрешило бы импорт именно этих буквальных формул. Отсутствие найденного erratum не названо доказательством отсутствия исправления вообще. Даже корректный unbalanced-range theorem потребовал бы отдельного переноса к общим gcd-весам (8) и balanced pairs; такого переноса здесь не доказано.

## 10. Проверки и судьба предсказаний

[FINITE_CELL | PAPER для точной алгебры; floating checks — DIAG.]

Точно проверены mu*1 на n<=128, gcd-факторизация и congruences `(1+jQ)r=r mod k`. Проверены рациональными вычислениями constants в §4 и §9. При 50/80 десятичных знаках независимая периодическая residue-сумма с digamma-весами совпала с Vasyunin-Gram для всех h,k<=12: максимальная ошибка соответственно <3.1e-51 и <1.6e-81. Это проверки нормировок, не интервальные сертификаты.

Для N=3,8,16,32,64 проверены (6),(8),(15), положительный Gram (10) и sine-action (17). Независимый прямой period-residue возврат для (15) вычислялся при N<=16; остальные сравнения использовали уже проверенный Gram. Euclid-итерация проверена для coprime a<b<=30; поскольку period samples в этом тесте вычислялись через ту же конечную c0, это проверка ориентации/телескопирования, не независимый аудит T1.

| N | E_N, DIAG | ||F_N||_2 log N, DIAG | L_N(F_N), DIAG |
|---:|---:|---:|---:|
| 3 | 0.767783886938 | 0.204946534261 | 0 exactly |
| 8 | 0.313172950035 | 0.241602262260 | -0.0374563477294 |
| 16 | 0.184522364000 | 0.249758418407 | -0.0475225790688 |
| 32 | 0.121694611637 | 0.253666446359 | -0.0492646389042 |
| 64 | 0.0864678566738 | 0.255681683682 | -0.0465795771828 |

Нулевая строка N=3 доказана точно: a_3=0, а единственный оставшийся cot(pi/2)=0. Decimal near-zero не используется как доказательство. Ни один из этих N не выдаётся за измерение на S или cofinal тест.

P1 — HIT: (6), правильные знак и gcd. P2 — HIT: |u_N|<=30. P3 — HIT для gcd-перегруппировки; предположение о сохранении mu modular inversion отвергнуто точным примером 2->4 mod7. P4 — HIT как normalization audit. P5 — нижняя оценка истинного signed trace NOT_PROVED; reciprocity не объявлена запрещённым маршрутом. Fourier-object §4 выведен после freeze внутри выбранного подхода; его дополнительная вычислительная проверка объявлена до запуска и не приписывается задним числом исходным P1-P5.

### Минимальный воспроизводимый контроль

Сохранить блок как verify_reciprocity.py и выполнить `uv run --with mpmath python verify_reciprocity.py`. N — длина словаря; в цикле заданы проверяемые значения, dps — рабочая десятичная точность. Код проверяет нормировки, не RH.

```python
import math
from functools import lru_cache
import mpmath as mp

def mobius(n):
    out = [1] * (n + 1)
    prime = [True] * (n + 1)
    out[0] = 0
    for p in range(2, n + 1):
        if prime[p]:
            for j in range(p, n + 1, p):
                prime[j] = False
                out[j] *= -1
            for j in range(p*p, n + 1, p*p):
                out[j] = 0
    return out

mu = mobius(64)
for dps in (50, 80):
    mp.mp.dps = dps
    C = mp.log(2*mp.pi) - mp.euler
    @lru_cache(None)
    def V(h, k):
        d = math.gcd(h, k)
        h, k = h//d, k//d
        return mp.fsum(mp.mpf((r*h) % k)/k * mp.cot(mp.pi*r/k)
                       for r in range(1, k))
    def J(h, k):
        d = math.gcd(h, k)
        return (C*(mp.mpf(1)/h + mp.mpf(1)/k)/2
                + mp.mpf(k-h)/(2*h*k)*mp.log(mp.mpf(h)/k)
                - mp.pi*d/(2*h*k)*(V(h,k)+V(k,h)))
    @lru_cache(None)
    def periodic_weight(p, r):
        return (mp.digamma(mp.mpf(r+1)/p)
                - mp.digamma(mp.mpf(r)/p))/p
    err = mp.mpf(0)
    for h in range(1, 13):
        for k in range(1, 13):
            p = math.lcm(h, k)
            direct = mp.fsum(mp.mpf((r % h)*(r % k))/(h*k)
                            * periodic_weight(p,r) for r in range(1,p+1))
            gram = J(h,k)-J(h,1)/k-J(1,k)/h+C/(h*k)
            err = max(err, abs(direct-gram))
    print('dps', dps, 'independent Gram error', mp.nstr(err, 5))
    for N in (3, 8, 16, 32, 64):
        L = mp.log(N)
        a = [mp.mpf(0)] + [mu[n]*mp.log(mp.mpf(N)/n)/L
                           for n in range(1,N+1)]
        s = mp.fsum(a[n]/n for n in range(1,N+1))
        b = 1+(mp.fsum(a)-s)/2
        u = mp.fsum(a[n]*mp.log(n)/n for n in range(1,N+1))
        q = a[:]
        q[1] -= s
        T = mp.fsum(q[h]*q[k]*math.gcd(h,k)/(h*k)*V(h,k)
                    for h in range(1,N+1) for k in range(1,N+1))
        norm2 = mp.fsum(q[h]*q[k]*math.gcd(h,k)**2/(12*h*h*k*k)
                        for h in range(1,N+1) for k in range(1,N+1))
        norm2 += (mp.mpf('0.5')-q[1])/mp.pi**2
        E = 1+2*b*u-mp.pi*T
        assert norm2 > 0 and norm2 <= 49/L**2
        print(N, mp.nstr(E,14), mp.nstr(mp.sqrt(norm2)*L,14))
```

## 11. Closeout, две допустимые репрезентации и K8A

Закрыты все N в (2),(7),(13),(15),(16), не только численная сетка. Но (13) относится к другой норме; существенная стрелка к (22) не закрыта. Поэтому PROOF_PROGRESS означает конечные/безусловные вспомогательные теоремы, а RH_SIGN_PROGRESS остаётся NONE. Простое новое имя для (22) не считается продвижением по исходной арифметической оценке.

**Репрезентация A:** сам полный signed trace (14) на точных Fourier-коэффициентах (19), возможно с Abel/Fejer regularization и отдельно оплаченной ошибкой снятия сглаживания. Kill-power высокий: aliasing §6 немедленно отвергает norm-only bounds. Цена: средняя для конечной проверки, высокая для source-specific cofinal estimate. Такой estimate не предъявлен.

**Репрезентация B:** точная gcd-weighted reciprocity (8)-(9) с перенесёнными inverse-residue весами mu, без раздельной оплаты ветвей. Kill-power высокий против потери gcd/инверсии/знака; цена конечного расчёта примерно квадратичная по числу индексов до вычисления самих cotangent sums, аналитическая цена высокая. Никакой новый bound для balanced remainder не импортируется из unbalanced результатов.

Для §6: DOWNSTREAM_CONSUMER=контроль фактического signed trace; ORIGINAL_OBJECT_IS=NOT_NECESSARY для generic L2 operator bound; FAILURE_TYPE=COUNTEREXAMPLE; EPISTEMIC_STATUS=MATHEMATICALLY_DEAD только для общей оценки всех полиномов; REOPEN_TRIGGER=source-specific ограничение именно F_N, а не изменение константы общей L2-оценки.

Для (22): DOWNSTREAM_CONSUMER=RH; ACTUAL_CONSUMER_REQUIREMENT=source-correct bounded pointwise-zero residual subsequence; необходимость именно данного taper и S для RH UNKNOWN; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; REOPEN_TRIGGER=доказанная совместная нижняя оценка L_N(F_N), либо другая оценка оптимального NB/Weil consumer. Никакой смерти route-family не объявляется.

```yaml
iteration:
  target: TRUE_SIGNED_MOBIUS_CORE_AFTER_R10
  status: OPEN
  cognitive_operator_used: EXACT_RECIPROCITY_AND_ADDITIVE_FOURIER_DUALITY
  new_gap_name: ACTUAL_MOBIUS_ERROR_RATIONAL_TRACE_LOWER_BOUND
  invariant_learned: FULL_DIVISOR_CANCELLATION_GIVES_SMALL_ADDITIVE_L2_NOT_SMALL_NB_NORM
  forbidden_future_move: PASS_L2_LIMIT_THROUGH_UNBOUNDED_RATIONAL_SAMPLING
  next_decisive_test: CONTROL_THE_TRACE_USING_THE_ACTUAL_COEFFICIENT_RELATIONS_19
  route_score: 3
```

Записаны только новый freeze и этот новый вердикт под docs/routeB_bus/proshka; старые результаты, state-файлы и Lean не изменяются. Freeze commit/blob указаны в YAML. Final commit/blob и SHA256 локальной копии сообщаются в delivery receipt после remote readback; самореферентный hash в файл не вставляется. Численная диагностика не является независимым аналитическим аудитом. **RH: не доказана.**
