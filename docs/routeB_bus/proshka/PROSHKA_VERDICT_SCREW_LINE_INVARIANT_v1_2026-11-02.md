# STATUS: TRY_SCREW_LINE_SOURCE_MATCHED_PASSIVITY

```yaml
OPERATIVE_CLASS: TRY_SCREW_LINE_SOURCE_MATCHED_PASSIVITY
REQUEST: SCREW_LINE_INVARIANT_v1
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: 1c91c4c86ef6987782c08c84e22707d1b7324646
INBOX_PARENT_OBSERVED: 3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
WINDOW: L=log(m), N=m, PHYSICAL_L2, ORIGINAL_EVEN_CARRIER
RESULT: EXACT_SCREW_PULLBACK_AND_CONDITIONAL_PASSIVITY_LEMMA
SOURCE_SPECIFIC_POSITIVE_HAMILTONIAN: NOT_CONSTRUCTED
PRIME_HINGE_EQUALS_POSITIVE_CANONICAL_ATOM: REFUTED_AS_DIRECT_IDENTIFICATION
RH_JUDGE: CONDITIONAL_EXACT_GRAM_PASS_NO_EXTRA_SCALE_CREDIT
PLANTED_QUARTET_JUDGE: STRICT_NEGATIVE_UPPER_ON_ORIGINAL_CONSTANT_MODE
CONREY_LI_SHIFT_POSITIVITY: NOT_IMPORTED_AND_REJECTED
FINITE_GLOBAL_KREIN_INDEX_ASSUMED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS: SCOPED_FALSIFICATION_AND_EXPLICIT_PLANTED_WITNESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
VERIFIER: PAPER
INDEPENDENT_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NEW_CCM_EIGENPROBLEMS: 0
FLOATING_CHECK_PRECISIONS: [45,75]
RH_PROVED: false
ROUTE_PROMOTION: false
WRITE_SCOPE: docs/routeB_bus/proshka/
```

Ы. Получено точное представление исходного A_m через screw-kernel с сохранёнными граничными массами. Доказана одна лемма о сохраняемом матричном инварианте. Однако принадлежность действительного арифметического продолжения положительному классу этой леммы не доказана. Удары g' в log(p^k) нельзя просто объявить положительными каноническими массами: их прямой Gram-вклад неопределён. Это не опровержение возможности иной, нелокальной канонической реализации ζ.

## 1. Фиксированный словарь и граница импорта

[S1] Suzuki, arXiv:2206.03682v4, (1.1)–(1.9), Theorems 1.2–1.4, Proposition 3.1. [S2] arXiv:2209.04658v3, (1.10), Theorem 1.2, Corollary 1.2. [S3] arXiv:1204.1827v2, (2.1)–(2.6), Theorem 2.3, Lemmas 4.2–4.5, §5. [S4] Conrey–Li, arXiv:math/9812166v1, §3.1. Формулы и нужные страницы PDF просмотрены, включая скриншоты. Текущий статус всей последующей литературы не классифицируется: разбор относится к указанным версиям.

[R1] f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf, `PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md`, §§2–5.
[R2] 3ce4968d7ae23390f65e6c62daa6c3cf2cf6960d: RH-case-split obstruction для ненормированного центрированного делительного lift. Его следствие о лишнем положительном вкладе наследуется, заново не доказывается.

Пусть Xi(z)=xi(1/2-iz), z_rho=i(rho-1/2). Во всех суммах ниже нули комплексные, со всеми кратностями. Используем g=-Psi из [S1], g(0)=0, и

    g(t)=sum_rho [cos(z_rho t)-1]/z_rho^2,
    K_g(s,t)=g(s-t)-g(s)-g(-t).
                                                        (1)

На компактах ряд для g и K_g сходится абсолютно: |Im z_rho|<1/2 и sum |z_rho|^-2<infinity. Это не утверждение об абсолютной сходимости дважды продифференцированного ряда. Без RH K_g является эрмитовым ядром, но не заведомо Hilbert-Gram. Именно глобальная положительность такого ядра является RH-критерием [S1].

## 2. Точный возврат A_m: дифференциальные меры, а не отсчёты линии

**[FINITE_CELL | PAPER; A/LA плюс исходная E/F-идентичность.]** Для нулевого продолжения оконной функции f положим

    mu_f = D(f 1_[-b,b])
         = f'_int(x)1_(-b,b) dx + f(-b) delta_-b - f(b) delta_b,
    b=L/2, L=log m.
                                                        (2)

Масса mu_f равна нулю. Для любого f,h из исходного конечного carrier:

    k(f,h) = integral integral K_g(s,t) d(conj(mu_f))(s) d(mu_h)(t).
                                                        (3)

Доказательство. В точном ряде

    K_g(s,t)=sum_rho (exp(i z_rho s)-1)(exp(-i z_rho t)-1)/z_rho^2

разрешён обмен с конечными BV-мерами, благодаря равномерной абсолютной сходимости. Распределительное интегрирование по частям даёт

    integral (exp(i z s)-1)/z d(conj(mu_f))(s)
        = -i conjugate(fhat(conjugate(z))),
    integral (exp(-i z t)-1)/z d(mu_h)(t) = i hhat(z).

Произведение даёт ровно полную Weil-форму из исходника, без 2pi, L или нового веса. Концы окна необходимы уже для постоянной моды.

Если phi_n — исходный физически ортонормированный базис, то

    (A_m)_jk = [mu_phi_j,mu_phi_k]_{K_g}.
                                                        (4)

Под RH можно взять x_gamma(t)=(exp(-i gamma t)-1)/gamma в l2 по реальным нулям с весами кратности. Тогда (3) равна Hilbert-норме integral x(t) dmu_f(t). Без RH остаётся (3), но не право заменить pairing абсолютными квадратами. A_m — Gram линейных функционалов от отрезка линии, НЕ матрица K_g(omega_j,omega_k).

Особенно полезная проверка, действительная без RH:

    phi_0=L^-1/2 1_[-L/2,L/2],
    <phi_0,A_m phi_0> = -2g(L)/L.
                                                        (5)

Она следует из двух endpoint-масс в (2). Прямой arithmetic-return этой формулы проверен при m=2,4,8; все prime powers и полюс сохранены.

## 3. Что именно является числом отрицательных квадратов

**[FINITE_CELL | PAPER; LA.]** n_-(A_m) — отрицательный индекс K_g на конкретном пространстве мер {mu_f:f in V_m}. Он не обязан равняться максимальному индексу K_g на всех тестах и всех окнах.

Для усечённой нулевой формы из [R1] остаётся точная конгруэнция

    A_<T=E_T^* Jcal_T E_T.

На вещественном чётном carrier критическая пара кратности nu даёт [2nu]; комплексная четверка даёт diag(4nu,-4nu). Если активные evaluation-строки независимы, n_-(A_<T)=n_-(Jcal_T). Одна четверка даёт одно отрицательное направление в чётном секторе, не nu таких направлений. В полной неограниченной тестовой системе число отрицательных квадратов может быть бесконечным; глобальный класс N_kappa с фиксированным конечным kappa здесь не предполагается.

При положительном пороге mu индекс из [R1] иной. Для блоков A=[[D,B*],[B,G]] относительно J+J-perp и mu>lambda_max(D):

    N_A(mu)-dim J = n_-(G-mu I+B(mu I-D)^-1 B*).
                                                        (6)

В нулевых координатах сохраняются полный хвост, пороговая метрика и поправка исключения J. Называние этого индекса «Крейн–Лангер» не удаляет ни одного из трёх членов. Для сжатия J-perp в (3) просто берутся меры соответствующих линейных комбинаций phi_n.

## 4. ОДНА ЛЕММА: каноническая пассивность с потоками и ударами

**[ABSTRACT | PAPER; LA/A.]** Обозначим J0=[[0,-1],[1,0]]. Пусть между ударами фундаментальная матрица M(t,z), M(t0,z)=I, удовлетворяет

    J0 dM/dt = z H(t) M,
    H(t)=H(t)^* >=0,
                                                        (7)

где H вещественна и локально интегрируема. В момент t_n задан rank-one удар

    M(t_n+,z)=S_n(z) M(t_n-,z),
    S_n(z)=I-z J0 W_n,
    W_n=alpha_n v_n v_n^T, alpha_n>=0, v_n real.
                                                        (8)

На каждом конечном отрезке сначала предполагается конечное число ударов; предельный случай разрешён лишь при сходимости форм и transfer-матриц. Тогда при Im z=y>0 сохраняется инвариант

    I(t,z):=[M(t,z)^* J0 M(t,z)-J0]/(2iy) >=0.
                                                        (9)

Точнее,

    I(t,z)=integral_t0^t M(s,z)^* H(s) M(s,z) ds
           +sum_(t0<t_n<=t) M(t_n-,z)^* W_n M(t_n-,z).
                                                        (10)

Доказательство. Из M'=-z J0 H M и J0^2=-I получаем

    (M* J0 M)'=2iy M* H M.

Для (8) W_n J0 W_n=0, поэтому точно

    S_n* J0 S_n-J0=2iy W_n.

Интегрирование и телескопирование дают (10), а каждый его член положителен. Для произвольного согласованного удара вместо (8) достаточно матричного условия (S_n*J0 S_n-J0)/(2iy)>=0. Общее full-rank атомное H нельзя без проверки заменить формулой I-z J0 H.

Связь с кругами Вейля. При вещественном self-adjoint terminal-условии, Y(t0)=(1,q(z)) и нулевом terminal J0-потоке, та же формула даёт

    Im q(z)=y integral Y* H Y + y sum Y_-* W_n Y_- >=0.
                                                        (11)

В обычной невырожденной реализации это Herglotz-свойство Weyl-функции; геометрически соответствующие круги Вейля вложены. Неподтверждённый scalar radius не вводится.

**Граница леммы.** (7)–(10) доказывают сохранение, если H и W_n уже получены из источника и имеют указанный знак. Это не доказательство знака действительного H_zeta. Нужен также точный supplier Weyl-функции, а не произвольная положительная система.

Для нашей Xi требуемая функция:

    Q_zeta(z)=-Xi'(z)/Xi(z)=i xi'/xi(1/2-iz).
                                                        (12)

Нужна analytic source-matching, включая нормировку и отсутствие потерянных полюсов. В силу (1) и [S1], принадлежность именно (12) классу Herglotz эквивалентна требуемой глобальной положительности. Таков точный неоплаченный вход, а не новый доказанный инвариант ζ.

## 5. Почему изломы log(p^k) ещё не 2x2 канонические удары

**[ABSTRACT/FINITE_CELL | PAPER; E/I для веса, LA/A для расчёта.]** Один арифметический член в g имеет вид

    g_n(t)=c_n (|t|-a_n)_+,
    a_n=log n, c_n=Lambda(n)/sqrt(n)>0.
                                                        (13)

Следовательно, g' имеет положительный скачок c_n. Но при L=a_n+epsilon, 0<epsilon<a_n, и t_±=±L/2, его двухточечное screw-ядро равно

    [K_gn(t_i,t_j)] = [[0,c_n epsilon],[c_n epsilon,0]].
                                                        (14)

На (1,-1) оно имеет значение -2c_n epsilon<0. На исходной нормированной постоянной моде это точно -2c_n epsilon/L: обычный отрицательный prime-atom полной Weil-формы. Никакой «положительный Gram increment» не возник.

Таким образом, опровергнута только ПРЯМАЯ идентификация положительного scalar скачка g' с положительным вкладом канонической массы. (14) само по себе не запрещает нелокальную реализацию после взаимодействия с прежним kernel; вывод о смерти всей canonical-route отсюда был бы неверен.

На t>0 вне атомов непосредственно из определения g:

    g''(t)=j(t)-2 cosh(t/2),
    j(t)=exp(-t/2)/(1-exp(-2t)),
    Delta g'(a_n)=c_n.
                                                        (15)

Это аффинная система для (g,g'), а не заданная спектральная каноническая система. Точный локальный homogeneous lift действует на (g,g',1): генератор имеет строки (0,1,0),(0,0,j-2cosh),(0,0,0), удар равен I+c_n E_23. Требуемые source-matched 2x2 матрицы из (15) не следуют. В точке 0 нужна исходная регуляризация; (15) не заменяет её.

## 6. Два судьи: RH и одна посаженная четверка

### 6.1. RH-ветка, включая ограничение 3ce4968

**[COFINAL_FAMILY | CONDITIONAL: RH; algebra PAPER.]** Под RH:

    Im Q_zeta(x+iy)/y = sum_gamma nu_gamma/|gamma-(x+iy)|^2 >=0,
    k[f]=sum_gamma nu_gamma |fhat(gamma)|^2.
                                                        (16)

Ряд Q понимается симметрично; ряд для мнимой части абсолютно сходится. В (3) нет вычитания ненормированного делительного Gram и нет постулированного дополнительного положительного кредита порядка log^2 m. Поэтому именно obstruction [R2] не воспроизводится: (3) — точное равенство исходной формы, а не новая majorizing-форма. Это условный контроль корректности представления, не предпосылка доказательства RH.

### 6.2. w-мир: точный отказ и на Weyl-стороне, и внутри A_m

**[COFINAL_FAMILY | PAPER under the explicitly specified RH baseline.]** Пусть Xi_0 — RH-baseline (можно взять действительную Xi в условной RH-ветке), а

    Xi_w(z)=Xi_0(z) [(z^2-w^2)(z^2-conj(w)^2)]^nu,
    w=gamma+i eta, gamma>eta>0, nu>=1.
                                                        (17)

Это сохраняет real-even симметрию, но не заявляется ζ с тем же Euler product. Добавка к g гладкая, поэтому расположение и размеры старых prime-изломов не меняются; гладкая часть источника меняется.

Положим B0=2 sum_(real zeros of Xi_0) nu_gamma/gamma^2<infinity. Тогда -B0<=g_0(t)<=0, а

    g_w(t)=g_0(t)+4nu Re[(cos(wt)-1)/w^2].
                                                        (18)

Выберем gamma=2pi/log 2 и 0<eta<1/2; m_k=2^k, L_k=k log2. Здесь gamma L_k=2pi k. При

    a_w=Re(1/w^2)=(gamma^2-eta^2)/(gamma^2+eta^2)^2>0

получаем исходный чётный единичный trial phi_0 и строгий upper:

    <phi_0,A_mk^w phi_0>
      =-2g_w(L_k)/L_k
      <= [2B0-8nu a_w(cosh(eta L_k)-1)]/L_k
      -> -infinity.
                                                        (19)

Это настоящий отрицательный upper, а не отсутствие lower bound. Все исходные N=m_k и обе границы удержаны. На этих ячейках чётная форма имеет ровно одно отрицательное направление: положительный baseline плюс четверка имеет negative rank <=1, а (19) даёт >=1. Никакая реальная off-line четверка ζ здесь не утверждается.

На Weyl-стороне Q_w=Q_0-nu P_w'/P_w. В верхней точке z=w-i epsilon:

    Im Q_w(z)=-nu/epsilon+O(1)<0

при достаточно малом epsilon>0. Строгий бюджет: на диске, не содержащем других полюсов, пусть |regular part|<=M; при epsilon<min(radius,nu/(2M)) имеем upper <=-nu/(2epsilon). Herglotz-инвариант обязан сломаться.

Точный конечный контроль без baseline: w=1+i/4, z=1+i/8, P_w=z^4-15z^2/8+289/256 даёт

    Im[-P_w'(z)/P_w(z)]=-1077536/204315<0.
                                                        (20)

Таким образом, обе стороны одного и того же source-matched инварианта действительно распознают посаженную четверку.

## 7. Где именно находится барьер Suzuki в наших координатах

Параметры нельзя смешивать: t=log a — длина канонического развития; omega — СДВИГ СПЕКТРАЛЬНОГО АРГУМЕНТА. В наших обозначениях

    Theta_omega(z)=Xi(z-i omega)/Xi(z+i omega).
                                                        (21)

Увеличение t при omega>1 не приближает omega к нулю.

Из [S3] используются ровно следующие факты. h_omega(x)=x^-1 sum_(n<=x)c_omega(n) g_omega(n/x), где c_omega(n)=n^omega product_(p|n)(1-p^-2omega). Особенность g_omega у 1 имеет порядок (1-x)^(omega-1): непрерывность при omega>1, L2-порог omega>1/2. Для omega>1 построен Hamiltonian diag(d(a)^-2,d(a)^2), d(a)=det(I+H_omega,a)/det(I-H_omega,a); обратимость оплачена. В диапазоне (1/2,1] остаются регулярность/детерминанты; при 1/2 теряется Hilbert–Schmidt; ниже 1/2 дополнительно не доказана innerness. Это три разных препятствия, не один «барьер omega>1».

Точный unitary dictionary, выведенный здесь: x=exp u, F(x) -> exp(u/2)F(exp u) переводит Hankel-kernel h_omega(xy) в

    k_omega(u+v)=exp((u+v)/2) h_omega(exp(u+v)).
                                                        (22)

Для a=exp b=sqrt m сжатие на x<a эффективно живёт на [-b,b], потому что k_omega(u+v)=0 при u+v<0. Новые особенности входят на u+v=log n при L=log n, но теперь n — ВСЕ целые с c_omega(n), а не только prime powers. Это другой оператор, не A_m. Совпадение окон не доказывает изометрию форм.

При omega>1 даже посаженный мир проходит innerness-судью: если omega>eta, все корни P_w(z+i omega) лежат снизу, а P_w(z-i omega)/P_w(z+i omega) — конечный inner-фактор. При RH-baseline произведение с Theta_omega^0 тоже inner. Но при 0<omega<eta/2 знаменатель имеет непогашенный верхний полюс z=w-i omega. Поэтому развитие по t при безопасном omega не обнаруживает скрытую четверку.

Чтобы добраться до (12), нужна ещё малая omega:

    Q_omega(z)=(i/omega)(1-Theta_omega(z))/(1+Theta_omega(z))
        -> -Xi'(z)/Xi(z)
                                                        (23)

локально вне нулей. Если все эти source-functions для omega downarrow0 являются Herglotz, соответствующее положительное продолжение действительно исключает верхние полюсы. Именно этот независимый от RH supplier пока не получен. Прямая локальная сохранность (10) его не заменяет.

## 8. Conrey–Li: какой именно сильный инвариант нельзя использовать

[S4] опровергает не все positive-H канонические системы, а дополнительную положительность комплексного сдвига в H(E), E(z)=xi(1-iz)=Xi(z+i/2): Re<F,F(.+i)>_{H(E)}>=0 на его области. Для нашего Fourier-знака сдвиг F(z+i) соответствует умножению физического теста на exp(x), но норма H(E) содержит вес |Xi(t+i/2)|^-2 и не является исходной L2-нормой. Не всякий оконный тест принадлежит H(E); данный перевод применяется только при членстве в обеих нужных областях.

Точный диагностический объект из [S4, (3.4)]:

    Re[xi(1+282i)/xi(2+282i)]
      =-0.0001319572933720834407131353022886181415496...
                                                        (24)

Он отрицателен в опубликованном контроле и воспроизведён здесь при 45/75 dps. Это не новая interval-сертификация. Подмена (9) требованием положительности такого сдвига проваливает RH-ветку: она требует более сильное свойство, уже нарушенное действительной ζ. Положительный canonical H при omega=1/2 этим не опровергается.

## 9. Что именно осталось и что не следует объявлять закрытым

Минимальный SOURCE_MATCHED_PASSIVITY contract:

    Construct from the original arithmetic source H and transfer data;
    prove H>=0 and every jump J-positive on every finite interval;
    prove that the resulting Weyl function is exactly Q_zeta,
    OR obtain the correctly normalized family Q_omega for omega downarrow0.

Ни определение H через неизвестный положительный square root, ни восстановление H из предполагаемо Herglotz Q не поставляют этот контракт: это круг.

Альтернатива без 2x2-догадки — продлевать точное K_g. Для любого конечного старого Gram K>=0 и нового блока [[K,b],[b*,d]] правильный критерий:

    b in ran K,       d-b* K^dagger b >=0.
                                                        (25)

При K>0 это обычный Schur-комплемент. В (25) b зависит от всего прежнего g, не только от одного prime-скачка. Это точный дискриминатор локальной идеи, не доказанный кофинальный знак.

| Представление | Дискриминатор | Сила / стоимость |
|---|---|---|
| Полное screw-kernel расширение | Нижний envelope Schur-дефекта (25), со range-guard; отрицательный upper опровергает конкретный шаг | 9/10 / 3/10 finite, кофинальный знак отдельный |
| Source Hankel-resolvent при малом omega | Контроль I±H_omega,a, determinant/regularity и точного Weyl-return; тест на посаженный полюс | 9/10 / 8/10 |

Нуль-согласованного float недостаточно: нужен полный interval Schur-bound либо точная факторизация; planted upper (19)/(20) служит обязательным отрицательным контролем.

DOWNSTREAM_CONSUMER: original CCM lower floor / Weil positivity.
ORIGINAL_OBJECT_IS: positive canonical realization is SUFFICIENT, not shown necessary for every admissible proof route.
FAILURE_TYPE: NO_DERIVATION for the arithmetic passivity supplier.
EPISTEMIC_STATUS: RESEARCH_DEBT; not route death.
SCOPED_KILL: direct raw-prime hinge = positive Gram increment, THEOREM_SHAPE only, evidence (14).
REOPEN_TRIGGER: nonlocal source-matched transfer map with actual local sign budget.
CLOSES: endpoint-safe screw pullback; normalization and index scope; planted-quartet discriminator.
OPENS: no new claimed mathematical supplier; SOURCE_MATCHED_PASSIVITY remains unpaid.

## 10. E/F/Z/LA/A/I and closeout

| Claim | Scope / verifier | Dependencies |
|---|---|---|
| (1) arithmetic screw and source identity | ABSTRACT / PAPER, inherited [S1] | E,F,A; Z for convergence |
| (2)–(5) exact finite-window return | FINITE_CELL / PAPER | LA,A; inherited source matching E,F |
| Finite negative-square count and (6) | FINITE_CELL / PAPER | LA; actual complex coordinates A, not count Z alone |
| Sole invariant lemma (7)–(11) | ABSTRACT / PAPER | LA,A; no E or F produces its sign hypotheses |
| Prime hinge and affine evolution (13)–(15) | ABSTRACT / PAPER | E,I for Lambda; LA,A for sign calculation |
| RH judge (16) | COFINAL_FAMILY / CONDITIONAL | RH explicitly, F,A,Z |
| Planted model (17)–(20) | COFINAL_FAMILY / PAPER conditional on specified baseline | A,F,LA; not original E |
| Suzuki small-omega source matching | ABSTRACT / CONDITIONAL at unpaid range | E,F,A,I; separate operator supplier needed |
| Conrey–Li exclusion | ABSTRACT / PAPER source audit; numerical replay diagnostic | A,LA; not RH assumed |

Предрегистрация до тестов: P1 endpoint-нормировка без лишних L/2pi; P2 indefinite prime hinge; P3 точный canonical flux; P4 нарушение planted invariant; P5 отрицательный ratio Conrey–Li; P6 никакого RH-вывода из конечных проверок. P1–P5 подтверждены в указанных областях; P6 соблюдён. Не зарегистрированный заранее дополнительный rational plant w=1+i/4 отмечен как дополнительный точный контроль, не как прежнее численное предсказание.

При 45/75 dps максимальные ошибки BV endpoint identity: 3.44e-46 / 2.85e-76; constant-mode full-source/screw identity: 1.41e-45 / 2.13e-75. Точные SymPy-проверки: flow flux, rank-one jump, negative prime block, quartet real-even symmetry; rational Pick value отрицателен. Новых CCM-спектров, Lean, Arb и независимых агентов не было.

Стратегическая память: не отождествлять атомы g'' с атомами H; не путать рост окна с уменьшением omega; не заменять shifted индекс сырым числом off-line четверок; не вносить Conrey–Li shift-positivity как более удобный invariant. Что стало точнее: цена source-matching и граница безопасного omega теперь отделены от линейной алгебры сохранения.

## CODEX DIRECTIVE

SCREW_SOURCE_MATCH_AUDIT: проверить (2)–(6), (10), (14), (19), (22)–(23) на исходных нормировках. Не строить новый CCM из произвольно выбранных positive 2x2 kicks. Для любого предложенного source transfer предъявить его Weyl-function и проверить оба судьи: RH exact Gram без лишнего положительного кредита и planted quartet negative upper. Независимый аудит должен отдельно отметить, что совпадение порогов L=log n не отождествляет Hankel operator (22) с Weil operator A_m. Успех аудита тождеств не повышает SOURCE_MATCHED_PASSIVITY и RH.

## Delivery and sources

Один новый Markdown в `docs/routeB_bus/proshka/PROSHKA_VERDICT_SCREW_LINE_INVARIANT_v1_2026-11-02.md`, ветка `proshka_inbox_2026-10-31`. Commit SHA и проверка remote blob сообщаются после записи отдельно. Старые вердикты, rh_clean, Lean и route-state не изменяются. Запись документа означает доставку PAPER-вывода, не kernel verification; axiom profile неприменим.

Primary sources:
- Suzuki, https://arxiv.org/abs/2206.03682v4
- Suzuki, https://arxiv.org/abs/2209.04658v3
- Suzuki, https://arxiv.org/abs/1204.1827v2
- Conrey–Li, https://arxiv.org/abs/math/9812166
- Rovnyak–Sakhnovich, definition of finite negative-square classes: https://journals.uwyo.edu/index.php/ela/article/view/235

Предел результата: ни глобальная положительность K_g для действительной ζ, ни её положительный source-Hamiltonian, ни RH здесь не доказаны. Доказаны точный оконный словарь, условная лемма сохранения, два явных отрицательных upper и корректные границы применения цитированных методов.

### Минимальное воспроизведение ключевых судей

Сохранить блок как `screw_checks.py`; выполнить `uv run --with sympy --with mpmath python screw_checks.py`. z — спектральная переменная, y>0 — её мнимая часть; H — произвольная вещественная симметричная матрица. Код проверяет тождества, не доказывает H_zeta>=0.

```python
import sympy as s
import mpmath as mp
J = s.Matrix([[0, -1], [1, 0]])
x, y, a, b, c, alpha, v1, v2 = s.symbols(
    'x y a b c alpha v1 v2', real=True)
z = x + s.I*y
H = s.Matrix([[a, b], [b, c]])
B = -z*J*H
assert s.simplify(B.conjugate().T*J + J*B - 2*s.I*y*H) == s.zeros(2)
v = s.Matrix([v1, v2]); W = alpha*v*v.T
S = s.eye(2) - z*J*W
assert s.simplify(S.conjugate().T*J*S - J - 2*s.I*y*W) == s.zeros(2)
q = s.symbols('q', positive=True)
A = s.Matrix([[0, q], [q, 0]]); u = s.Matrix([1, -1])
assert (u.T*A*u)[0] == -2*q
z = s.symbols('z'); w = 1 + s.I/4
P = (z*z-w*w)*(z*z-s.conjugate(w)**2)
Q = -s.diff(P, z)/P
assert s.simplify(s.im(Q.subs(z, 1+s.I/8))) == -s.Rational(1077536, 204315)
for dps in (45, 75):
    mp.mp.dps = dps
    def xi(s0):
        return s0*(s0-1)*mp.pi**(-s0/2)*mp.gamma(s0/2)*mp.zeta(s0)/2
    r = mp.re(xi(1+282j)/xi(2+282j))
    assert r < 0
    print(dps, mp.nstr(r, 40))
print('Exact controls passed; Conrey-Li replay is non-interval. No RH claim.')
```
