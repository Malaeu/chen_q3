# STATUS: TRY_RANK_TRACE_CCM_FULL_TAIL_RETURN

```yaml
OPERATIVE_CLASS: TRY_RANK_TRACE_CCM_FULL_TAIL_RETURN
REQUEST: CLAUDE_LAMZOURI_RANK_TRACE_IN_LITERAL_CCM
DATE: 2026-11-04
AUTHORITY: DIRECT_OWNER_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: rh_clean@cdb84497
INBOX_SOURCE_PIN: 75afd6a1f8e244f1da55e4c608233b22cc07c9f4
INBOX_HEAD_OBSERVED: 283176cd5262d8be89a86b1737079afeb67d5736
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
CARRIER: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
PRIMARY_CLAUDE_PDF: READ_RELEVANT_DEFINITIONS_LEMMAS_AND_ERROR_BUDGETS
ALPOGE_FURMAN_FULL_PAPER: NOT_RETRIEVED
LAMZOURI_FULL_PAPER: NOT_RETRIEVED
EXTERNAL_HEADLINE_PROPORTIONS: NOT_INDEPENDENTLY_ESTABLISHED_IN_THIS_VERDICT
RANK_TRACE_LEMMA: REPROVED_WITH_EXPLICIT_NONNEGATIVE_SLACK
SOURCE_TRACE_AND_FROBENIUS: EXACT_ALL_PRIME_POWERS_GAMMA_AND_POLE
ZERO_COUNT_TRANSFER: EXACT_WITH_EXPLICIT_FULL_TAIL_PAYMENT
NEW_POSITIVE_ZERO_PROPORTION_FOR_LITERAL_CCM: NOT_PROVED
ABSOLUTE_TAIL_BUDGET_RESULT: THIS_BUDGET_GIVES_EVENTUALLY_TRIVIAL_COUNT_LOWER_BOUNDS
QUIET_BLOCK_RESULT: NO_LEADING_GAIN_FROM_DELETION_ALONE
UNIVERSAL_0_68185_CCM_CEILING: NOT_CLAIMED
DENSITY_ONE_EQUALS_NO_OFF_LINE_ZEROS: false
EXACT_COFINAL_NO_OFF_LINE_ZEROS_EQUIVALENT_RH: true
TRACE_LEMMA_SEPARATOR_IS_SUPPLIED: false
VERIFIER: PAPER
NUMERICAL_CHECKS: DIAG_NOT_INTERVAL
EXACT_CONTROL_GROUPS: 12
SOURCE_CHECK_CELLS: [3, 8]
SOURCE_CHECK_DPS: 55
GAUSS_ORDERS: [24, 32]
NEW_ZERO_CENSUS: false
NEW_CCM_EIGENSYSTEMS: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS: SCOPED_FALSIFICATION_OF_MOMENT_ONLY_SIGN_INFERENCE
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_RANK_TRACE_CCM_2026-11-04.md
```

Ы. Алгебраический перенос выполнен, следы исходного A_m выписаны со всеми членами. Перенос численных процентов не выполнен: у буквального CCM другой carrier, другая нормировка единичного нуля и неоплаченный высоконулевой хвост. Доказано, что одно удаление тихого блока не улучшает ведущий rank–trace score. Существующая абсолютная оценка полного хвоста даёт в этом переносе лишь тривиальную нижнюю границу числа хороших нулей. Это недостаточность конкретного бюджета, не опровержение возможности более сильной совместной оценки.

## 1. Source lock и граница независимой проверки

**[FINITE_CELL | PAPER; проверка источников, не сертификат чужих результатов.]**

P1. Claude, PDF по указанному адресу, дата August 10, 2026, 35 страниц. Прочитаны определения §2, Lemmas 2.2 и 3.2–3.3, нулевой разбор §4, Theorem 5.8, Theorem D и замечания о прямоугольном окне/потолке. Ключевые страницы просмотрены web-screenshot. Алгебраическая лемма и её применение к CCM ниже передоказаны. Весь аналитический вывод headline-пропорций и Lean-экспорт здесь независимо не воспроизведены.

P2. Alpöge–Furman, arXiv:2608.13637. Полный arXiv-текст не удалось получить: обращения к PDF/HTML вернули cache miss. Официальный README `anthropics/formal-math/zeta23/README.md`, blob `302fa9094863279d0ec83fca012d2b7bf59d5ccd`, подтверждает связь проекта с этим препринтом. Его заявления о Lean — отчёт авторов, а не наш запуск kernel.

P3. Lamzouri, arXiv:2609.02882. Полный текст также не получен. Авторское выступление на MPIM подтверждает Hilbert-space подход. Точная лемма Ламзури не цитируется по пересказу и не объявляется проверенной. Ниже дана собственная Hilbert–Schmidt версия нужного неравенства.

Таким образом, это НЕ законченный независимый аудит всех трёх препринтов. Необходимая для данного переноса алгебра не зависит от неподтверждённых headline-утверждений.

R1. На `cdb84497`: `docs/routeB_bus/proshka/PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md`, §§2–5: точная попарная нулевая форма, ранг, Schur-порог и полный хвост.

R2. На том же pin: `docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator/spike_trend_310_600/spike248/TRACE_LEMMA.md`, blob `33d701c535b176aab27942b0575cf9d4f69566a2`, прочитан целиком.

R3. Унаследованный shrinking-kappa residual и bounded PAPER-аудит: `PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, blob `ebf7f8cab61a795118bda5dc7e65a0b3386247b7`; `SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_PAPER_AUDIT_2026-11-02.md`, blob `4e6165039aaa6e5d52774413ca39de596be409bd`. Их доказательства заново не объявляются результатом этой работы.

R4. DH900: `docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator/spike_trend_310_600/dh_census/RESULT.md`, blob `bc887e43df3a54c52f0402bf2d1430ee56953213`: 798 верхних корней, 746 на линии и 26 квартетов = 52 внелинейных верхних корня. Кратность 1 и полнота — numerical census, НЕ интервал.

R5. Balance/softness `75afd6a1`, blob `c150754c6c287545d3e893d60470c98998a98a45`: положительное направление/жёсткость ручек не являются доказательством исходного PSD. Старый вывод не повышается до закона знака.

Внешние адреса для воспроизводимости:
```text
https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
https://arxiv.org/abs/2608.13637
https://arxiv.org/abs/2609.02882
https://www.mpim-bonn.mpg.de/de/node/15886
https://github.com/anthropics/formal-math/tree/main/zeta23
```

Один важный предел импорта: 0.68185 заявлен в P1, Remark 1.1 для сертификатов из bandwidth-one информации. Это не доказанный здесь универсальный потолок любого CCM-аргумента. Более узкая оптимизация окна в Theorem D и это более широкое утверждение — разные результаты. Ни одно не используется как посылка наших новых доказательств.

## 2. Точный словарь окон и метрик

**[ABSTRACT | PAPER; A/LA, E/F для общего источника.]** Используем один и тот же полный Weil pairing W, с Fourier-знаком exp(-izx). В P1 высоту обозначим H, чтобы не смешать её с нашим cutoff T_m.

Их параметры: ell=log(H/(2pi)), L_g=lambda*ell, X=exp(L_g), 0<lambda<=1; модулированные тесты f_k(x)=phi(x)exp(i tau_k x) с support(phi) в [-L_g/2,L_g/2], tau_k в [H,2H], шагом 2pi/L_g. Количество тестов порядка H L_g/(2pi). Phi=Fourier(phi^2), a=||phi||_2^2/L_g. Матрица G=(W(f_k,f_l)); нормировка единичного нуля — G/(a L_g^2). Это не whitening физического Gram.

Наши параметры:

    L=log m, d=m+1, omega_j=2pi*j/L,
    phi_j(x)=d_j(-1)^j cos(omega_j x)/sqrt(L),
    d_0=1, d_j=sqrt(2) for j>0, |x|<=L/2;
    Omega=2pi*m/L, T_m=kappa_m Omega.

Синтез S_m в физическое L2 изометричен, A_m=S_m^* W S_m. Для их синтеза S_g имеем G=S_g^* W S_g. Равенство G=R^*A_mR допустимо ТОЛЬКО если S_g=S_mR; гладкий taper и высокая полосовая модуляция обычно не принадлежат нашему буквальному V_m.

Для прямоугольного полного Fourier-carrier j=-m,...,m есть точный изометрический переход к чётному:

    psi_j=L^-1/2 exp(i omega_j x)1_I,
    phi_0=psi_0,
    phi_j=(-1)^j(psi_j+psi_-j)/sqrt(2), j>0.

Поэтому A_even=E^*A_full E для явной изометрии E. Это сжатие, не равенство спектров полного и чётного блоков. Невырожденная конгруэнция сохраняет инерцию, но не след/Frobenius; они сохраняются при унитарной замене ортонормированного базиса.

### 2.1. Пуассон, алиасинг и точная масса одного нуля

Для полной решётки tau_k=tau_0+2pi*k/L_g и гладкого окна P1 использует sampling identity. Она получается из гребёнки Пуассона: support(phi) длины L_g убивает все ненулевые физические сдвиги на L_g в произведении. В частности,

    sum_(k in Z) |phihat(t-tau_k)|^2=L_g ||phi||^2=a L_g^2

для вещественного t. Конечный набор k даёт <=. Сама эта Parseval-идентичность верна и для прямоугольника; гладкость нужна для высоконулевых хвостов и моментных ошибок, а не для переименования окна.

Для нашего полного чётного ортонормированного базиса Parseval даёт непосредственно

    sum_(j>=0) |phihat_j(t)|^2=||cos(tx)||_(L2(I))^2
        =L/2+sin(Lt)/(2t),  t real,

с устранимым значением в t=0. Следовательно,

    2 sum_(j=0)^m |phihat_j(t)|^2 <= L+sin(Lt)/t <=2L.       (2.1)

На критической паре ±t кратности 1 стоит rank-one блок 2 e(t)e(t)^T. Поэтому безопасная нормировка для счёта верхних нулей:

    sigma=2L,   Ahat=A_m/sigma.                             (2.2)

Можно использовать меньший ДОКАЗАННЫЙ верхний bound на массу всех критических узлов рассматриваемой полосы. Например, при t>=H>0 подходит L+1/H. Но нельзя без доказательства поставить sigma=1 или перенести a L_g^2 из другого базиса. Для комплексных узлов абсолютные квадраты в (2.1) не подменяют знаковую нулевую форму.

Ядро физической проекции:

    K_m^E(x,y)=[D_m(2pi(x-y)/L)+D_m(2pi(x+y)/L)]/(2L),
    D_m(v)=1+2 sum_(j=1)^m cos(jv).

Именно это ядро, а не гладкое Phi(t-u), находится в наших моментных свёртках.

### 2.2. Почему нельзя подставить m в готовую долю

**[COFINAL_FAMILY | PAPER; A/I, проверка применимости внешнего бюджета.]**

Если попытаться отождествить высоту H с T_m, сохраняя полный prime cutoff X=m, то

    lambda_eff=log m/log(T_m/(2pi))
        =L/(L-log L+log kappa_m)>1                          (2.3)

для больших m. У нас симметричный низкочастотный carrier до ±Omega и счёт 0<gamma<T_m, не dyadic family [H,2H]. При shrinking kappa число верхних нулей N(T_m)~m и d~m, но совпадение размерностей не даёт равенства sampling kernels.

Существенная проверка оценки P1, Theorem 5.8: в её остатке присутствует

    ((ell^2+X) log ell)/(H ell).

При X=m,H=T_m~2pi*kappa*m/L вклад X log ell/(H ell)~log L/(2pi*kappa), то есть не o(1). Это доказанный провал ПОДСТАНОВКИ в данный бюджет, не доказательство расходимости истинного момента. Кроме того, у прямоугольника Fourier-хвост O(1/|gamma|), тогда как гладкий taper поставляет более быстрое убывание для контролируемой высотной отсечки.

Чтобы законно вернуться к их режиму, нужно менять семейство тестов: выбирать H и L_g независимо с X<=H/(2pi), высокую модуляцию и smooth taper. Это разрешённый другой carrier, но не улучшение буквального CCM и не новое доказательство сверх их результата.

## 3. Rank–trace: независимое доказательство с точным slack

**Теорема 1. [ABSTRACT | PAPER; LA.]** Пусть P>=0, rank P<=r, B=B^* и n_+(B)<=b. Для каждого c>0

    ||P+B||_F^2 >= c trP+2c trB-c^2 r/4-c^2 b.             (3.1)

При c=2 это именно

    r >=2trP+4trB-4b-||P+B||_F^2.                          (3.2)

Доказательство не требует положительности P+B. Положим B=R-N, R=B_+>=0, N=B_->=0, RN=0. Пусть Pi — ортопроекция на ran P, Sigma — на ran R, r0=rankP,b0=rankR. Положим X=P-Pi N Pi. ТОЧНО:

    ||P+B||_F^2-c trP-2c trB+c^2 r0/4+c^2 b0
      =||X-(c/2)Pi||_F^2
       +2||Pi N(I-Pi)||_F^2+||(I-Pi)N(I-Pi)||_F^2
       +||R-c Sigma||_F^2+2tr(PR)
       +c[2trN-tr(Pi N)].                                 (3.3)

Все слагаемые неотрицательны: tr(PR)>=0 и 0<=tr(Pi N)<=trN. Раскрытие квадратов доказывает (3.3); замена r0,b0 их верхними границами доказывает (3.1). Это также Hilbert-space доказательство для finite-rank P,R и trace-class N: нормы являются Hilbert–Schmidt нормами. Оно не атрибутируется недоступному тексту Ламзури.

Вторая полезная оценка. Для самосопряжённой A, a=trA>0, v=trA^2:

    n_+(A)>=a^2/v.                                       (3.4)

Действительно, сумма положительных eigenvalues >=a; Cauchy–Schwarz на положительном спектре даёт (3.4). Если trA>theta*d, theta>=0, то аналогично

    #{lambda(A)>theta}>=(trA-theta*d)^2/||A||_F^2.         (3.5)

Здесь используется сумма (lambda-theta)_+, которая >=trA-theta*d, и (lambda-theta)^2<=lambda^2 для lambda>theta. Это не утверждение, что сама A положительна.

## 4. Полные исходниковые моменты CCM

**[FINITE_CELL | PAPER; E/F/I/A/LA.]** Все формулы ниже верны для каждого целого m>=2. Обозначим c_*=EulerGamma+log(8pi)+pi/2, j(u)=exp(-u/2)/(1-exp(-2u)), c_n=Lambda(n)/sqrt(n), p(x)=sqrt(2)cosh(x/2). В чётном carrier нечётный полюс исчезает именно по чётности.

Определим симметричную матрицу перекрытий

    R(u)_jk=integral phi_j(x)[phi_k(x+u)+phi_k(x-u)]dx,
    R(0)=2I, R(u)=0 for u>=L.

При 0<=u<L, v=L-u, sinc(0)=1,

    R(u)_jk = d_j d_k (-1)^(j+k) v/L *
      [sinc((omega_j-omega_k)v/2) cos((omega_j+omega_k)u/2)
       +sinc((omega_j+omega_k)v/2) cos((omega_j-omega_k)u/2)].   (4.1)

Это интегрирование двух косинусов на фактическом перекрытии [-L/2,L/2-u]; на конце u=L нет положительной меры перекрытия.

Пусть

    H=-c_*I+integral_0^infinity j(u)[2I-R(u)]du,
    v_j=<phi_j,p>=sqrt(2)d_j sinh(L/4)/[sqrt(L)(omega_j^2+1/4)],
    P_ar=sum_(2<=n<=m) c_n R(log n).

Тогда исходная матрица ТОЧНО

    A=H+v v^*-P_ar.                                      (4.2)

Диагональный arch-константный член, весь интеграл до infinity и полюс сохранены. Интеграл конечен: 2I-R(u)=O_m(u) в нуле, j(u)=O(1/u). Для u>=L хвост равен

    2I[atanh(exp(-L/2))+atan(exp(-L/2))].

При n=m R(log n)=0, даже если m — простая степень. Это нулевой вклад, не выброшенный атом.

Оба искомых момента получаются без нулевой суммы:

    a_m=trA=trH+||v||^2-sum_n c_n trR_n,                  (4.3)

    v_m=||A||_F^2
      =trH^2+2v^*Hv+||v||^4
       -2 sum_n c_n tr(HR_n)-2 sum_n c_n v^*R_n v
       +sum_(n,l) c_n c_l tr(R_n R_l), R_n=R(log n).        (4.4)

Это безусловные конечные prime-power суммы с явными arch-интегралами. В двойной сумме сохранены ВСЕ n,l, включая n!=l: именно здесь живут корреляции, которые нельзя заменить диагональю с неоценённой ошибкой.

Для прямого вычисления следа:

    trR(u)=2/L[(L-u)(1+sum_(j=1)^m cos(omega_j u))
                    -sum_(j=1)^m sin(omega_j u)/omega_j], 0<=u<L. (4.5)

Таким образом, T1 подтверждён в смысле точного переноса, но точное вычислимое выражение ещё не означает требуемой асимптотики.

### 4.1. Элементарный верхний рост следа

**[COFINAL_FAMILY | PAPER; E/F/I/A.]** Из (4.1)–(4.5) следует

    |tr A_m|=O(m log m).                                 (4.6)

Подробности бюджета. Суммирование translation-энергий базиса даёт при u<=L

    0<=tr(2I-R(u))<=d Omega^2 u^2+4d u/L,
    tr(2I-R(u))<=4d.

Разделение arch-интеграла при 1/Omega и при 1 даёт O(d(1+log Omega)). Полюс стоит <=||p||_I^2=L+2sinh(L/2). Для log2<=u<=L формула Dirichlet kernel и sin(pi u/L)>=2 min(u,L-u)/L дают |trR(u)|=O(L), включая обе крайние области. Наконец sum_(n<=m)c_n<=2sqrt(m)L из Lambda(n)<=log n. Арифметический след поэтому O(sqrt(m)L^2)=o(mL). Это оценка по модулю, не источник знака A.

## 5. Подлинный нулевой счёт: нужна полная цена R_T

**[FINITE_CELL | PAPER; A/F/Z/LA, E на моментном возврате.]** Положим

    Z_T=A_<T, R_T=A-Z_T,
    A_<T=E_T^* Jcal_T E_T.

Счёт N=N(0,T) здесь строгий 0<gamma<T с кратностями. Граница gamma=T целиком относится к R_T. Пусть s1 — число простых критических верхних нулей; s2 — число различных многократных критических верхних нулей; b — число различных внелинейных верхних пар (одна пара вверху соответствует одной четверке).

Разделим Z_T/sigma=P1+B_bad: в P1 только простые критические пары ±gamma, в B_bad все остальные низкие нули. По (2.1)–(2.2):

    P1>=0, rankP1<=s1, trP1<=s1,
    n_+(B_bad)<=s2+b,
    N>=s1+2s2+2b.                                       (5.1)

Внелинейная четверка кратности nu даёт 4nu[(Re F)^2-(Im F)^2], а не модуль в квадрате. Кратность умножает блок, но не число его независимых положительных направлений.

Определим score Phi(M)=4trM-||M||_F^2. Из (3.2), (5.1):

    3s1+4s2+4b >= Phi(Z_T/sigma),
    s1 >= Phi(Z_T/sigma)-2N,
    Nd=s1+s2+2b >= [Phi(Z_T/sigma)-N]/2.                   (5.2)

Это точный перенос счёта. Матрица в score — НИЗКИЙ нулевой head, не автоматически полный A.

### 5.1. Полностью оплаченная версия с prime-side a_m,v_m

Пусть E>=||R_T||_1 (trace/nuclear norm), e=E/sigma. Из (4.3)–(4.4):

    Phi(Z_T/sigma) >=
    F_safe :=4a_m/sigma-4e-(sqrt(v_m)/sigma+e)^2.           (5.3)

Доказательство: trZ_T>=trA-||R_T||_1; ||Z_T||_F<=||A||_F+||R_T||_F<=sqrt(v_m)+E. Никакой положительности R_T не использовано.

Следовательно,

    s1 >= max(0,ceil(F_safe-2N)),
    Nd >= max(0,ceil((F_safe-N)/2)).                       (5.4)

Если используется верхняя оценка N_up вместо N, она ослабляет эти нижние границы законно. В интервале следует округлять именно доказанную НИЖНЮЮ границу F_safe. Число, полученное из float, не становится сертификатом.

Можно не брать модули хвоста. Точная неоценённая потеря равна

    J_tail=4trR_T/sigma-2tr(A R_T)/sigma^2+||R_T||_F^2/sigma^2,
    Phi(Z_T/sigma)=Phi(A/sigma)-J_tail.                   (5.5)

Это один совместный скаляр. Контроль J_tail сверху может быть существенно дешевле отдельного контроля ||R_T||_1, но такого source-bound здесь не получено.

### 5.2. Имеющийся абсолютный бюджет не даёт положительной доли

**[COFINAL_FAMILY | PAPER; A/Z/LA, только для явно выбранного envelope.]**

Для T>Omega, T>=e, R1 поставляет явный абсолютный envelope. Тот же вывод даёт trace norm, а не только operator norm: каждый комплексный нулевой rank-one summand имеет nuclear norm, равную произведению норм evaluation-векторов. Абсолютное суммирование той же оценки сохраняет константу:

    ||R_T||_1 <= E_m(T),
    E_m(T)=8(2m+1)sqrt(m)/L * (1+1/(4T^2))
            *Z(T)/(1-Omega^2/T^2)^2,
    Z(T)=log(T)/(pi T)+(log(T)+21/2)/T^2.                  (5.6)

Оба знака высот, все кратности и |Im z_rho|<1/2 сохранены. Для DH этот zeta-strip бюджет не импортируется: у его комплексных спектральных точек другая полоса.

Пусть kappa_m=1+c h/L, h=1+log L, 0<c<1 фиксировано. Для КОНКРЕТНОЙ правой части (5.6), а не для истинной нормы хвоста,

    E_m(T_m) ~ 2/(pi^2 c^2) * sqrt(m) L^3/h^2.            (5.7)

Совместим (4.6) и (5.3). Даже разрешая любую положительную скалярную нормировку,

    F_safe <=4a_m/sigma-E_m(T_m)^2/sigma^2
       <=4(max(a_m,0))^2/E_m(T_m)^2
       =O_c(m h^4/L^4)=o(m)=o(N(T_m)).                  (5.8)

Второй переход — максимум квадратичного полинома по 1/sigma. Остальные отрицательные члены safe-budget только ухудшают его. Поэтому (5.4) с данным E_m даёт eventually нуль для обоих lower counts.

Это строгий предел ЭТОГО абсолютного способа оплаты, не отрицательный результат о настоящем Z_T. Новый знаковый/совместный tail-bound или иное семейство окон может изменить вывод.

## 6. Тихое пространство: что действительно улучшается

**Теорема 2. [ABSTRACT | PAPER; LA.]** Пусть Q имеет r ортонормированных столбцов, U дополняет его до ортонормированного базиса, delta=||AQ||. Запишем

    [Q,U]^*A[Q,U]=[[D,K^*],[K,G]], G=U^*AU.

Тогда точно и с явным бюджетом

    trA-trG=trD,              |trD|<=r delta,
    ||A||_F^2-||G||_F^2=||D||_F^2+2||K||_F^2,
    0<=||A||_F^2-||G||_F^2<=2r delta^2,
    |Phi(A/sigma)-Phi(G/sigma)|
       <=4r delta/sigma+2r delta^2/sigma^2.                (6.1)

Доказательство: ортогональная блочная запись и ||AQ||_F^2=||D||_F^2+||K||_F^2<=r delta^2. Это не оценка спектра G.

**Следствие для того же J. [COFINAL_FAMILY | PAPER; R3+LA.]** При delta=o(m^-B) для каждого фиксированного B и r<=m+1, sigma>=1 правая часть (6.1) сверхполиномиально мала. Поэтому удаление J само по себе не создаёт нового ведущего члена в trace–Frobenius score.

Более сильное точное наблюдение: все активные evaluation-векторы нулей ниже T лежат в J^perp. Значит,

    P1 Q=0, B_bad Q=0, Z_T Q=0.

Переход к U НЕ меняет rankP1, n_+(B_bad), trP1, trB_bad, ||Z_T||_F, ни массу одного критического нуля. Он НЕ удаляет плохие четверки: J построено занулением всех низких фактических нулей, а не только плохих.

В этой блочной записи

    R_T=[[D,K^*],[K,R_11]],
    G=U^*Z_TU+R_11.                                      (6.2)

Невязка контролирует D,K, но НЕ R_11. Например, (5.5) содержит trR_11, tr[(U^*Z_TU)R_11] и ||R_11||_F^2. Это точное место неоплаченной цены.

Поэтому T2 подтверждён для заявленного механизма: одно вырезание тихих направлений не улучшает ведущую долю. Из этого НЕ следует, что никакая новая source-оценка на J^perp никогда не улучшит метод. Число 0.68185 не превращается в универсальный запрет для всех новых входов.

### 6.1. Два момента плюс произвольно большой тихий блок не решают знак

**[ABSTRACT | PAPER; LA, scoped counterexample.]**

    A_+=diag(1,1,13), A_-=diag(-3,9,9),
    tr A_+=tr A_-=15, ||A_+||_F^2=||A_-||_F^2=171.

Инерции различны. При добавлении любого нулевого блока сохраняются оба момента и delta=0. Например, на первом координатном векторе A_- имеет строгий верхний Rayleigh -3<0. Это опровергает общий вывод «два момента + большой тихий блок => отсутствие отрицательного направления». Это не counterexample для actual zeta.

## 7. Сто процентов, b=0 и TRACE_LEMMA — три разные цели

**[COFINAL_FAMILY | PAPER; LA/A; RH-импликации с унаследованным source return.]**

1. s1(T)/N(T)->1 НЕ означает b(T)=0. К положительному простонулевому baseline можно добавить одну off-line четверку: в верхней полуплоскости появятся 2 точки, а отношение N/(N+2) всё ещё стремится к 1. Это ровно planted discriminator, а не гипотеза о настоящих нулях ζ.

2. b(T)=0 для неограниченных возрастающих T, если b считает ВСЕ off-line пары ниже T, эквивалентно RH. Условия «все нули простые и на линии» сильнее: b=0 не исключает многократные критические нули. В dyadic полосе один выбранный subsequence без плохих нулей недостаточен, если полосы не покрывают хвост; ниже-cutoff formulation устраняет этот пробел.

3. Для целочисленного закрытия simple-line счёта по (5.4) достаточно

    3N-F_safe<1.                                         (7.1)

Тогда s1>N-1, значит s1=N. Если доказана только F_safe=(3-o(1))N, дефект ещё может расти и (7.1) не следует. Ошибка o(N) не есть ошибка <1. Для одного b=0 условие (7.1) избыточно, но это честный достаточный integer gate.

### 7.1. Собственная finite Hilbert-space дверь к полному знаку

Пусть q=d-r, G=U^*AU, trG>0. Из (3.4):

    (trG)^2/||G||_F^2 > q-1  ==> G>0.                    (7.2)

Это сильный finite certificate: число положительных eigenvalues целое и не больше q. Для q=1 достаточно trG>0. Для q>1 (7.2) требует эффективный ранг почти максимальный; оно не следует из малой невязки или известных пропорциональных моментных асимптотик. Оно также не необходимо для G>=0.

Если (7.2) доказано на кофинальной исходной семье и delta_m->0, блочная оценка даёт

    lambda_min(A_m)>=-2delta_m.

Унаследованный off-line negative-witness return тогда исключает off-line нули. Это conditional consumer, не поставленная в этой работе оценка (7.2). Более слабый постоянный пол G>=-C также достаточен при унаследованной NOESCAPE constant-floor теореме. Никакого нового знака отсюда не объявляется.

### 7.2. TRACE_LEMMA Codex: проверено, но separator нельзя получить из названия

R2 предполагает 0<r<d/2 и delta=||AQ||<lambda_r(A). Его следствия корректны:

    lambda_0>-lambda_r,
    trA>(d-2r)lambda_r,
    lambda_0>-trA/(d-2r).

Но уже из ТОГО ЖЕ строгого separator следует более точный знакомый NOESCAPE-вывод

    lambda_0>=-delta.                                    (7.3)

Действительно, как минимум r singular values <=delta по min–max на ran Q. Все eigenvalues с индексом j>=r больше delta. Следовательно, все r нижних eigenvalues попали в [-delta,delta]. Для (7.3) условие r<d/2 не нужно; оно нужно только делению trace-оценки.

Значит, TRACE_LEMMA родственна методу через спектральный счёт, но она ПОТРЕБЛЯЕТ именно missing separator. Два момента его автоматически не дают. Один достаточный finite gate, также полученный из (3.5), —

    trA>delta*d,
    (trA-delta*d)^2/||A||_F^2 > d-r-1.                    (7.4)

Он даёт как минимум d-r eigenvalues >delta и вместе с quiet singular-value count — separator. (7.4) не доказано для настоящей кофинальной семьи.

### 7.3. Сравнение с J^perp и законом баланса

По точному head-индексу при независимости строк b=n_-(Z_T), но полный G содержит R_11. Даже G>=0 в одной конечной ячейке не доказывает b(T)=0 без оплаты этого хвоста. При кофинальном нижнем поле full G и доказанном quiet return применяется иной negative-witness argument и действительно получается RH-эквивалентная граница.

Закон баланса из 75afd6a1 — не эта граница: он описывает soft/rigid directions в пространстве параметров и совместимость dual trace-условий. Пустое допустимое множество тоже может быть «жёстким». Ни stiffness, ни kernel параметрического отображения не поставляют lower floor исходного G. T4 поэтому верен лишь для кофинального exact-no-quartet/floor consumer, а не для density-one и не для одного закона баланса.

## 8. Discriminators без смены источника

**[FINITE_CELL / COFINAL_FAMILY | PAPER, числа census отдельно DIAG.]**

DH. Лемма (3.1) универсальна; для нулевого переноса нужны DH's actual signed log-derivative coefficients, его odd-gamma, отсутствие ζ-полюса и его собственный tail bound. Подстановка положительных Λ_ζ вместо b_D(n) запрещена. R4 даёт DIAG s1=746,s2=0,b=26,N=798. Тогда (5.2) разрешает

    Phi<=3*746+4*26=2342,
    Phi-2N<=746, (Phi-N)/2<=772.

Никакого b=0 не получается. Это точная проверка счётных коэффициентов на сохранённом numerical census, не новый прогон DH-моментов или сертификат полноты/простоты. При нехватке dimension d для независимости всех rows нельзя дополнительно утверждать равенство n_-(head)=26.

F_a. Нули произведения xi(s+a)xi(s-a) сохраняются со сдвигами и правильными кратностями, дают indefinite blocks. Одновременно меняются prime-power веса, gamma и pole terms. Rank–trace лемма остаётся верной; old zeta moment asymptotics для нового источника не импортируются. Обработка комплексных точек модулем в квадрате уничтожила бы этот discriminator.

Подсадка. Добавление одной четверки добавляет один bad block (в чётном вещественном секторе), изменяет первые два момента и сохраняет разрешение b>=1. Для каждого конечного cutoff со всеми включёнными точками перенос (5.2) верен. В asymptotic density finite number of exceptions может исчезнуть; это причина integer guard (7.1), не разрешение объявить отсутствие квартета.

Удвоенный атом 2. Source formulas (4.2)–(4.4) пересчитываются с изменённым coefficient и остаются точными для изменённой формы. Но у этой произвольной weight-операции не предъявлен соответствующий L-function zero dictionary. Нельзя продолжать пользоваться старыми ζ-нулями в (5.1). Это явное место source-matching fail, а не положительный обход отрицательного контроля.

E/I входят в точные weights Λ(n) и их целочисленную prime-power поддержку, а также в оценку (4.6). F входит в gamma/pole и unconditional explicit formula. Никакое число конечных critical zeros не использовано как доказательство глобальной положительности. Умеренность коэффициентов, нужная для импортируемых mean-value estimates, не заменяет полученную отдельно подпись bad blocks.

## 9. Кванторы, прогнозы, стоимость следующего хода

| Запрос | Verdict | Точный достигнутый результат |
|---|---|---|
| (1) G <-> A_m | REDUCED / exact source dictionary | Один W, разные synthesis maps; дана буквальная even isometry и масса нуля |
| (2) rank–trace + prime moments | PROVED_PAPER | (3.1)–(3.3), (4.3)–(4.4), tail-safe (5.4) |
| Положительная новая доля ниже T_m | NOT_PROVED | Используемый absolute E_m приводит к нулевому lower count |
| (3) выигрыш от удаления J | REFUTED_AS_AUTOMATIC_MECHANISM | Head score неизменен точно; full score меняется не больше (6.1) |
| Универсальный потолок 0.68185 для всех CCM путей | OPEN / not asserted | Это не следствие quiet calculus; внешний extremal certificate здесь не проверен |
| (4) b=0 / 100% | REDUCED | exact cofinal b=0 iff RH; density one не достаточно; simplicity сильнее |

Предрегистрация локальных тестов создана до их выполнения. P1 exact slack, P2 overlap/source moments, P3 quiet-score, P4 equal-moment opposite inertia, P5 insufficiency данного E_m, P6 density vs exact absence — подтверждены указанными PAPER-доказательствами и отдельными проверками. Никакой измеренный эффект не переименован задним числом.

User predictions:

- T1, p=.70: CONFIRMED для точных моментов и переноса с хвостом; не для обещания новой численной доли.
- T2, p=.60: CONFIRMED_SCOPED для одного quiet deletion. Универсальная невозможность превысить внешний потолок любым новым механизмом не доказана.
- T3, p=.25: NOT_CONFIRMED; улучшение сверх .68185 не получено. Не объявлено refuted для всех допустимых семейств.
- T4, p=.60: PARTIAL. Cofinal exact absence и complementary floor ведут к RH; density-one и parameter balance не являются тем же утверждением.

Две перепараметризации одного remaining object до любых больших расчётов:

A. Совместный tail-moment (5.5), вместо nuclear absolute budget. Kill-power 5/5 для ложного переноса процентов, cost medium. Нужна source-оценка J_tail и первых двух моментов в одной нормировке, с полными cross terms. Сама запись тождества не является новой оценкой.

B. Инерция/эффективный ранг непосредственно на J^perp, (7.2) или более слабый constant-floor. Kill-power 5/5 для RH-consumer, cost high. Не требует обещанного процента или точного b в отдельном cutoff, но требует настоящий source-signed bound. Это альтернатива A, не дополнительная обязательная лестница.

DISCRIMINATOR для zero-consistent результата: интервал полного Schur/complement Rayleigh на фиксированном witness с U<0 либо lower envelope для всего complement; ненулевая unresolved eigenvalue не заменяется нулём. Для exact-no-exception count — certified integer deficit <1, не fitted density.

### K8A

DOWNSTREAM_CONSUMER: unchanged literal-family lower floor or exact cofinal no-off-line count.
ACTUAL_CONSUMER_REQUIREMENT: source-signed cofinal inequality; для простого rank-count маршрута дополнительно integer-scale deficit.
ORIGINAL_REQUESTED_OBJECT: rank–trace transfer and improvement from J.
ORIGINAL_OBJECT_IS: exact transfer PROVED; new percentage NOT_NECESSARY for the weaker floor consumer.
KNOWN_WEAKER_INTERFACES: G_m>=-C on an unbounded family plus full quiet residual suffices through inherited NOESCAPE; it does not require all zeros simple.
FAILURE_TYPE: NO_DERIVATION of signed tail/complement bound; COUNTEREXAMPLE only to generic two-moment-plus-quiet sign inference.
EPISTEMIC_STATUS: RESEARCH_DEBT for actual new arithmetic sign.
REOPEN_TRIGGER: independently proved joint J_tail bound improving (5.8), or cofinal lower floor / integer-scale certificate with complete source return.
NOVELTY_AXIS: exact literal moment translation, transparent Hilbert–Schmidt slack, and quantitative quiet-block invariance; no claim of historical priority.
KILL_SCOPE: THEOREM_SHAPE only for generic moment-only sign inference.
KILL_EVIDENCE_KIND: exact equal-moment matrices with a strict negative Rayleigh upper -3.
ROUTE_FAMILY_DEAD: false.

Один следующий Codex target: независимо проверить теоремы (3.3), (5.3)–(5.8), (6.1) и найти/проверить один SOURCE-bound для J_tail (5.5), прежде чем считать большие spectra. Consumer — (5.4). Успех в арифметической части: quantified upper J_tail с budget, меняющим lower count; не новый fit. Failure output: SOURCE_TAIL_MOMENT_BOUND_UNPAID с точным неоплаченным cross term. Нельзя подставлять RH, положительный zero prefix, или малую R_T Q вместо R_11.

## 10. Проверки, воспроизведение и handoff

Исполнено 12 exact rational/symbolic control groups, включая 36 count-configurations внутри одной группы. Источник на m=3,8 пересчитан без нулевого списка при 55 dps, Gauss orders24/32,8 panels. Проверены independent direct overlap integrals, trace contraction, Frobenius expansion, endpoint atom. Новые eigenproblems не запускались.

| m | tr A, DIAG | ||A||_F^2, DIAG | max matrix refinement |
|---:|---:|---:|---:|
| 3 | 2.0080325094994680721233155533 | 2.0787274003375577636338337988 | 2.86e-55 |
| 8 | 6.4830798894227381988686100441 | 13.7369487433705586024185425124 | 2.21e-52 |

Max independent overlap discrepancy <1.33e-55; moment bookkeeping discrepancy <2.70e-54. Эти quadrature values — DIAG, не certified signs or errors. Начальный harness вызвал неподдержанную lambda-form mpmath matrix constructor, получив zero matrix; exact overlap/trace assertion это остановил до результатов. Исправлено на явный список entries, математические формулы и predictions не менялись.

Следующий appendix воспроизводит проверки. Рабочая директория: любая с правом записи; Python с sympy и mpmath. Для uv: `uv run --with sympy --with mpmath check_rank_trace.py`. Он сохраняет CHECK_RESULTS.json рядом со скриптом. Это не Lean gate.

Публикуется только этот новый Markdown в docs/routeB_bus/proshka/ на inbox-ветке. Concurrent HEAD не сбрасывается на заданный старый pin. Commit SHA возвращается после записи и readback; источник не утверждает собственный ещё не созданный SHA. Проверка Git из корня клона:

```sh
git fetch origin proshka_inbox_2026-10-31
git log -1 --format='%H %s' origin/proshka_inbox_2026-10-31 -- docs/routeB_bus/proshka/PROSHKA_VERDICT_RANK_TRACE_CCM_2026-11-04.md
git show origin/proshka_inbox_2026-10-31:docs/routeB_bus/proshka/PROSHKA_VERDICT_RANK_TRACE_CCM_2026-11-04.md > /tmp/rank_trace_verdict.md
```

Lean files written: NONE. Expected Lean axiom profile: NOT_APPLICABLE. Independent analytic audit: NOT_PERFORMED. Re-running this arithmetic harness checks normalizations and witnesses; it does not promote a new zero proportion, global positivity, or RH.

### Executable appendix

```python
from __future__ import annotations
import json, time
from pathlib import Path
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parent
START = time.monotonic()
checks = []
def record(name, detail=None):
    checks.append({'name':name,'status':'PASS','detail':detail})
def fnorm2(A):
    return sp.trace(A.T*A)

# Exact projection/slack identity: Q has a known positive/negative spectral split.
for k in range(1, 5):
    W = sp.Matrix([[1,k],[0,1],[k,0],[1,-1]])
    P = W*W.T
    Pi = W*(W.T*W).inv()*W.T
    I = sp.eye(4)
    R = sp.diag(sp.Rational(k,3),0,sp.Rational(2,5),0)
    N = sp.diag(0,sp.Rational(k+1,4),0,sp.Rational(1,7))
    Qb = R-N
    Sigma = sp.diag(1,0,1,0)
    c = sp.Rational(k+1,2)
    X = P-Pi*N*Pi
    lhs = fnorm2(P+Qb)-c*sp.trace(P)-2*c*sp.trace(Qb)+c*c*2/4+c*c*2
    rhs = (fnorm2(X-c*Pi/2)+2*fnorm2(Pi*N*(I-Pi))
           +fnorm2((I-Pi)*N*(I-Pi))+fnorm2(R-c*Sigma)
           +2*sp.trace(P*R)+c*(2*sp.trace(N)-sp.trace(Pi*N)))
    assert sp.simplify(lhs-rhs)==0 and lhs>=0
    record(f'exact_rank_trace_slack_{k}',str(lhs))

A1=sp.diag(1,1,13); A2=sp.diag(-3,9,9)
assert sp.trace(A1)==sp.trace(A2)==15
assert fnorm2(A1)==fnorm2(A2)==171
assert A1.det()>0 and A2.det()<0
record('same_moments_different_inertia',{'trace':15,'frobenius_squared':171})
for r in (1,4,11):
    Z=sp.zeros(r)
    assert sp.trace(sp.diag(Z,A1))==sp.trace(sp.diag(Z,A2))
    assert fnorm2(sp.diag(Z,A1))==fnorm2(sp.diag(Z,A2))
record('quiet_padding_does_not_resolve_sign')
D=sp.Matrix([[1,2],[2,-1]])/100
K=sp.Matrix([[1,2],[3,4],[5,6]])/200
G=sp.Matrix([[2,1,0],[1,-1,2],[0,2,3]])
AA=D.row_join(K.T).col_join(K.row_join(G))
assert sp.trace(AA)-sp.trace(G)==sp.trace(D)
assert fnorm2(AA)-fnorm2(G)==fnorm2(D)+2*fnorm2(K)
record('exact_quiet_trace_and_frobenius_split')
A,R=sp.Matrix([[1,2],[2,3]]),sp.Matrix([[0,1],[1,-2]])
sigma=sp.Rational(7,3)
Phi=lambda X:4*sp.trace(X)-fnorm2(X)
assert sp.simplify(Phi((A-R)/sigma)-Phi(A/sigma)
    +4*sp.trace(R)/sigma-2*sp.trace(A*R)/sigma**2+fnorm2(R)/sigma**2)==0
record('exact_signed_tail_penalty')
# Counting implications, with arbitrary positive integer multiplicities represented by N.
for s1 in range(4):
  for s2 in range(3):
    for b in range(3):
      N=s1+2*s2+2*b
      score=3*s1+4*s2+4*b
      assert s1>=score-2*N
      assert s1+s2+2*b>=sp.Rational(score-N,2)
record('integer_count_algebra_36_configurations')
assert 746+2*26==798
assert (3*746+4*26)-2*798==746
assert sp.Rational(3*746+4*26-798,2)==772
record('DH_900_count_accounting_NOT_census_certification', {'s1_DIAG':746,'b_DIAG':26,'N_DIAG':798,'score_upper':2342})
# One off-line quartet can be present while the limiting critical fraction is one.
n=sp.symbols('n',positive=True)
assert sp.limit(n/(n+2),n,sp.oo)==1
record('density_one_not_exact_absence')
# A strict quiet separator supplies the sharper floor, not just a trace estimate.
vals=[sp.Rational(-1,1000),sp.Rational(1,2000),2,3]
delta=sp.Rational(1,1000)
assert max(abs(t) for t in vals[:2])<=delta<vals[2]
assert vals[0]>=-delta
record('separator_floor_normalization')

mp.mp.dps=55
numerics=[]
def trmp(A): return mp.fsum(A[j,j] for j in range(A.rows))
def normmax(A): return max(abs(x) for x in A)
def source(m,order):
    L=mp.log(m); d=m+1; om=[2*mp.pi*j/L for j in range(d)]
    ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
    def Rentry(j,k,u):
        if u>=L: return mp.mpf(0)
        v=L-u
        return (ds[j]*ds[k]*(-1)**(j+k)*v/L *
           (mp.sinc((om[j]-om[k])*v/2)*mp.cos((om[j]+om[k])*u/2)
           +mp.sinc((om[j]+om[k])*v/2)*mp.cos((om[j]-om[k])*u/2)))
    def Rmat(u): return mp.matrix([[Rentry(j,k,u) for k in range(d)] for j in range(d)])
    def Rtrace(u):
        if u>=L: return mp.mpf(0)
        return 2/L*((L-u)*(1+mp.fsum(mp.cos(om[j]*u) for j in range(1,d)))
             -mp.fsum(mp.sin(om[j]*u)/om[j] for j in range(1,d)))
    def phi(j,x):return ds[j]*(-1)**j*mp.cos(om[j]*x)/mp.sqrt(L)
    max_overlap=mp.mpf(0)
    for u in (L/7,L/3,mp.log(2)):
      if u>=L: continue
      for j,k in ((0,0),(0,1),(1,2),(m,m)):
        val=mp.quad(lambda x:phi(j,x)*phi(k,x+u),[-L/2,-u/2,L/2-u])
        val+=mp.quad(lambda x:phi(k,x)*phi(j,x+u),[-L/2,-u/2,L/2-u])
        max_overlap=max(max_overlap,abs(val-Rentry(j,k,u)))
      assert abs(Rtrace(u)-trmp(Rmat(u)))<mp.mpf('1e-45')
    assert normmax(Rmat(L))==0
    assert normmax(Rmat(0)-2*mp.eye(d))<mp.mpf('1e-45')
    xs,ws=mp.gauss_quadrature(order,'legendre')
    cs=mp.euler+mp.log(8*mp.pi)+mp.pi/2
    tail=mp.atanh(mp.exp(-L/2))+mp.atan(mp.exp(-L/2))
    H=(-cs+2*tail)*mp.eye(d)
    ht=mp.mpf(d)*(-cs+2*tail)
    for panel in range(8):
      lo=L*panel/8; hi=L*(panel+1)/8
      for j in range(order):
        u=(lo+hi)/2+(hi-lo)*xs[j]/2
        wt=(hi-lo)*ws[j]/2*mp.exp(-u/2)/(-mp.expm1(-2*u))
        H+=wt*(2*mp.eye(d)-Rmat(u))
        ht+=wt*(2*d-Rtrace(u))
    v=mp.matrix([mp.sqrt(2)*ds[j]*mp.sinh(L/4)/(mp.sqrt(L)*(om[j]**2+mp.mpf(1)/4)) for j in range(d)])
    prime=mp.zeros(d); pieces=[]
    for n in range(2,m+1):
      fac=sp.factorint(n)
      if len(fac)==1:
        p=next(iter(fac)); c=mp.log(p)/mp.sqrt(n)
        Rn=Rmat(mp.log(n)); prime+=c*Rn; pieces.append((c,Rn))
    A=H+v*v.T-prime
    trace=ht+(v.T*v)[0]-mp.fsum(c*trmp(Rn) for c,Rn in pieces)
    f2=(trmp(H*H)+2*(v.T*H*v)[0]+(v.T*v)[0]**2
        -2*mp.fsum(c*trmp(H*Rn) for c,Rn in pieces)
        -2*mp.fsum(c*(v.T*Rn*v)[0] for c,Rn in pieces)
        +mp.fsum(c*e*trmp(Rn*Rl) for c,Rn in pieces for e,Rl in pieces))
    errors={'overlap_integral':mp.nstr(max_overlap,8),
      'trace_contract':mp.nstr(abs(trace-trmp(A)),8),
      'frobenius_expand':mp.nstr(abs(f2-trmp(A*A)),8)}
    assert max_overlap<mp.mpf('1e-45')
    assert abs(trace-trmp(A))<mp.mpf('1e-43')
    assert abs(f2-trmp(A*A))<mp.mpf('1e-42')
    return A,{'m':m,'gauss_order':order,'dps':mp.mp.dps,
        'trace':mp.nstr(trace,35),'frobenius_squared':mp.nstr(f2,35), 'errors':errors}
for m in (3,8):
    a,row=source(m,24)
    aa,row2=source(m,32)
    row2['refinement_matrix_difference']=mp.nstr(normmax(a-aa),12)
    numerics.extend([row,row2])
    elapsed=time.monotonic()-START
    print(f'[{m}/8] source moments complete, elapsed {elapsed:.1f}s',flush=True)
result={'exact_control_groups':len(checks),'checks':checks,'source_norm_checks':numerics,
        'numeric_status':'DIAG_NOT_INTERVAL','lean':False,'arb':False}
(ROOT/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))

```
