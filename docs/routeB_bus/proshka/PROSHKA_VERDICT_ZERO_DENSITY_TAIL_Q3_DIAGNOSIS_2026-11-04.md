# STATUS: TRY_ZERO_DENSITY_TAIL_AND_Q3_SOURCE_RETURN

```yaml
OPERATIVE_CLASS: TRY_ZERO_DENSITY_TAIL_AND_Q3_SOURCE_RETURN
REQUEST: ZERO_DENSITY_TAIL_PLUS_Q3_DIAGNOSIS
DATE: 2026-11-04
AUTHORITY: DIRECT_OWNER_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: rh_clean@adbba53f898bdae1e5b9ff7eed7cf32d2f501c90
INBOX_PIN: eada41db0128c5b240a5dbca52cb49ef532f851d
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RANK_TRACE_BLOB: b0337bb10193b2498e6c35997a49237174c84a2c
DOSSIER_PIN: e64edd5f
Q3_ARCHIVE_BLOB: 45673892a89a7fa5aef62722df57a8d38e595e2f
ROUTE: CHALLENGER_NOT_RH
DENSITY_INPUT: UNCONDITIONAL_UNIFORM_INGHAM_WITH_LOG_POWER_5
DENSITY_THEOREM_REPROVED: false
NEW_TAIL_BOUND: O_c_LOG_m_POWER_7_OVER_1_PLUS_LOG_LOG_m_SQUARED
TAIL_NORM: NUCLEAR
MULTIPLICITIES_AND_BOTH_HEIGHT_SIGNS: RETAINED
PARITIES: EVEN_AND_ODD_SEPARATELY_AND_FULL_DIRECT_SUM
TAIL_BOUND_IS_ASYMPTOTIC_EQUALITY: false
TAIL_ERROR_IN_NORMALIZED_RANK_TRACE: o_N
NEW_POSITIVE_SIMPLE_ON_LINE_PROPORTION: NOT_PROVED
UNPAID_COUNT_INPUT: LEADING_NORMALIZED_SECOND_MOMENT_OF_LITERAL_CCM
Q3_QUOTED_SHIFT_ROBUST_TRACE_CAP: REFUTED
Q3_KILL_SCOPE: THEOREM_SHAPE_OF_LEMMA_9_27_AS_PRINTED
Q3_KILL_WITNESS: TAU_LOG_2_OVER_2PI_K_1_T_5625
Q3_GAP_ONLY_AT_t_TO_ZERO: false
Q3_CURRENT_LEAN_PIPELINE_AUDITED: false
FIXED_PHYSICAL_COMPLEMENT_GAIN: EXCLUDED_USING_INHERITED_THEOREM_4
RATE_LOG_m_OVER_SQRT_m_UNCONDITIONAL: NOT_DERIVED_FROM_THEOREM_4_ALONE
D1: CONFIRMED_AS_UPPER_BOUND
D2: REDUCED_TO_SECOND_MOMENT
D3: UNRESOLVED
D4: REFUTED_AS_EXCLUSIVE_DIAGNOSIS
D5: NOT_OBTAINED
VERIFIER: PAPER
EXACT_ALGEBRA_CHECKS: 18
DIAGNOSTIC_DPS: 65
NEW_ZERO_CENSUS: false
NEW_CCM_EIGENSYSTEMS: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
WRITE_BRANCH: proshka_inbox_2026-10-31
```

## 0. Результат

Ы. Плотностный ход работает: множитель sqrt(m), возникший из оплаты каждого нуля по худшему отступу 1/2, снимается. Для исходного прямоугольного CCM и T_m=(1+c(1+log L)/L)2pi m/L, 0<c<1 фиксировано, доказано

    ||R_T_m||_1 = O_c(L^7/(1+log L)^2),  L=log m.                 (A)

Это верхняя оценка полного ядерного хвоста, а не его асимптотика и не знак. Теорема действует для всех достаточно больших исходных m. Константа зависит от абсолютной константы классической плотностной теоремы; численный onset не вычислен.

Дополнительно оплачено влияние этого хвоста на rank-trace score: оно o(N(T_m)). Положительная доля пока не следует: нужен ведущий второй момент полной исходной матрицы, а не новая оценка тихой невязки. При старой безопасной нормировке sigma=2L simple-zero lower bound остается тривиальным даже после снятия хвоста. При sigma=L+O(1) сформулирован точный достаточный моментный критерий.

У Q3 обнаружена более ранняя, строгая ошибка: цитируемый shift-robust cap 9.27 ложен уже при K=1, B=75, t=75^2 и tau=log(2)/(2pi). Атом стоит точно в центре гауссиана; непрерывная верхняя цена убывает, дискретная масса не убывает. Это не рассуждение по аналогии с CCM и не гипотеза о RH.

## 1. Источники и граница импорта

**[FINITE_CELL | PAPER; source verification.]**

R1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_RANK_TRACE_CCM_2026-11-04.md` прочитан по eada41db; blob указан в YAML. Используются точная нулевая форма, (4.1)-(4.6), (5.1)-(5.8). Локальная старая копия имеет другую контрольную сумму и не заменяет этот pin.

R2. `docs/routeB_bus/proshka/PROSHKA_VERDICT_MYTHOS_HYPOTHESIS_DOSSIER_2026-11-03.md`, e64edd5f, Теорема 4/раздел 6: точные f_m в J-perp и предел (L/sqrt m)(C+uB)[f_m]. Это унаследованный PAPER-вход; его доказательство не повторяется.

R3. Исторический текст Q3 найден и прочитан на adbba53f:
`q3.lean.aristotle/literature/zotero/X3GJJT7W/fulltext.md`, blob 45673892a89a7fa5aef62722df57a8d38e595e2f. Проверены раздел 6, Lemmas 9.25-9.28, Theorem 12.6 и Section 13. Это архивная версия, содержащая ровно процитированную формулу 9.27; вывод не распространяется молча на исправленные версии или весь нынешний Lean-проект. Архимедов floor 2.5e-4 и рецепт B(K)=max(K+1,75) взяты из запроса; сам floor здесь заново не сертифицируется.

P1. Ingham (1940), *On the estimation of N(sigma,T)*, Q. J. Math. os-11, 201-202: используется классическая БЕЗУСЛОВНАЯ равномерная оценка

    N(sigma,U) <= C_I U^[3(1-sigma)/(2-sigma)] (log U)^5,
    1/2 <= sigma <= 1, U >= U_I.                            (1.1)

C_I и U_I абсолютны. Современный первичный источник: Chourasiya-Simonic, arXiv:2507.15184v2, introduction, включая определение счета с кратностями и uniformity. PDF pp.1-2 прочитан и просмотрен скриншотами. Их более сильные explicit constants и компьютерно проверенный начальный диапазон НЕ используются: достаточно старой (1.1), без RH/LH и без положительной таблицы нулей. Оригинальная публикация Ingham библиографически проверена, ее полный двухстраничный текст отдельно не получен. Импорт (1.1): THEOREM, не новая работа автора.

Используется также N(U)<=C_N U log U для U>=U_N, со счетом всех верхних нулей и кратностей. Это обычный безусловный счет, уже входивший в R1. Gamma/digamma имеют ту же нормировку, что в R1. Никакой положительный хвост не импортируется.

```text
https://arxiv.org/html/2507.15184v2
https://arxiv.org/pdf/2507.15184v2
https://doi.org/10.1093/qmath/os-11.1.201
```

## 2. Оплата одного нуля: именно m^|beta-1/2|

**[FINITE_CELL | PAPER; A/LA/F.]** Пишем rho=beta+i gamma, gamma>0, a=|beta-1/2|. Для четного carrier можно сменить знак спектральной точки и пользоваться z=gamma+i eta, |eta|=a. L=log m, Omega=2pi m/L. Унаследованная точная колонка:

    F_j(z)=2 d_j z sin(zL/2)/(sqrt(L)(z^2-omega_j^2)),
    omega_j=2pi j/L, d_0=1, d_j=sqrt(2) (j>0).

При gamma>=T>Omega:

    |sin(zL/2)|^2 <= exp(aL)=m^a,
    |z^2-omega_j^2| >= gamma^2-omega_j^2,
    |z|^2 <= gamma^2+1/4.

Следовательно, для evaluation-вектора e_E(z) имеем

    ||e_E(z)||^2 <= K_m(T) m^a/gamma^2,
    K_m(T)=4(2m+1)/L * (1+1/(4T^2))/(1-Omega^2/T^2)^2.    (2.1)

Нечетная колонка имеет модуль

    |F_j^O(z)|=2sqrt(2/L) omega_j |sin(zL/2)|/|z^2-omega_j^2|.

Поэтому sum_j |F_j^O(z)|^2 подчиняется той же (2.1): sum omega_j^2<=m Omega^2 и Omega<gamma. Константа не улучшается ради красоты.

Каждое слагаемое безусловной нулевой формы имеет ранг один, хотя не обязано быть положительным или даже само по себе эрмитовым. Его ядерная норма равна произведению норм двух evaluation-векторов. Реальность базиса и паритет дают равенство этих норм. Отраженные и сопряженные нули возвращают действительную самосопряженную форму; треугольное неравенство не меняет ее знак на PSD.

Определим счет с кратностями

    W_m(T)=sum_(rho: gamma>=T, gamma>0) m^|beta-1/2|/gamma^2.

Тогда для каждого паритетного блока отдельно

    ||R_T^E||_1, ||R_T^O||_1 <= 2 K_m(T) W_m(T).          (2.2)

Множитель 2 оплачивает обе высоты +/-gamma. Для полного carrier E direct_sum O годится удвоенная правая часть. Равенство высоты T включено в хвост; все кратности включены ровно один раз в W_m.

Это подтверждает разбор Mythos: sqrt(m) в старом envelope было заменой m^a<=m^(1/2), а не обязательным размером исходного хвоста. Степень m^a связана с экспоненциальным типом evaluation, но суммирование многих нулей требует плотности, а не одного supremum a.

## 3. Взвешенный счет и полный бесконечный хвост

**Теорема 1. [COFINAL_FAMILY | PAPER; THEOREM (1.1), Z/F/A.]** Пусть

    A_m(U)=sum_(0<gamma<=U) m^|beta-1/2|,
    d_T=(4/3)log T-L > 0.

Симметрия rho -> 1-conjugate(rho) сохраняет положительную высоту и кратность. Послойное интегрирование дает точное равенство, с несущественными для интеграла строгими границами:

    A_m(U)=N(U)+2L integral_0^(1/2) m^a N(1/2+a,U) da.    (3.1)

В частности, сдвиг левых нулей не объявляется отрицательным весом: он оплачен через отражение.

Положим f(a)=3(1/2-a)/(3/2-a). Тогда

    f(a)=1-2a/(3/2-a) <= 1-(4/3)a,
    (f(a)+a)'=1-3/(3/2-a)^2 <= -1/3.                    (3.2)

Таким образом, набросок показателя Mythos верен. Для всех U>=T>=max(U_I,U_N,e):

    A_m(U) <= C_N U log U
       +2 C_I L U(log U)^5 integral_0^(1/2)
                      exp(-[(4/3)log U-L]a) da
    <= C_N U log U + (2 C_I L/d_T) U(log U)^5.           (3.3)

Это равномерная оценка для всех U>=T при одном фиксированном m. Здесь T_m действительно порядка m/log m, а не m; положительность d_T явно проверяется, а не теряется под знаком '~'.

Stieltjes-интегрирование, с N(T-) на нижнем конце, дает

    W_m(T)=-A_m(T-)/T^2+2 integral_T^infinity A_m(U)/U^3 dU.

Граничный член неположителен. Введем P_5(v)=v^5+5v^4+20v^3+60v^2+120v+120. Получаем

    W_m(T) <= [2 C_N(log T+1)+(4 C_I L/d_T)P_5(log T)]/T. (3.4)

Верхняя граница в infinity равна нулю по (3.3). Это оплата ВСЕГО бесконечного хвоста, не одной диадической полосы.

Совместив с (2.2), имеем явный в терминах C_I,C_N envelope

    E_den(m,T)=8(2m+1)/(LT) * (1+1/(4T^2))
      /(1-Omega^2/T^2)^2
      *[2 C_N(log T+1)+(4 C_I L/d_T)P_5(log T)].          (3.5)

Он оценивает ядерную норму каждого паритета. Для полного блока можно взять 2E_den. Неизвестной smallest Gram eigenvalue или RH-посылки в (3.5) нет.

Для h=1+log L, epsilon=ch/L, kappa=1+epsilon, T=kappa 2pi m/L и больших m:

    log T=L-log L+log(2pi kappa),
    d_T>=L/6,
    (1-kappa^-2)^-2=O_c(L^2/h^2),
    (2m+1)/(LT)=O(1).

Например, log T>=7L/8 уже следует при L>=16 из log L<=L/8+log(2pi). Поэтому (3.5) доказывает (A). Все constants uniform при фиксированном c>0; uniformity c->0 не заявляется.

**Граница.** Доказано O_c(L^7/h^2), а не E~L^7/h^2 и не оптимальная степень логарифма. Более сильная логарифмическая плотность может уменьшить 7; для задачи o(N) это не требуется. Критический запас в показателе (3.2), а не современное улучшение далеко от 1/2, уже снимает sqrt(m).

## 4. Почему теперь ошибка rank-trace действительно o(N)

Одного E_den=polylog недостаточно без контроля множителя при смешанном моменте. Ниже этот контроль оплачен со стороны исходных матриц.

**Лемма 2. [COFINAL_FAMILY | PAPER; E/I/F/A/LA.]** Для буквального полного/even CCM:

    ||A_m||_F=O(sqrt(m)L^(5/2)),
    tr A_m=mL(1+o(1)).                                  (4.1)

Доказательство грубой первой оценки. В полном физически ортонормированном exponential-базисе j=-m,...,m оператор простых есть сумма двух направлений обрезанных сдвигов. Для каждого x коэффициенты этого exponential-sum имеют модули не больше c_n=Lambda(n)/sqrt(n). Узлы theta_n=log n/L на окружности имеют разделенность >=1/(mL), включая круговой зазор. Матрица Dirichlet kernel D_m(2pi(theta_n-theta_k)) имеет абсолютные суммы строк <=(2m+1)+2mL(1+log m): используем |D_m(2pi theta)|<=min(2m+1,1/(2||theta||)) и гармоническую сумму по двум сторонам узла. Schur test, разделение двух направлений и интегрирование по x дают

    ||B_m||_F^2 <=4[(2m+1)+2mL(1+L)] sum_(n<=m) c_n^2
                  =O(mL^5),
    sum c_n^2 <= L^2(1+L).

Это грубая оценка; точные корреляции n!=k не занулены. Использованы только фактическая целая решетка и Lambda(n)<=log n.

Архимедов оператор имеет operator norm O(L). Для единичного trigonometric f его interior derivative <=Omega и sup norm <=sqrt((2m+1)/L); поэтому

    ||f-T_u f||^2 <= min(4, Omega^2 u^2+4(2m+1)u/L).

Интегрирование с j(u), разделенное при u~L/m и 1, дает O(L). Его Frobenius norm O(sqrt m L). Полюс имеет ранг один и норму <=||sqrt(2)cosh(x/2)||_I^2=L+2sinh(L/2)=O(sqrt m). Сжатие на even не увеличивает HS-норму. Первая (4.1) доказана.

Для второй оценки prime trace в R1 ограничен O(sqrt m L^2), pole trace O(sqrt m+L). Arch symbol a_Gamma(v)=Re psi(1/4+iv/2)-log pi удовлетворяет a_Gamma(v)=log(|v|/(2pi))+O(v^-2) вдали от нуля и имеет конечную нижнюю границу. Для j>=1 Fourier probability density cosine-моды сосредоточена около +/-omega_j; ее масса в |v|<omega_j/2 есть O(1/j). Это следует прямо из двух sinc-колонок. Их момент порядка 1/2 конечен и <=C(1+omega_j)^(1/2), равномерно при L>=1. Jensen для log дает верх log(2+omega_j)+O(1); низкочастотная leakage дает нижнюю log omega_j-O(1)-O(log(2+omega_j)/j) при omega_j>=2. Суммирование j=1,...,m, отдельно O(L) малых j, дает arch trace m(log m-log L)+O(m+L^2). Это mL(1+o(1)); остальные части o(mL). Никакой нулевой знак не использован.

Теперь для любой sigma asymp L и N=N(T_m)~m из R1,(5.3):

    F_safe=4trA/sigma-4E_den/sigma
                    -(||A||_F/sigma+E_den/sigma)^2,
    F_safe=Phi(A/sigma)-o(N),
    Phi(X)=4trX-||X||_F^2.                              (4.2)

Действительно, потеря не больше

    4E_den/sigma+2||A||_F E_den/sigma^2+E_den^2/sigma^2
     =O_c(L^6/h^2+sqrt(m)L^(15/2)/h^2+L^12/h^4)=o(m).   (4.3)

Это закрывает именно прежний хвостовой барьер второго момента.

### 4.1. Доля: что получено, что осталось

**[COFINAL_FAMILY | PAPER / CONDITIONAL as indicated.]** При старой sigma=2L simple-count lower bound не становится положительным. Cauchy дает ||A||_F^2>=(tr A)^2/(m+1), поэтому

    F_safe-2N <= -(1/4+o(1))m.                           (4.4)

Это предел ЭТОЙ безопасной нормировки; не отрицательная доля и не запрет лучшим нормировкам.

Без таблицы нулей существует постоянная gamma_*>0, ниже которой нет нетривиальных нулей: xi не имеет вещественных нулей на компактном отрезке [0,1], а нули целой xi дискретны. Ее численное значение не требуется. Точная sampling-оценка R1 дает для критического простого нуля

    2||e_E(gamma)||^2 <= L+sin(L gamma)/gamma <= L+1/gamma_*.

Поэтому допустима sigma_m=L+1/gamma_*=L+O(1). Положим

    v_m=||A_m||_F^2/(sigma_m^2 N(T_m)).

Из (4.1)-(4.3) и унаследованного rank-trace:

    s_1(T_m)/N(T_m) >= max(0,2-v_m-o(1)),
    N_distinct(T_m)/N(T_m) >= max(0,(3-v_m)/2-o(1)).       (4.5)

Это новый полностью оплаченный перенос, но v_m еще НЕ оценено ведущей константой. Для доли >0 достаточно limsup v_m<2; для >=1/2 достаточно limsup v_m<=3/2; для >=2/3 достаточно limsup v_m<=4/3. Ни один из этих supplier здесь не доказан. Из грубой (4.1) следует лишь v_m=O(L^3).

Точное оставшееся арифметическое выражение — (4.4) R1, особенно

    sum_(n,k<=m) Lambda(n)Lambda(k)/sqrt(nk)
                   tr(R(log n)R(log k)),                (4.6)

совместно с arch/prime и pole/prime cross-термами. Ведущую константу нельзя получить удалением n!=k. Резонанс (1-Omega^2/T^2)^-2 теперь стоит лишь polylog и НЕ мешает масштабу o(N). Прямоугольный край остается важен для ведущего source-момента и sampling; новая оценка не превращает literal CCM в внешнее Gabor-окно.

## 5. Дискриминаторы: почему плотность не доказывает RH

**[ABSTRACT / COFINAL_FAMILY | PAPER; A/F/Z.]**

Подсадка конечного числа квартетов не разрушает асимптотическую плотностную оценку: счет меняется на O(1). Когда T_m проходит их высоты, их вклад вообще уходит из R_T в точную голову. Плохой знак головы не удален. До этого момента добавка оплачивается явно своим m^a/gamma^2. Таким образом, polylog-хвост совместим с наличием фиксированного off-line квартета; он не является положительным оператором и не дает b=0.

DH. Формула rank-one оплаты остается верной с его фактической полосой |beta-1/2|<=A_D и множителем 1+A_D^2/T^2. Но (1.1) для DH не дана: гамма-фактор, полюсы и log-derivative coefficients другие. 26 quartets до 900 — numerical census, не плотностная теорема. Никакая zeta-плотность на DH не переносится.

F_a=xi(s+a)xi(s-a), a>0. Из отражения как минимум половина верхних нулей xi имеет beta>=1/2. Их сдвиг вправо дает N_F(1/2+a/2,U)>=N_zeta(U)/2 при малом a>0. Это порядок U log U, несовместимый с (1.1) при sigma=1/2+a/2. Для больших a берем любой фиксированный sigma в (1/2,min(1,1/2+a)). Поэтому использование zeta-плотности для F_a было бы ложным. Все Gamma/pole изменения также обязательны.

Удвоенный атом 2 меняет исходную форму. Нельзя сохранить ее старую нулевую сумму и применить к новой форме тот же E_den. Сначала необходима matching completion/divisor; здесь она не выдумана. Положительность первых нескольких нулей нигде не служит доводом.

## 6. Q3: кэп 9.27 ложен уже в конечной точке

**Теорема 3. [FINITE_CELL | PAPER; E/I/A; KILL_SCOPE=THEOREM_SHAPE.]** Рассматриваем именно напечатанное и приведенное в запросе неравенство

    2 sum_(n>=2) Lambda(n)/sqrt(n)
      exp[-4pi^2 t(log n/(2pi)-tau)^2]
       <= exp(pi K)[rho(t)+2pi K sigma(t)].               (6.1)

При K=1, tau=log2/(2pi), t=5625 оно неверно. Любой B>0, в частности B=75, не устраняет свидетель: Fejer taper в центре равен 1.

Левая часть >=w_2=sqrt(2)log2>14/15. Последнее следует из log2>2/3 и sqrt2<10/7. Все остальные члены неотрицательны.

Для правой части положим A=4pi^2t, b=1/2. Точно

    sigma(t)=sqrt(pi/A) exp(1/(16A)) [1+erf(1/(4sqrt A))],
    rho(t)=1/A+sigma(t)/(4A).                            (6.2)

Из by<=Ay^2/2+b^2/(2A):

    sigma(t)<=sqrt(2pi/A) exp(1/(8A)).

При t=5625, A=22500pi^2, элементарные границы pi>3, pi<22/7, sqrt2<10/7, sqrt(pi)>12/7, exp(1/(8A))<1001/1000 дают

    sigma<1001/180000, rho<1/200000, exp(pi)<24.

Следовательно, правая часть (6.1) строго меньше

    24[1/200000+(44/7)(1001/180000)]
       =62929/75000 <14/15.                              (6.3)

Получен отрицательный верхний envelope RHS-LHS<62929/75000-14/15<0. Это точный контрпример действительному prime-источнику, не toy-matrix. exp(pi)<24 можно проверить из pi<22/7 и ряда exp с геометрической верхней оценкой остатка; численная таблица не является основанием (6.3).

При 65 dps, только DIAG:

    RHS=0.5473092957792358318519336245184927103992,
    atom2=0.9802581434685471917139017236352333812915.

### 6.1. Точная строка ошибки в архивном доказательстве

В proof Lemma 9.27 написано: bound the sum by an integral of the positive integrand, затем (9.21). Положительность integrand не разрешает заменить сумму масс над сужающимся пиком интегралом без добавочной lattice/point-mass цены. При tau=xi_2 масса атома всегда w_2, а интеграл ширины t^(-1/2) уходит к нулю.

Кроме того, при c=2pi tau верная замена координаты для такого интеграла:

    integral_1^infinity (log x)/sqrt x
          exp[-t(log x-c)^2] dx
      =exp(c/2) integral_(-c)^infinity (y+c)exp(y/2)exp(-t y^2)dy.

В (9.21) одновременно используется иной коэффициент 4pi^2t и нижний предел 0 вместо -c. Это не тождество исходной левой части. Но даже исправление этих двух опечаток НЕ чинит сумму -> интеграл: атомный контрпример остается.

Если TP действительно является суммой нормированных rank-one sampling operators с заявленными весами, центрирование на p=3 дает eigenvalue lower bound 2log3/sqrt3>1. Поэтому uniform I-TP>=0 для ВСЕХ shifts, содержащих xi_3, также несовместимо с этой нормировкой. При иной нормировке kernel sections требуется заново вычислить trace; ее нельзя менять молча.

## 7. Снятие тепла: корректная граница после ремонта кэпа

**[ABSTRACT | PAPER; A/LA.]** Выделим вопрос пределов отдельно от уже опровергнутой (6.1). Для двух ИНТЕГРАЛЬНЫХ функций из запроса, независимо от ложного lattice bound, из (6.2):

    t -> 0+:
    sigma(t) ~ exp(1/(64pi^2t))/(sqrt(pi)*sqrt t),
    rho(t) ~ exp(1/(64pi^2t))/(16pi^(5/2)t^(3/2));

    t -> infinity:
    sigma(t) ~ 1/(2sqrt(pi)*sqrt t),
    rho(t) ~ 1/(4pi^2t).

Значит exp(pi K)[rho+2pi K sigma] расходится при t->0. При фиксированном t она расходится и при K->infinity. Чтобы эта конкретная функция оставалась ограниченной при K->infinity, требуется t как минимум порядка K^2 exp(2pi K), а не t~K^2. При пользовательском t=B(K)^2~K^2 она ведет себя как sqrt(pi)exp(pi K). Это асимптотика формулы кэпа, не доказательство actual operator blow-up по неверному upper bound.

Тепловой множитель S_t имеет Fourier symbol exp(-4pi^2t xi^2). На band |xi|<=K:

    ||S_t f||^2>=exp(-8pi^2tK^2)||f||^2,
    ||S_t^-1||=exp(4pi^2tK^2).

Поэтому запас, измеренный в сглаженной норме, при возврате в исходную норму может вырождаться. На всем L2 inverse неограничен. Ненулевой multiplier дает L2-плотность образа, но она НЕ является доказанной плотностью в топологии полной формы Вейля с ее endpoint/prime/pole terms.

Важно: одна неограниченность inverse не опровергает перенос НЕОТРИЦАТЕЛЬНОСТИ. Если same-source identity действительно доказана на form-core и смешанные формы непрерывны в нужной топологии, то знак проходит по плотности даже с исчезающим строгим запасом. Здесь должны быть доказаны именно эти предпосылки, а не сохранен фиксированный gain.

### 7.1. Точный RH-содержащий переход Q3

В архиве R3, Theorem 12.6, после positivity конечной Toeplitz формы написано: (A1')-(A2) extend from the dense cone to all W_K. Это допустимый общий принцип лишь при одних и тех же source, норме и кванторах параметров.

Требуется совместный контракт:

    для каждого исходного Weil-square f * f^*, выбрать ДОПУСТИМЫЕ
    сглаженные approximants, на которых доказана именно полная source-форма;
    приблизить исходный тест с исчезающей ошибкой ВСЕХ смешанных членов
    и без удаления prime powers, Gamma, полюсов и граничных масс.

Положительность одного выбранного smoothing schedule не обеспечивает плотности всего допустимого cone. Section 6.2 использует свободный scale; Lemma 6.3 использует узкие Fejer hats, тогда как большой B и выбранное t из positivity recipe имеют другие кванторы. Существование произвольных approximants и существование положительного семейства не доказывают существование ПОЛОЖИТЕЛЬНЫХ approximants для каждого f.

В Lemma 9.25 (RKHS-Weil Isometry) дополнительно требуется доказать Gram identity W(phi_x,phi_y)=k(x,y). Из абстрактного положительного RKHS kernel и названия Weil representation это равенство не следует. После правильного source identification и form-core transfer cofinal lower floor имеет унаследованный RH-consumer. Само утверждение compact-union после уже доказанной positivity на каждом полном compact формально безвредно; содержание лежит ДО него.

Дополнительный domain guard: в архиве есть линейный functional integral a(xi)Phi(xi)dx-sum w_n Phi(xi_n) на ВСЕХ nonnegative compact Phi. Он не может быть неотрицателен на таком cone. Узкий четный tent вокруг +/-xi_2 имеет arch integral O(width), но сохраняет отрицательный атом -w_2. Поэтому его positivity следует проверять на правильном cone корреляционных/Weil-square тестов, а не на всех pointwise-positive Phi. Это контрпример напечатанному слишком широкому классу, не контрпример критерию Вейля.

## 8. Согласование с Теоремой 4: скорость нужно формулировать честно

**[COFINAL_FAMILY | PAPER; inherited R2 plus LA.]** На унаследованных единичных f_m in J-perp и m_k:

    C[f_m] ~ c_gamma sqrt(m)/L, c_gamma=(gamma^2+1/4)^(-2)>0,
    W[f_m]=o(sqrt(m)/L).

Предположим, что перенос Q3 действительно дал в ЭТИХ физических координатах

    -B <= theta_m C+E_m I.

Тогда обязательно

    (1-theta_m) C[f_m] <= W[f_m]+E_m.                    (8.1)

При E_m=O(1) отсюда следует отсутствие любого fixed theta<1. Но из Теоремы 4 ОДНОЙ не следует 1-theta_m=O(L/sqrt m): для этого нужен дополнительный UPPER bound W[f_m]=O(1). При нем (8.1) действительно дает нужную скорость. Без него честный вывод:

    1-theta_m <= o(1)+O(L/sqrt m),                       (8.2)

с неизвестной скоростью первого слагаемого. И даже при дополнительном bound это необходимая верхняя оценка gain, не асимптотическое равенство.

Нельзя напрямую отождествить Q3 t или K с CCM L,m без единичного source/norm map. Возможны фиксированный RKHS-gain и вырождающийся physical-gain; это не противоречие. Невозможен именно фиксированный выигрыш после корректного равномерного возврата к данному дополнению.

## 9. Ledger, predictions, reopen triggers

| Claim | Scope | Verifier/class | Result |
|---|---|---|---|
| Zero-wise nuclear payment m^a | FINITE_CELL | PAPER, A/F/LA | Both parities; all multiplicities |
| Weighted tail (3.5) | COFINAL_FAMILY | PAPER + THEOREM Ingham | Proved, not numerical onset |
| Polylog tail (A) | COFINAL_FAMILY | PAPER | sqrt(m) removed |
| Source rough HS and leading trace | COFINAL_FAMILY | PAPER, E/I/F/A | Proved as (4.1) |
| Rank-trace tail cost o(N) | COFINAL_FAMILY | PAPER | Proved |
| Fraction >=1/2 or 2/3 | COFINAL_FAMILY | CONDITIONAL | Needs normalized second moment |
| Q3 (9.19) all shifts | FINITE_CELL | PAPER | Refuted by actual atom2 |
| Correct full Weil form positivity | COFINAL_FAMILY | CONDITIONAL / OPEN | Not supplied |
| Physical fixed gain excluded | COFINAL_FAMILY | PAPER, inherited R2 | Exact consumer retained |

Predictions MYTHOS, unchanged priors:

- D1 (.50): CONFIRMED as an upper-bound theorem. No asymptotic equivalence is inferred.
- D2 (.35): REDUCED. The old tail obstruction is paid; sigma=2L still gives zero simple-count guarantee, sharper sigma leaves limsup v_m<2 unpaid.
- D3 (.15): UNRESOLVED. >=0.5 would follow from limsup v_m<=1.5, not established.
- D4 (.60): REFUTED in its exclusive wording. A finite atom already contradicts quoted 9.27; after repair, heat/source/form-core matching still bears the RH content. The L/sqrt m rate needs the extra bound specified in section 8.
- D5 (.03): NOT OBTAINED. Tail smallness permits finite off-line exceptions; no source sign proved.

Before executing the checks in the appendix the following expectations were registered: the density exponent slack is nonnegative; both parity column bounds hold with the displayed coefficient; the shifted atom violates the cap; the cap integral closed form agrees with direct quadrature. All passed at their stated EXACT/DIAG scope. These checks do not verify the imported Ingham theorem or replace its quantifiers.

Reopen triggers: (i) a source proof of limsup v_m<2, retaining all terms of (4.6); (ii) a corrected point-mass-aware Q3 cap and a SAME-SOURCE form-core map for its admissible parameters; (iii) an upper bound W[f_m]=O(1) to sharpen (8.2). Densities alone, a critical-line prefix, or a smaller quiet residual do not satisfy these triggers.

Two alternative representations of the still-open sign/moment input: keep the joint signed tail scalar from R1 (high kill-power, moderate analytic cost), or work directly on the source double-prime overlap kernel (high kill-power, higher cost; targets the now unpaid leading moment). Neither is authorized as a proof by renaming. The cheapest decisive test of any claimed uniform Q3 cap is to center it at a single prime node, before any large run.

K8A: downstream consumer is the original full Weil form / complement floor, not a smoothed surrogate. The requested tail bound is supplied but is NOT sufficient for that consumer. Failure type of quoted 9.27: COUNTEREXAMPLE, theorem-shape only. Global sign remains RESEARCH_DEBT; no route-family death or RH claim. Independent analytic review, Lean and Arb were not executed.

Delivery: exactly this new Markdown file; no route state or Lean source modified. Commit SHA is returned in the delivery message after GitHub write/readback, since a file cannot contain its own commit hash in advance. Gate: verify the returned blob, extract the Python appendix, run it, then independently audit (3.1)-(4.5) and the finite counterexample. Passing code checks does not promote PAPER to LEAN.

## Appendix. Reproducible checks

The script below checks algebra and DIAG normalizations. It uses no zero list and computes no CCM spectrum. Run with Python plus sympy/mpmath, for example `uv run --with sympy --with mpmath check.py` after extracting this block. Numeric output is not an interval certificate.

```python
#!/usr/bin/env python3
"""Exact algebra and DIAG checks only; no zeta-zero list or interval sign gate."""
import json
from fractions import Fraction
import sympy as s
import mpmath as mp

# Registered before execution: exponent monotonicity, norm return, endpoint
# conventions, and the shifted atom counterexample. No RH/sign conclusion.
checks = []
def eq(name, lhs, rhs=0):
    assert s.simplify(lhs-rhs) == 0, name
    checks.append(name)

a, ell, x, t = s.symbols('a ell x t', real=True)
f = 3*(s.Rational(1,2)-a)/(s.Rational(3,2)-a)
eq('density_exponent_exact', f, 1-2*a/(s.Rational(3,2)-a))
eq('density_derivative', s.diff(f,a), -3/(s.Rational(3,2)-a)**2)
eq('weighted_derivative_at_zero', s.diff(f+a,a).subs(a,0), -s.Rational(1,3))
eq('linear_density_slack', 1-s.Rational(4,3)*a-f, 8*a*a/(3*(3-2*a)))
P5 = sum(s.factorial(5)/s.factorial(k)*ell**k for k in range(6))
eq('integrated_log_polynomial', P5-s.diff(P5,ell), ell**5)
eq('P5_at_zero', P5.subs(ell,0), 120)
eq('density_uniform_gap', s.Rational(4,3)*s.Rational(7,8)-1, s.Rational(1,6))
N0, u = s.symbols('N0 u', positive=True)
eq('single_layer_cake', 1+s.integrate(ell*s.exp(ell*u),(u,0,a)), s.exp(ell*a))

v = s.Matrix([1+s.I,2-s.I,-s.I])
w = s.Matrix([2,s.I,1-s.I])
R = v*w.conjugate().T
eq('rank_one_norm_product', s.trace(R.conjugate().T*R), (v.conjugate().T*v)[0]*(w.conjugate().T*w)[0])
A = s.Matrix([[2,1],[1,-1]])
B = s.Matrix([[1,s.Rational(1,2)],[s.Rational(1,2),2]])
phi = lambda X: 4*s.trace(X)-s.trace(X*X)
eq('signed_tail_score', phi(A-B), phi(A)-4*s.trace(B)+2*s.trace(A*B)-s.trace(B*B))
q = s.symbols('q')
eq('simple_proportion_score', 4-q-2, 2-q)
eq('distinct_proportion_score', (4-q-1)/2, (3-q)/2)
eq('safe_2L_score_ceiling', 4*s.Rational(1,2)-s.Rational(1,4)-2, -s.Rational(1,4))

# Rational majorant in section 9: all transcendental input bounds are proved
# in the PAPER text. This is NOT an interval evaluation of pi or exp.
cap_upper = Fraction(24)*(Fraction(1,200000)+Fraction(44,7)*Fraction(1001,180000))
assert cap_upper == Fraction(62929,75000)
assert cap_upper < Fraction(14,15)
checks.extend(['rational_cap_upper', 'rational_atom_contradiction'])

A0, b = s.symbols('A0 b', positive=True)
y = s.symbols('y', nonnegative=True)
# Completing the square and its stationary point.
eq('gaussian_square', -A0*y*y+b*y, -A0*(y-b/(2*A0))**2+b*b/(4*A0))
eq('gaussian_peak_exponent', (b*b/(4*A0)).subs({b:s.Rational(1,2),A0:4*s.pi**2*t}), 1/(64*s.pi**2*t))
eq('pullback_gain', ((1-t)*x), x-t*x)

mp.mp.dps=65
def cap(t0):
    aa=4*mp.pi**2*t0
    sig=mp.sqrt(mp.pi/aa)*mp.exp(1/(16*aa))*(1+mp.erf(1/(4*mp.sqrt(aa))))
    rho=1/aa+sig/(4*aa)
    return rho,sig
rho,sig=cap(mp.mpf(5625))
diag={'cap_K1_t5625':mp.nstr(mp.exp(mp.pi)*(rho+2*mp.pi*sig),40),
      'atom2':mp.nstr(mp.sqrt(2)*mp.log(2),40)}
quadrature=[]
for tt in [mp.mpf(1),mp.mpf(5625)]:
    rr,ss=cap(tt)
    aa=4*mp.pi**2*tt
    # Scale to avoid missing a narrow Gaussian near the origin.
    sn=2/mp.sqrt(aa)*mp.quad(lambda z:mp.exp(-z*z+z/(2*mp.sqrt(aa))),[0,1,mp.inf])
    rn=2/aa*mp.quad(lambda z:z*mp.exp(-z*z+z/(2*mp.sqrt(aa))),[0,1,mp.inf])
    assert abs(ss-sn)<mp.mpf('1e-60') and abs(rr-rn)<mp.mpf('1e-60')
    quadrature.append({'t':str(tt),'max_abs_error':mp.nstr(max(abs(ss-sn),abs(rr-rn)),8)})

# Direct evaluation formulas, both parities, no zeros are used.
columns=[]
for mm in [3,8,40]:
    LL=mp.log(mm); Om=2*mp.pi*mm/LL
    z=mp.mpf('1.1')*Om+mp.mpf('0.3')*1j
    ev=[]; od=[]
    for j in range(mm+1):
        om=2*mp.pi*j/LL
        dj=1 if j==0 else mp.sqrt(2)
        ev.append(2*dj*z*mp.sin(z*LL/2)/(mp.sqrt(LL)*(z*z-om*om)))
        if j:
            od.append(-2j*mp.sqrt(2/LL)*om*mp.sin(z*LL/2)/(z*z-om*om))
    gam=mp.re(z)
    bound=4*(2*mm+1)/LL*(1+1/(4*gam**2))/(1-Om**2/gam**2)**2*mm**mp.mpf('0.3')/gam**2
    re=mp.fsum(abs(vv)**2 for vv in ev)/bound
    ro=mp.fsum(abs(vv)**2 for vv in od)/bound
    assert re<1 and ro<1
    columns.append({'m':mm,'even_bound_ratio':mp.nstr(re,12),'odd_bound_ratio':mp.nstr(ro,12)})

result={'status':'EXACT_ALGEBRA_PLUS_DIAG_NOT_INTERVAL',
        'exact_checks':len(checks),'exact_check_names':checks,
        'rational_cap_upper':str(cap_upper),'rational_atom_lower':'14/15',
        'diagnostic':diag,'quadrature':quadrature,'column_bounds':columns,
        'new_zero_census':False,'new_CCM_spectra':False,'LEAN':False,'ARB':False}
print(json.dumps(result,indent=2,ensure_ascii=False))

```

Executed output:

```json
{
  "status": "EXACT_ALGEBRA_PLUS_DIAG_NOT_INTERVAL",
  "exact_checks": 18,
  "exact_check_names": [
    "density_exponent_exact",
    "density_derivative",
    "weighted_derivative_at_zero",
    "linear_density_slack",
    "integrated_log_polynomial",
    "P5_at_zero",
    "density_uniform_gap",
    "single_layer_cake",
    "rank_one_norm_product",
    "signed_tail_score",
    "simple_proportion_score",
    "distinct_proportion_score",
    "safe_2L_score_ceiling",
    "rational_cap_upper",
    "rational_atom_contradiction",
    "gaussian_square",
    "gaussian_peak_exponent",
    "pullback_gain"
  ],
  "rational_cap_upper": "62929/75000",
  "rational_atom_lower": "14/15",
  "diagnostic": {
    "cap_K1_t5625": "0.5473092957792358318519336245184927103992",
    "atom2": "0.9802581434685471917139017236352333812915"
  },
  "quadrature": [
    {
      "t": "1.0",
      "max_abs_error": "1.186946e-66"
    },
    {
      "t": "5625.0",
      "max_abs_error": "4.6365077e-69"
    }
  ],
  "column_bounds": [
    {
      "m": 3,
      "even_bound_ratio": "0.153641489167",
      "odd_bound_ratio": "0.116618666829"
    },
    {
      "m": 8,
      "even_bound_ratio": "0.043401314176",
      "odd_bound_ratio": "0.0292671021079"
    },
    {
      "m": 40,
      "even_bound_ratio": "0.0138691898359",
      "odd_bound_ratio": "0.00804286314893"
    }
  ],
  "new_zero_census": false,
  "new_CCM_spectra": false,
  "LEAN": false,
  "ARB": false
}

```
