# STATUS: TRY_EULER_SIGN_CONE_DH_SCOPE
```yaml
OPERATIVE_CLASS: TRY_EULER_SIGN_CONE_DH_SCOPE
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_DH_ARCHIVE_AND_EULER_CONE_REQUEST
SOURCE_BASE: d26831357b6cb3b2b7d4a569d2031e454952b246
SOURCE_KERNEL_COMMIT: c31645a3efd410417f6e2027b4474711bd443348
SOURCE_KERNEL_BLOB: 98380adf97aab19a900e332b6583c8f731b6d3f6
SOURCE_DH_NORMALIZATION_BLOB: eaebfaf7d208a02be8411259e1401a99c61f9bb4
SOURCE_DH_RESULT_BLOB: c8f4bd8b672325d2405f0d27ac7e39b5e5968c32
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
OLD_DH_BEURLING_VERDICT: RECOVERED_FROM_CONCURRENT_OWNER_RELAY
OLD_VERDICT_COMMIT: 4a8ca65f47f276a17e5215d4507db189c77a5f41
OLD_VERDICT_BLOB: b947112504dd70461d143be5ce1471eb4ca93322
OLD_VERDICT_WRITTEN_BY_THIS_RESPONSE: false
OLD_VERDICT_PRESENT_ON_TARGET_BRANCH: VERIFIED
OLD_WITNESS_USED: SECTION_7_NORMALIZED_PROJECTION_OF_DH_BOTTOM
REVISION_REASON: ORIGINAL_SOURCE_BECAME_AVAILABLE_DURING_READBACK
E_CONE_FLOOR: PROVED
LITERAL_CONE_DIMENSION: CHARACTERIZED_NOT_NUMERICALLY_DETERMINED
MAXIMALITY_SCOPE_1: ALL_NONNEGATIVE_ATOMIC_WEIGHTS_WITH_NO_SIZE_BOUND
MAXIMALITY_SCOPE_2: INDEPENDENT_ATOM_DELETION_BOX_WITH_FIXED_WEIGHT_UPPERS
MAXIMALITY_SCOPE_3: PRIME_BLOCK_DELETION_PRESERVING_FIRST_SECOND_POWER_RATIO
UNRESTRICTED_ZETA_COMPLEMENT_BOUND: NOT_PROVED
D2_SIGN_ADAPTED_CONE: EVENTUALLY_OUTSIDE_USING_INHERITED_DH_C
D2_LITERAL_Q_NONPOSITIVE_CONE: NOT_DETERMINED
DH_SIGN_TRANSFER: REFUTED_BY_EXACT_LITERAL_CARRIER_PRIME_BLOCK_TEST
DH_TEST_IS_D2: false
BEURLING_TRANSFER: CONDITIONAL_ON_SEPARATELY_SUPPLIED_FORM_AND_DOMAIN
VERIFIER: PAPER
EXACT_ALGEBRA_CONTROLS_PASSED: 8
INDEPENDENT_ANALYTIC_AUDIT: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
```

## 0. Источники, параллельная доставка и классификация

Во время работы исходный DH/Beurling-вердикт был добавлен в запрошенную ветку отдельным owner-relay коммитом `4a8ca65f47f276a17e5215d4507db189c77a5f41` (Mythos). Его путь: `docs/routeB_bus/proshka/PROSHKA_VERDICT_FAKE_WORLD_EFZ_DH_2026-11-02.md`, blob `b947112504dd70461d143be5ce1471eb4ca93322`. Коммит содержит сообщение о verbatim-доставке; побайтного сравнения с первоначальным отсутствовавшим вложением эта сессия не выполняла. Файл прочитан из ветки; повторно создавать либо менять его не требуется. Его появление разрешило первоначальный source-gap. Собственный коммит `3646052237f8d5b3c7b33b8e0280593fe293f171` содержал предварительный разбор до обнаружения relay; настоящая редакция исправляет его устаревшие пометки об отсутствии источника.

Прочитаны:
- S1: `docs/routeB_bus/fake_worlds_2026-11-02/NORMALIZATION_DH.md` и `RESULT.md` на SOURCE_BASE d268313. Первый задаёт DH-форму, второй — численные диагностики, не сертификаты.
- S2: `PROSHKA_VERDICT_KERNEL_ORTHOGONALITY_2026-11-02.md` на c31645a, §§1–3 и (12).
- S3: восстановленный `PROSHKA_VERDICT_FAKE_WORLD_EFZ_DH_2026-11-02.md` на 4a8ca65, §§1,3–8. Его кофинальные DH-Q/DH-N/DH-C здесь используются как унаследованные PAPER-выводы, не как независимо проверенные этой сессией теоремы. Конкретный complement-witness — нормированная проекция bottom в §7, (7.1); именно он проверяется ниже. Глобальная quartet-функция §6.1 — другой промежуточный свидетель.

Классификация теперь сохраняет легенду S3: **E** — Euler product и точные коэффициенты/prime-power support; **F** — конкретное функциональное уравнение с gamma/pole-данными; **Z** — счёт нулей/кратностей, НЕ их расположение; **LA** — линейная алгебра и Fourier-геометрия окна. В S3 дополнительно нужны **A** (аналитическое продолжение и фактические узлы) и **I** (обычная целочисленная структура). Их нельзя скрывать внутри E/F/LA. Новые конусные знаки ниже не используют нулевую явную формулу; исходное W и сам DH-witness наследуют свои A/F/Z-поставщики. Нижняя оценка из E всегда применяется к уже определённой F-форме.

## 1. Нормировки и ответ (a)

[FINITE_CELL | PAPER; F.] Пусть W=J_m^perp — реальный чётный carrier, q=dim W. Все функции продолжаются нулём, L=log m. В координатах независимых оконных ядер из c31645a:

    f=sum c_alpha k_alpha,    ||f||²=c^T G c,    G>0,
    Q_f(s)=c^T R(s)c,         R(0)=2G, R(L)=0.

Положим P[f]=sum_(p^k<=m) w_(p^k) Q_f(log p^k), w_(p^k)=log(p)/p^(k/2)>0, и

    B0[f]=A[f]+|<p,f>|² >=0,
    k[f]=B0[f]-c_*||f||²-P[f].                           (1)

Здесь A — весь положительный архимедов jump-интеграл, включая хвост. Нечётный полюс занулён по чётности. Запрос задаёт

    C_m={f in W: Q_f(log p^k)<=0 for every p^k<=m}.

[COFINAL_FAMILY | PAPER; E, при заданной F-нормировке.] Для КАЖДОГО m и f in C_m:

    P[f]<=0,    k[f]>=-c_*||f||².                        (2)

Доказательство — сумма неположительных корреляций с положительными весами и B0>=0. Никакого условия на расположение нулей не нужно. Атом n=m, если он существует, умножается на Q_f(L)=0.

Нужно отличать H_m из c31645a от полной A. Для I_m=integral_0^L exp(s/2)R(s)ds точное pole/continuum-равенство даёт

    B0_matrix=H_m+I_m+4G.

Поэтому матрица M_m в (12) предшественника равна точно

    M_m=P12_matrix-B0_matrix+4G,                         (3)

где P12 содержит только простые и квадраты. На C_m уже P12[f]<=0, следовательно c^T M_m c<=4c^T Gc. Здесь K=4, а не 4+C3: высшие степени в (12) уже вычтены. Это квадратичное неравенство НА КОНУСЕ, не Loewner-неравенство на всём W.

## 2. Размер конуса: точная геометрия, а не вычитание числа атомов

[FINITE_CELL | PAPER; LA.] Удалим тождественно нулевые ограничения, в частности n=m. Положим

    M_n=G^(-1/2) R(log n) G^(-1/2),    x=G^(1/2)c.

Тогда C_m изометричен замкнутому однородному полуалгебраическому множеству

    {x in R^q: x^T M_n x<=0 for every retained prime power n}. (4)

При q=0 имеем W=C_m={0}, и сферический критерий ниже не применяется. При q>0 оно инвариантно при x->-x; выпуклость не гарантирована. Поэтому число неравенств не является коразмерностью. Если ограничений не осталось, C_m=W. Иначе определим достигаемый минимум

    eta_m=min_(||x||=1) max_n x^T M_n x.                  (5)

Точная трихотомия:
- eta_m>0: C_m={0}.
- eta_m<0: C_m содержит открытый сектор; dim(C_m)=q и его сферическая мера положительна.
- eta_m=0: ненулевые допустимые векторы есть, но строгого сектора нет; 1<=dim(C_m)<=q-1.

Доказательство: компактность сферы; непрерывность конечного списка форм. В третьем случае каждый допустимый ненулевой вектор лежит хотя бы на одной границе x^T M_n x=0. Конечное объединение нулевых множеств ненулевых квадратичных полиномов имеет размерность <=q-1. В первом случае единичный допустимый вектор невозможен.

Это полная характеристика типа размера. Значение eta_m для буквального W в этом ответе НЕ вычислено и не оценено кофинально. Исходники не содержат такого сертификата; одно равенство W=ran(E^T) его не даёт.

Для линейного S contained C_m обязательно

    dim S <= min_n [n_-(M_n)+n_0(M_n)].                   (6)

Действительно, S не может пересечь положительное спектральное пространство соответствующей формы. Одновременные ограничения могут уменьшить размер ещё сильнее. Достаточный сертификат C_m={0}: найти t_n>=0 с sum t_n M_n positive definite. Тогда сумма допустимых неравенств противоречит положительности на каждом ненулевом x.

Препятствие универсальному размеру из одного знака весов: на R^q одна форма -I даёт весь R^q, I даёт только {0}, а diag(I_j,0) даёт подпространство размерности q-j. Это ABSTRACT/LA-контроли, не другие CCM. Они исключают вывод о размере без фактических correlation matrices, но не предсказывают eta_m литерального источника.

Отдельно: «наибольшее подпространство» вообще может не существовать по включению. Для q(x,y)=x²-y² все прямые x=t y, |t|<=1, — максимальные неположительные подпространства размерности 1, но никакое одно не содержит остальные. Для настоящего W можно искать максимальную РАЗМЕРНОСТЬ по критерию (10), не приписывая ему канонический максимизатор. Это LA-препятствие единственному неоговорённому максимальному подпространству, не вычисление размерности буквального C_m.

## 3. Ответ (b): строго определённые понятия максимальности

### 3.1 Только неотрицательность, без upper на веса

[FINITE_CELL | PAPER; E+LA.] Зафиксируем W и B0, но разрешим любую неотрицательную меру sum a_n delta_(log n) на указанном конечном наборе атомов, без ограничения величины a_n. Тогда C_m — МАКСИМАЛЬНЫЙ класс векторов, на котором из этих данных следует floor (2), и даже floor с любым фиксированным конечным slack, общим по разрешённым a_n.

Доказательство: если f notin C_m, есть n0 с Q_f(log n0)>0. Увеличивая только a_(n0) до infinity, получаем

    B0[f]+beta||f||²-sum a_n Q_f(log n) -> -infinity

при любом заранее фиксированном beta. Положительность B0 не может поглотить атом неограниченной величины. Обратное направление — (2).

Для ТОЧНОЙ (12), где высокие степени уже удалены, соответствующий максимальный sign-only класс больше:

    C12_m={f in W: Q_f(log p)<=0, Q_f(2log p)<=0
                    at every retained prime or prime square}. (7)

На C12_m выполнено (12) с K=4 для всех m. Полный Weil-floor здесь >=-(c_*+C3)||f||² с уже доказанной C3=(1+sqrt(2))(8+5log2)<28. Высшие степени не выброшены, а оплачены. C_m contained C12_m; строгость включения для данного W не утверждается.

ВАЖНО: масштабирование a_n — контрпример к выводу ИЗ ОДНОГО ЗНАКА, не другая система настоящих простых с прежними нулями. Оно не опровергает арифметического усиления для фиксированных Lambda.

### 3.2 Фиксированные верхние веса и совместная архимедова цена

[FINITE_CELL | PAPER; E+F+LA.] Для n=p или p² положим

    P12_plus[f] =sum w_n [Q_f(log n)]_+,
    P12_minus[f]=sum w_n [-Q_f(log n)]_+,
    D_(m,beta)={f in W: P12_plus[f]<=B0[f]+beta||f||²}, beta>=0. (8)

Тогда на D_(m,beta) доказана (12) с K=4+beta. Это явный, потенциально больший класс: C12_m contained D_(m,0). Более того, B0[f]>0 для ненулевого компактно поддержанного f, поэтому каждая ненулевая точка C12_m имеет окрестность в D_(m,0). Это не утверждение, что C12_m ненулево или что D_(m,0)=W.

Класс (8) МАКСИМАЛЕН для следующего точного сертификата: оценка должна переживать независимое удаление/ослабление каждого атома,

    0<=a_n<=w_n.

Точно, для каждого фиксированного f,

    sup_(0<=a_n<=w_n) sum a_n Q_f(log n)=P12_plus[f].      (9)

Оптимум достигается выбором a_n=w_n на положительных корреляциях и a_n=0 на отрицательных. Поэтому (8) необходимо и достаточно для такого deletion-robust сертификата. Архимедов и полюсный члены остаются полностью, без модулей по ним.

Для линейного подпространства S с синтезом U условие S contained D_(m,beta) равносильно конечному семейству

    U^T [B0_matrix+beta G-sum_(n in B)w_n R(log n)] U >=0
                      for every subset B of retained atoms. (10)

Это точный LA-критерий; число условий может быть большим. Непроверенная положительная часть целевой матрицы не выдается за независимо построенный фактор.

### 3.3 Более сильный E-класс: не разрывать степени одного простого

[FINITE_CELL | PAPER; E+F+LA.] Предыдущая модель допускает независимое ослабление p и p². У настоящего источника их веса связаны. Сохраним эту связь:

    U_p[f]=p^(-1/2)Q_f(log p)+1_(p²<=m)p^(-1)Q_f(2log p),
    P12[f]=sum_(p<=m) (log p) U_p[f].

Конус Cblock_m={f in W: U_p[f]<=0 for every p<=m} содержит C12_m и также даёт (12) с K=4. Это не равенство с C12_m: положительная корреляция при p теперь может оплачиваться отрицательной при p² с ТОЧНЫМ коэффициентом p^(-1/2).

Ещё более широкий явный класс:

    Pi_plus[f]=sum_p(log p)[U_p[f]]_+,
    Pi_minus[f]=sum_p(log p)[-U_p[f]]_+,
    Dblock_(m,beta)={f in W: Pi_plus[f]<=B0[f]+beta||f||²}. (11a)

На Dblock_(m,beta) доказана (12) с K=4+beta, а для полной формы floor >=-(c_*+beta+C3)||f||². Имеем D_(m,beta) contained Dblock_(m,beta), поскольку [a+b]_+<=[a]_++[b]_+.

Этот класс МАКСИМАЛЕН для независимого ослабления целых prime-блоков с сохранением отношений весов:

    sup_(0<=theta_p<=1) sum_p theta_p(log p)U_p[f]=Pi_plus[f]. (11b)

Доказательство как в (9), теперь выбирается весь p-блок, а не каждый его атом. В отсутствие upper на theta_p максимальный robust sign-cone равен Cblock_m. Для полной, не обрезанной на квадрате prime-суммы аналогичное утверждение использует U_p^all=sum_(k:p^k<=m)p^(-k/2)Q_f(klog p) и даёт floor -c_* на конусе U_p^all<=0. Масштабируются все степени одного простого совместно.

Это использует настоящий E-факт о коэффициентах. Но оно по-прежнему не объявляет изменение prime multiplicities системой с прежним функциональным уравнением: максимальность относится к указанному классу сертификатов с фиксированным B0.

### 3.4 Непокрытый остаток

[COFINAL_FAMILY | CONDITIONAL: отсутствующая оценка.] На W outside Dblock_(m,beta) положителен

    Eblock[f]=Pi_plus[f]-B0[f]-beta||f||².

Для НАСТОЯЩИХ весов нужное неравенство эквивалентно

    Pi_minus[f] >= Eblock[f].                             (11)

Здесь внутренняя компенсация p с p² уже сохранена; остаётся совместный баланс разных prime-блоков против B0. Все mixed correlations содержатся в Q_f. Не доказаны ни Dblock_(m,beta)=W с одним beta на неограниченной семье, ни (11) на оставшихся направлениях.

Для фиксированных настоящих коэффициентов формально наибольший класс есть {P12<=B0+beta||f||²}. Это ровно искомое неравенство, не дополнительный E-сертификат. Называть его решением пункта (b) было бы кругом. Результаты максимальности выше относятся только к явно названным классам информации.

## 4. Ответ (c): восстановленный DH-свидетель и два разных конуса

### 4.1. Согласование констант

[FINITE_CELL | PAPER; F+LA.] S1 пишет знаковую константу c_D^arch=log(5/pi)+psi(3/4)<0, а S3 §3.2 обозначает через c_D её положительную противоположность. Во избежание путаницы здесь

    beta_D=gamma+log(8pi/5)-pi/2>0,
    K_D[f]=A_D[f]-beta_D||f||²-P_D[f],
    P_D[f]=sum_(2<=n<=m)b(n)n^(-1/2)Q_f(log n),   A_D>=0. (12a)

Это одна и та же форма обоих источников; полюса нет. Коэффициенты периодического ряда D имеют a(1..5)=(1,tau,-tau,-1,0), tau>0. Логарифмическая производная даёт

    b(2)=tau log2>0,
    b(3)=-tau log3<0,
    b(6)=(1+tau²)log6>0.                                  (12b)

Суммируются все целые n, но не утверждается, что каждый коэффициент ненулевой. Это не положительная Mangoldt-мера.

### 4.2. Выход фактического projected witness из sign-adapted конуса

[COFINAL_FAMILY | PAPER on S3 suppliers; F + LA; actual signed coefficients, inherited witness uses A/F/Z, no Euler product for DH.] Положим

    C_D^sgn={f in W_D: b(n)Q_f(log n)<=0 for every retained n}.

На этом конусе P_D<=0 и K_D[f]>=-beta_D||f||². Теперь используем РОВНО свидетель §7 S3. Пусть v_m — единичный bottom A_m^D с eigenvalue -R_m, Pi_m — проекция на J_m^D и delta_m=||A_m^D Pi_m||. S3 доказывает R_m->infinity и delta_m->0. Для R_m>delta_m определено

    y_m=(I-Pi_m)v_m/||(I-Pi_m)v_m||,
    y_m in W_D,
    K_D[y_m] <= U_m := -R_m+delta_m²/(R_m-delta_m).         (12c)

Точно ||Pi_m v_m||<=delta_m/R_m, поэтому знаменатель не нулевой. Как только

    R_m-delta_m²/(R_m-delta_m)>beta_D,                     (12d)

имеем K_D[y_m]<-beta_D. Следовательно

    y_m NOT IN C_D^sgn,
    P_D[y_m]>A_D[y_m]>=0,
    exists n<=m: b(n)Q_(y_m)(log n)>0.                    (12e)

Условие (12d) выполняется на всех достаточно поздних m по унаследованным R_m->infinity, delta_m->0. Новых нулевых оценок или знака из явной формулы в этом выводе нет. Полная кофинальная конструкция y_m НЕ выводится из одной E: она является входом S3. Простая отрицательность K_D<0 недостаточна — сравнивать нужно с -beta_D.

### 4.3. Буквальный Q<=0-конус — это не C_D^sgn

[FINITE_CELL | PAPER; F+LA, obstruction to transferring E.] Буквальная замена опоры в пользовательском C_m даёт

    C_D^naive={f in W_D: Q_f(log n)<=0 at every active DH atom}.

Если проверять только prime-power n, этот класс ещё шире. Ни один из них не является sign-adapted конусом. Из (12e) возможны две альтернативы:

    b(n)>0 and Q_n>0;  OR  b(n)<0 and Q_n<0.

Только первая исключает C_D^naive. Источник S3 не содержит покоординатных знаков корреляций y_m, поэтому утверждение y_m outside C_D^naive НЕ ДОКАЗАНО. Не доказано и обратное включение. Подмена конуса в (c) явно не производится.

Точный остаток этой проверки: если y_m принадлежал бы C_D^naive, то из (12c) при (12d) обязательно

    sum_(b(n)<0)|b(n)|n^(-1/2)[-Q_n]
      > A_D[y_m]+sum_(b(n)>0)b(n)n^(-1/2)[-Q_n].           (12f)

Это совместимо со знаками DH. В S3 не дана оценка, запрещающая (12f). Поэтому расположение именно y_m относительно буквального Q<=0-конуса требует дополнительного источникового знака. Это НЕ доказательство математической невозможности такой классификации и НЕ новое опровержение zeta E-floor.

### 4.4. Точный контроль с настоящими DH-коэффициентами, НЕ свидетель §7

[FINITE_CELL | PAPER; F+LA and actual signed coefficient data.] Возьмём L=log4, исходные два фазированных ортонормированных режима phi_0,phi_1 и единичный f=(phi_0-phi_1)/sqrt2. Это вектор полного чётного carrier V_4; его принадлежность W_D не утверждается.

Из буквальной q_even-формулы:

    Q_f(log2)=0,  Q_f(log4)=0,
    Q_f(log3)=[u(1+cos u)-(2sqrt2-1)sin u]/(2pi)<0,
    u=2pi(1-log3/log4),  pi/3<u<pi/2.                    (13)

Последний интервал следует из 3^4>4^3 и 3^6<4^5. Функция u*cot(u/2) убывает: её производная (sin u-u)/(2sin²(u/2))<0. Поэтому u*cot(u/2)<pi/sqrt3<2sqrt2-1, что доказывает знак. Последнее числовое сравнение следует, например, из pi<22/7, sqrt3>173/100, sqrt2>707/500 и 2200/1211<457/250.

Тем не менее, для настоящих b(n) из (12b),

    P_D[f]=sum_(2<=n<=4)b(n)n^(-1/2)Q_f(log n)
          =b(3)Q_f(log3)/sqrt3 >0.                        (14)

Таким образом, ключевой E-переход «все Q<=0 => арифметическая сумма<=0» ложен для фактической DH-меры уже на полном конечном carrier. (14) НЕ утверждает K_D[f]<-beta_D, НЕ проверяет y_m и НЕ является контрпримером к искомому zeta bound. Он строго опровергает только перенос аргумента о знаке меры на DH.

## 5. Граница переноса к Бёрлингу

[ABSTRACT | PAPER; E.] Для положительных обобщённых простых r_j>1 там, где логарифмическая производная Euler-произведения абсолютно сходится, её атомы имеют веса log(r_j) r_j^(-k/2)>=0 в точках k log r_j. Тот же sign-cone аргумент переносится буквально на эту опору.

[ABSTRACT | CONDITIONAL; F/A/source contract.] Восстановленный S3 §8 относится к конкретной системе Diamond–Montgomery–Vorhauer. У неё есть положительное Euler-произведение и определённое продолжение с off-line zeros, но цитируемая теорема не задаёт весь требуемый completion/gamma/reflection/theta-radical/finite-return пакет. Для переноса ЧИСЛЕННОГО floor требуется отдельно заданная форма A_B-c_B I-P_B+O_B с A_B>=0, O_B>=0 и её область определения. Положительное Euler-произведение само не задаёт H_m от zeta и её pole/constant. Поэтому S3 верно оставляет SOURCE_TRANSFER_GAP, а не сертификат отрицательного Beurling-eigenvalue той же матрицы. Здесь этот статус не повышается. Системно-зависимая сумма высших степеней может быть конечна при гипотезах S3, но константу C3<28 нельзя переносить без обычной целочисленной опоры.

## 6. Леджер, дискриминатор, проверки и доставка

| Узел | Тип | Scope / verifier | Результат |
|---|---|---|---|
| (2), конусный floor | E с заданной F | COFINAL_FAMILY / PAPER | Все m, но только C_m |
| (4)–(6), размер и подпространства | LA | FINITE_CELL / PAPER | Точный критерий; literal eta_m не решён |
| Sign-only максимальность | E+LA | ABSTRACT / PAPER | Только класс произвольных положительных весов |
| (8)–(11b), совместный бюджет | E+F+LA | FINITE_CELL / PAPER | Максимальные atom/prime-block deletion-robust конусы |
| (11), оставшийся знак | E+F | COFINAL_FAMILY / CONDITIONAL | Не доказан |
| (12c)–(12e), projected DH witness | F+LA; witness inherits A/F/Z; E отсутствует у DH | COFINAL_FAMILY / PAPER on S3 | Вне sign-adapted конуса при всех достаточно больших m |
| (12f), принадлежность того же witness буквальному Q<=0 | дополнительные знаки actual correlations | COFINAL_FAMILY / CONDITIONAL | Не решена; не выдана за невозможность |
| (13)–(14), DH-контроль | F+LA + точные signed coefficients, не E самой DH | FINITE_CELL / PAPER | Ошибка переноса знака доказана |
| Beurling | E / отдельно F,A | ABSTRACT / PAPER и CONDITIONAL | Перенос знака, не формы |

Восемь групп exact-algebra self-checks выполнены: нормировка floor/(12), максимумы по удалению атомов и prime-блоков, остаток (11), три типа конуса, DH recurrence, свидетель (13), signed baseline и projected upper/threshold (12c)–(12e). Первые два промежуточных запуска остановились на несокращённых символьных log/trig-выражениях; нормализация проверок исправлена, математические формулы не менялись. Финальный запуск прошёл. Это не независимый аудит, не interval/Lean-сертификат и не расчёт размерности C_m настоящей семьи. Унаследованный DH-Q/DH-N/DH-C заново полностью не аудирован.

Два следующих представления: (i) строгая cone-feasibility (5) или положительная комбинация M_n — высокая сила для определения размера, умеренная finite-cell цена; (ii) prime-block бюджет (11a) и точный signed остаток (11) — высокая сила для покрытия дополнения, кофинальная цена пока неоплачена. DISCRIMINATOR: сертифицированный знак eta_m, либо конкретный допустимый вектор с проверенными всеми корреляциями. Для буквального DH-конуса нужен полный список Q_(y_m)(log n), а не только eigenvalue. Для sign-adapted исключения достаточно строгого upper (12d).

DOWNSTREAM_CONSUMER: constant lower floor on literal CCM.
ACTUAL_CONSUMER_REQUIREMENT: all of W on an unbounded family, not merely a nonempty cone.
ORIGINAL_OBJECT_IS: requested unrestricted maximal E/F cone unspecified as an information class; covered cones are sufficient only on their sets.
FAILURE_TYPE: NO_DERIVATION for cofinal full coverage, actual cone dimension and literal-Q D2 membership.
EPISTEMIC_STATUS: RESEARCH_DEBT, not death of the CCM inequality.
REOPEN_TRIGGER: signed estimate (11), certified eta_m, or source-controlled correlation signs in (12f).

CODEX DIRECTIVE: audit (2),(3),(9),(11a),(11b),(12c)–(12f),(13),(14) using S3 §7 witness; distinguish sign-adapted from literal-Q cones. Do not promote a cone floor to a floor on W. Never identify the V_4 control with the projected DH witness.

Source base d268313 and inbox c31645a have diverged (common ancestor d142486). Source base is the mathematical pin, NOT the delivery parent. Original DH verdict was concurrently relayed at 4a8ca65 and is preserved unchanged. The present revised report follows the existing branch; no rebase, force push or rh_clean write is performed. Only this report is changed by its correction commit. Commit SHA and blob are reported after readback. No Lean files or route state are changed; no Lean axiom profile is claimed.
