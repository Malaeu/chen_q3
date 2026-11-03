# STATUS: TRY_PASSIVE_SECTION_SIGN_CORRECT_SOURCE_BUDGET

```yaml
OPERATIVE_CLASS: TRY_PASSIVE_SECTION_SIGN_CORRECT_SOURCE_BUDGET
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_PROVE_P_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: 1d3818cd227bf5f27786adf0c82e5b5d5d9ab11b
HANDOFF_PATH: docs/routeB_bus/screw_line_2026-11-02/passivity_check/PROSHKA_HANDOFF.md
HANDOFF_BLOB: d9fc618e8b377aeb3d885d999ea0a05c0f944cfe
P_SOURCE_READ_AT: 11f6368323d8aaac3d3c0a6a95873b86294cc540
P_SOURCE_SHA256: a8bcbdcbdedc9d339c75b74046e80ade1da673786088c2662edb390255b0ec75
P_SOURCE_BLOB: 755c8535d18a9ea68d366934f4158981a50c0728
P_SOURCE_CANON_PATH_AT_BASE: NOT_FOUND
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
INBOX_HEAD_OBSERVED: e4390b8f39143977b7118428f946b75033510c23
ROUTE: CHALLENGER_NOT_RH
REQUESTED_P: NOT_PROVED
ZETA_P_REFUTED: false
NEW_SOURCE_POSITIVITY: NONE
MAIN_RESULT: EXACT_WHOLE_HISTORY_SCHUR_CURVATURE_AND_SIGN_CORRECT_BIRTH_BUDGET
AFFINE_ARITHMETIC_PARAMETER_SCHUR: MATRIX_CONCAVE_WHILE_OLD_BLOCK_POSITIVE
INVERSE_KINK_POSITIVITY: DOES_NOT_REQUIRE_POSITIVE_INERTIA
INFERENCE_REJECTED: POSITIVE_INVERSE_KINKS_ARE_POSITIVE_SCHUR_ENERGY_CREDITS
SCOPED_KILL: SAME_SMOOTH_SOURCE_AND_NONNEGATIVE_PRIME_WEIGHT_KINKS_SUFFICE_FOR_P
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE: DOUBLED_ATOM_2_ONE_ANCHOR_SCHUR_UPPER_LESS_THAN_MINUS_ONE_QUARTER
ALTERED_SOURCE_IS_ZETA: false
RH_JUDGE: CONDITIONAL_PASS_OF_EXACT_IDENTITIES_NOT_NEW_PROOF
W_JUDGE: SOURCE_MATCHED_NEGATIVE_CONTROL_RETAINED
VERIFIER: PAPER
VERIFIER_DETAIL: ANALYTIC_IDENTITIES_PLUS_EXACT_RATIONAL_SOURCE_UPPER_CERTIFICATE
SYMBOLIC_CONTROL_GROUPS: 5
FLOATING_SIGN_DECISIONS: 0
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_EXECUTED: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_RESULT: SCOPED_FALSIFICATION_OF_SIGN_ONLY_COMPENSATION
RH_PROVED: false
ROUTE_STATE_CHANGED: false
```

## 0. Результат и его граница

Ы. Полное (P) для действительного g_zeta не доказано. Получен точный бюджет продолжения, в котором сохранены все старые узлы, гладкий источник и все арифметические изломы. В нем поправка от изменения оптимального предиктора имеет отрицательный знак. Неотрицательные квадраты, приведенные в запросе, относятся к производной ОБРАТНОЙ формы; они не являются положительными приращениями Schur-энергии.

Доказан более сильный отрицательный контроль, чем один отдельно взятый hinge: сохраняем весь гамма-фактор, оба полюса, начальную кривую до log(2) и все арифметические веса кроме удвоенного веса при 2. У этого источника сохраняется цитируемый закон неотрицательных inverse-kinks, однако при положительном старом узле 1/64 и новом узле log(3) дополнение Шура строго меньше -1/4. Это НЕ контрпример для zeta. Он отвергает только вывод из неизмененного гладкого источника и знаков арифметических изломов без количественного использования точных весов.

Другая конструкция, использующая именно все точные коэффициенты zeta, этим не исключена. Никакая эквивалентность с RH не используется как причина отказаться от доказательства; ниже зафиксировано конкретное невыведенное матричное сравнение.

## 1. Source lock, определения, проверенные импорты

S1. Handoff прочитан на BASE; Git blob d9fc618e8b377aeb3d885d999ea0a05c0f944cfe. В нем сам знак полного Schur-продолжения оставлен открытым. Указанный пользователем SHA-256-префикс handoff не пересчитывался из независимо скачанного файла; здесь зафиксирован возвращенный connector-blob.

S2. `docs/routeB_bus/proshka/PROSHKA_VERDICT_PASSIVE_SECTION_P_2026-11-03.md`: по этому пути на BASE получен 404. Поэтому источник НЕ подменен: прочитан прежний inbox-коммит 11f6368, а доступные локальные полные байты независимо дают ровно SHA-256 a8bcbdcb... и blob 755c8535..., указанные выше. Используются его точная форменная нормировка, короткая коэрцитивность и (17), а не недоказанная глобальная положительность.

S3. `docs/routeB_bus/screw_line_2026-11-02/passivity_check/RESULT.md` на BASE, blob 025f7c6e90bed728f805fd504da5c044e22ff490: раздел (ii) явно различает scalar source-kink, derivative-kink обратной оконной формы и сырой шаг changing carrier. Новые знаки исходного оператора из его численных таблиц не импортируются.

S4. Предыдущая первая ступень log(3), blob 2b5bbfd2c99e8fc1193188c941d509cbccf6d094, уже содержала doubled-atom constant-test control. Здесь не заявляется повторное открытие того примера: его знак пересертифицирован независимо только рациональными операциями и превращен в строгий Schur-контрпример с положительной историей. Положительный компьютерный сертификат первой ступени в новом доказательстве не используется и заново не аудировался.

P1. Masatoshi Suzuki, arXiv:2206.03682v4, (1.1), (1.3), (1.4), (1.9), Theorems 1.1–1.2. Первичный PDF прочитан, страницы 1 и 3 просмотрены скриншотами. Импорт арифметического определения и его нулевой идентичности: THEOREM. Использование положительной нулевой меры: CONDITIONAL ON RH. https://arxiv.org/pdf/2206.03682v4

Все последующие новые вычисления выполняются на полном источнике

    g=-Psi,  K(s,t)=g(s-t)-g(s)-g(t),  c_k=Lambda(k)/sqrt(k).

Для компактного профиля f, продолженного нулем, используем

    Q_f(u)=2 Re integral conjugate(f(x)) f(x+u) dx,
    j(u)=exp(-u/2)/(1-exp(-2u)),
    c_*=gamma_E+log(8*pi)+pi/2,
    p(x)=sqrt(2)cosh(x/2), q(x)=sqrt(2)sinh(x/2),

    W[f]=integral_0^infinity j(u)||f-T_u f||^2 du
         -c_*||f||^2-sum_(k>=2)c_k Q_f(log k)
         +|<p,f>|^2-|<q,f>|^2.                         (1)

Все степени простых сохранены. Точки kernel и конечная cosine-компрессия A_m — разные Gram-объекты одной формы: переход идет через распределительные производные с endpoint-массами. В формулах для A_m сохраняются N=m, L=log(m), физическая L2-метрика; локальные L-производные берутся при фиксированном числе мод, не как производные дискретного m.

## 2. Одна лемма для полного прошлого и всего нового блока

**[ABSTRACT | PAPER; LA/A.]** Пусть M(u) — непрерывная эрмитова матрица, кусочно C2 по вещественному параметру, с блоками

    M=[[C,B],[B*,D]],  C(u)>0,
    S=D-B* C^-1 B,  F=C^-1 B,
    T=[-F;I],  Y=B'-C'F.                                (2)

Размеры старого и нового блоков произвольны. Тогда на гладких участках ТОЧНО

    S'=T* M' T,
    S''=T* M'' T - 2 Y* C^-1 Y.                         (3)

Если M' имеет скачок, а M непрерывна, то

    Delta S'=T* (Delta M') T.                           (4)

**Доказательство.** MT=[0;S]. Из C F=B следует F'=C^-1Y. Поэтому T'=[-C^-1Y;0], T'^*MT=0 и

    (T* M T)'=T* M' T.

Старый блок M'T равен Y. Следовательно, два смешанных слагаемых при повторном дифференцировании равны -Y*C^-1Y каждое. Это дает (3). Непрерывность C^-1,B,T дает (4). Положительность C, а не всего M, устанавливает знак второго члена. Никакой RH, положительного будущего или отдельного контроля каждого атома здесь не предполагается.

### 2.1. Интегрированный полный бюджет

Для alpha<beta внутри области C>0, без столкновений узлов и сингулярной стартовой точки, из (3)–(4):

    S(beta)=S(alpha)+(beta-alpha)S'_+(alpha)
       +integral_alpha^beta (beta-u) T* M''_reg T du
       -2 integral_alpha^beta (beta-u) Y* C^-1 Y du
       +sum_(alpha<u_l<beta) (beta-u_l) T_l* Delta M'_l T_l.
                                                               (5)

Это точное равенство всех блоков, не сумма отдельных минимумов. Старые арифметические взаимодействия входят также в C,B,F,Y,T на каждой u. Скаляр c_* и линейные части g не потеряны: они входят в начальные M(alpha),M'(alpha) и response. В нуле у g есть логарифмический cusp; (5) не разрешает ставить alpha=0 и выдумывать конечную начальную производную. Для coincident новых узлов сначала используются непротиворечивые конечные ограничения и затем непрерывность самой Gram-матрицы, а не необоснованный предел производных.

### 2.2. Точная версия для движения узлов из (P)

Старые узлы фиксированы. На любом локальном affine-пути всех новых узлов x_i(u)=r_i+v_i u старым узлам соответствует v_i=0. Матрица M есть именно (K(x_i,x_j)); поэтому C'=0 и Y=B'. Пусть

    p_0(s)=j(|s|)-2cosh(s/2),  s!=0.

Вне столкновений и атомных событий

    (M''_reg)_ij=(v_i-v_j)^2 p_0(x_i-x_j)
                    -v_i^2 p_0(x_i)-v_j^2 p_0(x_j).       (6)

Для i=j первое слагаемое равно нулю по определению, поскольку g(x_i-x_i)=g(0) постоянно; 0*p_0(0) не вычисляется. Для события u_l и a_k=log k>0:

    (Delta M')_ij=sum_k c_k[
       |v_i-v_j| 1_{|x_i-x_j|=a_k}
       -|v_i| 1_{|x_i|=a_k}-|v_j| 1_{|x_j|=a_k}].         (7)

Слагаемые с нулевой скоростью дают нуль. Формула следует из точного скачка производной convex hinge (|r+vu|-a)_+, равного |v| при пересечении +/-a. Одновременные события суммируются. На ограниченном пути сумма конечна.

Итак, у (P) атомные матричные вклады (7) вообще не имеют предписанного Loewner-знака. Даже внутри (log n,log(n+1)) остаются события x_new-s_old=log k: нумерация секций не удаляет старые shifted-взаимодействия. В (5) дополнительно имеется отрицательная цена перестройки оптимального предиктора. Это source-exact формула той совместной компенсации, которую требовалось доказать; ее правая часть не стала неотрицательной.

## 3. Где на самом деле находятся положительные квадраты запроса

**[FINITE_CELL | PAPER; E/I/A/LA.]** Рассмотрим цитируемую локальную производную исходного четного оконного A(L) при фиксированном carrier-порядке. Пусть e — вектор физического endpoint-functional. При рождении a_k=log k:

    Delta A'_L=-2 c_k e e*.                              (8)

Действительно, для четного профиля при L=a_k+h,

    Q_f(a_k)=2 h |f(a_k/2)|^2+O(h^2),

а слева корреляция нового атома равна нулю. В (1) prime-term имеет знак MINUS. Поляризация дает (8). Другие гладкие слагаемые не имеют этого скачка. Формула не объявляет changing-native matrices вложенными Gram-матрицами точек.

На фиксированном L и при обратимом A положим r=A^-1 l для произвольного evaluation l. Если l и l' не имеют скачка,

    Delta (l* A^-1 l)'=-r* (Delta A')r
                      =2 c_k |e*r|^2 >=0.                (9)

Это точно положительный квадрат из вопроса. Для (9) A НЕ обязана быть положительной: она может иметь любое число отрицательных собственных значений, лишь бы была обратимой.

Если разделить этот же M=A на старую и новую части, то по (4), при C>0,

    Delta S'=-2 c_k eta eta* <=0,
    eta=e_new-B* C^-1 e_old.                             (10)

И, когда S обратима,

    Delta (S^-1)'=2 c_k(S^-1 eta)(S^-1 eta)* >=0.          (11)

Таким образом, знак (9) — следствие ОТРИЦАТЕЛЬНОГО primal-kink, а не дополнительный положительный запас Schur-энергии. В source-node формулировке вместо (8) используется (7), а не подмена одного семейства другим.

### 3.1. Непроходимая без дополнительного бюджета граница inverse-аргумента

Скалярная модель A(u)=1-u имеет

    A(0)=1,  (A^-1)'=1/(1-u)^2>0,

но A(u)<0 при u>1. В u=1 стоит полюс обратного ответа. Модель с birth-kink A(u)=1-(u-a)_+ дает еще и положительный скачок derivative inverse в u=a. Она начинает положительно, имеет правильный знак inverse-birth и все равно проходит через нуль позднее.

На гладком участке при r=A^-1 l, w=l'-A'r:

    (l*A^-1l)''=2 Re(l''*r)+2 w*A^-1 w-r*A''r.            (12)

Пока A>0, средний квадрат положителен. Однако r и w могут расходиться при приближении к первому нулю A. Ограниченность коэффициентов источника сама по себе не ограничивает эти solution-dependent величины. Интегрирование (9) или (12) через такой полюс без независимого no-pole бюджета незаконно.

Это не контрпример к A_zeta. Это точная причина, по которой положительные inverse-kinks не могут считаться сертификатом P. Физически это податливость: она возрастает именно при размягчении, а не при увеличении нижнего энергетического пола.

## 4. Попытка совместной арифметической компенсации: точный остаток

**[ABSTRACT | PAPER; LA/A, source E/F/I при подстановке коэффициентов.]** Не разделим прошлые атомы по модулям. Варьируем сразу любую конечную линейную комбинацию исходных арифметических весов:

    M(u)=M_0+u M_1,
    C(u)=C_0+u C_1>0, B(u)=B_0+u B_1, D(u)=D_0+u D_1.

Положим

    F_0=C_0^-1 B_0, T_0=[-F_0;I], Y_0=B_1-C_1 F_0.

Тогда весь ответ нового блока равен

    S(u)=S(0)+u T_0* M_1 T_0
                    -u^2 Y_0* C(u)^-1 Y_0.              (13)

**Доказательство.** C(u)^-1B(u)=F_0+u C(u)^-1Y_0. Подставить в D-B*C^-1B и раскрыть. Это дает (13) без усечения по u и без коммутативности блоков.

В частности,

    S''(u)=-2 Y(u)* C(u)^-1Y(u) <=0.                     (14)

Следовательно, Schur-ошибка матрично ВОГНУТА по affine arithmetic-homotopy, пока старый блок положителен. Неотрицательный square кредит после оптимизации прошлого здесь не возник: точный нелинейный остаток (13) отрицателен. Это не доказывает невозможность правильного количественного endpoint-bound; напротив, для доказанного положительного C(u) нижняя хорда S(u)>=(1-u)S(0)+uS(1) верна на [0,1]. Но конечный S(1) — именно неоплаченный источник, его нельзя внести как предпосылку.

### 4.1. Прямо для атома 2 в настоящих point-координатах

Пусть старый узел s>0 мал, t=log3, a=log2, t-s>a. Добавим к g_zeta член u(|x|-a)_+. Это именно изменение веса при 2 на u, не перестановка узлов. Тогда

    C=K_zeta(s,s),  b(u)=b(0)-u s,
    d(u)=d(0)-2u(t-a),

    sigma_u^2=sigma_0^2
       +2u[b(0)s/C-(t-a)]-u^2 s^2/C.                    (15)

Таким образом, d^2 sigma_u^2/du^2=-2s^2/C<0. Более того, b(0)/C ->1/2 при s down to0, так что первая производная при действительном источнике также отрицательна для достаточно малого s. Положительные веса в этом точном остатке не работают как автономные положительные credits. Значение при реальном весе c_2 остается предметом количественного source-баланса.

## 5. Строгий контроль: тот же гладкий источник, положительные inverse-kinks, отрицательное P

**[FINITE_CELL | PAPER; exact rational arithmetic; not the zeta source.]** Определим

    g_2(t)=g_zeta(t)+c_2(|t|-log2)_+,
    c_2=log2/sqrt2.                                      (16)

Это удвоение только веса при 2. Гамма-фактор, оба полюса, все остальные арифметические члены и вся кривая на |t|<=log2 сохраняются ТОЧНО. Все веса по-прежнему неотрицательны и поддержаны на prime powers. Значения Lambda уже не настоящие: divisor-identity ordinary von Mangoldt изменена. Функциональное уравнение аналитической completion для этого altered source не утверждается. Поэтому (16) не является ни другой записью zeta, ни контрпримером к P_zeta.

Возьмем L=log3 и единичную постоянную форму f=L^-1/2 1_[-L/2,L/2]. Для q_j=2j+1/2 точно

    W_2[f]=-c_*+(2/L) sum_(j>=0)(1-3^(-q_j))/q_j^2
          +(8/L)(sqrt3+1/sqrt3-2)
          -4(log2/sqrt2)(1-log2/L).                       (17)

В (17) сохранены gamma, оба полюсных сектора (нечетный на этом тесте равен нулю по четности), и весь arch-tail. Атом 3 имеет нулевое overlap на endpoint, а атомы >=4 не входят по поддержке.

Выполненный заново rational-only сертификат дает

    -30407771/125000000 < W_2[f] < -9567901/40000000
                                  < -23/100,
    -267250807/10^9 < L W_2[f] < -13139267/50000000
                                  < -1/4.                (18)

Никаких floating-решений знака в (18) нет. Использованы 128 положительных экспоненциальных arch-термов, рациональный верх их бесконечного хвоста, 2048 harmonic-термов для gamma_E, ряды log и arctan с явными остатками и integer sqrt.

Теперь старый узел s=1/64. При этой поддержке атом 2 вообще отсутствует, поэтому из короткой леммы S2

    C=K_2(s,s)=K_zeta(s,s)>=s/4=1/256>0.

Новый узел t=log3 принадлежит требуемой секции [log2,log3]. По точному constant-mode identity его диагональ d=L W_2[f]. Следовательно,

    S_2=d-|K_2(s,t)|^2/C <= d < -1/4.                    (19)

Это строгий отрицательный UPPER envelope для самого Schur-продолжения при положительном прошлом, а не провал достаточной нижней оценки. В этом же altered world quoted native inverse-kinks (9) остаются неотрицательными. Значит, утверждение «тот же гладкий gamma/pole flow и неотрицательные prime-supported inverse-kinks обеспечивают P» ложно даже на первой секции с атомом.

Этот контроль усиливает прежний constant-test: теперь перечислены конкретные старый/новый узлы и проверен guard G_old>0. Исторической новизны самого doubled-atom примера не заявляется.

### Как проверены остатки (18)

Для рационального x in [1,2], r=(x-1)/(x+1),

    log x=2 sum_(j=0)^(N-1) r^(2j+1)/(2j+1)+R,
    0<=R<=2r^(2N+1)/[(2N+1)(1-r^2)].

Другие положительные x сводятся степенями 2. Pi зажата формулой Machin 16 arctan(1/5)-4 arctan(1/239), с alternating-series remainder. Для Euler gamma

    H_N-log N-1/N < gamma_E < H_N-log N;

неравенство следует суммированием 0<log(1+1/k)-1/(k+1)<1/k-1/(k+1). Для arch-tail, K=128, q_K=2K+1/2:

    0<sum_(j>=K)(1-3^(-q_j))/q_j^2
      <1/q_K^2+1/(2q_K).

3^(-q_j)=3^(-1/2)9^(-j), так что достаточно рационального enclosure sqrt3. Interval operations в приложении реализованы через fractions.Fraction. Десятичная печать или mpmath не нужны.

## 6. Два судьи и граница локальной геометрии

**[COFINAL_FAMILY | CONDITIONAL ON RH; A/Z/LA.]** В RH-ветке полная screw-Gram сумма положительна, значит P верно обычной конгруэнцией. Все тождества (3)–(15) согласованы с этой веткой: они не требуют положительного знака каждого отдельного гладкого или атомного вклада. Никакой ненормированный дополнительный lift или расходящийся новый положительный reserve не введен. Это проверка, не доказательство RH.

**[COFINAL_FAMILY | PAPER for the planted model with a positive pure-point baseline; A/LA.]** Для

    g_w(t)=g_0(t)+4nu Re[(cos(wt)-1)/w^2],
    w=2pi/log2+i eta, 0<eta<1/2,

старые арифметические изломы не меняются. Если S0=sum nu_gamma/gamma^2 для baseline и a_w=Re(w^-2)>0, то на L_k=k log2

    2Psi_w(L_k)<=4S0-8nu a_w[cosh(eta L_k)-1]<0

для всех достаточно поздних k. Берется один фиксированный достаточно малый положительный старый узел; его существование обеспечивается неизмененным ведущим short-support cusp и ограниченной гладкой perturbation. Новый Schur остаток не превосходит отрицательной диагонали. Этот planted world проходит знак quoted inverse-kinks и проваливает P. Гладкий поток здесь изменен, что явно отличается от более сильного контроля §5, где gamma/pole flow не менялся.

Предыдущая положительная первая ступень log3 (при ее заявленном computer-assisted PAPER статусе) не доказывает произвольную склейку. Полная совместная матрица не является direct sum отдельных положительных short-window форм. В настоящем P эту связь вычитает B*C^-1B. Ее нельзя потерять ни под названием «геометрия», ни под названием «пассивные рождения».

## 7. Где именно остался неоплаченный source-знак

Унаследованный объект (17) из S2 сохраняется без скалярного ослабления. Для свежей положительной формы T_delta и exact response V требуется

    C - V T_delta^-1 V* >=0,                              (20)

на всем form-замыкании свежих профилей и для каждой допустимой истории. Конечное старое C>0 не доказывает (20). Равномерная оценка (20) НЕ получена ни из (5), ни из (9).

Попытка по рождениям должна дать нижнюю границу полной правой части (5), с сохранением отрицательной адаптации и действительных событий (7). Для гладкого оконного source-transport rank-one рождения имеют знак (10); положительный бюджет следует искать в остальной совместной source-геометрии, а не повторно записывать (9) как приход энергии.

Это точное место остановки настоящего доказательства. Ни контрпример к zeta, ни глобальная пассивность, ни RH здесь не заявлены.

### Две репрезентации одного объекта и цена

| Репрезентация | Что проверять | Сила / цена / риск |
|---|---|---|
| Полный integrated Schur-бюджет (5), source matrices (6)–(7) | Общий нижний envelope, а не знак каждого event | Может закрыть семейство при source-оценке; алгебра оплачена, новый знак дорог; риск inverse/past amplification |
| Двойственное сравнение (20) в полной fresh-form метрике | Источник-заданная contraction или factorization C-VT_delta^-1V* | Сохраняет всю геометрию, не теряет ее в beta I; сила максимальная, новый аналитический supplier пока отсутствует |

Это не две новые независимые задачи, а два точных представления того же продолжения. Запуск еще одной численной серии на положительных секциях не оплачивает общий квантор.

DISCRIMINATOR: для заранее закрепленных узлов и нормировки проверять signed Schur quadratic form, а не inverse-kink. PASS finite допускается только из lower enclosure >=0; KILL только из upper<0. При нуль-согласованном интервале нужен полный более узкий enclosure или точный источник-заданный фактор. Разрешение сетки, положительный scalar inverse или малость локального остатка этого не заменяют.

## 8. Ledger, предрегистрация, handoff

| Claim | Scope | Verifier | E/F/Z/LA/A/I |
|---|---|---|---|
| Schur derivative, curvature and exact affine remainder | ABSTRACT | PAPER | LA/A |
| Whole-node source event matrices | FINITE_CELL | PAPER | E/F/I/A/LA |
| Negative native energy kink / positive inverse kink | FINITE_CELL | PAPER | E/I/A/LA |
| Full smooth source doubled-2 Schur countermodel | FINITE_CELL | PAPER, exact rational certificate | F_gamma,pole and I-support retained; exact E_zeta deliberately broken |
| RH judge | COFINAL_FAMILY | CONDITIONAL | A/Z/LA |
| Planted quartet judge | COFINAL_FAMILY | PAPER on specified model | A/LA, inherited conditional baseline |
| P for actual zeta | COFINAL_FAMILY | CONDITIONAL / unpaid | No source sign supplied |

Предсказания записаны до исполнения новых проверок: отрицательная affine adaptation; inverse-sign identity также при indefinite full M; doubled-2 upper<-23/100; doubled-2 one-anchor Schur upper<-1/4. Все проверены. Это не объявление заранее предсказанными новых аналитических идей: речь о регистрации ожидаемых результатов исполняемых контролей.

Выполнено пять exact-symbolic групп: affine identity; первая/вторая производные на трех рациональных состояниях нелинейного пути; birth signs для положительной и неопределенной полной матрицы; inverse pole; one-anchor arithmetic curvature. Отдельно rational-only source certificate §5. Первый запуск сертификата прошел математические assert, но остановился при печати количества десятичных цифр очень большого целого из-за Python security limit; изменена только диагностическая печать на bit_length и исполнение повторено. Математические параметры и thresholds не менялись.

Независимого аналитического аудита нет. Lean, Arb, новых CCM eigensystem-сканов и доказательства P нет. SymPy-проверки подтверждают конечные алгебраические экземпляры; универсальные формулы доказаны выше, а не заменены этими тестами.

CODEX DIRECTIVE — одна: проверить полный source-to-Schur budget (3)–(15) и воспроизвести rational countermodel (18)–(19), не меняя цель P и не повышая route-state. При запуске приложений использовать из корня репозитория обычный Python; symbolic appendix требует SymPy (`uv run --with sympy python symbolic_checks.py`). Rational appendix использует только стандартную библиотеку. Извлекать два fenced-python приложения byte-exact; изменять пороги нельзя. Критерий успеха: identities verified, all strict rational assertions hold, P остается OPEN. Это проверка source-математики, не фиктивный Lean gate.

K8A: DOWNSTREAM_CONSUMER=P with the unchanged full zeta kernel. ACTUAL_CONSUMER_REQUIREMENT=nonnegative full-history Schur residual for every finite configuration on every section. ORIGINAL_REQUESTED_OBJECT=kink-covered smooth flow. ORIGINAL_OBJECT_IS=NOT_NECESSARY; any correct source-matched joint bound suffices. FAILURE_TYPE=NO_DERIVATION for P, COUNTEREXAMPLE for the sign-only compensation inference. EPISTEMIC_STATUS=RESEARCH_DEBT for P; MATHEMATICALLY_DEAD only for the stated inference class of §5. REOPEN_TRIGGER=source-sensitive quantitative bound using exact weights, including (5)'s losses, or proof of (20). NOVELTY_AXIS=whole-history curvature and independently certified Schur control, not a new global sign.

Closeout: исходная положительность не доказана; строго отделены обратная податливость и Schur-энергия. Убит перенос знаков inverse-kinks в энергетический reserve. Нельзя снова интегрировать inverse-form через необработанный полюс или заменять точные source weights одним знаком. Следующий дешёвый решающий контроль любого предложенного положительного representation: одинаковые nodes, нормировка, вся история, doubled-2 source и w-world; затем проверка точного возврата к настоящим весам zeta.

Repository delivery: intended branch proshka_inbox_2026-10-31; only this new Markdown under docs/routeB_bus/proshka/ is written. No Lean files or route-state files are written. Commit SHA and verified remote blob are reported in the accompanying response, not self-inserted into the file. A repository write certifies delivery, not mathematical correctness.

## Appendix A. Исполненный rational-only certificate

```python
"""Exact rational controls; no floating decisions, external dependencies, or RH input."""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(self, b):
        b = cv(b); return I(self.lo+b.lo, self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi, -self.lo)
    def __sub__(self,b): return self + -cv(b)
    def __rsub__(self,b): return cv(b) + -self
    def __mul__(self,b):
        b=cv(b); p=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=cv(b); assert not(b.lo<=0<=b.hi)
        return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,b): return cv(b)/self

def cv(x): return x if isinstance(x,I) else I(x)
def log_small(x, n=48):
    x=F(x); assert 1<=x<=2
    r=(x-1)/(x+1)
    s=2*sum((r**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    err=2*r**(2*n+1)/(F(2*n+1)*(1-r*r))
    return I(s,s+err)
def log_q(x):
    x=F(x); assert x>0
    k=0
    while x>=2: x/=2; k+=1
    while x<1: x*=2; k-=1
    return log_small(x)+k*log_small(F(2))
def log_i(x):
    x=cv(x); return I(log_q(x.lo).lo,log_q(x.hi).hi)
def sqrt_q(x, bits=90):
    x=F(x); assert x>=0
    den=1<<bits
    num=isqrt((x.numerator*den*den)//x.denominator)
    lo=F(num,den); hi=F(num+1,den)
    assert lo*lo<=x<=hi*hi
    return I(lo,hi)
def atan_inv(q, n=40):
    x=F(1,q)
    s=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    t=F((-1)**n)*x**(2*n+1)/F(2*n+1)
    return I(min(s,s+t),max(s,s+t))
def coarse(x, denominator=10**9):
    x=cv(x)
    return [str(F(x.lo.numerator*denominator//x.lo.denominator,denominator)),
            str(F(-((-x.hi.numerator*denominator)//x.hi.denominator),denominator))]

pi=16*atan_inv(5)-4*atan_inv(239)
log2=log_q(2); L=log_q(3); sq2=sqrt_q(2); sq3=sqrt_q(3)
# 0 < H_N-log(N)-gamma < 1/N, by integral comparison.
N=2048
HN=sum((F(1,k) for k in range(1,N+1)),F(0))
gamma=HN-log_q(N)-I(0,F(1,N))
cstar=gamma+log_i(8*pi)+pi/2
Ntail=128
s=I(0)
for k in range(Ntail):
    a=F(4*k+1,2)
    s += (1-(1/sq3)*F(1,9**k))/(a*a)
a=F(4*Ntail+1,2)
# Positive omitted terms <= sum_(k=Ntail)^infty 1/(2k+1/2)^2.
tail=F(1,a*a)+F(1,2*a)
s += I(0,tail)
H=2*s/L
pole=8*(sq3+1/sq3-2)/L
prime_unit=2*(log2/sq2)*(1-log2/L)
W_one=-cstar+H+pole-prime_unit
W_double=W_one-prime_unit
d_double=L*W_double
assert W_double.hi < -F(23,100)
assert d_double.hi < -F(1,4)
# A convenient coarse independently checkable enclosure.
assert W_double.lo > -F(1,4)
assert W_double.hi < -F(235,1000)
output={
 "arithmetic":"fractions.Fraction with rational remainder enclosures only",
 "registration":"registration.json",
 "arch_terms":Ntail,"gamma_harmonic_terms":N,
 "W_actual_constant_enclosure":coarse(W_one),
 "W_doubled_constant_enclosure":coarse(W_double),
 "new_diagonal_doubled_enclosure":coarse(d_double),
 "W_doubled_upper_below_minus_23_over_100":True,
 "Schur_upper_below_minus_1_over_4":True,
 "Schur_old_anchor":"s=1/64; positive by the unchanged short-support lemma",
 "true_zeta_P_tested":False,
 "raw_upper_numerator_bits":W_double.hi.numerator.bit_length(),
 "raw_upper_denominator_bits":W_double.hi.denominator.bit_length()
}
Path(__file__).with_name('rational_output.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
```

## Appendix B. Исполненные exact-symbolic controls

```python
"""Exact symbolic checks of full block identities; no numerical spectral inference."""
import sympy as sp
from pathlib import Path
import json
x=sp.symbols('x', real=True)
C0=sp.Matrix([[3,1],[1,2]])
C1=sp.Matrix([[1,1],[1,0]])
B0=sp.Matrix([[1,2],[-1,1]])
B1=sp.Matrix([[2,0],[1,-1]])
D0=sp.Matrix([[7,1],[1,8]])
D1=sp.Matrix([[0,2],[2,-1]])
I=sp.eye(2)

def zero(M):
    assert all(sp.cancel(v)==0 for v in M)
def block(C,B,D): return C.row_join(B).col_join(B.T.row_join(D))
C=C0+x*C1; B=B0+x*B1; D=D0+x*D1
F0=C0.inv()*B0; Y0=B1-C1*F0
S0=D0-B0.T*F0
T0=(-F0).col_join(I)
M1=block(C1,B1,D1)
S=D-B.T*C.inv()*B
zero(S-(S0+x*T0.T*M1*T0-x*x*Y0.T*C.inv()*Y0))
print('PASS affine whole-history Schur identity')
# Nonlinear path: test exact derivatives at three rational parameter values.
C=C0+x*C1+x*x*sp.eye(2)
B=B0+x*B1+x*x*sp.Matrix([[1,0],[0,-1]])
D=D0+x*D1+x*x*sp.Matrix([[2,1],[1,3]])
M=block(C,B,D); F=C.inv()*B; S=D-B.T*F
Y=B.diff(x)-C.diff(x)*F; T=(-F).col_join(I)
for t in [sp.Rational(0),sp.Rational(1,7),sp.Rational(2,5)]:
    zero(S.diff(x).subs(x,t)-(T.T*M.diff(x)*T).subs(x,t))
    zero(S.diff(x,2).subs(x,t)-(T.T*M.diff(x,2)*T-2*Y.T*C.inv()*Y).subs(x,t))
print('PASS first derivative and negative-adaptation curvature, three exact states')
# Birth kinks: covariance Schur and inverse give opposite signs.
for sign in [1,-1]:
    M0=block(C0,B0,sign*D0)
    e=sp.Matrix([1,2,3,-1]); c=sp.Rational(2,3)
    jump=-2*c*e*e.T
    F=C0.inv()*B0; T=(-F).col_join(sp.eye(2))
    eta=e[2:4,0]-B0.T*C0.inv()*e[0:2,0]
    zero(T.T*jump*T+2*c*eta*eta.T)
    inv=M0.inv()
    zero(-inv*jump*inv-2*c*(inv*e)*(inv*e).T)
print('PASS Schur/inverse kink signs with positive and indefinite full matrices')
# An inverse can have positive derivative on both sides of an unprotected pole.
r=1/(1-x)
assert sp.simplify(sp.diff(r,x)-1/(1-x)**2)==0
assert r.subs(x,2)<0
print('PASS inverse-positive-derivative pole control')
# Exact one-anchor response to the coefficient of the atom at log 2.
b,d,s,Cs,ell,c=sp.symbols('b d s Cs ell c', real=True, nonzero=True)
S=(d-2*c*ell)-(b-c*s)**2/Cs
zero(sp.Matrix([sp.diff(S,c,2)+2*s*s/Cs]))
print('PASS exact prime-amplitude curvature for a fixed old anchor')
Path(__file__).with_name('symbolic_output.json').write_text(json.dumps({
 'groups':5,'states_in_nonlinear_group':3,
 'full_inertia_cases':[1,-1], 'arithmetic':'SymPy exact rational/symbolic',
 'all_pass':True,'zeta_P_proved':False},indent=2)+'\n')

```
