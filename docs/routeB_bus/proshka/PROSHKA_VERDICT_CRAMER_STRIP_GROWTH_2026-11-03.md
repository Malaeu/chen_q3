# STATUS: KILL_CRAMER_POLE_ONLY_SUBEXPONENTIAL

```yaml
OPERATIVE_CLASS: KILL_CRAMER_POLE_ONLY_SUBEXPONENTIAL
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_CRAMER_HORIZONTAL_GROWTH_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_BASE: 50777d478c72298ff65c7ffaa2b3783aec183dd6
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_PLANTED_COMMIT: 11f6368323d8aaac3d3c0a6a95873b86294cc540
SOURCE_PLANTED_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PASSIVE_SECTION_P_2026-11-03.md
SOURCE_PLANTED_SHA256: a8bcbdcbdedc9d339c75b74046e80ade1da673786088c2662edb390255b0ec75
SOURCE_PLANTED_BLOB: 755c8535d18a9ea68d366934f4158981a50c0728
ROUTE: CHALLENGER_NOT_RH
KILL_SCOPE: THEOREM_SHAPE
KILL_TARGET: SUBEXPONENTIAL_BOUND_AFTER_CRAMER_ARITHMETIC_POLE_SUM_AND_LOG_MONODROMY_SUBTRACTION
KILL_EVIDENCE_KIND: EXACT_SOURCE_ASYMPTOTIC_AND_STRICT_NEGATIVE_UPPER_FOR_BOUND_DEFECT
KILL_EVIDENCE_REFERENCE: SECTIONS_3_THROUGH_5
KILL_APPLIES_TO_ALL_POSSIBLE_ENTIRE_RENORMALIZATIONS: false
FAILURE_TYPE: COUNTEREXAMPLE_TO_STATED_CANONICAL_BOUND
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THE_SPECIFIED_POLE_ONLY_NORMALIZATION
CANONICAL_REMAINDER_HORIZONTAL_TYPE: 1/2
CANONICAL_REMAINDER_LEADING_SIZE: exp(x/2)*log(x)/(2*pi)
UNIFORMITY: 0<=Im(z)<=1_as_Re(z)_tends_to_plus_infinity
RAW_V_HORIZONTAL_TYPE: sup_Re(rho)_minus_1/2
RAW_SUBEXPONENTIAL_BOUND: NOT_PROVED
PHRAGMEN_LINDELOF_APPLICATION: MISSING_HORIZONTAL_BOUNDARY_DATA
EXACT_FULL_SUBTRACTION: PROVED_BUT_TRANSFERS_ZERO_RESONANCES_TO_COUNTERTERM
PLANTED_QUARTET: ENTIRE_WITH_EXACT_HORIZONTAL_TYPE_eta
VERIFIER: PAPER
NEW_FLOATING_CONTROLS: NORMALIZATION_ONLY
NUMERICAL_DPS: [50,70]
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
REPOSITORY_WRITTEN: false
WRITE_CAPABILITY_OBSERVED: GITHUB_READ_ACTIONS_ONLY
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: EXACT_RAW_HORIZONTAL_INDICATOR_AND_LAPLACE_SAFE_SUBTRACTION_CRITERION
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
```

Ы. Стандартное вычитание арифметических полюсов и логарифмической монодромии НЕ оставляет субэкспоненциальный остаток. Для точной центрированной функции ζ остаток имеет главный член порядка exp(x/2) log(x), равномерно вплоть до вещественной границы. Это установлено из формулы Крамера, без RH. Изменение вычитания на целую функцию меняет вопрос; поэтому ниже нормировка задана явно.

Есть и точный положительный результат о правильном дискриминаторе: горизонтальный показатель роста НЕВЫЧТЕННОЙ V на каждой фиксированной высоте равен supremum(Re(rho)-1/2). Доказательство использует Laplace-преобразование по горизонтальной координате и непогашаемые простые полюса. Требуемая субэкспоненциальная оценка для этой V не получена. Отказ от ее объявления доказанной связан с конкретным отсутствующим граничным бюджетом, не с историческим статусом RH.

## 1. Источники, нормировка и область утверждений

R1. Указанный base существует: `50777d478c72298ff65c7ffaa2b3783aec183dd6`. Его metadata прочитаны через GitHub; новые численные матрицы из этого коммита не используются. Указанный PASSIVE_SECTION_P по каноническому пути на base не был доступен при intake; применен явно закрепленный прежний inbox-коммит `11f6368`. Полные локальные байты R1: 37850; SHA-256 и Git blob независимо пересчитаны и совпадают с header. Из R1 используется только определенный w-контроль, особенно (20), а не недоказанная положительность.

P1. H. Cramer, *Studien uber die Nullstellen der Riemannschen Zetafunktion*, Math. Z. 4 (1919), 104-130: определение на p.109, представление (13) на p.114, вычеты на p.115, монодромия (21) на p.117. Прочитаны соответствующие извлеченные страницы оригинала. Вызов PDF screenshot вернул Cache miss; загрузка PDF в контейнер также не прошла. Визуальный просмотр оригинала НЕ заявляется. Две нормировки независимо проверены алгебраически и численно ниже.

P2. G. Illies, *Cramer functions and Guinand equations*, Acta Arith. 105 (2002), 103-118: Introduction и Theorem §3. Это первичная современная работа, подтверждающая нормировку продолжения, полюсов и уравнение Гинана. PDF-текст прочитан; screenshot также вернул Cache miss.

P3. M. Suzuki, arXiv:2206.03682v4, (1.1)-(1.3). Первая страница просмотрена PDF-screenshot. Импортируется полный источник Ψ и его нулевая запись; положительность не импортируется.

P4. DLMF 25.2, 25.10 и 5.11: полюс ζ в 1 и разложение Лорана, симметрии нулей, секторная асимптотика digamma. Количественные переходы к нашей асимптотике выведены ниже.

Адреса первичных источников:
```text
https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0004/PPN266833020_0004.pdf
https://www.impan.pl/shop/en/publication/transaction/download/product/82943
https://arxiv.org/pdf/2206.03682v4
https://dlmf.nist.gov/25.2
https://dlmf.nist.gov/25.10
https://dlmf.nist.gov/5.11
```

**[ABSTRACT | PAPER; E/F/Z/A, conventions.]** Пишем rho=beta+i*tau, tau>0, и сохраняем все кратности nu_rho. Функция Крамера в первоначальной НЕЦЕНТРИРОВАННОЙ нормировке:

    U(z)=sum_(tau>0) nu_rho exp(rho*z), Im z>0.

Наша центрированная функция:

    V(z)=exp(-z/2)U(z)
        =sum_(tau>0) nu_rho exp((rho-1/2)z)
        =sum_(tau>0) nu_rho exp(i*gamma_rho*z),
    gamma_rho=tau+i(1/2-beta).                              (1)

gamma_rho здесь КОМПЛЕКСНА, пока не доказана RH. Если вместо нее взять только вещественную ординату tau, получится другая функция, не различающая off-line четверки. Сумма по ОБОИМ знакам tau не сходится в верхней полуплоскости как обычный ряд. В (1) всегда используется верхняя половина нулей.

Ряды сходятся абсолютно и локально равномерно в Im z>0, потому что 0<beta<1 и N(T)=O(T log(2+T)). Необходимые счетные оценки не являются утверждением о расположении нулей на прямой.

Ниже "равномерно субэкспоненциально" означает:

    for every epsilon>0 there are C_epsilon,X_epsilon
    such that |R(x+i*y)|<=C_epsilon exp(epsilon*x)
    for x>=X_epsilon and 0<y<=1.                           (2)

Достаточно опровергнуть положительное направление x→+infinity, чтобы опровергнуть двустороннюю версию. В точках x=log(p^m) после правильного вычитания используется устранимое продолжение остатка, а не исключение окрестностей полюсов.

## 2. Что именно вычитаем: сходящаяся нормировка главных частей

**[ABSTRACT | PAPER; E/I/A, import P1.]** Положим a_n=log n и

    b_n=Lambda(n)/(n log n),  n>=2.

Так b_(p^r)=1/(r p^r), остальные b_n равны нулю. Арифметическая мероморфная часть Крамера в центрированной нормировке:

    P_C(z)=z/(2*pi*i) [ exp(z/2) sum_(n>=2) b_n/(z-a_n)
                       -exp(-z/2) sum_(n>=2) b_n/(z+a_n) ]. (3)

Обе суммы нормально сходятся вне полюсов. Для больших n знаменатель по модулю не меньше (log n)/2 на каждом фиксированном компакте. Сходимость sum b_n/log n следует, например, из точного положительного интеграла

    sum b_n/log n = integral_0^infinity log(zeta(1+u))du < infinity.

У нуля подынтегральная функция равна -log u+O(u), на бесконечности экспоненциально убывает. Здесь не нужна RH или нулевая зона.

Прямая проверка вычетов дает

    Res_(z=+a_n) P_C = Lambda(n)/(2*pi*i*sqrt(n)),
    Res_(z=-a_n) P_C = Lambda(n)/(2*pi*i*sqrt(n)).          (4)

Это именно вычеты V. В U вычеты различаются: Lambda(n)/(2*pi*i) и Lambda(n)/(2*pi*i*n).

Нормировка важна. Голая бесконечная сумма всех главных частей не получает сходимость автоматически; даже симметричное спаривание +/- полюсов здесь не дает конечного фиксированного рода по одним степеням log n. Два нормальных решения Mittag-Leffler задачи могут отличаться целой функцией, что способно изменить горизонтальный показатель. Поэтому неопределенное "вычесть полюсы" еще не определяет остаток.

Логарифмическая часть в нормировке V:

    B(z)=exp(-z/2)/(2*pi*i)*log z/(1-exp(-z))
        =log z/(4*pi*i*sinh(z/2)).                        (5)

Используется ветвь, совпадающая с вещественным log x при x>0. В литературной U это log z/(2*pi*i*(1-exp(-z))); выражение без центрирующего множителя или со знаменателем 1-exp(z) нельзя молча переносить в (1).

Определим конкретный проверяемый остаток:

    R(z)=V(z)-P_C(z)-B(z).                                (6)

Дополнительное вычитание известной главной части в z=0 не меняет результатов при x→+infinity: в центрированной нормировке это O(exp(-x/2)/x). Мы не требуем равномерного контроля возле z=0.

## 3. Уже граничный источник опровергает равномерный субэкспоненциальный бюджет

**[COFINAL_FAMILY | PAPER; E/F/A.]** Уравнение Гинана для U после центрирования и граничной симметрии дает при x>0, x!=log(p^r):

    2 Re V(x+i0)=2cosh(x/2)-j(x),
    j(x)=exp(-x/2)/(1-exp(-2x)).                           (7)

Симметрия V(-conj z)=conj V(z) следует из rho -> 1-conj rho среди верхних нулей. Значение при -x в формуле Гинана получается продолжением через отрицательную вещественную ось; вне ее полюсов оно совпадает с верхним граничным значением. Так (7) не требует RH.

На каждом положительном вещественном x вне полюсов P_C(x) и B(x) чисто мнимы. Следовательно,

    Re R(x)=cosh(x/2)-j(x)/2
           =exp(x/2)/2-exp(-x/2)/(2*(exp(2x)-1)).          (8)

Это точная формула для действительного источника ζ. В частности, правая часть >=exp(x/2)/3 при x>=log 2.

Если (2) верно, можно при каждом таком x перейти y↓0, поскольку R имеет продолжение через границу. Получили бы

    exp(x/2)/3 <= C_epsilon exp(epsilon*x),

что невозможно при epsilon<1/2. Можно взять явно x_N=log(N+1/2), чтобы ни одна точка не была арифметическим полюсом.

Более общий вывод: такой же контрконтроль относится к любой нормальной полярной вычитаемой функции, чисто мнимой на положительной вещественной оси, и любой логарифмической поправке с тем же свойством. Он НЕ запрещает дополнительно вычесть целую функцию с экспоненциальной действительной частью.

Связь с пружиной точна, но распределительна. Дифференцирование (1.1) Suzuki на x>0 дает

    Psi''=2cosh(x/2)-j(x)
             -sum_(n>=2) Lambda(n)/sqrt(n) delta_(log n). (9)

Именно этот distribution равен 2 Re V(x+i0). Вне атомов это (7); в точке a_n вещественная часть r_n/(x-a_n+i*y), r_n=Lambda(n)/(2*pi*i*sqrt(n)), стремится к -Lambda(n)/(2sqrt(n))*delta_(a_n). Поэтому полюсная нормировка и удары исходной Ψ совпадают. Никакого незаконного абсолютного двукратного дифференцирования ряда по нулям не требуется.

## 4. Сильнее: после стандартного вычитания остается exp(x/2) log x даже на фиксированной горизонтали

### 4.1. Точная формула Крамера

**[ABSTRACT | PAPER; E/F/A, THEOREM P1.]** Введем

    I(z)=integral_0^1 exp(s*z) log|zeta(s)| ds,
    J(z)=integral_0^infinity [u/(exp(u)-1)] du/(u+z),
    c0=1/4+(EulerGamma+log(2*pi))/(2*pi*i),

    A(z)=exp(-z/2) [ c0(1+1/z)
             +psi(z/(pi*i))/(2*pi*i)-J(z)/(2*pi*i*z) ],

    H_zeta(z)=exp(z/2)/2-exp(-z/2)*z*I(z)/(2*pi*i).        (10)

Тогда (13) Крамера, переведенное в (1), дает

    V(z)=P_C(z)+H_zeta(z)+A(z),                          (11)
    R(z)=H_zeta(z)+A(z)-B(z).

I и H_zeta — целые функции: log|zeta(s)| интегрируема на [0,1], а ζ(s)<0 при 0<=s<1. Последнее следует из чередующегося eta-ряда при 0<s<1 и ζ(0)=-1/2. Идентичность (11) первоначально в правой верхней четверти, затем продолжается; ниже достаточно Re z>0, 0<=Im z<=1 после снятия арифметических полюсов.

A — известная архимедова функция. Она не содержит неизвестных нулей. Для x→+infinity, 0<=y<=1,

    |A(x+i*y)-B(x+i*y)| <= C exp(-x/2) log(2+x).           (12)

Для J достаточно |J(z)|<=pi^2/(6x). Для digamma применяется секторная асимптотика ψ(w)=log w+O(1/|w|) при w=z/(pi*i); аргументы остаются в фиксированном секторе вдали от отрицательной вещественной оси. Для B используется |sinh(z/2)|>=sinh(x/2). Все константы в (12) независимы от y.

### 4.2. Доказательство равномерной асимптотики

**[COFINAL_FAMILY | PAPER; A.]** Положим v=1-s и

    a(v)=log[-v*zeta(1-v)], a(0)=0.

На [0,1] это гладкая вещественная функция. Из Laurent-разложения ζ в 1:

    a(v)=-EulerGamma*v+O(v^2).

Для совершенно определенного бюджета можно взять

    M2=(1/2)max_(0<=v<=1)|a''(v)|<infinity;
    |a(v)+EulerGamma*v|<=M2*v^2.                         (13)

Этот компактный максимум не зависит от положения комплексных нулей и не предполагает целевой оценки. Конечность следует из ненулевости -vζ(1-v) на вещественном компакте после устранения полюса.

Так как log|ζ(1-v)|=-log v+a(v),

    exp(-z)*I(z)=integral_0^1 exp(-z*v)[-log v+a(v)]dv.

Для Re z>0:

    integral_0^infinity exp(-z*v)(-log v)dv
            =(log z+EulerGamma)/z,
    integral_0^infinity v exp(-z*v)dv=1/z^2.

Хвосты с v>=1 оплачены оценками log v<=v-1 и элементарными экспоненциальными интегралами. При x>=1, 0<=y<=1:

    |z exp(-z)I(z)-(log z+EulerGamma-EulerGamma/z)|
    <=sqrt(2)*[2M2/x^2
           +exp(-x)*(1/x+EulerGamma*(1+1/x))].            (14)

Итак, из (11)-(14):

    exp(-z/2)R(z)
       =1/2-(log z+EulerGamma)/(2*pi*i)
            +EulerGamma/(2*pi*i*z)+O(x^-2)
            +O(exp(-x)log(2+x)),                         (15)

РАВНОМЕРНО по 0<=y<=1. В частности,

    R(x+i*y)/(exp((x+i*y)/2)*log x) -> i/(2*pi)           (16)

равномерно в той же полосе. Поэтому для всех достаточно больших x и всех 0<=y<=1:

    |R(x+i*y)| >= exp(x/2)*log x/(4*pi).                 (17)

Это уже опровержение субэкспоненциальности на КАЖДОЙ фиксированной горизонтали, не только проблемы y↓0.

Строго отрицательный верхний envelope для предполагаемой оценки (2), при 0<epsilon<1/2:

    C_epsilon exp(epsilon*x)-|R(x+i*y)|
    <=C_epsilon exp(epsilon*x)-exp(x/2)log x/(4*pi)<0.    (18)

Именно (18) является KILL, а не неуспехом достаточной оценки.

Даже вычитание ведущего гладкого члена

    H_lead(z)=exp(z/2)[1/2-(log z+EulerGamma)/(2*pi*i)]

не дает субэкспоненциальность: оставшийся ненулевой член exp(z/2)*EulerGamma/(2*pi*i*z) в (15) по-прежнему имеет показатель 1/2. Конечное уменьшение степенного множителя не равно уменьшению экспоненциального показателя.

Этот результат не меняется от наличия или отсутствия RH. В RH-ветке исходная V на фиксированной y ограничена, но P_C сама содержит встречные экспоненциальные члены. Их вычитание разрушает уже имевшуюся компенсацию.

## 5. Свое полное вычитание возможно — но тогда нулевая информация переезжает в него

**[ABSTRACT/COFINAL_FAMILY | PAPER; E/F/A.]** Разрешим вычесть всю явно заданную целую H_zeta из (10). Получится точное равенство

    R_full=V-P_C-B-H_zeta=A-B,
    R_full(x+i*y)=O(exp(-x/2)log(2+x)), 0<=y<=1.          (19)

Это безусловная оценка, сильнее запрошенной по скорости. Но она НЕ дает требуемого короткого замыкания: исходная V равна R_full плюс три НЕсубэкспоненциальных контрчлена. H_zeta зависит от log|ζ(s)| на целом интервале (0,1), а не только от локальных principal parts.

Более точно, пусть S=P_C+B+H_zeta. Для каждого фиксированного y>0 рассмотрим одностороннее Laplace-преобразование по x. Из (19) преобразование R_full голоморфно при Re p>-1/2 (интеграл можно начать с x=1, что убирает все локальные вопросы). Значит, все полюса преобразования исходной V при p=rho-1/2, Re p>0, если они существуют, перешли в преобразование S с ТЕМИ ЖЕ вычетами. Это следует из теоремы следующего раздела и равенства V=S+R_full.

Таким образом, (19) — не доказательство отсутствия этих полюсов. Оно лишь перераспределяет их между слагаемыми. Это точная проверка возврата: нельзя восстановить нижний пол исходной формы из положительного/малого исправленного объекта, не оплатив поправку.

Тот же вывод относится к слову "тень": название не добавляет положительности или контроля экспоненциального типа.

## 6. Точный полезный дискриминатор: показатель НЕВЫЧТЕННОЙ V

### Теорема

**[COFINAL_FAMILY | PAPER; Z/F/A.]** Положим

    alpha=sup_(rho, Im rho>0)(Re rho-1/2), 0<=alpha<=1/2.

Для каждого фиксированного y>0:

    limsup_(x->+infinity) log|V(x+i*y)|/x = alpha.         (20)

Значение log 0 понимается как -infinity. Никакая простота нулей, гипотеза разделенности или максимум, достигающий supremum, не предполагается.

### Доказательство

Из (1) сразу:

    |V(x+i*y)|<=exp(alpha*x) Z(y),
    Z(y)=sum_(tau>0) nu_rho exp(-tau*y)<infinity.          (21)

Это дает верхнюю сторону. Для нижней используем не "доминирование одного слагаемого", которое могло бы потерять компенсации, а полюса преобразования ВСЕЙ суммы.

При Re p>alpha абсолютная сходимость дает

    L_y(p):=integral_0^infinity exp(-p*x)V(x+i*y)dx
       =sum_(tau>0) nu_rho exp(i*y*(rho-1/2))
                                  /(p-(rho-1/2)).        (22)

Правая часть мероморфна на всей p-плоскости: вне конечного числа близких полюсов ее ряд нормально сходится на компактах благодаря exp(-tau*y). В каждой различной точке p=rho-1/2 вычет равен

    nu_rho exp(i*y*(rho-1/2)) !=0.                       (23)

Ни другие нули, ни кратность не могут его погасить: одинаковые нули добавляются с одной положительной кратностью.

Предположим, что limsup в (20) равен h<alpha. Выберем h<q<alpha. Тогда интеграл слева в (22) голоморфен при Re p>q. По определению supremum существует нуль с Re(rho)-1/2>q. Мероморфная правая часть имеет там непогашенный полюс (23), противоречащий голоморфности левой после единственности продолжения. Получено (20).

Если alpha=0, тот же аргумент исключает h<0, используя существование нулей с Re(rho)-1/2>=0. Симметрия rho ->1-conj rho гарантирует alpha>=0. Отражение дает аналогичный показатель слева. ∎

### Следствие — точная достаточная цель

    RH iff for SOME fixed y0>0 and EVERY epsilon>0,
       |V(x+i*y0)|<=C_epsilon,y0 exp(epsilon*x)
       for all sufficiently large x.                    (24)

В RH-ветке даже |V(x+i*y)|<=Z(y0) для y>=y0. Равномерность до y=0 не нужна для исключения off-line нулей. Если вместо complex gamma использовать только реальные ordinates, (20) теряется и такая оценка проходит planted-мир без обнаружения нарушения.

**Граница:** (20)-(24) — доказанные импликации и точный показатель; alpha=0 для настоящей ζ в этой работе НЕ доказано.

## 7. Почему Фрагмен–Линделёф не замыкает недостающее автоматически

**[ABSTRACT | PAPER; A.]** В полуполосе x>=x0, 0<=y<=H корректна следующая элементарная версия.

Пусть F голоморфна внутри, непрерывна на границе и имеет грубый рост |F|<=C exp(Ax) равномерно по y. Если на ОБЕИХ горизонтальных границах для каждого epsilon>0 имеется |F|<=C_epsilon exp(epsilon*x), то такая оценка имеет место во всей полуполосе.

Доказательство: применить максимум на прямоугольнике к

    F(z) exp(-epsilon*z) exp(-delta*exp(a*(z-x0))),
    0<a<pi/(2H), delta>0.

На верхней и нижней границах дополнительный множитель имеет модуль <=1; на правой вертикали он подавляет любой exp(Ax), потому что cos(a*y)>=cos(aH)>0. Левая вертикаль компактна. Сначала правая граница идет к infinity, затем delta↓0. Это доказывает утверждение без скрытого предположения о результате.

Но исходные сведения не дают обе нужные горизонтальные границы. "Большая высота" Y делает коэффициенты малыми, не меняя x-показатель. Например, для Y>=1 и tau0=min tau>0:

    Z(Y)<=Z(1) exp(-tau0*(Y-1)),
    |V(x+i*Y)|<=Z(1)exp(alpha*x-tau0*(Y-1)).              (25)

При фиксированном Y экспонента по x остается alpha. При Y→infinity и фиксированном x это очень малая величина; такой порядок кванторов не дает subexponential x-bound на верхней стороне неограниченной полосы.

На нижней границе после стандартного вычитания действует (8), а не малый envelope. Вычеты простых задают сингулярную часть, но не полную граничную норму или допустимую целую часть. После полного вычитания (19) PL можно применить, однако контрчлен требует обратного возврата и содержит все возможные полюса (23).

Именно здесь попытка PL останавливается. Это отсутствие конкретного boundary supplier, не утверждение о невозможности любого нового арифметического доказательства.

## 8. Обязательный w-судья, без потери экспоненциального сигнала

**[COFINAL_FAMILY | PAPER for the specified planted control; A/F/LA.]** Положим gamma0=2*pi/log 2, 0<eta<1/2, кратность nu>=1. Добавим две верхние спектральные точки gamma0+i*eta, gamma0-i*eta (полная симметричная четверка в Xi). Тогда

    V_w(z)-V_0(z)
       =nu[exp(i*(gamma0+i*eta)*z)+exp(i*(gamma0-i*eta)*z)]
       =2nu exp(i*gamma0*z)cosh(eta*z)=:E_w(z).           (26)

E_w целая: ни новые prime-poles, ни log-monodromy не появляются. При z=x+i*y:

    |E_w(z)|>=nu exp(-gamma0*y)
                     [exp(eta*x)-exp(-eta*x)], x>=0.    (27)

При z=iY, напротив,

    |E_w(iY)|<=2nu exp(-gamma0*Y).                        (28)

Следовательно, все локальные polar data и малая величина на большой мнимой высоте совместимы с настоящим горизонтальным ростом exp(eta*x). Он сохраняется на КАЖДОЙ фиксированной y>0 и равномерно снизу на 0<y<=1 после замены exp(-gamma0*y) на exp(-gamma0).

В Laplace-координате (22) появляются полюса p=eta+i*gamma0 и p=-eta+i*gamma0. Поэтому (20) видит добавленную четверку независимо от возможной осцилляционной компенсации.

Связь со старой пружиной: (26) интегрируется в

    Psi_w(t)-Psi_0(t)=-4nu Re[(cos(w*t)-1)/w^2],
    w=gamma0+i*eta.

На L_k=k log 2 это ровно гиперболический вклад из (20) R1. Нормировка, четность и кратность совпадают. Фиксированное вычитание P_C и B оставляет (26) неизменным, хотя у остатка ζ уже имеется больший паразитный показатель 1/2.

Если дополнительно вычесть фиксированную H_zeta, planted остаток равен R_full,0+E_w и растет. Однако для source-adapted полного вычитания H_w=H_0+E_w рост переедет в вычитаемый член и исчезнет из остатка. Именно поэтому (19) нельзя предъявить как доказательство отсутствия четверки: источник возвращается только вместе с H_w.

Равенство w-модели той же арифметической ζ НЕ утверждается: она меняет гладкую/целую часть источника. Контроль запрещает вывод из одних сингулярностей, симметрий и вертикального убывания.

## 9. Что из попытки можно потратить дальше

**Лемма безопасного вычитания [ABSTRACT | PAPER; A].** Для фиксированного y0>0 пусть V=R+S, R(x+i*y0) субэкспоненциальна, а одностороннее x-Laplace-преобразование S независимо продолжается ГОЛОМОРФНО на Re p>0. Тогда RH следует из (22)-(23).

Доказательство: преобразование R голоморфно на Re p>0 из subexponential bound; сумма с преобразованием S тоже. Непогашенные off-line полюса невозможны. Нормировка или регуляризация S должна быть установлена до применения, не через предположение об отсутствии этих полюсов.

Полное вычитание (19) не поставляет эту лемму: его S как раз наследует все возможные правые полюса. Проверять только малость R недостаточно.

Два допустимых представления того же consumer:

| Представление | Решающий проверяемый объект | Kill-power / цена |
|---|---|---|
| Невычтенная V на одной фиксированной горизонтали | Оценка типа alpha=0 через исходную арифметику; полюса (22) — точный судья | Высокая; нормировка дешева, новый арифметический bound дорог и не получен |
| Laplace-safe source subtraction | Одновременно малый R и независимо голоморфный при Re p>0 transform S | Высокая против скрытой потери четверки; перенос полюсов проверяется раньше численного скана |

Это не два новых задания владельцу и не разрешение расширять вычислительный диапазон. Единый следующий математический объект — контрчлен вместе с его x-Laplace transform, а не отдельно "красивый" остаток.

DISCRIMINATOR_FOR_ZERO_CONSISTENT_RESULT: nonzero residue (23); in the planted control the point p=eta+i*gamma0 has residue nu exp(i*y0*(eta+i*gamma0)). Ни нулевой график, ни малая вертикальная амплитуда не заменяют этот тест.

## 10. Классификация и closeout

| Claim | Scope | Verifier / зависимости | Граница |
|---|---|---|---|
| (1), centered normalization and convergence | ABSTRACT | PAPER; F/Z/A | Upper-half zeros, not real ordinates only |
| (3)-(5), prime poles and log term | ABSTRACT | PAPER; E/I/F/A, THEOREM P1/P2 | Explicit fixed subtraction |
| (7)-(9), exact source boundary | ABSTRACT | PAPER; E/F/A | Distribution at poles; pointwise away |
| (15)-(18), actual source exponential remainder | COFINAL_FAMILY | PAPER; A/E/F | Disproves only the specified normalization |
| (19), decaying fully subtracted remainder | COFINAL_FAMILY | PAPER; A/E/F | No safe return to raw V |
| (20), exact horizontal indicator | COFINAL_FAMILY | PAPER; A/Z/F | Not a proof alpha=0 |
| Strip PL lemma | ABSTRACT | PAPER; A | Needs both horizontal boundary inputs |
| w control (26)-(28) | COFINAL_FAMILY | PAPER; A/LA/F | Artificial planted source, not counterexample to ζ |
| Raw subexponential estimate / RH | COFINAL_FAMILY | CONDITIONAL | NOT PROVED |

DOWNSTREAM_CONSUMER: exclude off-line zeros without altering the original Xi/Weil source.
ACTUAL_CONSUMER_REQUIREMENT: raw V has nonpositive horizontal type on one fixed y0>0, or a Laplace-safe subtraction as in §9.
ORIGINAL_REQUESTED_OBJECT: uniform subexponential remainder after stated pole/log subtraction.
ORIGINAL_OBJECT_IS: NOT_NECESSARY; under the specific standard normalization it is false even in the RH branch.
KNOWN_WEAKER_INTERFACES: (24), or §9 with independently verified holomorphy of S-transform.
FAILURE_TYPE: COUNTEREXAMPLE for the precise canonical remainder; NO_DERIVATION for raw alpha=0.
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD for (2) with R=(6); RESEARCH_DEBT for the unchanged global consumer.
REOPEN_TRIGGER: a different explicit subtraction together with proof that its return cannot absorb the positive-Re(p) poles (23), or a direct source bound on raw V.
NOVELTY_AXIS: source-exact normalization audit, uniform counter-asymptotic, and pole-based proof of the exact horizontal indicator; no historical priority claimed.
WHAT_MUST_NOT_BE_REPEATED: infer horizontal type from decay at x fixed,Y→infinity; infer a growth bound from local principal parts; discard the entire Cramer component; treat real ordinates as complex spectral zeros.

Computational status: two exact symbolic groups; four boundary checks; nine asymptotic checks; six planted checks at 50 dps. A separate Cramer-source versus first-25-critical-zero-prefix control was run at 50 and 70 dps. It is a normalization diagnostic, NOT a zero-census proof or an interval certificate. No CCM eigensystem was computed.

The initial 50-dps prefix comparison missed a 1e-34 diagnostic threshold: discrepancy 8.4782286642e-34. This was retained, not silently called a pass. Direct log(zeta(1+u)) rounded to zero for large u before multiplication by an exponentially growing factor. A stable positive Dirichlet tail and 70 dps reduced discrepancy to 7.5527165575e-41. No mathematical formula, theoretical bound or requested sign was changed. The difference includes the unsummed zero prefix tail; no completeness certificate is inferred.

Predictions were saved before these controls. P1 normalizations: confirmed algebraically and by source match. P2 boundary identity: confirmed. P3 leading and next term: confirmed in nine diagnostic samples; theorem is analytic. P4 full subtraction: confirmed by exact identity, fails consumer return without the counterterm. P5 planted growth: proved, all six numerical controls agree. P6 source normalization: initial numerical threshold failed, stabilized repeat passed; neither is a universal theorem.

No independent analytical reviewer, Lean or Arb was used. The derivations are author PAPER results. Cramer/Illies imports are specified separately from new deductions. The GitHub connector exposed read actions, but no create/update/blob-write/ref-update action in this turn; plugin discovery found only the already installed GitHub integration. No commit or push was performed, and no new SHA is claimed. The complete text and executable controls are in this one file.

## Appendix A. Registered controls

```json
{
  "request": "CRAMER_POLE_SUBTRACTION_PL_2026-11-03",
  "test_status": "registered before this session's numerical and symbolic controls",
  "predictions": {
    "P1": "Centered prime-pole residues are Lambda(n)/(2*pi*i*sqrt(n)) at both signs; monodromy subtraction is log(z)/(4*pi*i*sinh(z/2)).",
    "P2": "Cramer source formula minus prime-pole sum has real boundary cosh(x/2)-exp(-x/2)/(2*(1-exp(-2*x))).",
    "P3": "R=V-P_C-B has scaled asymptotic exp(-z/2)R=1/2-(log(z)+EulerGamma)/(2*pi*i)+EulerGamma/(2*pi*i*z)+O(x^-2) for fixed bounded y.",
    "P4": "Subtracting the entire real-segment zeta integral makes R a universal archimedean remainder but does not bound the original V.",
    "P5": "The planted quartet is entire, invisible to prime polar data, vertically small and horizontally of exact exponential type eta.",
    "P6": "The Cramer source formula agrees with a finite zero-series normalization control, without treating the latter as a universal certificate."
  }
}
```

## Appendix B. Reproducible diagnostic controls

Save the next block as `check_cramer.py` in a directory with Appendix A saved as `registration.json`. Run with Python 3, mpmath and SymPy; for example `uv run --with mpmath --with sympy python check_cramer.py`. It writes `results.json`. The finite samples validate normalizations, not the universal inequalities proved above.

```python
import json
import mpmath as mp
import sympy as sp
from pathlib import Path
ROOT=Path(__file__).resolve().parent
assert (ROOT/'registration.json').exists()
mp.mp.dps=50

def ell(s):
    if s == 1:
        raise ValueError('logarithmic endpoint is integrated, not evaluated')
    return mp.log(-mp.zeta(s))

def core_integral(z):
    # Return exp(-z) I(z); interval [0,1] includes an integrable logarithm at v=0.
    def integrand(v):
        if not v:
            return mp.mpf(0)  # value at a single endpoint does not affect the integral
        return mp.exp(-v*z)*ell(1-v)
    return mp.quad(integrand, [0, mp.mpf('.01'), mp.mpf('.1'), mp.mpf('.5'), 1])

def B(z):
    return mp.log(z)/(4*mp.pi*1j*mp.sinh(z/2))

def A(z):
    J=mp.quad(lambda u: (u/mp.expm1(u) if u else mp.mpf(1))/(u+z), [0,1,5,20,mp.inf])
    c=mp.mpf(1)/4+(mp.euler+mp.log(2*mp.pi))/(2*mp.pi*1j)
    return mp.exp(-z/2)*(c*(1+1/z)+mp.digamma(z/(mp.pi*1j))/(2*mp.pi*1j)-J/(2*mp.pi*1j*z))

def R_scaled(z):
    return mp.mpf('.5')-z*core_integral(z)/(2*mp.pi*1j)+mp.exp(-z/2)*(A(z)-B(z))

out={'kind':'noninterval diagnostic normalization checks', 'dps':mp.mp.dps, 'boundary':[], 'asymptotic':[], 'plant':[]}
for x in map(mp.mpf,['0.3','1.1','3','8']):
    r=mp.exp(x/2)*R_scaled(x)
    rhs=mp.cosh(x/2)-mp.exp(-x/2)/(2*(-mp.expm1(-2*x)))
    err=abs(mp.re(r)-rhs)
    assert err < mp.mpf('1e-45')
    out['boundary'].append({'x':str(x),'error':str(err)})
for x in (10,30,100):
    for y in (mp.mpf('0'),mp.mpf('.25'),mp.mpf('1')):
        z=mp.mpc(x,y)
        r=R_scaled(z)
        lead=mp.mpf('.5')-(mp.log(z)+mp.euler)/(2*mp.pi*1j)
        res=r-lead-mp.euler/(2*mp.pi*1j*z)
        out['asymptotic'].append({'x':x,'y':str(y),'scaled_modulus':str(abs(r)), 'x2_next_remainder':str(abs(res)*x*x)})
        assert abs(res)*x*x < 2
eta=mp.mpf(1)/4; gamma=2*mp.pi/mp.log(2)
for x in (4,16,64):
    for y in (mp.mpf('.1'),mp.mpf('1')):
        z=mp.mpc(x,y)
        E=2*mp.exp(1j*gamma*z)*mp.cosh(eta*z)
        lo=mp.exp(-gamma*y)*(mp.exp(eta*x)-mp.exp(-eta*x))
        assert abs(E) >= lo*(1-mp.mpf('1e-45'))
        out['plant'].append({'x':x,'y':str(y),'magnitude':str(abs(E)), 'lower':str(lo)})
# Exact finite analogue of the x-Laplace transform and its nonzero residues.
s,etaS,gamS,yS=sp.symbols('s eta gam y', real=True)
lam=etaS+sp.I*gamS
expr=sp.exp(sp.I*yS*lam)/(s-lam)
assert sp.simplify(sp.limit((s-lam)*expr,s,lam)-sp.exp(sp.I*yS*lam))==0
# Repeated pole subtraction with the centered normalization.
a=sp.symbols('a', positive=True)
resplus=sp.exp(-a/2)*sp.exp(a)*a/sp.exp(a)
resminus=sp.exp(a/2)*a/sp.exp(a)
assert sp.simplify(resplus-resminus)==0
out['exact_symbolic_groups']=2
(ROOT/'results.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print(json.dumps(out, indent=2))
```

The separate source normalization block below is saved as `check_source.py` and run with `uv run --with mpmath python check_source.py`. Its 25 critical zeros are a diagnostic finite prefix only. It does not establish the zero count or the validity of RH below or above that height.

```python
import json
import mpmath as mp
from pathlib import Path
mp.mp.dps=70
ROOT=Path(__file__).resolve().parent

def logzeta1(u):
    if not u: return mp.mpf(0)
    if u < mp.mpf('1e-18'):
        return -mp.log(u)+mp.log1p(mp.euler*u-mp.stieltjes(1)*u*u)
    if u > 60:
        return mp.log1p(mp.fsum(mp.power(n,-1-u) for n in range(2,64)))
    return mp.log(mp.zeta(1+u))

def Ac(z):
    J=mp.quad(lambda u: (u/mp.expm1(u) if u else 1)/(u+z),[0,1,5,20,mp.inf])
    cc=mp.mpf(1)/4+(mp.euler+mp.log(2*mp.pi))/(2*mp.pi*1j)
    return mp.exp(-z/2)*(cc*(1+1/z)+mp.digamma(z/(mp.pi*1j))/(2*mp.pi*1j)-J/(2*mp.pi*1j*z))

def Ic_scaled(z):
    return mp.quad(lambda v: mp.exp(-v*z)*mp.log(-mp.zeta(1-v)) if v else 0,[0,mp.mpf('.01'),mp.mpf('.1'),mp.mpf('.5'),1])

z=mp.mpc('.3','1')
ints=[0,mp.mpf('.01'),mp.mpf('.1'),1,5,15,40,80,160,300]
minus=-mp.quad(lambda u:mp.exp(z*u)*logzeta1(u),ints)
plus=mp.quad(lambda u:mp.exp(-z*u)*logzeta1(u),ints)
Pc=z/(2*mp.pi*1j)*(mp.exp(z/2)*minus-mp.exp(-z/2)*plus)
H=mp.exp(z/2)*(mp.mpf('.5')-z*Ic_scaled(z)/(2*mp.pi*1j))
source=Pc+H+Ac(z)
zeros=[mp.im(mp.zetazero(n)) for n in range(1,26)]
prefix=sum(mp.exp(1j*t*z) for t in zeros)
err=abs(source-prefix)
assert err < mp.mpf('1e-34')
out={'kind':'noninterval source normalization only; finite critical-zero list is not used as a complete zero certificate', 'dps':mp.mp.dps,'z':str(z), 'source':str(source),'zero_prefix_25':str(prefix), 'abs_difference':str(err),'last_ordinate':str(zeros[-1]), 'prime_integral_truncation':300}
(ROOT/'source_results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
```

Selected executed outputs:
```json
{
  "kind": "noninterval source normalization only; finite critical-zero list is not used as a complete zero certificate",
  "dps": 70,
  "z": "(0.3 + 1.0j)",
  "source": "(-0.0000003296518489169345812410682484273031259604549543960766032602632379236576 - 0.0000006472397483322457227582524212753370488084464741730507663571943544773879j)",
  "zero_prefix_25": "(-0.0000003296518489169345812410682484273030575178923134925396751587878991250059 - 0.0000006472397483322457227582524212753370807453899558845940919066706266361114j)",
  "abs_difference": "7.55271655750965009726588232203582485078231689970417522012026792819753e-41",
  "last_ordinate": "88.80911120763446542368234807950937839544489340981867504219987161881401",
  "prime_integral_truncation": 300
}
```