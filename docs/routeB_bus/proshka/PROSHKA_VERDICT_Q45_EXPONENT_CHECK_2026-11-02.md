# STATUS: TRY_Q45_EXPONENT_CHECK

```yaml
OPERATIVE_CLASS: TRY_Q45_EXPONENT_CHECK
REQUEST_ID: Q45_EXPONENT_CHECK_v1
DATE: 2026-11-02
TASK_MODE: DIRECT_OWNER_SOURCE_LOCKED_EXPONENT_AUDIT
BASE: 9c4cbbbf566815030c3e8746876d6e0c6ef7244a
INBOX_SOURCE: 174263d1a095e5cc680cf9e5c5e2ee543106f2bd
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
OBSTRUCTION_SOURCE_BLOB: d2b7a5496a3edb1a59ce853f89125f8ce637a9e8
Q45_POLYLOG_REDUCTION_BLOB: 0f9771e5949456e1c00cfd336e88f84ce103f643
Q45_SHORT_DIVISOR_BLOB: bfb4d3788d78e7edce97b2f03b2b8ad782abc87e
Q45_VERDICT_BLOB: f07dd43fbd168c705397605463084cae114590ad
RESTRICTED_RECEIVER_BLOB: 897a92716a746ce8b9a36adb77e66c83b19bdf59
RESULT: ARCHIVED_EXPONENT_BALANCE_CONFIRMED_WITH_LOG_AND_SCOPE_CORRECTIONS
MISSING_LOG_FACTOR_IN_SHORT_REQUEST: log_L
QUARTER_WINDOW_VS_Q45: EXPONENT_COMPARISON_ONLY_NO_UNPROVED_PAIR_TRANSFER
PRICE_ONLY_FIXED_STRIP_IMPROVEMENT: NOT_OBTAINABLE_FROM_REPORTED_ENVELOPE
ACTUAL_J_LONG_LOWER_BOUND: NOT_NEWLY_PROVED
MINIMAL_DIRECTED_TARGET: EXPLICIT_ORIGINAL_Q45_PHASE_MARGIN
NORM_ONLY_BILINEAR_SHORTCUT: REFUTED_FOR_GENERAL_BOUNDED_COEFFICIENTS_WITH_SAME_WEIGHT
ACTUAL_MOBIUS_ESTIMATE_REFUTED: false
RH_ASSUMED: false
RH_PROVED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROGRESS_SCOPE: COMPLETION_ENVELOPE_BOOTSTRAP_AND_NORM_ONLY_SHORTCUT_ONLY
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
EXACT_CONTROL_GROUPS: 7
INDEPENDENT_ANALYTIC_REVIEW: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NEW_CCM_EIGENPROBLEMS: 0
WRITE_BRANCH: proshka_inbox_2026-10-31
ROUTE_STATE_CHANGED: false
```

Ы. Баланс показателей подтверждён. Две поправки: архивная цена содержит дополнительный множитель log L; оценка Q45 относится к исходной complex actual pair, а не автоматически к новому чётному quarter-window свидетелю. Для краевого свидетеля выходная полуплоскость без нового арифметического выигрыша не лучше входной. Это ограничение данного доказательного бюджета, не нижняя оценка настоящего J_long и не невозможность нового арифметического доказательства.

## 0. Источники и область задания

Прочитаны на BASE:

- S0: `docs/routeB_bus/audits/POLYLOG_RECEIVER_AUDIT_2026-11-02/Q27_Q45_OBSTRUCTION.md` полностью.
- S1: `docs/literature/openai_math_2026-10-07/CCM_Q45_PAIR_POLYLOG_DIVISOR_REDUCTION.md` полностью, особенно A1–A6 и completion budget.
- S2: `docs/literature/openai_math_2026-10-07/CCM_Q45_PAIR_SHORT_DIVISOR_QUADRATURE.md` полностью, особенно S8–S9.
- S3: `docs/literature/openai_math_2026-10-07/PROSHKA_CCM_ACTUAL_MOBIUS_FORCING_SEAM_Q45_VERDICT_2026-10-26.md`, §§1–3, 5–7: определение настоящей пары, направление (6.1), все возвраты.
- S4: `docs/literature/openai_math_2026-10-07/CCM_RESTRICTED_PRIME_RECEIVER.md` полностью: исходный краевой свидетель и его carrier.
- S5: `docs/literature/openai_math_2026-10-07/CCM_Q45_CONCLUSION.md` полностью.
- S6: `docs/routeB_bus/proshka/PROSHKA_VERDICT_POLYLOG_REENTRY_CENTERED_BUDGET_2026-11-02.md` на INBOX_SOURCE, §§0–6: quarter-window свидетель, H_m, допустимый subpolynomial бюджет.

Файлы S1–S5 вне `docs/routeB_bus/` открыты именно для нужных здесь исходных формул; запись туда не производится. Нового независимого аудита всех аналитических поставщиков S1–S6 нет. CALIBRATE_EULER_LEVER_v1 не объявляется выполненным этим отдельным Q45-ответом; G0 ниже рассматривается только как предложенный инструмент.

Внешняя первичная сверка: NIST DLMF §27.4, (27.4.5), и §27.5, (27.5.2), (27.5.5); D. R. Heath-Brown, *Prime Numbers in Short Intervals and a Generalized Vaughan Identity*, Canad. J. Math. 34 (1982), 1365–1377, DOI 10.4153/CJM-1982-095-9, издательская запись/авторское введение. Из последней не импортируется оценка для нашего C. Тождество Вона ниже доказано непосредственно.

## 1. Зафиксированный скаляр; не меняем C или пару

**[COFINAL_FAMILY | CONDITIONAL: существование гипотетического off-line w; остальные определения исходные.]**

Пусть w=eta+i gamma, 0<eta<1/2, — гипотетический нуль, nu — его кратность. Профили g,k отдельно нормированы как в S3. Корреляция

    C(v)=integral_R conjugate(g(t)) k(t+v) dt

комплексна. В частности, её комплексный нормирующий коэффициент не заменяется модулем. Сохраняются оба направления времени и контакты M_C(±1/2)=M'_C(±1/2)=0.

Пишем L=log m, y=L-2log L, D=floor(m/L^6). Конечная длинная сумма:

    J_long(m;w)=sum_(1<=k<L^6) log(k)/sqrt(k)
       * sum_(D<d<=m/k) mu(d)/sqrt(d)
         [C(y-log(dk))+C(y+log(dk))].                 (1.1)

Все нецелые края понимаются буквально. Условие k<L^6 необходимо для непустой суммы, а не замена исходного cutoff. S1 даёт J=J_long+o_w(1); полная mixed-fee — дважды эта ошибка, затем original projection-return o_w(1) один раз. Self-термы O_w(1), arch-терм O_w(L) сохранены.

Новый чётный H_m из S6 и исходный complex sparse P из S1–S4 не отождествляются. Ниже сравнение с quarter-window сигналом — проверка показателей при условии наличия соответствующего переноса. Единственный используемый как actual-pair потребитель — краевой S3–S4.

## 2. Передоказательство арифметики опубликованной цены

**[COFINAL_FAMILY | CONDITIONAL на Mertens-premise; A/LA.]** Предположим только для расчёта

    |M(x)|<=K x^beta,   M(x)=sum_(d<=x) mu(d),
    fixed 1/2<=beta<1.                                  (2.1)

Для каждого k ставим B_D(x)=M(x)-M(D) и

    F_k(x)=x^(-1/2)[C(y-log(kx))+C(y+log(kx))].

Тогда B_D(D)=0, |B_D(x)|<=2K x^beta при x>=D, и точно

    sum_(D<d<=m/k)mu(d)F_k(d)
      =B_D(m/k)F_k(m/k)-integral_D^(m/k) B_D(x)F'_k(x)dx.

Нижний M(D) сохранён. Верхний край имеет аргументы C(-2log L), C(2L-2log L) и оплачен исходными хвостами, не объявлен нулём. Подстановка v=log(kx)-y и S1 A1 для C,C' даёт

    |J_long| <= A_(w,beta) K exp((beta-1/2)y)
                      sum_(k<L^6) log(k)/k^beta + o_w(1). (2.2)

Константа зависит от фиксированных w,beta, но не от m. При X>=2

    integral_1^X (log t)t^(-beta)dt
     =X^(1-beta)[log X/(1-beta)-1/(1-beta)^2]
        +1/(1-beta)^2.

Следовательно sum_(k<L^6)log(k)/k^beta=O_beta(L^(6-6beta)log L). Кроме того,

    exp((beta-1/2)y)=m^(beta-1/2)L^(1-2beta).

Итак, ровно опубликованная цена:

    B_beta(m)=m^(beta-1/2)L^(7-8beta)log L,
    |J_long|<=A_(w,beta)K B_beta(m)+o_w(1).               (2.3)

В коротком запросе log L пропущен. На строгие m-показатели это не влияет, на equality-case влияет. При beta=1 нельзя подставлять beta=1 в O_beta из (2.3): сумма равна O((log L)^2), и цена

    B_1(m)=sqrt(m)(log L)^2/L.                           (2.4)

Она хуже сохранённого в S3 (6.6) fallback sqrt(m)/L. Никакого нового Mertens-bound здесь не получено.

## 3. Два сравнения; открытая полуплоскость не улучшается

**[ABSTRACT | PAPER: арифметика показателей, LA.]**

Сигналы:

    X_quarter=m^(eta/2),
    X_edge=m^eta L^(-2eta).

Их отношения к цене задаются точно:

    B_beta/X_quarter
      =m^(beta-1/2-eta/2)L^(7-8beta)log L;               (3.1)
    B_beta/X_edge
      =m^(beta-1/2-eta)L^(7-8beta+2eta)log L.            (3.2)

Строгое отрицательное значение m-показателя обеспечивает o(1), независимо от фиксированных логарифмических степеней.

### 3.1. Равенство степеней не спасает архивный бюджет

Для edge равенство eta=beta-1/2 даёт

    B_beta/X_edge=L^(6-6beta)log L -> infinity, beta<1.  (3.3)

Для quarter равенство eta=2beta-1 совместимо с 0<eta<1/2 только при 1/2<beta<3/4. Тогда 7-8beta>1 и отношение в (3.1) также расходится. Вне этого диапазона формальная equality-ветвь не соответствует исходному нулю в критической полосе.

При beta=1 edge-отношение для каждого eta<1/2 равно

    m^(1/2-eta)L^(2eta-1)(log L)^2 -> infinity.

Даже более дешёвый endpoint fallback sqrt(m)/L не меняет положительный m-показатель.

### 3.2. Выходная граница

Пусть входная полуплоскость задаётся beta_0>=1/2. Даже предоставив максимально благоприятный Mertens-перенос: для каждого epsilon>0 доступны (2.1) с beta=beta_0+epsilon<1, получаем:

| Witness | Условие подавления сигнала | Выходная полуплоскость |
|---|---|---|
| Quarter, если отдельно оплачен перенос Q45 | eta>2(beta_0-1/2) | Re s>2beta_0-1/2 |
| Исходный edge actual pair | eta>beta_0-1/2 | Re s>beta_0 |

При beta_0>=3/4 quarter-строка не исключает ни одного нового нуля с Re s<1. Например beta_0=11/12 даёт quarter-границу 4/3, edge-границу 11/12.

Это не доказательство обратной теоремы «одной геометрической записи zero-free region автоматически достаточно для Mertens со всеми нужными константами». Такой перенос здесь предоставлен условно, в наиболее выгодной версии. Даже эта версия не даёт self-improvement.

### 3.3. Точное препятствие именно логическому выводу из upper

Если B_beta/X_edge -> infinity, скалярная модель

    J_model(m)=-nu exp(-i gamma y) X_edge

удовлетворяет |J_model|<=A B_beta для всех достаточно больших m при любом фиксированном A>0, но НЕ даёт благоприятного запаса над -nu X_edge в фазовой компоненте. Аналогично для quarter в неподавляемом диапазоне.

Модель не объявляется настоящей mu-суммой. Она доказывает, что одного опубликованного upper и оплаченных меньших ошибок логически недостаточно для нового исключения нуля. Расходимость цены НЕ доказывает расходимость или плохой знак actual J_long. Утверждение о самом CCM не опровергнуто.

## 4. Минимальная направленная цель на той же actual pair

**[COFINAL_FAMILY | CONDITIONAL на новый арифметический вход; E/F/A/I и LA при возврате.]**

Положим

    Z_w(m)=Re(exp(i gamma y) J_long(m;w)),
    X_w(m)=exp(eta y)=m^eta/L^(2eta).

S3 (6.1), S1 A6 и оплаченный o(1)-возврат требуют именно LOWER:

    Z_w(m) >= -(nu-theta_w/2) X_w(m)-o_w(X_w(m)),
    theta_w>0 fixed,                                    (4.1)

на одной неограниченной исходной семье. Gamma, eta, nu и вес C принадлежат той же фиксированной hypothetical pair. Не нужны uniformity по всем w, upper на положительную часть Z_w, либо all-P операторная норма.

Эквивалентная удобная нормированная цель: liminf Z_w/X_w > -nu на выбранной семье. Сильнее необходимого, но достаточно:

    [ -Z_w(m) ]_+ = o_w(X_w(m)).                         (4.2)

Условие |J_long|=o(X_w) ещё сильнее; положительную компоненту оно ограничивает напрасно. Более тонкий leading-coefficient выигрыш тоже допустим: достаточно independently proved upper на (-Z_w)_+ с коэффициентом строго меньше nu при масштабе X_w. Это уже ломает баланс без требования понизить m-показатель actual J.

Опубликованная fixed theta-форма не объявляется необходимым условием любого доказательства RH. Если все остальные fees возвращены с явным upper F_w(m)=O_w(L), достаточно направленного запаса a_w(m) над -nu X_w, для которого 2a_w(m)>F_w(m) eventually на выбранной семье. Например a_w/L -> infinity достаточно при известных таких fees. До отдельного учёта их коэффициентов безопасный опубликованный интерфейс — (4.1).

### 4.1. Точный размер выигрыша относительно цены Q45

Предположим новый ОДНОСТОРОННИЙ upper на (-Z_w)_+ вида

    A_w m^(beta-1/2-Delta) L^(7-8beta-v) (log L)^(1-u),    (4.3)

где Delta — выигрыш m-показателя, v,u — логарифмические выигрыши. Для o(X_edge) достаточно и для данного monomial-envelope необходимо:

    Delta>beta-1/2-eta;

либо при равенстве:

    7-8beta-v+2eta<0,

либо при одновременном равенстве последней степени нулю: u>1.

Это следует прямым делением (4.3) на X_edge. Если m-показатель положителен, никакие фиксированные v,u его не исправляют.

В частности, при Delta=0 и eta=beta-1/2 требуется

    v>6(1-beta),

либо v=6(1-beta) вместе с u>1. Чисто логарифмический ремонт может решить equality-case для точной beta-предпосылки, но не сдвинуть открытую границу на фиксированное расстояние.

Чтобы при лучшем входном beta_0+epsilon получить открытую полуплоскость Re s>beta_1<beta_0 через edge, достаточно нового направленного power saving Delta=beta_0-beta_1, равномерного по m; epsilon выбирается ПОСЛЕ фиксации проверяемого нуля, достаточно малым. Для исключения самого граничного eta=beta_1-1/2 нужны отдельно строгий показатель либо логарифмический/коэффициентный запас. Для покрытия всех eta>0 достаточно, например, (-Z_w)_+<=C_(w,epsilon)m^epsilon для каждого epsilon>0.

Это спецификация недостающего supplier, не полученная оценка.

## 5. Что считалось бы независимым источником выигрыша

### 5.1. Более сильный all-prefix Mertens-bound уже содержит более сильную зону

**[ABSTRACT | PAPER; E/I + A/LA.]** Если |M(x)|<=K x^b, b<1, то

    F(s)=s integral_1^infinity M(x)x^(-s-1)dx

голоморфна при Re s>b. При Re s>1 она равна sum mu(n)n^-s=1/zeta(s) по частичному суммированию. Аналитическое продолжение равенства zeta(s)F(s)=1 исключает нули zeta при Re s>b; точка s=1 обрабатывается как полюс zeta/нуль F, а не как нуль zeta.

Поэтому подстановка новой универсальной M-оценки с меньшим b уже импортирует усиленную zero-free информацию. Это не запрещает доказывать такую M-оценку арифметически; это запрещает выдавать её за бесплатный промежуточный вход Q45.

Направленная оценка (4.1) на конкретном C существенно уже all-prefix Mertens. Её независимое доказательство допустимо, хотя через receiver оно и должно исключить соответствующий нуль: это цель, не признак круговости.

### 5.2. mu*1=delta и mu*log=Lambda: точное несокращение

**[FINITE_CELL | PAPER; E/I/LA.]** Для любого веса W на n<=m

    sum_(dk<=m) mu(d) log(k) W(dk)
       =sum_(n<=m) Lambda(n) W(n).                       (5.1)

Здесь W(n)=n^(-1/2)[C(y-log n)+C(y+log n)] — буквальный вес. Контактные моменты оплачивают соответствующий непрерывный фон, но log(k) не заменяется единицей. Поэтому mu*1=delta не зануляет (5.1): уже при n=p коэффициент равен log p, не нулю. Все степени простых возвращаются с их исходными коэффициентами. Это строгий запрет только на такой неверный шаг сокращения.

### 5.3. Vaughan/Heath–Brown: допустимый источник разложения, не поставленный bound

**[ABSTRACT | PAPER; E/I/LA.]** Обозначим mu_U=mu 1_(n<=U), Lambda_V=Lambda 1_(n<=V), 1 — постоянную арифметическую функцию, * — Dirichlet convolution. Тогда

    Lambda = mu_U*log - mu_U*1*Lambda_V
             +Lambda_V + mu_>U*1*Lambda_>V.              (5.2)

Доказательство: log=1*Lambda и mu*1=delta; раскладываем mu и Lambda на короткую/длинную части. Тождество (5.2) сохраняет W(n), phase, все знаки и cutoff n<=m. Разложения Хит-Брауна дают дополнительные переменные, но сами также являются тождествами; их релевантность не означает оценки нашего конкретного C.

**Точный контроль norm-only завершения с ТЕМ ЖЕ C.** Выберем v_0 с C(v_0)!=0 и малое фиксированное a>0. Рассмотрим прямоугольник

    k ~ K_m=L^2,
    d ~ A_m=exp(y-v_0)/K_m = exp(-v_0)m/L^4,

с относительной шириной a. Для больших m он целиком лежит в d>D, k<L^6, dk<m. На нём y-log(dk) близко к v_0, а C(y+log(dk)) равномерно исчезающе мало. По непрерывности C можно выбрать фазу zeta_m, |zeta_m|=1, так что

    Re{exp(i gamma y) zeta_m
       [C(y-log(dk))+C(y+log(dk))]} <= -c_w<0

на всём прямоугольнике. Подставив коэффициенты a_d=zeta_m на d-прямоугольнике и 0 вне его, а b_k=1 на k-прямоугольнике и 0 вне, получаем

    Re sum_(d,k rectangle) a_d b_k log(k)/sqrt(dk)
       exp(i gamma y)[C(y-log(dk))+C(y+log(dk))]
       <= -c'_w sqrt(m) log L/L.                        (5.3)

Действительно, членов ~A_m K_m, вес ~log K_m/sqrt(A_m K_m), откуда величина ~sqrt(A_m K_m)log K_m ~sqrt(m)log L/L. Все константы фиксированы после выбора C,v_0,a. Если C тождественно нулевая, J_long=0 и этот контроль не нужен; настоящая пара имеет ненулевой transform из S3 (2.7).

(5.3) — не замена mu(d) в исходной задаче и не контрпример actual-pair цели. Это доказательство, что из одной нормы коэффициентов |a_d|,|b_k|<=1 и аналитичности именно этого C power saving не следует. Нужна настоящая арифметическая корреляция mu/Type-II coefficients с весом; простого уменьшения числа k недостаточно.

### 5.4. G0 и положительность Lambda: место потери применимости

**[ABSTRACT | PAPER; E/A/LA.]** Для sigma>1 тождество

    3+4cos(theta)+cos(2theta)=2(1+cos(theta))^2>=0

даёт положительную комбинацию абсолютно сходящихся Euler-сумм. Она не даёт знак произвольной комплексной корреляции C. Более точно, контакты S1 дают для

    W_y(x)=x^(-1/2)Re{exp(i gamma y)
                 [C(y-log x)+C(y+log x)]}

    integral_0^infinity W_y(x)dx
      =Re{exp(i gamma y)[exp(y/2)M_C(-1/2)
                        +exp(-y/2)M_C(1/2)]}=0.          (5.4)

Всякий нетождественно нулевой такой W_y меняет знак. Поэтому он не является неотрицательной смесью точечно неотрицательных G0-ядер без дополнительного подписанного остатка. На исходном конечном отрезке хвосты дают уже оплаченный o(1), но не желаемую одностороннюю оценку prime-вклада.

Даже при предоставленном G0/PNT-конверте вида sqrt(m)exp(-r(L))L^B с r(L)=o(L), его отношение к X_edge имеет логарифм

    (1/2-eta)L-r(L)+(B+2eta)log L -> +infinity

для каждого eta<1/2. Это точный показатель данного envelope; он не доказывает, что все применения E/G0 обязаны иметь эту цену.

**Ответ об источнике.** В прочитанных закреплённых материалах и проверенных первичных справках нет поставленного directed bound (4.1) или power saving (4.3) на actual C. (5.2) и его multilinear варианты — реальные арифметические инструменты, не сводимые к формулировке zero-free strip, но нужная оценка полученных Type-I/II сумм здесь не доказана. Невозможность всякого такого доказательства НЕ утверждается. Запрещены лишь явно опровергнутые shortcuts (5.1) как нуль и norm-only переход, опровергнутый (5.3).

## 6. RH sanity и пределы переносов

**[ABSTRACT | PAPER; LA/A.]** Формальный beta=1/2 в (2.3) даёт L^3 log L. Это допустимый subpolynomial бюджет для каждого фиксированного eta>0. Он не обязан быть O(1). Утверждение |M(x)|=O(sqrt x) не приписывается RH; здесь это только подстановка в условную формулу.

При beta=1/2+epsilon цена m^epsilon L^(3-8epsilon)log L. Для edge можно выбрать epsilon<eta, для формального quarter-сравнения epsilon<eta/2. Подстановка eta=0 как будто actual off-line pair сохранилась в RH-мире неправомерна: её исходная предпосылка eta>0. Расходимость отдельной допустимой polylog-платы не уничтожает subpolynomial receiver.

Нельзя применять analytic-strip A1 к произвольной compact-support автокорреляции на H_m: она равна нулю на (L,infinity), и голоморфное продолжение тогда было бы тождественно нулевым, против C_f(0)=1. Этот scope-obstruction уже доказан в S1; здесь не переименован в новый. Малая размерность H_m, centered Gram O(L^2), quiet residual и count-геометрия не заменяют отсутствующую actual-pair оценку.

## 7. Реестр E/F/Z/LA/A/I

Здесь E — эйлерова арифметика и коэффициенты; F — конкретные gamma/pole/functional-equation данные; Z — численный счёт/плотность нулей, не фактическое расположение; LA — линейная/Fourier-алгебра и расчёт показателей; A — аналитическое продолжение и оценки; I — структура обычных целых.

| Шаг | Класс | Scope/verifier | Что получено |
|---|---|---|---|
| Q45 A1–A6, полная корреляция и контакты | F/A + E/I/LA при арифметическом возврате | COFINAL_FAMILY/CONDITIONAL, исходные PAPER suppliers | Не новый gain |
| (2.2) -> (2.3), beta=1 endpoint | A/LA | COFINAL_FAMILY/CONDITIONAL on M-bound | Цена с log L подтверждена |
| (3.1)–(3.3), no-bootstrap вывод | LA | ABSTRACT/PAPER | Обе степени и equality-case |
| Сигналы S4 и S6 | E/F/A/LA, гипотетический нуль | COFINAL_FAMILY/CONDITIONAL | Наследуемые, не заново вся цепь |
| Полный gain criterion (4.1)–(4.3) | LA/A и inherited receiver | COFINAL_FAMILY/CONDITIONAL | Точный достаточный supplier, не доказанный знак |
| M-bound -> zero-free half-plane | E/I/A/LA | ABSTRACT/PAPER | Прямое доказательство через интеграл |
| (5.1), (5.2) | E/I/LA | FINITE_CELL/PAPER | Точные тождества, все powers |
| Norm-only obstruction (5.3) | A/LA | COFINAL_FAMILY/PAPER, НЕ genuine mu | Настоящий C, искусственные ограниченные коэффициенты |
| G0 positivity и контакт (5.4) | E/F/A/LA | ABSTRACT/PAPER | Только scope-boundary переноса |

Новый Z-вход не используется. Расположение гипотетического w относится к A/условию свидетеля; оно не маскируется словом «счёт».

## 8. Предрегистрация, результат и две допустимые репрезентации

Перед исполняемыми контролями зарегистрированы: P1 — цена содержит log L и beta=1 отдельно; P2 — edge equality даёт L^(6-6beta)log L; P3 — log saving не сдвигает фиксированную открытую границу; P4 — нужен фазовый LOWER; P5 — mu*log возвращает Lambda, не нуль. Все пять подтверждены приведёнными вычислениями/доказательствами. Регистрация относится к executable controls после чтения источников, не выдаётся за ставку до всякого рассуждения.

| Репрезентация | Решающий тест | Сила/цена |
|---|---|---|
| Направленная Type-I/II сборка для буквального W_C,y | Новый upper на отрицательную фазовую часть, удовлетворяющий (4.1)/(4.3), с полными краями | 5/5 и высокая новая арифметическая цена |
| Совместная Stieltjes-форма (psi-(x-1)) против W'_C,y | Независимый signed lower, без раздельных модулей; точный continuum-control | 5/5 и умеренная алгебраическая, высокая арифметическая цена |

Это оценки исследовательской полезности, не вероятности. Сам возврат в одну из двух форм не является прогрессом знака.

DISCRIMINATOR: для фиксированной actual pair сравнивать НИЖНИЙ envelope Z_w+(nu-theta_w/2)X_w с полным error upper. Малость |M|, finite fits и положительность другой метрики не заменяют этого. Для исключения неверного norm-only supplier применять (5.3); нельзя выдавать этот planted контроль за genuine mu.

### Единственная CODEX DIRECTIVE

`Q45_DIRECTED_GAIN_SOURCE_GATE`: проверить (2.2)–(4.3) против S1/S2/S3, сохранив phase, complex normalization, beta<1 и два разных witness-carrier. Следующий новый арифметический кандидат принимать только в виде независимой оценки (4.1) либо (4.3) на ТОМ ЖЕ C, с полным cutoff d>D, dk<=m и обеими ориентациями. Если кандидат пользуется лишь coefficient norms, прогнать буквальный product-rectangle (5.3) и остановить этот shortcut. Не заменять actual C произвольной положительной автокорреляцией; не импортировать M(x)<=x^(beta_0-Delta) как якобы уже известный вход. Не менять RH exports или production N=m.

## 9. Closeout / consumer contract / доставка

DOWNSTREAM_CONSUMER: исходный actual-pair margin, затем archived subpolynomial/negative-witness receiver.
ACTUAL_CONSUMER_REQUIREMENT: направленный запас над -nu X с оплаченными self/arch/projection fees; абсолютный o(X) достаточен, но не необходим.
ORIGINAL_REQUESTED_OBJECT: проверка exponent bootstrap и точный новый арифметический gain.
ORIGINAL_OBJECT_IS: exponent audit выполнен; новый supplier НЕ получен.
KNOWN_WEAKER_INTERFACES: (4.1), либо меньший направленный запас, превосходящий весь явный error budget; не обязательно полный Mertens-bound или all-P upper.
FAILURE_TYPE: NO_DERIVATION для genuine signed gain; COUNTEREXAMPLE только для norm-only general-coefficient shortcut.
EPISTEMIC_STATUS: RESEARCH_DEBT для исходной арифметики, не MATHEMATICALLY_DEAD.
REOPEN_TRIGGER: источник одностороннего билinear/Stieltjes сокращения с реальными mu и этим C.
NOVELTY_AXIS: проверен предельный показатель и strict endpoint; дан same-weight norm-only falsifier, а не новая RH-теорема.
FORBIDDEN_REPEAT: считать log-фактор fixed-power выигрышем; переносить Q45 между разными pair/carrier без бюджета; выдавать расходящийся upper за lower actual суммы.
ROUTE_SCORE: 4 для аудита попытки, 2 для прогресса исходного знака.

Вердикт — один новый Markdown в `docs/routeB_bus/proshka/`; старые файлы не меняются. Встроенный код ниже выполнен: 7 exact-control groups, без eigenproblems, Lean, Arb или независимого аналитического аудита. Git-запись сама не является проверкой теорем. Коммит и remote-blob сообщаются отдельно после фактической записи. Скрипт проверяет алгебру, НЕ аналитические утверждения о C или Mobius cancellation.

Реплей из корня репозитория: извлечь следующий python-блок в временный файл и запустить Python 3. Он использует только стандартную библиотеку, создаёт рядом `results.json`. Lean handoff и axiom profile неприменимы: Lean-source не добавляется.

## Приложение: исполняемые локальные контроли

```python
#!/usr/bin/env python3
"""Exact local controls for Q45_EXPONENT_CHECK_v1; no analytic/RH certification."""
from fractions import Fraction as F
from collections import defaultdict
import json
from pathlib import Path

def factor(n):
    out={}; p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n):
    f=factor(n)
    return 0 if any(v>1 for v in f.values()) else (-1)**len(f)

def ds(n):
    return [d for d in range(1,n+1) if n%d==0]

def add_scaled(out, log_vector, scale):
    for p,v in log_vector.items(): out[p]+=scale*v

def clean(v): return {p:a for p,a in v.items() if a}

def lam(n):
    f=factor(n)
    return {next(iter(f)):1} if len(f)==1 else {}

def run():
    reports=[]
    # e^((beta-1/2)y) times the k sum: y=L-2 log L, k<L^6.
    for b in (F(1,2),F(2,3),F(3,4),F(7,8),F(11,12),F(19,20)):
        assert -2*(b-F(1,2))+6*(1-b)==7-8*b
        eta=b-F(1,2)
        assert 7-8*b+2*eta==6-6*b
        assert 6-6*b>0
    reports.append('power_and_log_exponents_exact')
    # Equality for the quarter-window witness in the source range 0<eta<1/2.
    for b in (F(3,5),F(2,3),F(7,10)):
        eta=2*b-1
        assert 0<eta<F(1,2)
        assert b-F(1,2)-eta/2==0
        assert 7-8*b>0
    reports.append('quarter_equality_not_paid')
    b0=F(11,12)
    assert 2*b0-F(1,2)==F(4,3)
    for delta in (F(0),F(1,24),F(1,12),F(5,12)):
        eta=b0-F(1,2)-delta
        assert F(1,2)+eta==b0-delta
        assert 7-8*b0+2*eta==6-6*b0-2*delta
    reports.append('gain_and_zero_free_frontier_exact')
    for n in range(1,129):
        divs=ds(n)
        assert sum(mu(d) for d in divs)==(1 if n==1 else 0)
        x=defaultdict(int)
        for d in divs: add_scaled(x,factor(n//d),mu(d))
        assert clean(x)==lam(n)
    reports.append('mobius_identities_with_formal_logarithms')
    # Lambda=mu_U*log - mu_U*1*Lambda_V + Lambda_V + mu_>U*1*Lambda_>V.
    for U,V in ((1,1),(2,3),(5,7)):
        for n in range(1,97):
            out=defaultdict(int)
            for d in ds(n):
                if d<=U: add_scaled(out,factor(n//d),mu(d))
            for d in ds(n):
                for c in ds(n//d):
                    if d<=U and c<=V: add_scaled(out,lam(c),-mu(d))
                    if d>U and c>V: add_scaled(out,lam(c),mu(d))
            if n<=V: add_scaled(out,lam(n),1)
            assert clean(out)==lam(n)
    reports.append('vaughan_identity_retains_literal_coefficients')
    for nu in range(1,8):
        theta=F(1,3)
        assert -F(nu)+theta/2 > -F(nu)
        # Positive component may be arbitrarily large: only the negative part is constrained.
        assert max(-1000,0)==0
    reports.append('required_one_sided_lower_orientation')
    for c in (F(-1),F(-2,3),F(0),F(3,5),F(1)):
        assert 3+4*c+(2*c*c-1)==2*(1+c)**2>=0
    reports.append('euler_trigonometric_identity')
    return {'groups_passed':len(reports),'checks':reports,
            'analytic_proofs_checked_by_this_program':False,
            'new_actual_pair_bound':False,'RH_proved':False}

if __name__=='__main__':
    result=run()
    print(json.dumps(result,ensure_ascii=False,indent=2))
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')

```

Исполненный результат: 7 групп прошли. `new_actual_pair_bound=false`, `RH_proved=false`.
