# STATUS: TRY_POLYLOG_EVEN_SIGNED_PRIME_FLOOR

```yaml
OPERATIVE_CLASS: TRY_POLYLOG_EVEN_SIGNED_PRIME_FLOOR
DATE: 2026-11-02
TASK_MODE: OWNER_DIRECT_RESEARCH_SYNTHESIS
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_ARCHIVE_COMMIT: a8f0df144461e9cd10c5149721fedb0448800acb
SOURCE_RESTRICTED_RECEIVER_BLOB: 897a92716a746ce8b9a36adb77e66c83b19bdf59
SOURCE_POLYLOG_WITNESS_BLOB: 718f9f9160182ef117bda274896a86bc057b6412
SOURCE_Q04_CONCLUSION_BLOB: e11e483f065759bd35ea19373c57b831273756e8
SOURCE_RAW_LIFT_COMMIT: 4af702e412410d8e5d70a01aa9e37c1e6cb507e3
SOURCE_RAW_LIFT_BLOB: b780faf8aa71d25d4101009acd0fd5a7688e81e6
SOURCE_ARITHMETIC_COMMIT: a4ab9e92bf080ee3bcfd729af067ade6fc6392fc
RESULT: WEAKER_RECEIVER_RECOVERED_AND_CENTERED_GRAM_BUDGET_PROVED
CORRECTION: PREVIOUS_ASSERTION_THAT_LOGARITHMIC_FLOOR_IS_INSUFFICIENT_WAS_TOO_STRONG
NEW_RESULTS:
  - EVEN_POLE_FREE_POLYLOG_WITNESS_REPROOF_WITH_FRACTIONAL_WINDOW_TRANSLATION
  - UNIFORM_CENTERED_MULTIPLIER_BOUND_8_SQRT_1_PLUS_ABS_T
  - CENTERED_DIVISOR_GRAM_UPPER_BOUND_POLYLOG_SQUARED_ON_TWO_CONTACT_BAND
  - ARCHIMEDEAN_BOUND_O_LOG_LOG_M_ON_SAME_SPACE
NEW_PRIME_ONE_SIDED_EXPONENT_GAIN: NONE
RH_PROVED: false
RH_ASSUMED: false
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NEW_CCM_EIGENPROBLEMS: 0
NUMERICAL_CHECKS: NORMALIZATION_ONLY_60_DPS
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: AUXILIARY_UNIFORM_BOUND_AND_RECEIVER_REPROOF_NOT_RH_CLOSURE
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
ROUTE_STATE_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Результат и исправление курса

Ы. RH в этой работе не доказана. Выполнена конкретная перекомпоновка, а не объявление нового имени старому неизвестному.

В архиве уже имеется более слабый достаточный вход, чем постоянный пол на всём J_m-perp: субполиномиальный нижний пол на подпространстве исходного оператора размерности O(log²m). Поэтому моя прежняя фраза «пол -log m недостаточен» была неверна для полной архивной цепочки. Из одного утверждения lambda_min -> -infinity этого действительно не следует; архивный степенной отрицательный свидетель даёт более сильную импликацию.

Восстановленный receiver НЕ объявляется новым открытием. Ниже он дополнительно воспроизведён для чётного блока посредством более простого сдвига на четверть окна. Это требует только всех экспоненциальных хвостовых норм фиксированного разделителя, а не сильного двойного экспоненциального supplier старого receiver. Цена — меньший, но всё ещё положительный показатель отрицательного роста.

Новый непосредственно оценённый объект — полный центрированный делительный Gram. Для него доказан верхний бюджет O(log²m) на том же пространстве. Требуемая односторонняя prime-оценка остаётся открытой. Никакой вывод о знаке исходной формы не делается из положительности вспомогательного Gram.

## 1. Источники и неизменённый оператор

Прочитаны через GitHub:

S1. `docs/literature/openai_math_2026-10-07/CCM_RESTRICTED_PRIME_RECEIVER.md` на source archive commit: отрицательный степенной свидетель, контакты и signed prime receiver.

S2. `docs/literature/openai_math_2026-10-07/CCM_POST_Q26_POLYLOG_WITNESS.md` на том же commit: перенос исходного отрицательного свидетеля в полосу |j|<=ceil(8 log²m), bounded PAPER audit с наследуемыми входами.

S3. `docs/literature/openai_math_2026-10-07/CCM_JOINT_Q04_CONCLUSION.md`: уже известный constrained Z_half bound и явное предупреждение, что положительная метрика не даёт знак её производной. Этот предупреждающий результат не переименовывается в новый.

S4. `docs/routeB_bus/proshka/PROSHKA_VERDICT_DIVISOR_GRAM_PULLBACK_PREFLIGHT_2026-11-02.md` на 4af702e: точный raw/centered lift, все floor-компенсаторы и raw no-go.

S5. `docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_COMPLEMENT_FLOOR_2026-11-02.md` на a4ab9e9: физические корреляции, все prime powers, высшие степени с C3<28.

S6. `docs/routeB_bus/proshka/PROSHKA_VERDICT_MARKOV_2026-10-29.md`, прочитан на b7f710f3d0163055834812644219542e72c087d1, blob ac4661568b9279935a9d868f5e85c8b4c6392610: положительный jump-transform сам по себе требует ещё острой оценки. Старый Poincare-front здесь не объявляется закрытым.

Внешние первичные справки: NIST DLMF 25.2.8 (Euler--Maclaurin), 25.4.4 (завершённая xi), 5.11.9 (gamma на вертикальных прямых), 27.2 (Lambda). Новый multiplier-bound ниже выведен непосредственно; никакая условная zero-free теорема или ZF78 не импортируется.

L=log m, b=L/2, I_m=[-b,b]. K_m — литеральная чётная CCM-матрица на частотах 2pi n/L, n=0,...,m, с нулевым продолжением за окно и физической L²-метрикой. Все простые степени, полюсы и endpoint-эффекты сохранены.

Обозначим

    M_m=min(m,ceil(8L²)),   Omega_0=2pi M_m/L.

H_m — чётные тригонометрические формы с n<=M_m и двумя ТОЧНЫМИ контактами:

    f(b)=0,          integral_I_m cosh(x/2) f(x) dx=0.       (1)

Первый контакт обеспечивает f(-b)=0 и глобальное H¹ нулевого продолжения. Второй убирает чётный полюс; нечётный полюс равен нулю по чётности. H_m не определяется через спектр K_m или через неизвестный нуль. При больших m:

    dim H_m=M_m-1=O(L²),        ||f'||_2<=Omega_0||f||_2.   (2)

Матрица остаётся K_m с N=m: малые коэффициенты дополняются нулями, новая production-семья не вводится.

## 2. Почему именно такой малый тест-класс достаточен

**[COFINAL_FAMILY | PAPER, импликация при гипотетическом off-critical нуле.]** Если существует rho=1/2+eta+i gamma, eta>0, то существуют a_rho>0 и m0(rho), такие что

    lambda_min(K_m restricted to H_m)<=-a_rho m^(eta/2)
    для ВСЕХ целых m>=m0(rho).                            (3)

Это более слабая скорость, чем m^eta/(log m)^(2eta) из S1--S2, но она достаточна для того же subpolynomial receiver. Ни существование off-line нуля, ни RH не утверждаются.

### Доказательство с полным возвратом

**Разделитель.** Положим X(z)=4xi(1/2-iz) и выберем z0=gamma+i eta из соответствующей орбиты нулей. Пусть nu — кратность. Функция

    B(z)=X(z)/[(z²-z0²)(z²-conj(z0)²)]^nu

целая, чётная, вещественного типа и ненулевая в z0. Существуют вещественные a,b, для которых

    G(z)=(z²+1/4)(a+bz²)B(z),             G(z0)=i.          (4)

Действительно, Im(z0²)!=0, поэтому a+bz0² может принимать любое комплексное значение. Тогда G(conj z0)=-i; G зануляется во всех остальных нулях X и в z=+/-i/2. Множитель кратности в явной формуле сохранён.

На каждой фиксированной горизонтальной полосе gamma-фактор и стандартные полиномиальные оценки zeta дают для G и его производных экспоненциальное убывание по Re z. В частности, |G(t)|<=C exp(-|t|/8). Обратный Fourier-образ g вещественен, чётен, гладок, и для любых фиксированных A,q:

    |g^(q)(x)|<=C_(A,q) exp(-A|x|).

Это следует сдвигом Fourier-контура на обе горизонтальные прямые Im z=+/-A. Никакая нижняя оценка |X| не нужна: делится только на фиксированный полином с устранимыми особенностями.

**Фазово согласованный сдвиг.** Возьмём

    t_m=(pi/gamma)*floor(gamma L/(4pi)),
    u_m(x)=g(x-t_m)+g(x+t_m).

Нормы ||u_m||_2 и каждого фиксированного производного L¹-норматива ограничены независимо от m. Оба экспоненциальных момента нулевые, поскольку G(+/-i/2)=0. Полная безусловная нулевая формула сокращается до выбранной орбиты:

    k[u_m]=-16 nu cosh²(eta t_m)
          <=-4nu exp(-2eta*pi/gamma) m^(eta/2).            (5)

Это отрицательный UPPER envelope. В остальных нулях значение остаётся ровно нулевым. Выбрана вся орбита, не один член знаковой суммы.

**Обрезка.** Пусть chi_m — чётный smooth cutoff, равный 1 при |x|<=3L/8 и равный 0 в окрестности |x|>=L/2, с производными порядка O(L^-q). Центры u_m лежат при |x|<=L/4. Поэтому расстояние от центров до области изменения cutoff не меньше L/8. Все экспоненциальные хвостовые оценки g дают для d_m=(chi_m-1)u_m, любых фиксированных q,A,N:

    ||exp(A|x|) d_m^(q)||_(L1+L2)=O(m^-N).                (6)

Выбирается достаточно сильная ФИКСИРОВАННАЯ экспоненциальная норма g после фиксации A,N; меняющийся порядок производной не вводится. На арифметической стороне mixed correlations с такой ошибкой оплачиваются суммой sum(log n)n^(-3/2)<infinity, полюсами и интегралом s j(s). Нормы самого u_m с фиксированным весом растут лишь степенно. Поэтому полный cutoff-error есть O(m^-N) после увеличения фиксированного хвостового бюджета. Все prime powers остаются.

**Fourier-return.** Для F_m=chi_m u_m и omega_n=2pi n/L его коэффициенты удовлетворяют при |omega_n|>=1:

    |c_n|<=C L^-1/2[exp(-|omega_n|/8)+m^-N |omega_n|^-2].  (7)

Первый член — full-line G с единичными фазами сдвига; второй получается двумя интегрированиями по частям для d_m. Суммирование геометрического и степенного хвостов, а не одного coefficient-upper, даёт для e_m=F_m-P_M F_m:

    ||e_m||_2+||e_m||_infinity<=C[m^(-2pi)+m^-N],
    ||e'_m||_2<=C(1+L)[m^(-2pi)+m^-N].                   (8)

Здесь eventually M=ceil(8L²), Omega_0>=16pi L. У F_m оба endpoint-значения равны нулю; скачки нулевого продолжения P_MF_m равны endpoint-ошибкам из (8).

Для arch mixed-form используем производную корреляции с двумя endpoint-массами. Её абсолютная величина ограничена суммой ||u||||e'|| и ||u||_infinity(|e(-b)|+|e(b)|); интеграл s j(s) конечен. Полюсный и prime mixed-error ограничены C sqrt(m)(1+L)||u||||e||. Это даёт, например, безопасный полный бюджет

    C m²(1+L)^4[m^(-2pi)+m^-N]=o(1),     N>3.            (9)

Эта намеренно грубая цена уже достаточна; ни одна ошибка не спрятана под утверждением L²-непрерывности глобальной формы.

**Два точных контакта внутри M.** В чётных cosine-координатах нормированный endpoint-вектор имеет компоненты d_n(-1)^n/sqrt(2M+1), d0=1,dn=sqrt2. Вектор p_M, p=sqrt2 cosh(x/2), пропорционален d_n(-1)^n/(1/4+omega_n²). Их нормированная корреляция равна

    r_M=S1/sqrt((2M+1)S2),
    Sj=sum_(n=0)^M d_n²/(1/4+omega_n²)^j.

Для L>=16 и M=ceil(8L²): S1<=L+4, S2>=L/pi, откуда r_M<1/2. Gram двух нормированных контактов >=I/2. Кроме того, ||p||/||p_M||<=6 для достаточно больших m. Контактные ошибки P_MF_m из (6)--(8) поэтому исправляются коэффициентной поправкой O((1+L)[m^(-2pi)+m^-N]) ВНУТРИ той же малой полосы. Источниковая полиномиальная норма K_m (NOESCAPE (2.3)) делает её полную quadratic/mixed цену o(1).

Полученный v_m принадлежит H_m точно, имеет ограниченную норму и

    <v_m,K_m v_m>=-16nu cosh²(eta t_m)+o(1).

Отрицательность гарантирует v_m!=0. Нормирование и (5) доказывают (3). ∎

### Receiver

**[COFINAL_FAMILY | CONDITIONAL на ещё не доказанную нижнюю оценку.]** Достаточно:

    для каждого epsilon>0 существует C_epsilon<infinity,
    K_m|H_m >= -C_epsilon m^epsilon I
    на неограниченной семье исходных m.                  (10)

Семья может зависеть от epsilon. Если существовал бы off-critical нуль с eta>0, берём epsilon=eta/4 и сравниваем (10) с (3). Степенная отрицательная верхняя оценка побеждает lower на любой неограниченной семье. Следовательно (10) влечёт RH. Обратно RH даёт неотрицательную полную форму, а значит (10).

Любая фиксированная polylog-цена C(1+log m)^r достаточна. Даже exp(sqrt(log m)) достаточна. Одна фиксированная положительная степень m^alpha вообще не достаточна для исключения произвольно малого eta этим аргументом. Это точное различие кванторов, а не numerical-fit.

## 3. Архимедова часть на этом пространстве уже мала

**[COFINAL_FAMILY | PAPER.]** Для f in H_m имеем глобальное H¹ и

    ||f-T_s f||<=min(s Omega_0,2)||f||.

Поскольку

    j_+(s)=exp(-5s/2)/(1-exp(-2s))<=exp(-s/2)/(2s),

разбиение интеграла при 1/Omega_0 и 1 даёт

    0<=H_+[f]<=[3+2log(max(1,Omega_0))]||f||².            (11)

Конкретно: малый интеграл <=1/4, средний <=2log Omega_0, дальний <=4exp(-1/2); их постоянная сумма меньше 3.

На чётном f pole-cancellation из S5 даёт O=I_L+R0, где

    R0=integral_0^L exp(-s/2)Q_f(s)ds,       0<=R0<=4||f||².

Неотрицательность R0 следует из Fourier-множителя 1/(t²+1/4). На H_m полюс O=0, следовательно I_L=-R0. Исходный arch-term равен H_++4||f||²-R0, поэтому для полного prime-power оператора P_m:

    K_m|H_m=B_m-P_m|H_m,
    -c_* I<=B_m<=[7+2log(max(1,Omega_0))-c_*]I.            (12)

Здесь c_*=gamma_E+log(8pi)+pi/2. В частности ||B_m||=O(log log m). Никакой полюс не выброшен без контакта.

Непосредственный достаточный source-target:

    lambda_max(P_m restricted to H_m)<=C_epsilon m^epsilon
    для каждого epsilon>0, кофинально или на неограниченной семье. (13)

Это только нужная ВЕРХНЯЯ сторона, не ||P_m||. Требование двухсторонней малой нормы могло бы быть излишне сильным. (13) НЕ ДОКАЗАНО.

## 4. Новый бюджет центрированного делительного lift

### 4.1. Равномерная сумма минус интеграл

**[ABSTRACT | PAPER.]** Для каждого целого N>=1 и вещественного t определим

    z_N(t)=sum_(k=1)^N k^(-1/2+it),
    c_N(t)=N^(1/2+it)/(1/2+it),      b_N=z_N-c_N.

Тогда

    |b_N(t)|<=8 sqrt(1+|t|).                              (14)

Доказательство. Положим T0=1+|t|, M=ceil T0<=2T0. Если N<=M, то sum k^-1/2<=2sqrt N и |c_N|<=2sqrt N, откуда |b_N|<=4sqrt(2T0). Если N>M, пишем

    b_N-b_M=sum_(k=M+1)^N k^-s-integral_M^N u^-s du,
    s=1/2-it.

Сравнение каждого k^-s с интегралом на [k-1,k] даёт

    |b_N-b_M|<=|s|integral_M^N u^-3/2 du
               <=2|s|/sqrt M<=2sqrt T0.

Итого |b_N|<=(4sqrt2+2)sqrt T0<8sqrt T0. Все N,t охвачены; переход к аналитически продолженной zeta не заменяет конечную сумму. ∎

### 4.2. Полный выход и физическая норма

Операторы ровно из S4, без обрезания выходов:

    Z_N f=sum_(k<=N) k^-1/2 f(x+log k),
    C_N f=integral_0^N u^-1/2 f(x+log u)du,
    Ztilde_N=Z_N-C_N.

Их Fourier-множитель равен b_N. Для каждого глобального f in H¹, Parseval и Cauchy--Schwarz дают

    ||Ztilde_N f||²
      <=64[||f||²+||f||||f'||].                           (15)

Входной Fourier-образ НЕ считается компактно поддержанным: оценены все его хвосты через H¹. На H_m это <=64(1+Omega_0)||f||².

Положим

    Gtilde_m[f]=sum_(d=2)^m Lambda(d)/d
                       ||Ztilde_floor(m/d) f||².

Элементарный Chebyshev-upper psi(x)<=4(log2)x и частичное суммирование дают

    sum_(d<=m) Lambda(d)/d<=4(log2)(1+L).

Следовательно

    0<=Gtilde_m[f]<=B(L)||f||²,                           (16)
    B(L)=256(log2)(1+L)(1+Omega_0)=O(L²),     f in H_m.

Все степени простых сохранены. Для фильтра d=p или p² та же верхняя оценка верна по положительности удаляемых слагаемых. Полюсные контакты не нужны для (15); endpoint-контакт нужен, чтобы нулевое продолжение входа действительно было H¹.

Для полноты, psi(2n)-psi(n)<=log binom(2n,n)<=2n log2: каждый prime-power в (n,2n] входит в соответствующую valuation-строку биномиального коэффициента. Телескопирование на степенях двойки даёт использованный psi-upper. Ни PNT, ни RH здесь не нужны.

### 4.3. Точный signed remainder и его статус

Перенос S4 остаётся точным:

    Gtilde_m=G_m-integral_0^L exp(s/2)Q_f(s)Phi_m(s)ds,
    Phi_m(s)=sum_(d=2)^m Lambda(d)/d * floor(floor(m/d)exp(-s)).

Для q_m=H_+-S_m^(1,2) положим R_m=q_m-Gtilde_m. Из (16):

    q_m-B(L)||f||²<=R_m<=q_m,              f in H_m.        (17)

Поэтому существование субполиномиального нижнего пола для R_m ЭКВИВАЛЕНТНО такому полу для q_m. Постоянный lower для R_m больше не является обязательным. Для всего carrier оценка (16) с тем же B(L)=O(L²) не заявляется.

Это не положительный sign supplier. Оно означает: centered Gram на выбранном receiver целиком помещается в допустимый polylog-бюджет. Его положительность не может сама контролировать неоплаченный signed residual. Добавлять к ещё не оценённому q_m это положительное выражение и затем объявлять R_m>=0 было бы кругом.

## 5. Что попытка не закрыла

Не получена (13), ни эквивалентная односторонняя оценка R_m. В частности, количество O(log²m) координат само не ограничивает наибольшее собственное значение signed prime-компрессии. Упомянутая в старом Q04 положительная метрика уже имела неизвестную signed derivative; её не следует выдавать за новый источник положительности.

Сильнейший контроль: при произвольном растущем m матрицы X_m=diag(-m^alpha,0) и Y_m=0 удовлетворяют 0<=Y_m<=B(L)I, но не дают subpolynomial lower для X_m. Это только ABSTRACT-контроль ошибочного логического перехода, не другой CCM и не опровержение (13).

MARKOV rollback тоже не дал недостающего знака: точный ground-transform требует оценки jump-energy против variance. Замена physical constant-slack на произвольную постоянную ошибку в theta-weighted норме меняет задачу, так как соответствующие веса не равномерно эквивалентны на растущих окнах.

Таким образом, RH не закрыта не по причине её исторического статуса, а по конкретной причине: в этой работе отсутствует доказательство (13). Все остальные результаты выше не подменяют это неравенство.

## 6. Реестр, выбор и стоп-условие

| Утверждение | Scope | Verifier | Граница |
|---|---|---|---|
| Архивный polylog receiver уже существовал | COFINAL_FAMILY | PAPER | Чтение S1--S2; не новое открытие |
| Чётный quarter-window receiver (3) | COFINAL_FAMILY | PAPER | Гипотетический off-line нуль; все late m |
| H¹, contact Gram, low-band arch bound | COFINAL_FAMILY | PAPER | Только точный H_m |
| Uniform multiplier (14), centered budget (16) | ABSTRACT / COFINAL_FAMILY | PAPER | Все N,t; затем точный source-weight |
| Prime-upper (13), lower R_m | COFINAL_FAMILY | CONDITIONAL | Не установлены |
| RH export | COFINAL_FAMILY | CONDITIONAL | Требует (13); не сделан |

Два допустимых представления оставшейся задачи:

1. **Прямая signed prime-компрессия на H_m.** Определить exact coefficient matrix из всех Q(log n), не брать модуль каждой корреляции. Один source-dependent upper envelope для lambda_max с любым subpolynomial бюджетом закрывает receiver. Решающее действие: 5/5; алгебраическая цена: 2/5; новая арифметическая цена пока неизвестна.
2. **Полный centered residual (17).** Все rational atoms и floor-компенсатор сохраняются. Требуется источник-заданное разложение signed remainder с subpolynomial lower; собственный square root предполагаемой PSD-матрицы запрещён как круг. Решающее действие при успехе: 5/5; цена coefficient audit: 3/5; риск — повторение уже известного signed prime-front.

Оценки силы/цены — порядковые исследовательские приоритеты, не вероятности успеха.

DISCRIMINATOR: для каждого заранее выбранного кандидата b_m — certified LOWER envelope для b_m I - compression(P_m,H_m); для опровержения — UPPER envelope того же минимального eigenvalue <0 либо точный Rayleigh-свидетель. Нуль-согласованный результат требует сужения полного enclosure или source-defined факторизации. Конечное прохождение не заменяет квантор всех epsilon и неограниченных m.

**Единственная CODEX DIRECTIVE:** независимо проверить quarter-window receiver §§1--2 и elementary budget §§3--4, сверить его с S1--S3 и записать точный weakest consumer (13). Не запускать новый спектральный scan ради подтверждения тренда, не переписывать глобальный export и не повышать статус после аудита тождеств. Дальнейшая математическая попытка разрешена только с новым signed inequality на (13) или полном (17), а не с ещё одной верхней нормой положительного auxiliary lift.

## 7. Предрегистрация и выполненные проверки

Предсказания записаны в registration.json до исполнения проверок.

P1: phase-locked quartet даёт -16nu cosh² — подтверждено exact SymPy identity и PAPER-расчётом.

P2: два контакта и Gram-margin — exact identity для f=(d²/dx²-1/4)(1+cos x)²; analytic Gram-bound выше. Дополнительные 60-dps значения normalized correlations при L=16,20,32,64: 0.0440680, 0.0394967, 0.0312428, 0.0220947.

P3: (14) — доказано на бумаге; 90 конечных 60-dps controls, maximum ratio к bound 0.178646935. Это не interval-certification.

P4: (16) — PAPER-следствие (14), Parseval и arithmetic weight budget, не численная экстраполяция.

P5: полная output-space норма centered lift совпадает с exact floor identity для N=1,2,5 и настоящего двухконтактного cosine-теста на L=log16. Максимальное абсолютное расхождение <1.56e-61 при 60 dps. Внешняя область интегрирована; точный нулевой pole-moment использован явно.

P6: положительный auxiliary budget не доказывает source lower — exact ABSTRACT plant проверен.

Первый технический запуск был прерван малым timeout; завершённый запуск использует аналитическую cosine-корреляцию вместо вложенной квадратуры. Ни один результат прерванного запуска не засчитан как проверка.

## 8. Dependency epistemics и closeout

DOWNSTREAM_CONSUMER: безусловная RH через literal off-critical adverse receiver.
ACTUAL_CONSUMER_REQUIREMENT: (13), subpolynomial one-sided prime upper на source-defined H_m.
ORIGINAL_REQUESTED_OBJECT: полное закрытие RH, допускается rollback стратегии.
ORIGINAL_OBJECT_IS: RH остаётся целью; constant complement floor NOT_NECESSARY для данного receiver.
KNOWN_WEAKER_INTERFACES: любой фиксированный polylog lower на H_m; либо (10); эквивалентно (13) с arch-budget (12).
FAILURE_TYPE: NO_DERIVATION of (13).
EPISTEMIC_STATUS: RESEARCH_DEBT, не математическая невозможность.
REOPEN_TRIGGER: новый независимый signed arithmetic bound для (13)/(17), с настоящим original-source return.
NOVELTY_AXIS: even quarter-window reproof и uniform centered-Gram estimate; старый polylog receiver не присваивается как новый.

Что стало меньше: не обязательны все J_m-perp, постоянный остаток и capacity lower; остаётся меньший исходный тест-класс и subpolynomial цена. Это ослабление уже существовало в архиве и теперь возвращено в текущую постановку.

Что доказано дополнительно: bounded centered lift на этом классе с явным B(L)=O(L²), и полный чётный receiver без сильного double-exponential cutoff supplier.

Что не делать снова: объявлять controlled auxiliary norm контролем signed source derivative; требовать фиксированный constant floor, когда потребителю достаточно (10); игнорировать endpoint при использовании Fourier-derivative норм.

Memory entry: POLYLOG_EVEN_REENTRY / REPRESENTATION_SHIFT / SOURCE_SIGN_STILL_OPEN / next decisive object is the signed prime matrix, not another positive Gram norm.

Независимый аудит этого нового документа не выполнен. Lean и Arb не запускались. Запись Markdown в Git доказывает доставку, не его математическую правильность. Исходные артефакты, принятые вердикты и route-state не изменяются.

## 9. Доставка и воспроизведение

REPOSITORY_WRITTEN: false. В доступном в этой сессии GitHub-коннекторе обнаружены операции чтения, но операции create/update не предоставлены. Никакого commit SHA для этой работы не выдумывается. Наблюдавшийся HEAD inbox: 3ce4968d7ae23390f65e6c62daa6c3cf2cf6960d; patch добавляет новые файлы, не редактирует этот HEAD и не меняет route-state.

Пакет содержит этот Markdown, registration.json, checks.py и результаты законченного запуска. Для воспроизведения из каталога пакета:

```bash
uv run --with sympy --with mpmath python rh_polylog_reentry/checks.py
```

checks.py — конечные точные и высокоточные контроли нормировок, не алгоритм доказательства RH. Сам аналитический вывод находится в §§2--4.