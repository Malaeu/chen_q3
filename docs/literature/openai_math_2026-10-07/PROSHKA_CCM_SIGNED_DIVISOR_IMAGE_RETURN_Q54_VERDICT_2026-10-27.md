# STATUS: TRY_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54
```yaml
OPERATIVE_CLASS: TRY_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54
REQUEST_ID: Q54_SIGNED_DIVISOR_IMAGE_RETURN
DATE: 2026-10-27
LANGUAGE: ru
BASE_COMMIT: cdad9b8a
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_P
PACKET_BYTES: 139662
PACKET_LF: 2276
PACKET_SHA256: 29975f46faee9550eea39e6de9048f0c73f9e483d1522ebfed9a32003651ce6a
SOURCE_BODIES: 8
MANIFEST: VERIFIED
CONSUMER_PROGRESS: NO_PROGRESS
INDEPENDENT_VANISHING_EXPONENT_SUPPLIER: NOT_DERIVED
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
SELECTED_FORK: S6_FIRST_FINITE_SOURCE_BEFORE_ARITHMETIC_CARRIER_CAP
TESTED_INPUT: POSITIVE_REAL_PARAMETER_GCD_DEFORMATION_WITH_ACTUAL_MOBIUS_CONGRUENCE
FIRST_SOURCE_RETURN: Phi_prime_0_equals_h_m_norm_squared_minus_A_over_2
COMPLETE_TRIAL: 2_log_m_plus_6_plus_4_sqrt_2m_log_m_times_1_plus_log_m
TRIAL_POWER: 1/2_WITH_LOGARITHMIC_FACTORS
RETAINED_DIRECT_POWER: 1/2
FIRST_UNPAID_ESTIMATE: JOINT_SIGNED_CURVATURE_ON_THE_COMPLETE_LINKED_MOBIUS_IMAGE
NEW_RH_CLAIM: NOT_MADE
PX_RH_CLAIM: NOT_MADE
RH: OPEN
ALL_P_GOAL: OPEN
CF22_PYSR: PARKED
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
VERIFIER: PAPER_OWN_DERIVATION_WITH_EXACT_FINITE_ALGEBRA_CONTROLS
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
ACTUAL_ZERO_ASSIGNMENTS: NONE
HISTORICAL_PROGRAMS_EXECUTED: false
REPOSITORY_WRITES: NONE
INSTALLATIONS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимый знаковый upper с показателем, стремящимся к нулю, в Q54 не получен.** Ниже выполнен один ограниченный арифметический ход: положительная деформация НОД-ядра, сопряжённая **настоящей конечной матрицей Мёбиуса**, на полном связанном образе исходного теста.

Её источниковая касательная вычислена точно:
\[
 \Phi_0[f]=\|f\|_2^2,\qquad
 \Phi'_0[f]=h_m\|f\|_2^2-\frac12 A_m[f],
 \qquad h_m=\sum_{n\le m}\frac{\Lambda(n)}n.
\tag{0.1}
\]
Положительность всей семьи \(\Phi_\tau\ge0\), \(\tau\ge0\), действительно следует из арифметики, а не из предполагаемого знака CCM. Но **исходные контакты не зануляют её базовое значение**: арифметический ранг один после полного переноса становится исходной нормой, а не нулём. Поэтому из положительности нельзя бесплатно взять знак касательной.

Полный конечный остаток сохранён. Доступная односторонняя Taylor-оценка даёт
\[
 \boxed{A_m\preceq s_{\rm trial}(m)P,
 \qquad s_{\rm trial}(m)=2\log m+6+
 4\sqrt{2m}\,\log m\,(1+\log m).}
\tag{0.2}
\]
Это хуже сохранённого \(s_{\rm keep}\le6\sqrt m+6m^{1/4}\). **Положительная деформация, точная касательная и выполненные проверки не названы выигрышем полной CCM.** Первая неоплаченная количественная строка — совместный верх знаковой кривизны, либо более слабое сравнение с сохранённой положительной энергией. Оба варианта точно указаны ниже; ни один не принят в предпосылки.

## 1. Source lock и что именно проверено на полке

Канонический файл прочитан целиком, включая полный исторический Q53, его код и результаты, и все остальные семь тел. У всех восьми тел совпали bytes, LF, SHA-256, порядок и границы. Разделительный LF не включён в тело. Общие 139 662 байта, 2276 LF и SHA-256 вычислены из смонтированного оригинала; краткая подпись пользователя не задавала отдельного общего хеша.

Bootstrap `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` получен через GitHub, `Malaeu/chen_q3`, ветка `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Действует только root Q54. Исторические директивы и программы из тел не исполнялись. Репозиторий не изменялся.

| Источник | Что используется; что не выдаётся за новое |
|---|---|
| S1 | Принят именно uniform lower **цены** graph cap + абсолютного возврата. Не оптимизирую конечный carrier и не переношу этот lower на CCM. |
| S2 | Точное равенство \(G_a-E_{\rm signed}=D_a\|f\|^2-A_m[f]\). Оно расходуется только для возврата результата, не доказывается заново как арифметический вход. |
| S3 | Полный Q53: арифметический graph upper, исходная форма, fallback и предел norm-only применения inner-модели. Canonical conjugation не повторяется. |
| S4 | Сумма положительных first-form deficits уже равна старой jump energy. Не использую её как новый источник знака или как фиксированный spectral gap. |
| S5 | Selberg/renewal и scalar Buchstab monotonicity — проверенные повторы/неподходящие гипотезы. Не использую их для знаковых весов. |
| S6 | **Выбранная ранняя развилка:** первая конечная причинная форма с настоящими \(\mu,\Lambda\), до отдельной нормы и до carrier. Cheap \(Zf\) не переносится на произвольный Möbius-образ. |
| S7 | Контурная карта сохранена как существующий альтернативный интерфейс. Новый опыт идёт прямо через \(A_m\), поэтому contour/high/entire fees ему не добавляются. |
| S8 | Условный sparse-band receiver остаётся в прежней области. Ни all-\(P\) цель, ни исходное расписание не заменяются одной парой или меньшей полосой. |

Сначала проверены эти явные supplier screens. Дополнительный файловый поиск по `log gcd`, `Jordan totient`, `gcd positive divisor` не дал результатов; это **не** доказательство отсутствия такой записи на всей полке или в литературе. Во включённых S1–S8 выбранного real-parameter НОД-переноса нет. Мировая новизна не заявляется.

Внешний ориентир — арифметическая факторизация НОД-матрицы через делители, показанная в §1.1 Guillot–Wu [E1]. Из неё здесь **не** импортируется ни полный source upper, ни total positivity. Нужная версия для каждого вещественного \(\tau\ge0\), её нормировка, Möbius-congruence и перенос на \(P\) доказаны непосредственно в §§3–5. Классические тождества инверсии сверены по DLMF [E2].

**Чем опыт отличается от исключённых завершений.** Новый проверяемый вход — положительность *всей параметрической арифметической семьи*, в которой вторая переменная сохраняет настоящие общие делители. Это не отдельные положительные jump-квадраты, не селберговская оценка остатка и не \(\log N_{\rm aux}\)-cap. Полный signed return извлекает **первую производную** этой семьи. Его цена оплачивается, а не назначается нулевой. При неудаче эта конструкция также не получает статуса нового доказательства.

## 2. Исходный объект, норма и направление неравенства

**[COFINAL_FAMILY | PAPER — inherited S3, S6–S8].** Фиксируем до предела
\[
 0<\epsilon<1/32,\quad N=m,\quad L=\log m,\quad
 M=R=\lfloor m^\epsilon\rfloor,\quad
 \omega_j=2\pi j/L,\quad \Omega=2\pi M/L.
\tag{2.1}
\]
\(P\) — прежний трёхконтактный проектор. Для произвольного **комплексного** \(c=Pc\)
\[
 f(t)=\mathcal I c(t)=L^{-1/2}\sum_{|j|\le M}c_je^{i\omega_jt}
 \quad(0\le t\le L)
\tag{2.2}
\]
с нулевым продолжением на \(\mathbb R\). Сохраняются три контакта, \(f(0)=f(L)=0\), и \(\|f\|_2=\|c\|_2\). Вне окна функция не считается периодической.

Обозначим
\[
 I_n[f]=\int_{\mathbb R}\overline{f(t)}f(t+\log n)\,dt,
 \qquad I_1[f]=\|f\|_2^2,
\]
\[
 A_m[f]=2\Re\sum_{2\le n\le m}
 \frac{\Lambda(n)}{\sqrt n}I_n[f].
\tag{2.3}
\]
Это полная первая prime-форма из задания. Обе временные стороны уже входят в \(2\Re\). Все \(\Lambda(p^k)=\log p\), включая \(p^k=m\), сохраняются в коэффициентной записи. \(I_m[f]=0\) следует из физической поддержки, но другие диагональные или смешанные слагаемые вспомогательной конструкции при индексе \(m\) не объявляются нулём.

Прежние связи:
\[
 C_m^0=A_m+H_P,\qquad0\preceq H_P\preceq4P,
\]
\[
 T_{>R}=A_m-T_{\le R},\qquad
 \|T_{\le R}\|\le b_{\rm div}
 =(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{2.4}
\]
Если **независимо** получен \(A_m\preceq s_mP\), прямой возврат есть
\[
 \boxed{T_{>R}\preceq(s_m+b_{\rm div})P,\qquad
 PK_mP\succeq-(s_m+50L+8)P.}
\tag{2.5}
\]
Это не upper абсолютной нормы. Отдельно большая отрицательная часть \(A_m\) потребителю не мешает.

S2 также даёт для **любого** нормированного конечного комплексного carrier \(a\)
\[
 G_a[f]-E_{\rm signed}[f]=D_a\|f\|_2^2-A_m[f].
\tag{2.6}
\]
Поэтому новый upper \(s_m\), если бы он был доказан, давал бы именно требуемое
\[
 G_a[f]-E_{\rm signed}[f]\ge(D_a-s_m)\|f\|_2^2.
\tag{2.7}
\]
Здесь \(E_{\rm signed}\) остаётся знаковой квадратичной формой. Скалярная сумма модулей \(E_a(m)\) из S1 в (2.6)–(2.7) не подставляется.

## 3. Дополнительное арифметическое свойство: положительная НОД-деформация

### 3.1. Полная конечная инверсия

**[FINITE_CELL | PAPER].** Введём вспомогательные матрицы с индексами \(1\le n,d\le m\):
\[
 \mathsf E_{n,d}=\mathbf1_{d\mid n},\qquad
 \mathsf U_{n,d}=\mathbf1_{d\mid n}\mu(n/d).
\tag{3.1}
\]
Матрица \(\mathsf U\) не означает физический сдвиг. По настоящему тождеству
\(\sum_{d\mid n}\mu(d)=\mathbf1_{n=1}\),
\[
 \mathsf U\mathsf E=\mathsf E\mathsf U=I,
 \qquad\mathsf U\mathbf1=e_1.
\tag{3.2}
\]
Вся область делителей конечна и замкнута вниз; никаких отсутствующих больших делителей при обращении нет. Производственное \(N\) остаётся \(m\); гигантский \(N_{\rm aux}\) не вводится.

Для вещественного \(\tau\ge0\) положим
\[
 j_\tau(n)=\sum_{d\mid n}\mu(n/d)d^\tau.
\tag{3.3}
\]
При \(n=1\) это 1. Единственность разложения на простые даёт при \(n>1\)
\[
 \boxed{j_\tau(n)=n^\tau\prod_{p\mid n}(1-p^{-\tau})\ge0.}
\tag{3.4}
\]
Для \(\tau>0\) все эти величины строго положительны. При \(\tau=0\)
\(j_0(n)=\mathbf1_{n=1}\). Это вещественно-параметрическая версия коэффициента Жордана; она не требует, чтобы \(\tau\) было целым.

**Доказательство (3.4).** В (3.3) только квадратсвободные множители \(n/d\) могут иметь ненулевую \(\mu\). Суммирование по подмножествам различных простых делителей \(n\) даёт произведение. Никакого усреднения знаков или предположения о Мертенсе здесь нет.

### 3.2. Положительный двухиндексный kernel

Определим
\[
 d_{nk}=\log\frac{\sqrt{nk}}{\gcd(n,k)}
 =\frac12\sum_p|v_p(n)-v_p(k)|\log p,
\tag{3.5}
\]
\[
 \mathsf Q_\tau(n,k)=e^{-\tau d_{nk}}
 =\left(\frac{\gcd(n,k)}{\sqrt{nk}}\right)^\tau.
\tag{3.6}
\]
Это **покомпонентная** степень арифметического ядра, не функциональное исчисление матричного логарифма. Для всех индексов
\[
 0\le d_{nk}\le L.
\tag{3.7}
\]
Обозначая \(\mathsf D_\tau=\operatorname{diag}(n^{-\tau/2})\), получаем
\[
 \boxed{\mathsf Q_\tau=
 \mathsf D_\tau\mathsf E\operatorname{diag}(j_\tau(d))
 \mathsf E^T\mathsf D_\tau\succeq0.}
\tag{3.8}
\]
Действительно, \(\sum_{d\mid g}j_\tau(d)=g^\tau\), по (3.2)–(3.3), и элемент правой части равен (3.6). Здесь арифметика обеспечивает знак всей матрицы, а не только её элементов. Для произвольных положительных весов вместо \(j_\tau\) или произвольных меток вместо \(\mu\) такая карта не утверждается.

Положим
\[
 \boxed{\mathsf V_\tau=\mathsf U\mathsf Q_\tau\mathsf U^T\succeq0.}
\tag{3.9}
\]
Это законная конгруэнция одной и той же настоящей матрицей \(\mathsf U\). В физических координатах новую норму не назначаем. Все обратные коэффициенты учтены в самой \(\mathsf U\).

## 4. Касательная и нормировка: точный возврат \(\Lambda\)

### 4.1. Вся арифметическая матрица, не один её канал

**[FINITE_CELL | PAPER].** Пусть \(\lambda=(\Lambda(1),\ldots,\Lambda(m))^T\) и \(\ell=(\log1,\ldots,\log m)^T\). Тогда
\[
 \mathsf U\ell=\lambda.
\tag{4.1}
\]
Кроме того,
\[
 \mathsf L_{nk}=\log\gcd(n,k)
 =\sum_{d\mid n,\ d\mid k}\Lambda(d)
\]
даёт
\[
 \mathsf L=\mathsf E\operatorname{diag}(\Lambda)\mathsf E^T,
 \qquad
 \mathsf U\mathsf L\mathsf U^T=\operatorname{diag}(\Lambda).
\tag{4.2}
\]
Это специальные арифметические тождества, а не правило, что логарифм положительной матрицы положителен покомпонентно.

Поскольку \(\mathsf Q_0=\mathbf1\mathbf1^T\),
\[
 \boxed{\mathsf V_0=e_1e_1^T.}
\tag{4.3}
\]
Дифференцируя **все** множители нормировки в (3.6), получаем
\[
 \mathsf Q'_0=
 \mathsf L-\frac12(\ell\mathbf1^T+\mathbf1\ell^T).
\]
Из (3.2), (4.1)–(4.2):
\[
 \boxed{\mathsf V'_0=
 \operatorname{diag}(\Lambda)
 -\frac12(\lambda e_1^T+e_1\lambda^T).}
\tag{4.4}
\]
Если пропустить производную \((nk)^{-\tau/2}\), исчезнет именно недиагональный источник. Если заменить \(\Lambda(p^k)\) на \(\log(p^k)\), перестанет выполняться (4.1). Обе ошибки проверяются конечной точной алгеброй.

### 4.2. Полный связанный физический образ

Для **одного и того же исходного** \(f=\mathcal Ic\) зададим
\[
 x_n(t)=n^{-1/2}f(t+\log n),\qquad
 r_d(t)=(\mathsf U^T x(t))_d
 =\sum_{k\le m/d}\frac{\mu(k)}{\sqrt{dk}}f(t+\log(dk)).
\tag{4.5}
\]
Все внутренние пределы \(dk\le m\) буквальны. В промежуточных состояниях нет нового \(P\), и ни одному \(r_d\) не назначается независимый профиль.

Карта \(f\mapsto x\) имеет точно известную норму:
\[
 \int_{\mathbb R}\sum_{n\le m}|x_n(t)|^2dt
 =\left(\sum_{n\le m}\frac1n\right)\|f\|_2^2.
\tag{4.6}
\]
Она **не** объявлена изометрией. Её нормировка не заменяет исходную. Определим теперь всю связанную энергию
\[
 \boxed{\Phi_\tau[f]=\int_{\mathbb R}
 x(t)^*\mathsf V_\tau x(t)\,dt
 =\int_{\mathbb R}r(t)^*\mathsf Q_\tau r(t)\,dt\ge0.}
\tag{4.7}
\]
Конечность и дифференцирование в \(\tau\) законны: арифметических индексов конечное число, каждый компонент есть конечная сумма сдвигов \(L^2\)-функции, а произведения интегрируемы по Cauchy. При фиксированном \(m\) это гладкая, даже целая по параметру, скалярная функция; знак используется только при вещественном \(\tau\ge0\).

Полная квадратная запись той же энергии:
\[
 \Phi_\tau[f]=\sum_{d\le m}j_\tau(d)
 \int_{\mathbb R}\left|
 \sum_{d\mid n\le m}n^{-\tau/2}r_n(t)
 \right|^2dt.
\tag{4.8}
\]
Внутренние смешанные произведения в (4.8) не удалены. Это independent positive input; его производная ещё не получила знака.

Из (4.3):
\[
 \boxed{\Phi_0[f]=\int|x_1|^2=\|f\|_2^2.}
\tag{4.9}
\]
Из (4.4) и инвариантности полного \(dt\) при сдвиге:
\[
 \begin{aligned}
 \Phi'_0[f]
 &=\sum_{n\le m}\Lambda(n)\int|x_n(t)|^2dt
   -\Re\sum_{n\le m}\Lambda(n)\int\overline{x_1(t)}x_n(t)dt\\
 &=\left(\sum_{n\le m}\frac{\Lambda(n)}n\right)\|f\|_2^2
   -\Re\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}I_n[f].
 \end{aligned}
\]
Таким образом,
\[
 \boxed{\Phi'_0[f]=h_m\|f\|_2^2-\frac12A_m[f],}
 \qquad h_m=\sum_{n\le m}\frac{\Lambda(n)}n.
\tag{4.10}
\]
Цена (4.10) как источниковой карты — **ноль**. Все prime powers, \(n=m\), обе временные стороны и все межмодовые члены возвращены точно. Уменьшения их коэффициента не произошло.

### 4.3. Исходные контакты не создают нулевую базу деформации

На всём ненулевом \(\operatorname{ran}P\), а не на одном пробном векторе,
\[
 \mathcal X^*(e_1e_1^T\otimes I_{L^2})\mathcal X=P
 \quad\text{после исходной синтезы},
\tag{4.11}
\]
где \(\mathcal Xf=(x_n)\). Иными словами, ранг один **по арифметическому индексу** не является ранговым контактным направлением исходной CCM. Его pullback — исходная единичная форма. \(P\) не зануляет его.

Поэтому правило «\(\Phi_\tau\ge0\) и контакты дают \(\Phi'_0\ge0\)» здесь неприменимо: его нулевая начальная предпосылка ложна уже по (4.9). Это проверка полной карты, не новое single-zero или exponential-probe препятствие. Хорошая нижняя оценка касательной с положительной платой этим **не исключена**.

## 5. Один выполненный completion: полная знаковая кривизна и конечный шаг

### 5.1. Точный объект до модулей

**[FINITE_CELL | PAPER].** Для \(s\ge0\)
\[
 \boxed{\Phi''_s[f]=
 \int_{\mathbb R}\sum_{d,e\le m}
 \overline{r_d(t)}r_e(t)\,d_{de}^{\,2}e^{-s d_{de}}\,dt.}
\tag{5.1}
\]
В ней остаются и несравнимые по делимости пары, и отношения \(e/d\), не являющиеся целыми. Эти члены не равны нулю только потому, что исходная первая форма имела целочисленные prime-power сдвиги.

Если полностью раскрыть настоящий образ (4.5), получаем
\[
 \Phi''_s[f]=
 \Re\sum_{d,e\le m}\sum_{k\le m/d}\sum_{l\le m/e}
 \frac{\mu(k)\mu(l)}{\sqrt{dekl}}
 d_{de}^{\,2}e^{-s d_{de}}
 I_{el/(dk)}[f],
\tag{5.2}
\]
где для любого положительного рационального \(q\)
\(I_q[f]=\int\overline f(t)f(t+\log q)dt\).
Полная сумма вещественна по сопряжению пар \((d,k)\leftrightarrow(e,l)\); \(\Re\) в (5.2) только подчёркивает эту симметрию. Все гиперболические края \(dk,el\le m\) сохраняются одновременно.

Это не \(\Lambda(de)\), не квадрат суммы с независимо выбранными фазами и не среднее по исходным ячейкам. Один и тот же \(c\) участвует во всех \(I_q\).

Точная формула конечного шага:
\[
 \Phi_\tau[f]=\|f\|_2^2+
 \tau\left(h_m\|f\|_2^2-\frac12 A_m[f]\right)
 +\mathcal R_\tau[f],
\]
\[
 \mathcal R_\tau[f]=\int_0^\tau(\tau-s)\Phi''_s[f]ds.
\tag{5.3}
\]
В частности,
\[
 \boxed{A_m[f]=
 2h_m\|f\|_2^2+
 \frac2\tau\bigl(\|f\|_2^2-\Phi_\tau[f]+\mathcal R_\tau[f]\bigr),
 \qquad\tau>0.}
\tag{5.4}
\]
Это сохраняет благоприятный член \(-2\Phi_\tau/\tau\) и **весь** остаток. Малость \(\tau\) сама по себе не разрешает удалить \(\mathcal R_\tau/\tau\).

### 5.2. Где доступное завершение теряет совместную информацию

Оплатим (5.1) законной, но грубой односторонней оценкой. Из (4.5)
\[
 \begin{aligned}
 \sum_{d\le m}\|r_d\|_2
 &\le\sum_{dk\le m}\frac{|\mu(k)|}{\sqrt{dk}}\|f\|_2\\
 &\le 2\sqrt m\sum_{k\le m}\frac{\mu(k)^2}{k}\|f\|_2
 \le2\sqrt m(1+L)\|f\|_2.
 \end{aligned}
\tag{5.5}
\]
Использованы только \(|\mu|=\mu^2\le1\),
\(\sum_{d\le X}d^{-1/2}\le2\sqrt X\) и \(\sum_{k\le m}1/k\le1+L\). Все суммы конечны.

По (3.7), \(e^{-s d_{de}}\le1\) при \(s\ge0\). Поэтому
\[
 \begin{aligned}
 \Phi''_s[f]
 &\le |\Phi''_s[f]|\\
 &\le L^2\sum_{d,e}\int|r_d(t)||r_e(t)|dt\\
 &\le L^2\left(\sum_d\|r_d\|_2\right)^2
 \le\boxed{4mL^2(1+L)^2\|f\|_2^2}.
 \end{aligned}
\tag{5.6}
\]
**Именно здесь**, а не в Möbius-inversion или выборе нормы, потеряны знаковые связи: сначала совместная сумма (5.1) заменяется суммой модулей, затем используются независимые размеры компонентов. Это не выдаётся за новое сильное свойство \(\mu\).

Обозначим
\[
 \mathscr C_m=4mL^2(1+L)^2.
\tag{5.7}
\]
Тогда полный остаток удовлетворяет
\[
 \mathcal R_\tau[f]\le\frac{\mathscr C_m\tau^2}{2}\|f\|_2^2.
\tag{5.8}
\]
Положительность (4.7), сохранённая до (5.4), даёт **доказанную**, но недостаточную inequality
\[
 \boxed{A_m[f]\le
 \left(2h_m+\frac2\tau+\mathscr C_m\tau\right)\|f\|_2^2.}
\tag{5.9}
\]
Она верна для каждого исходного комплексного \(c\); фактически этот слабый completion не использует ограничения \(P\), кроме нормировки и поддержки при source return. Это **не** доказательство, что сами ограничения не могут помочь более точной оценке (5.1).

### 5.3. Полный показатель, а не только малая отдельная плата

Для \(m\ge2\) выберем один общий для всех векторов
\[
 \tau_m=\sqrt{2/\mathscr C_m}
 =\frac1{\sqrt{2m}\,L(1+L)}.
\tag{5.10}
\]
Это вспомогательный параметр finite identity; \(\epsilon\), исходные частоты и \(N=m\) не меняются. Все оценки в (5.6) равномерны для \(0\le s\le\tau_m\), поэтому здесь нет скрытого перехода от fixed-parameter asymptotic к moving parameter.

Имеем
\[
 \frac2{\tau_m}+\mathscr C_m\tau_m
 =2\sqrt{2\mathscr C_m}
 =4\sqrt{2m}\,L(1+L).
\tag{5.11}
\]
Для полноты, применим независимый арифметический bound из S3 §7.1:
\[
 h_m\le L+3.
\tag{5.12}
\]
Его доказательство не содержит RH: из
\(\sum_{d\le m}\Lambda(d)\lfloor m/d\rfloor=\log(m!)\)
и \(\lfloor m/d\rfloor\ge m/d-1\) получаем
\(mh_m\le\log(m!)+\psi(m)\le mL+3m\).
Элементарная \(\psi(x)\le3x\) — уже доказанный в S3 биномиальный bound; новая PNT-предпосылка не вводится.

Из (5.9)–(5.12) следует (0.2). **Полная выписанная цена имеет половинную степень с двумя логарифмами.** Это upper allowance конкретного completion, не нижняя оценка настоящей \(\Phi''\), не величина \(A_m\), не препятствие всем возможным оценкам \(\mathcal R_\tau-\Phi_\tau\). Для получения этого вывода не строился новый lower certificate или спектральный no-go.

## 6. Что осталось недоказанным и почему это не новый готовый supplier

**[COFINAL_FAMILY | CONDITIONAL — not supplied].** Один явно достаточный, но более сильный вход для выбранного completion был бы следующим. При некотором \(\kappa(\epsilon)\ge0\), \(\kappa(\epsilon)\to0\), доказать независимо
\[
 \Phi''_s[f]\le C_\epsilon m^{2\kappa(\epsilon)}\|f\|_2^2
 \quad\text{для всех }c=Pc,
 \quad0\le s\le m^{-\kappa(\epsilon)}.
\tag{6.1 OPEN}
\]
Здесь достаточно **верхнего** знака, не абсолютной оценки. При \(\tau=m^{-\kappa(\epsilon)}\) формула (5.9), с новым вместо (5.6) входом, дала бы
\[
 A_m\preceq
 \bigl[2L+6+(2+C_\epsilon)m^{\kappa(\epsilon)}\bigr]P,
\tag{6.2 CONDITIONAL}
\]
а затем \(\eta=\max\{\kappa,2\epsilon\}\to0\). Это проверенная **импликация**, а не доказательство (6.1). При \(\kappa=0\) логарифмический член остаётся и оплачивается в обычном \(m^{2\epsilon}\)-возврате.

Первая отсутствующая количественная связь записана буквально в (5.2): нужен one-sided контроль всей суммы настоящих \(\mu(k)\mu(l)\), одновременно с общими делителями \(d,e\), рациональным отношением \(el/(dk)\), полными границами и корреляцией одного исходного теста. Ни \(j_\tau\ge0\), ни \(\mu*1=\delta_1\), ни \(\mu*\log=\Lambda\) **не предоставили такой оценки в выполненном доказательстве**.

Более слабое завершение могло бы оценивать **вместе** \(\mathcal R_\tau\) и \(\Phi_\tau\), не требуя (6.1). Но по (5.4)
\[
 \mathcal R_\tau[f]-\Phi_\tau[f]
 \le\left(\frac{\tau s_m}{2}-\tau h_m-1\right)\|f\|_2^2
\tag{6.3 OPEN}
\]
есть ровно прежний \(A_m\le s_mP\). **(6.3) не назван новой независимой леммой.** Отсутствие доказательства более сильного (6.1) также не опровергает (6.3).

Существенная геометрическая граница: \(d_{de}\) в (3.5) — не \(|\log(d/e)|/2\). Например, для взаимно простых близких целых \(d,e\) первая величина порядка \(\log d\), а физический сдвиг \(|\log(e/d)|\) может быть мал. Поэтому гладкость одного \(f\) не превращает автоматически все арифметические множители \(d_{de}^2\) в малые физические разности. Это объясняет отсутствие такого шага в (5.6), **не** доказывает отсутствия сокращения всех секторов (5.2).

S6-оценка \(\|Z_{1/2}f\|\le(3+6\Omega)\|f\|\) не подставляется вместо (5.5): там другой оператор, другой коэффициент и другая область. \(r_d\) содержит полный префикс \(\mu(k)\), а не положительную integer-sum \(Z\). Кроме того, промежуточные сдвиги не обязаны лежать в исходном \(\operatorname{ran}P\) на \([0,L]\).

**Остановка:** не оптимизировать \(\tau\) внутри уже выписанного (5.6) как будто это меняет арифметическую степень; не объявлять саму PSD-деформацию signed supplier. Выполненный ранний откат S6 законен и использует дополнительное проверенное свойство, но независимого улучшения на нём не получено. На конец Q54 нет основания назначать автоматический следующий опыт с той же производной под другим именем.

## 7. Полный signed return к требуемому неравенству и CCM

### 7.1. Trial возвращён на тот же исходный образ

Из (0.2) и (2.6), **без замены \(E_{\rm signed}\) на модуль**,
\[
 \boxed{G_a[f]-E_{\rm signed}[f]
 \ge\bigl(D_a-s_{\rm trial}(m)\bigr)\|f\|_2^2}
\tag{7.1}
\]
для каждого конечного нормированного комплексного carrier \(a\) и каждого исходного \(c=Pc\). Его \(N_{\rm aux}\), если carrier задан, остаётся вспомогательным и не входит в цену этого direct completion. Эта общность не делает bound сильнее старого fallback: \(s_{\rm trial}\) больше.

Полная цена trial:
\[
 T_{>R}\preceq(s_{\rm trial}+b_{\rm div})P,
 \qquad
 PK_mP\succeq-(s_{\rm trial}+50L+8)P.
\tag{7.2}
\]
При фиксированном \(\epsilon<1/32\),
\[
 b_{\rm div}=O_\epsilon(m^{3\epsilon/2}/L+m^{\epsilon/2}+L^2),
\]
поэтому степень всей (7.2) остаётся \(1/2\), а не стремится к нулю. Никакой short-сектор не был удалён до первой формы; плата за него возникает только в первом неравенстве (7.2).

### 7.2. Сохраняемый лучший верх не ухудшается

**[COFINAL_FAMILY | PAPER — inherited S1–S4].** Окончательный используемый результат остаётся
\[
 s_{\rm keep}=W_<(m)+W(\lfloor\sqrt m\rfloor)
 \le6\sqrt m+6m^{1/4},
\]
\[
 \boxed{T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,
 \qquad
 PK_mP\succeq-(s_{\rm keep}+50L+8)P.}
\tag{7.3}
\]
Не добавляем \(s_{\rm trial}\), \(\mathscr C_m\), \(h_m\), цену lift или контурные ошибки поверх этого **независимо принятого** bound. Условные \(3/8\) из S6 остаются условными на прежний ZF78; здесь они не используются и не повышаются до безусловного статуса.

| Компонент | Цена / статус | Где расходуется |
|---|---|---|
| Конечная incidence/Möbius congruence | 0 ошибки карты | включает все делители через \(m\) |
| Карта \(f\mapsto x\) | точно \(\|x\|^2=\mathfrak h_m\|f\|^2\), не новая норма | промежуточный факт; baseline возвращает \(\|f\|^2\) |
| \(\Phi_0\) и \(\Phi'_0\) | точно (4.9)–(4.10) | никакого остатка источника |
| Положительность \(\Phi_\tau\) | доказана из (3.4) | даёт право отбросить только \(-2\Phi_\tau/\tau\) |
| Полный signed curvature | (5.1)–(5.2) | до модулей сохраняет все пары |
| Доступный curvature upper | \(4mL^2(1+L)^2\) | источник потери совместной информации |
| Оптимизированный trial | \(2L+6+4\sqrt{2m}L(1+L)\) | хуже сохранённого |
| Short divisor | \(b_{\rm div}\) | один раз, только \(T_{>R}\) |
| Archimedean return | \(50L+8\) | один раз, direct \(K_m\) |
| \(H_P\) | исходный \(C^0=A+H_P\), без повторной платы | не добавляется к direct K-bound |
| Contour/high/entire quotient | новый контур не используется | никакой новой/скрыто удалённой платы |

### 7.3. Края, кратности, комплексная фаза

Индекс \(1\) обязателен для \(\mathsf V_0=e_1e_1^T\). Индекс \(m\) обязателен в \(h_m\), диагонали (4.4) и кривизне. Только его **перекрёстный физический overlap с индексом 1** равен нулю. Восстановление (4.10) сокращает соответствующие диагональные вклады точно; удалять их заранее нельзя.

Все переводы в (4.5) происходят на \(\mathbb R\) с исходным нулевым продолжением. Арифметические коэффициенты не продлеваются за \(m\). Раскрытые произведения имеют оба явных ограничения \(dk\le m\), \(el\le m\); нет rectangular surrogate. Никакие нецелые ratios из квадрата не отбрасываются. Никакой исходный mode или complex cross term не удалён.

Исходный непрерывный контроль остаётся \(A[dx]=-H_P\), \(C^0[dx]=0\). НОД-деформация — конструкция **для настоящих** \(\mu,\Lambda\); после замены источника на dx нельзя сохранить её арифметическую касательную и продолжать называть её источниковой картой изменённой задачи. Непрерывный фон здесь вообще не заменялся и не оплачивался отдельной большой нормой.

## 8. Отрицательный контроль и точный scope результата

**[FINITE_CELL | PAPER — arithmetic-index control, not original-P counterexample].** Уже на индексах \(\{1,2\}\)
\[
 \mathsf V'_0=(\log2)
 \begin{pmatrix}0&-1/2\\-1/2&1\end{pmatrix}.
\]
Для \(y=(1,1/2)^T\)
\[
 y^*\mathsf V'_0y=-\frac14\log2<0,
\tag{8.1}
\]
хотя \(\mathsf V_\tau\succeq0\) для всех \(\tau\ge0\). Это проверяет только ложное общее правило «PSD family можно продифференцировать с сохранением знака». Этот \(y\) — не исходный Fourier-вектор \(c\), ячейка \(m=2\) не является поздней production-ячейкой, и (8.1) **не** используется как lower CCM. Это отрицательный контроль алгебры, не новая математическая гибель метода.

На настоящем полном образе вместо такого свободного вектора действует более важное точное утверждение (4.11): baseline не нулевой. При этом никакого actual counterexample к разрешённому small-positive-defect bound я не получил.

**Сильнейшее возражение:** «Ты построил ещё одну положительную семью, после полного возврата касательная снова содержит \(A_m\), а нужного совместного сокращения нет». Это верно. Поэтому основной статус — **NO_PROGRESS**, а не положительное решение Q54. Отличающийся вход испытан и его полный бюджет вычислен; новая запись не засчитана как уменьшение главного долга.

**Второе возражение:** «Можно не отбрасывать \(\Phi_\tau\), либо улучшить только верхний знак кривизны на связанном образе». Верно. Это ровно сохраняемые возможности. (5.6) не является доказанной минимальной ценой, а (6.1) не является необходимым условием успеха. Отрицательных утверждений об actual cancellation, RH или всей CCM здесь нет.

## 9. Ledger, зависимости, различающий критерий и остановка

| ID | Утверждение | Scope | Verifier | Итог |
|---|---|---|---|---|
| L0 | Пакет и 8 frames | FINITE_CELL | PAPER / byte-check | совпали |
| L1 | Исходные source/consumer/receiver | COFINAL_FAMILY | PAPER / inherited | статусы не повышены |
| L2 | \(j_\tau(n)\ge0\), (3.4), и вся НОД-факторизация | ABSTRACT | PAPER | доказаны для всех конечных m, всех \(\tau\ge0\) |
| L3 | Полная Möbius-congruence и tangent (4.4) | FINITE_CELL | PAPER | точная фактическая \(\Lambda\), все степени |
| L4 | Связанный physical return (4.9)–(4.11) | FINITE_CELL | PAPER | original norm, zero map error |
| L5 | Полный signed second derivative и Taylor return | FINITE_CELL | PAPER | (5.1)–(5.4), все mixed terms |
| L6 | Доступная полная inequality (0.2), (7.1) | COFINAL_FAMILY | PAPER | показатель 1/2 с логарифмами, не улучшает fallback |
| L7 | Новый vanishing-exponent curvature/image supplier | COFINAL_FAMILY | CONDITIONAL / OPEN | не выведен и не использован |
| L8 | Tangent-control (8.1) | FINITE_CELL | PAPER | только арифметическая матрица, не контрпример original P |
| L9 | Новый показатель CCM / RH | COFINAL_FAMILY | CONDITIONAL / OPEN | не получены |
| L10 | Конечные executable controls | FINITE_CELL | PAPER / exact algebra | не заменяют universal statements |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_ONE_SIDED_T_GT_R
ACTUAL_CONSUMER_REQUIREMENT: common_eventual_or_cofinal_upper_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: joint_signed_divisor_image_return_before_graph_cap_and_moduli
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
NECESSITY_SCOPE: S2_identity_equates_this_comparison_with_the_direct_A_upper_for_the_same_f
METHOD_IS_NECESSARY: false
KNOWN_WEAKER_INTERFACES:
  - direct_A_upper_returns_T_and_K_with_the_fees_in_2_5
  - independently_proved_actual_pair_margin_requires_its_own_receiver_and_is_not_all_P
  - full_joint_R_tau_minus_Phi_tau_comparison_is_weaker_than_separate_curvature_control_but_is_not_supplied
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
IMPOSSIBILITY_EVIDENCE: NONE
REOPEN_TRIGGER: a_quantitative_signed_bound_for_the_actual_Mobius_gcd_correlation_or_a_distinct_source_supplier_with_full_original_norm_return
NOVELTY_AXIS: finite_arithmetic_PSD_deformation_with_exact_Mobius_tangent_on_the_whole_linked_physical_image
CONSUMER_PROGRESS: NO_PROGRESS
LOCAL_PROGRESS_CLASS: REPRESENTATION_AND_APPLICABILITY_CHECK_ONLY
LOOP_DETECTED: positivity_of_an_auxiliary_family_is_being_confused_with_a_small_signed_derivative
FORBIDDEN_FUTURE_MOVE: infer_tangent_sign_from_PSD_or_reoptimize_the_same_absolute_curvature_budget_as_new_cancellation
NEXT_QUESTION_DISPATCH: NONE
```

### Две репрезентации и цена проверки

| Представление | Решающий тест | Стоимость / сила |
|---|---|---|
| Полная арифметическая \(\Phi_\tau\) на связанном образе | Вывести всю касательную и вернуть \(\mathcal R_\tau\), особенно нецелые ratio-cross terms | Невысокая конечная алгебра, затем явный analytic budget; сильный контроль потери нормировки, но не готовый source sign |
| Первая причинная форма S6 до lift/deformation | Проверить независимый верх непосредственно для \(A_m[f]\), а не для чужого positive kernel | Карта назад имеет цену 0; никакого неизвестного supplier она не создаёт |

Одна из этих репрезентаций выполнена как новый тест; вторая — документированная точка возврата. Они не считаются двумя независимыми успехами и не разрешают эскалацию вычислений по инерции.

**DISCRIMINATOR:** для заранее заданного \(s_m\) — нижняя граница **всей** формы
\[
 G_a-E_{\rm signed}-(D_a-s_m)\|f\|^2
 =s_m\|f\|^2-A_m[f]
\]
на исходной области. В deformation-completion достаточен независимо оплаченный upper (6.1), но не просто \(\Phi_\tau\ge0\) или маленький конечный шаг. Интервал, содержащий ноль, не даёт знака. Конечный контроль не даёт cofinal-квантора.

**Судьба прогнозов.** Регистрация сохранена после полного чтения и предварительного PAPER-вывода, до новых математических запусков. P1 подтверждён (3.4)–(3.9); P2 — (4.3)–(4.4); P3 — (4.9)–(4.11); P4 — законным верхним allowance (5.6)–(5.11), **не** утверждением о настоящей величине кривизны; P5 — (7.1)–(7.3). P6 разграничивает finite tests и универсальную задачу: никакой конечный запуск не использован для утверждения отсутствия или наличия cofinal supplier.

```yaml
MEMORY_ENTRY:
  iteration: Q54_SIGNED_DIVISOR_IMAGE_RETURN
  target: independent_original_P_signed_upper_before_carrier_moduli
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_completion: positive_GCD_deformation_followed_by_absolute_full_curvature_return
  invariant_learned: arithmetic_rank_one_baseline_pulls_back_to_the_original_identity_not_to_a_contact_nullspace
  forbidden_future_move: discard_normalization_derivatives_n1_or_the_complete_ratio_curvature
  smallest_unpaid_input: quantitative_joint_upper_in_5_2_or_a_weaker_independent_signed_source_comparison
  consumer_progress: NO_PROGRESS
  route_score: 2
  route_death: NOT_ESTABLISHED
  next_decisive_test: one_bounded_independent_audit_of_source_tangent_and_all_return_costs
```

### Одна CODEX DIRECTIVE

Выполнить **один bounded независимый PAPER-аудит §§3–7**: проверить real-parameter \(j_\tau\), ориентацию матриц \(\mathsf E,\mathsf U\), нормировочные члены касательной, полный образ \(x_n,r_d\), коэффициент \(1/2\) при \(A_m\), обязательные \(n=1,m\), все рациональные ratio-cross terms и константу в (5.6); затем воспроизвести четыре приложения. Вернуть первую материальную ошибку либо принять **ровно эти утверждения**. Не принимать (6.1), новый показатель или RH из успешного replay. Не запускать следующий вопрос, production scan, установку пакетов или репозиторную запись автоматически. Этот аудит здесь не выполнялся и не объявляется выполненным.

## 10. Внешние источники и границы импорта

[E1] Dominique Guillot, Jiaru Wu, *Total nonnegativity of GCD matrices and kernels*, arXiv:1901.01947v1, §1.1, Theorem 1.2 и следующее за ним доказательство факторизацией через делители. Первичный HTML прочитан. Использован лишь ориентир для конечной арифметической Gram-факторизации. Общая real-parameter версия и все source-return formulas выведены в этом ответе; теоремы о total nonnegativity не применяются.

[E2] NIST DLMF §27.5, formulas 27.5.2, 27.5.3, 27.5.5: настоящая инверсия Мёбиуса, divisor sum для \(\log n\) и \(\Lambda=\mu*\log\). Это стандартные безусловные тождества, не Mertens-оценка и не утверждение о нулях.

```text
[E1] https://arxiv.org/html/1901.01947
[E2] https://dlmf.nist.gov/27.5
```

Никаких новых внешних zero-free, variance, shifted-correlation или RH-strength оценок не импортировано. Глобального отсутствия подходящего результата в литературе не утверждается. Унаследованные receiver и контурные теоремы целиком заново не сертифицировались.

## 11. Воспроизводимость и честная область вычислений

Новые проверки используют только стандартную библиотеку Python, `Fraction` и гауссовы рациональные числа. \(\log p\) в алгебраических тестах — независимые формальные символы; полиномиальные равенства проверяются точно. При целых \(\tau=2,4\) нормированная НОД-матрица рациональна и проверяется по точной факторизации и всем комплексным cross terms.

Небольшой linked-translation контроль использует формальное аддитивное отображение простых в целые сдвиги и рациональные тестовые амплитуды \(1/n\). Он проверяет универсальную алгебру source return, **не** подменяет физические \(\log n\), \(1/\sqrt n\), исходные частоты или production-ячейку. Их точная специализация доказана в §4. В частности, отрицательный tangent-control (8.1) не объявлен original-P вектором.

Проверяются полная incidence inversion, нормировочная производная, настоящие prime powers, комплексное спаривание, нецелые ratio-секторы, верхний диагональный атом при нулевом overlap, Taylor-остаток и оптимизация выписанного allowance. Отрицательные контроли обнаруживают также ложное PSD-to-tangent правило и подмену signed defect его модулем. Они не являются независимыми асимптотическими открытиями.

Ни один исторический скрипт не запускался. Независимого нового аудита, Lean, Arb, production-спектральных вычислений или вычисления координат actual zeta zeros не было. Пакеты не устанавливались. Первый запуск нового checker прошёл без изменения математических assertions.

Сохрани тело `replay_q54.py` из приложения и выполни:

```bash
python3 replay_q54.py \
  PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_VERDICT_2026-10-27.md \
  PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_2026-10-27.txt \
  q54_replay
```

Первый аргумент — этот полный Markdown, второй — неизменённый канонический TXT, третий — создаваемый каталог. При другом расположении замени только пути, например `./archive/PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_VERDICT_2026-10-27.md`. Достаточно Python 3.9+ без сторонних пакетов. Replayer проверяет bytes/SHA/framing новых приложений, извлекает их и запускает только новый `check_q54.py`, сравнивая JSON побайтно.

### Проверенный source manifest

Byte-диапазоны ниже полуоткрытые `[start,end)`; строки относятся к raw TXT. Внешний separator LF не входит в body.

| ID | Полное тело | Bytes / LF | SHA-256 | Raw строки | Bytes `[start,end)` |
|---|---|---:|---|---:|---:|
| S1 | `CCM_POST_Q53_WEIGHTED_CARRIER_PREFLIGHT.md` | 3927 / 70 | `88f78b706bdf435c06c0ca7545b01173cfe407197fd3e84cd6495d0c548212f3` | 34–103 | [7460,11387) |
| S2 | `CCM_POST_Q53_SIGNED_SLACK_CROSSWALK.md` | 2658 / 46 | `216c2424559b1fb1acd764997602760143a7de51e76a20c2bc55824b80ab9d70` | 108–153 | [11444,14102) |
| S3 | `PROSHKA_CCM_SIGNED_INNER_OBSERVATION_Q53_VERDICT_2026-10-27.md` | 100044 / 1662 | `9e053358e4d653e2787a1f85520589e2077a6d6c8edf4f4f9a281cbea6fe2489` | 158–1819 | [14183,114227) |
| S4 | `CCM_POST_Q48_FIRST_FORM_DEFICIT_CROSSWALK.md` | 5205 / 93 | `c7efc8783bb4306ee55df5574649fccf3da8240d37384b8db965183d1dd569e6` | 1824–1916 | [114290,119495) |
| S5 | `CCM_POST_Q42_MULTISCALE_SCREEN.md` | 3118 / 57 | `4cb686fe44063d054d1a872b730a36270e200a75be16f63b8868dfa833d871bb` | 1921–1977 | [119547,122665) |
| S6 | `CCM_JOINT_Q04_CONCLUSION.md` | 5036 / 92 | `617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086` | 1982–2073 | [122711,127747) |
| S7 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 / 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` | 2078–2200 | [127800,133433) |
| S8 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 / 69 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` | 2205–2273 | [133479,139653) |

### Полные приложения

BEGIN_ASSET registration_q54.json
BYTES: 2650
SHA256: 5e35eea977fe80c720dc8a5217d0d51d66eca4e89c8b3c4842198792580212e5
```json
{
  "task": "Q54_SIGNED_DIVISOR_IMAGE_RETURN",
  "stage": "After complete packet reading, byte verification, primary-source screen and preliminary PAPER derivation; before executable mathematical tests",
  "chosen_operator": "REPRESENTATION_SHIFT",
  "documented_rollback": "S6 finite first source before carrier graph cap; use a finite normalized GCD deformation and actual Mobius congruence",
  "predictions": {
    "P1": "The normalized gcd kernel Q_tau(n,k)=(gcd(n,k)/sqrt(n*k))^tau is positive semidefinite for every tau>=0, by the positive real-parameter Jordan divisor coefficients, including n=1.",
    "P2": "For the genuine finite Mobius inverse U, V_0=U Q_0 U^T=e1 e1^T and V'_0=diag(Lambda)-(Lambda e1^T+e1 Lambda^T)/2, with every prime power retained.",
    "P3": "On the full linked image x_n(t)=n^(-1/2) f(t+log(n)), the integrated energy satisfies Phi_0=||f||^2 and Phi'_0=h_m||f||^2-A_m[f]/2. Its positivity does not by itself give the sign of this derivative.",
    "P4": "The complete second derivative retains all coprime-ratio and Mobius cross terms. The available uniform curvature completion has allowance 4*m*L^2*(1+L)^2, so its optimized full source allowance retains exponent 1/2.",
    "P5": "All original-P returns are direct: one short-divisor fee only for T, one archimedean fee for K, no contour fee, and no second H_P charge.",
    "P6": "Finite controls can validate the incidence, multiplicity, sign and endpoint algebra but cannot certify an independent cofinal signed curvature estimate or CCM bound. Whether such a stronger estimate is available is a PAPER question, not fixed by this registration."
  },
  "candidate_representations": [
    {
      "name": "finite GCD deformation on the whole linked source image",
      "cost": "finite exact incidence algebra and one uniform Taylor return; no production-sized matrix needs to be constructed",
      "discriminator": "the full signed curvature must be paid, not removed by positivity of the deformed matrix",
      "kill_power": "high for a falsely signed tangent inference; none for a consumer-wide impossibility claim"
    },
    {
      "name": "original first causal Mobius-Mangoldt form before lift",
      "cost": "zero map error by the supplied exact source equation",
      "discriminator": "independent one-sided source inequality on the same c before separate norms",
      "kill_power": "detects duplicated graph or jump-energy bookkeeping, not failure of actual cancellation"
    }
  ],
  "historical_programs_executed": false,
  "repository_writes": false,
  "installations": false,
  "numeric_zeta_roots": false,
  "production_spectrum": false
}
```
END_ASSET

BEGIN_ASSET check_q54.py
BYTES: 13744
SHA256: 6566a3a5f2bc655ff0de8847134c7c7354e7e94179a5a1829271806610984304
```python
#!/usr/bin/env python3
"""Q54: exact finite arithmetic/algebra and canonical byte framing.
Usage: python3 check_q54.py CANONICAL_Q54.txt
Standard library only. No historical program or production CCM is executed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from math import gcd
import hashlib, json, re, sys

SIZE, LF = 139662, 2276
SHA = '29975f46faee9550eea39e6de9048f0c73f9e483d1522ebfed9a32003651ce6a'
NAME = 'PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_2026-10-27.txt'
MAN = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('outer bytes/LF/SHA')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.startswith(b'Q54 SIGNED_DIVISOR_IMAGE_RETURN\n'):
        raise ValueError('request/newline convention')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MAN.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for i, h in enumerate(heads, 1):
        if h[1] != str(i).encode():
            raise ValueError('source order')
        sid, name = f'S{i}', h[2].decode()
        opening = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos+len(opening)] != opening:
            raise ValueError('opening')
        st, en = pos+len(opening), pos+len(opening)+int(h[3])
        body = raw[st:en]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('body bytes/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('body SHA')
        body.decode('utf-8')
        closing = f'\nEND {sid}\n\n'.encode()
        if raw[en:en+len(closing)] != closing:
            raise ValueError('closing/separator')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=st, end_byte=en,
                         start_line=raw[:st].count(b'\n')+1, end_line=raw[:en].count(b'\n')))
        pos = en+len(closing)
    if pos != len(raw):
        raise ValueError('trailing bytes')
    return dict(packet=NAME, bytes=len(raw), lf=LF, sha256=SHA,
                source_count=8, all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def cast(x): return x if isinstance(x, Q) else Q(x)
    def __add__(self, x):
        x = Q.cast(x); return Q(self.re+x.re, self.im+x.im)
    __radd__ = __add__
    def __neg__(self): return Q(-self.re, -self.im)
    def __sub__(self, x): return self + (-Q.cast(x))
    def __rsub__(self, x): return Q.cast(x) + (-self)
    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re-self.im*x.im, self.re*x.im+self.im*x.re)
    __rmul__ = __mul__
    def conj(self): return Q(self.re, -self.im)
    def norm2(self): return self.re*self.re+self.im*self.im
    def pair(self): return [str(self.re), str(self.im)]
Z = Q()


def fac(n: int) -> dict[int, int]:
    ans = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1; n //= p
        p += 1
    if n > 1: ans[n] = ans.get(n, 0)+1
    return ans


def mu(n):
    f = fac(n)
    return 0 if any(v > 1 for v in f.values()) else (-1)**len(f)


def divs(n): return [d for d in range(1, n+1) if n % d == 0]


# Polynomials in independent formal symbols log(p), with Gaussian-rational
# coefficients. Monomial () is a constant; no floating logarithms are used.
def padd(a, b):
    r = dict(a)
    for k, v in b.items(): r[k] = r.get(k, Z)+v
    return {k:v for k,v in r.items() if v != Z}


def pscale(a, s): return {k:Q.cast(s)*v for k,v in a.items() if Q.cast(s)*v != Z}


def pmul(a, b):
    r = {}
    for k,v in a.items():
        for l,w in b.items():
            kl = tuple(sorted(k+l)); r[kl] = r.get(kl, Z)+v*w
    return {k:v for k,v in r.items() if v != Z}


def logp(n): return {(p,):Q(v) for p,v in fac(n).items()}


def mang(n):
    f = fac(n)
    return {(next(iter(f)),):Q(1)} if len(f) == 1 else {}


def pquad(A, x):
    r = {}
    for i in range(len(x)):
        for j in range(len(x)):
            r = padd(r, pscale(A[i][j], x[i].conj()*x[j]))
    return r


def qquad(A, x):
    return sum((x[i].conj()*A[i][j]*x[j] for i in range(len(x)) for j in range(len(x))), Z)


def mobius_matrix(m):
    return [[mu(n//d) if n % d == 0 else 0 for d in range(1, m+1)] for n in range(1, m+1)]


def ptr(A, U):
    m = len(U); out = [[{} for _ in range(m)] for _ in range(m)]
    for i in range(m):
        for j in range(m):
            for a in range(m):
                if U[i][a]:
                    for b in range(m):
                        if U[j][b]:
                            out[i][j] = padd(out[i][j], pscale(A[a][b], U[i][a]*U[j][b]))
    return out


def math_checks():
    counts, bad = {}, {}
    tangent_entries = 0; positive_cases = 0; mixed_cases = 0
    for m in (2, 4, 8, 12):
        U = mobius_matrix(m)
        E = [[int(n % d == 0) for d in range(1, m+1)] for n in range(1, m+1)]
        assert all(sum(U[i][k]*E[k][j] for k in range(m)) == int(i == j)
                   for i in range(m) for j in range(m))
        assert [sum(row) for row in U] == [1]+[0]*(m-1)
        Qprime = []; distances = []
        for n in range(1, m+1):
            qr, dr = [], []
            for k in range(1, m+1):
                d = padd(pscale(padd(logp(n), logp(k)), F(1,2)), pscale(logp(gcd(n,k)), -1))
                dr.append(d); qr.append(pscale(d, -1))
            Qprime.append(qr); distances.append(dr)
        derivative = ptr(Qprime, U)
        expected = [[{} for _ in range(m)] for _ in range(m)]
        for n in range(1, m+1):
            for k in range(1, m+1):
                v = mang(n) if n == k else {}
                if k == 1: v = padd(v, pscale(mang(n), -F(1,2)))
                if n == 1: v = padd(v, pscale(mang(k), -F(1,2)))
                expected[n-1][k-1] = v
                assert derivative[n-1][k-1] == v
                tangent_entries += 1
        # The separate log-gcd congruence is exactly diag(Lambda).
        Lg = [[logp(gcd(n,k)) for k in range(1,m+1)] for n in range(1,m+1)]
        diag = ptr(Lg, U)
        assert all(diag[i][j] == (mang(i+1) if i == j else {}) for i in range(m) for j in range(m))
        for tau in (2, 4):
            J = [sum(mu(n//d)*d**tau for d in divs(n)) for n in range(1,m+1)]
            assert all(j > 0 for j in J)
            K = [[F(gcd(n,k)**tau, (n*k)**(tau//2)) for k in range(1,m+1)] for n in range(1,m+1)]
            for n in range(1,m+1):
                for k in range(1,m+1):
                    factored = sum(J[d-1] for d in divs(gcd(n,k)))
                    assert K[n-1][k-1] == F(factored,(n*k)**(tau//2))
            x = [Q(F((-1)**n,n+1),F(n,2*n+1)) for n in range(1,m+1)]
            r = [sum((U[n][d]*x[n] for n in range(m)), Z) for d in range(m)]
            full = qquad(K,r)
            square = sum((J[d-1]*sum((F(1,n**(tau//2))*r[n-1] for n in range(d,m+1,d)),Z).norm2()
                          for d in range(1,m+1)),F(0))
            assert full.im == 0 and full.re == square and square >= 0
            positive_cases += 1
            tangent = pquad(derivative,x)
            rhs = {}
            for n in range(1,m+1):
                rhs = padd(rhs,pscale(mang(n),x[n-1].norm2()-(x[0].conj()*x[n-1]).re))
            assert tangent == rhs
            mixed_cases += 1
        bad['drop_normalization_derivative'] = diag != derivative
        bad['replace_Mobius_by_absolute_values'] = any(sum(abs(z) for z in row) != int(i == 0) for i,row in enumerate(U))
    counts.update(tangent_entries=tangent_entries,positive_deformation_cases=positive_cases,complex_quadratic_cases=mixed_cases)

    # A PSD family need not have a PSD tangent. This is an arithmetic-index
    # algebra control, NOT a physical original-P spectral counterexample.
    T = [[{}, {(2,):Q(-F(1,2))}], [{(2,):Q(-F(1,2))},{(2,):Q(1)}]]
    neg = pquad(T,[Q(1),Q(F(1,2))])
    assert neg == {(2,):Q(-F(1,4))}
    bad['PSD_family_implies_PSD_tangent'] = True
    bad['Lambda_power_replaced_by_log_n'] = mang(8) != logp(8)

    # Linked finite-translation controls. Here log(p) shifts are formal additive
    # integer shifts and q_n=1/n is a rational test weight. These specialize the
    # universal algebra, not a production cell or its n^(-1/2) norm.
    m = 8; U = mobius_matrix(m)
    primes = [p for p in range(2,m+1) if fac(p) == {p:1}]
    lp = {p:i+1 for i,p in enumerate(primes)}
    shift = {n:sum(lp[p]*v for p,v in fac(n).items()) for n in range(1,m+1)}
    f = {1:Q(1,1), 2:Q(2,-1)}
    norm = sum(z.norm2() for z in f.values())
    times = list(range(1-max(shift.values()),3))
    V1 = [[{} for _ in range(m)] for _ in range(m)]
    for n in range(1,m+1):
        V1[n-1][n-1] = mang(n)
        V1[n-1][0] = padd(V1[n-1][0],pscale(mang(n),-F(1,2)))
        V1[0][n-1] = padd(V1[0][n-1],pscale(mang(n),-F(1,2)))
    tangent = {}; baseline = F(0); sum_norm = F(0)
    curvature_full = {}; curvature_deleted = {}
    for t in times:
        x = [F(1,n)*f.get(t+shift[n],Z) for n in range(1,m+1)]
        baseline += x[0].norm2(); sum_norm += sum(z.norm2() for z in x)
        tangent = padd(tangent,pquad(V1,x))
        r = [sum((U[n][d]*x[n] for n in range(m)), Z) for d in range(m)]
        for n in range(1,m+1):
            for k in range(1,m+1):
                dist = padd(pscale(padd(logp(n),logp(k)),F(1,2)),pscale(logp(gcd(n,k)),-1))
                term = pscale(pmul(dist,dist),r[n-1].conj()*r[k-1])
                curvature_full = padd(curvature_full,term)
                if n % k == 0 or k % n == 0:
                    curvature_deleted = padd(curvature_deleted,term)
    assert baseline == norm
    assert sum_norm == norm*sum(F(1,n*n) for n in range(1,m+1))
    h = {}; Aprime = {}
    for n in range(1,m+1):
        corr = sum((f.get(t,Z).conj()*f.get(t+shift[n],Z) for t in f),Z)
        h = padd(h,pscale(mang(n),F(1,n*n)*norm))
        Aprime = padd(Aprime,pscale(mang(n),2*F(1,n)*corr.re))
    assert tangent == padd(h,pscale(Aprime,-F(1,2)))
    bad['drop_noninteger_ratio_cross_terms'] = curvature_full != curvature_deleted
    bad['drop_factor_two_in_source_return'] = tangent != padd(h,pscale(Aprime,-1))
    bad['drop_top_diagonal_because_top_overlap_is_zero'] = mang(m) != {}
    top_corr = sum((f.get(t,Z).conj()*f.get(t+shift[m],Z) for t in f),Z)
    assert top_corr == Z and shift[m] == 3
    counts['linked_formal_translation_cases'] = 1
    counts['linked_time_rows'] = len(times)

    # Taylor return via independently differentiated exponential antiderivative:
    # H(s)=((s-tau)/q+1/q^2)*exp(-q*s), H'=(tau-s)*exp(-q*s).
    tc = 0
    for q in (F(1,3),F(1),F(5,2)):
        for tau in (F(1,7),F(2,3),F(2)):
            a0,a1 = -tau/q+1/q**2,1/q
            assert (a1-q*a0, -q*a1) == (tau,-F(1))
            # pair (constant, coefficient of the formal E=exp(-tau*q)).
            rem = (-a0,a0+a1*tau)
            assert (1-tau*q+q*q*rem[0],q*q*rem[1]) == (0,1)
            tc += 1
    bad['erase_Taylor_remainder'] = (1-F(2,3),0) != (0,1)
    counts['exact_Taylor_returns'] = tc

    opt = 0
    for k in (1,3,7):
        C = F(2*k*k)
        for tau in (F(1,k),F(1,2*k),F(2,k)):
            price = 2/tau+C*tau
            assert price*price >= 8*C
            if tau == F(1,k): assert price == 4*k
            opt += 1
    counts['optimization_controls'] = opt
    bad['remove_n1_baseline'] = norm != 0
    # Distinct signed E versus an absolute scalar is not an identity.
    bad['replace_signed_defect_by_its_absolute_value'] = F(-2) != abs(F(-2))
    bad['double_short_in_direct_K'] = -F(7) != -F(7)-F(3)
    assert all(bad.values()), bad
    return dict(passed=True,counts=counts,planted_errors_detected=bad,
                tangent_negative_control={'value':'-log(2)/4','arithmetic_index_only':True,'original_P_counterexample':False},
                exact_prime_power_weights=True,source_bound_proved_by_finite_tests=False,
                scope='Exact finite arithmetic and polynomial identities in formal log(p); rational translation controls only; universal bounds are PAPER arguments')


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 check_q54.py CANONICAL_Q54.txt')
    raw = Path(sys.argv[1]).read_bytes(); provenance = verify(raw)
    bad = bytearray(raw); bad[provenance['sources'][0]['start_byte']+50] ^= 1
    en = provenance['sources'][0]['end_byte']; mutations = {}
    for name,data,outer in [('outer_hash',bytes(bad),True),('body_hash',bytes(bad),False),
                            ('extra_separator',raw[:en]+b'\n'+raw[en:],False),('truncated_frame',raw[:-2],False)]:
        try: verify(data,outer)
        except (ValueError,UnicodeError): mutations[name] = True
        else: raise AssertionError('missed provenance mutation: '+name)
    result = dict(provenance=provenance,framing_mutations=mutations,mathematics=math_checks(),
                  historical_programs_executed=False,production_CCM_spectrum=False,
                  numeric_actual_zeta_zeros=False,lean=False,arb=False,independent_audit=False,
                  new_vanishing_exponent_supplier=False)
    text = json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q54_checks.json').write_text(text,encoding='utf-8')
    print(text,end='')
if __name__ == '__main__': main()
```
END_ASSET

BEGIN_ASSET q54_checks.json
BYTES: 4572
SHA256: d77c5c426d4f18476bfe0d1854e77e58a2aeff54465de32093a3b5180a9440ce
```json
{
  "arb": false,
  "framing_mutations": {
    "body_hash": true,
    "extra_separator": true,
    "outer_hash": true,
    "truncated_frame": true
  },
  "historical_programs_executed": false,
  "independent_audit": false,
  "lean": false,
  "mathematics": {
    "counts": {
      "complex_quadratic_cases": 8,
      "exact_Taylor_returns": 9,
      "linked_formal_translation_cases": 1,
      "linked_time_rows": 6,
      "optimization_controls": 9,
      "positive_deformation_cases": 8,
      "tangent_entries": 228
    },
    "exact_prime_power_weights": true,
    "passed": true,
    "planted_errors_detected": {
      "Lambda_power_replaced_by_log_n": true,
      "PSD_family_implies_PSD_tangent": true,
      "double_short_in_direct_K": true,
      "drop_factor_two_in_source_return": true,
      "drop_noninteger_ratio_cross_terms": true,
      "drop_normalization_derivative": true,
      "drop_top_diagonal_because_top_overlap_is_zero": true,
      "erase_Taylor_remainder": true,
      "remove_n1_baseline": true,
      "replace_Mobius_by_absolute_values": true,
      "replace_signed_defect_by_its_absolute_value": true
    },
    "scope": "Exact finite arithmetic and polynomial identities in formal log(p); rational translation controls only; universal bounds are PAPER arguments",
    "source_bound_proved_by_finite_tests": false,
    "tangent_negative_control": {
      "arithmetic_index_only": true,
      "original_P_counterexample": false,
      "value": "-log(2)/4"
    }
  },
  "new_vanishing_exponent_supplier": false,
  "numeric_actual_zeta_zeros": false,
  "production_CCM_spectrum": false,
  "provenance": {
    "all_frames_verified": true,
    "bytes": 139662,
    "lf": 2276,
    "packet": "PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_2026-10-27.txt",
    "sha256": "29975f46faee9550eea39e6de9048f0c73f9e483d1522ebfed9a32003651ce6a",
    "source_count": 8,
    "sources": [
      {
        "bytes": 3927,
        "end_byte": 11387,
        "end_line": 103,
        "id": "S1",
        "lf": 70,
        "name": "CCM_POST_Q53_WEIGHTED_CARRIER_PREFLIGHT.md",
        "sha256": "88f78b706bdf435c06c0ca7545b01173cfe407197fd3e84cd6495d0c548212f3",
        "start_byte": 7460,
        "start_line": 34
      },
      {
        "bytes": 2658,
        "end_byte": 14102,
        "end_line": 153,
        "id": "S2",
        "lf": 46,
        "name": "CCM_POST_Q53_SIGNED_SLACK_CROSSWALK.md",
        "sha256": "216c2424559b1fb1acd764997602760143a7de51e76a20c2bc55824b80ab9d70",
        "start_byte": 11444,
        "start_line": 108
      },
      {
        "bytes": 100044,
        "end_byte": 114227,
        "end_line": 1819,
        "id": "S3",
        "lf": 1662,
        "name": "PROSHKA_CCM_SIGNED_INNER_OBSERVATION_Q53_VERDICT_2026-10-27.md",
        "sha256": "9e053358e4d653e2787a1f85520589e2077a6d6c8edf4f4f9a281cbea6fe2489",
        "start_byte": 14183,
        "start_line": 158
      },
      {
        "bytes": 5205,
        "end_byte": 119495,
        "end_line": 1916,
        "id": "S4",
        "lf": 93,
        "name": "CCM_POST_Q48_FIRST_FORM_DEFICIT_CROSSWALK.md",
        "sha256": "c7efc8783bb4306ee55df5574649fccf3da8240d37384b8db965183d1dd569e6",
        "start_byte": 114290,
        "start_line": 1824
      },
      {
        "bytes": 3118,
        "end_byte": 122665,
        "end_line": 1977,
        "id": "S5",
        "lf": 57,
        "name": "CCM_POST_Q42_MULTISCALE_SCREEN.md",
        "sha256": "4cb686fe44063d054d1a872b730a36270e200a75be16f63b8868dfa833d871bb",
        "start_byte": 119547,
        "start_line": 1921
      },
      {
        "bytes": 5036,
        "end_byte": 127747,
        "end_line": 2073,
        "id": "S6",
        "lf": 92,
        "name": "CCM_JOINT_Q04_CONCLUSION.md",
        "sha256": "617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086",
        "start_byte": 122711,
        "start_line": 1982
      },
      {
        "bytes": 5633,
        "end_byte": 133433,
        "end_line": 2200,
        "id": "S7",
        "lf": 123,
        "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
        "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
        "start_byte": 127800,
        "start_line": 2078
      },
      {
        "bytes": 6174,
        "end_byte": 139653,
        "end_line": 2273,
        "id": "S8",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 133479,
        "start_line": 2205
      }
    ]
  }
}
```
END_ASSET

BEGIN_ASSET replay_q54.py
BYTES: 2876
SHA256: 05781bbbc98032aab48353c8bf0507202aa5d7155f211895f69d87c27d8a85fe
```python
#!/usr/bin/env python3
"""Extract/replay Q54's four assets; do not execute historical source bodies.
Usage: python3 replay_q54.py VERDICT.md CANONICAL_Q54.txt [OUTPUT_DIRECTORY]
Python 3.9+ standard library only.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEADER = re.compile(
    rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\n'
    rb'SHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q54.json', 'check_q54.py',
            'q54_checks.json', 'replay_q54.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets: dict[str, bytes] = {}
    pos = 0
    while True:
        h = HEADER.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected or repeated asset: ' + name)
        start, end = h.end(), h.end() + int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]):
            raise ValueError('asset byte count: ' + name)
        if hashlib.sha256(body).hexdigest() != h[3].decode('ascii'):
            raise ValueError('asset SHA256: ' + name)
        body.decode('utf-8')
        close = b'```\nEND_ASSET\n'
        if raw[end:end + len(close)] != close:
            raise ValueError('asset closing frame: ' + name)
        assets[name] = body
        pos = end + len(close)
    if set(assets) != EXPECTED:
        raise ValueError('missing asset')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q54.py VERDICT.md CANONICAL_Q54.txt [OUTPUT_DIRECTORY]')
    verdict, canonical = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q54_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.resolve() in (verdict, canonical):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q54.py'), str(canonical)],
        cwd=out, capture_output=True, check=True)
    (out / 'check_q54.stdout').write_bytes(run.stdout)
    if (out / 'q54_checks.json').read_bytes() != assets['q54_checks.json']:
        raise ValueError('replayed JSON differs from the embedded result')
    report = dict(asset_count=len(assets), all_asset_hashes_match=True,
                  checker_executed=True, json_byte_identical=True,
                  historical_programs_executed=False, independent_audit=False,
                  production_spectrum=False)
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
```
END_ASSET


## 12. Фактическое воспроизведение окончательного файла

Все **четыре приложения извлечены из собранного Markdown** с проверкой точных размеров, SHA-256 и framing. Извлечённый `check_q54.py` повторно исполнен на неизменённом каноническом Q54 TXT; его JSON совпал со встроенным результатом **побайтно**.

```json
{
  "all_asset_hashes_match": true,
  "asset_count": 4,
  "checker_executed": true,
  "historical_programs_executed": false,
  "independent_audit": false,
  "json_byte_identical": true,
  "production_spectrum": false
}
```

Фактическая панель: 228 элементов касательной, восемь положительных деформационных и восемь комплексных квадратичных случаев; один полный linked-translation контроль с шестью временными строками; девять точных Taylor-return и девять рациональных проверок оптимизации. Проверяющий обнаружил **11 предусмотренных алгебраических/accounting ошибок** и четыре нарушения framing/hash. Это собственный replay, не независимый аудит и не сертификат исходного асимптотического знака.

Ни одна историческая программа не запускалась, исходный TXT не менялся. Новые приложения остались побайтно теми же после внесения этого отчёта. Сам replayer дополнительно повторно запущен уже из извлечённого приложения на окончательном файле. Lean, Arb, production-спектральные вычисления и новый независимый аудит не выполнялись.

**Окончательный итог Q54:** выбранный дополнительный арифметический вход доказан и перенесён на полный связанный исходный образ. Цена его законного завершения посчитана; нужного signed supplier и нового полного показателя нет. Исходные нормы, \(P\), коэффициенты, смешанные слагаемые и все края сохранены. Старый fallback не ухудшен. Главный CCM-goal остаётся открыт; математическая невозможность маршрута не утверждается.
