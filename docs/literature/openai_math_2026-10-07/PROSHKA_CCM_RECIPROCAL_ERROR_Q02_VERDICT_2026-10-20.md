# STATUS: TRY_CCM_RECIPROCAL_ERROR_Q02
```yaml
OPERATIVE_CLASS: TRY_CCM_RECIPROCAL_ERROR_Q02
VERDICT_CODE: FOURIER_TAIL_AND_FAST_RECIPROCAL_RANGE_PAID_JOINT_SLOW_PLUS_CONTINUOUS_OPEN
DATE: 2026-10-20
REQUEST_FILE: PROSHKA_CCM_RECIPROCAL_ERROR_Q02_2026-10-20.txt
REQUEST_BYTES: 93065
REQUEST_LF_COUNT: 1518
REQUEST_SHA256: 21893c097ed643fef7c99ff9dbd148c0e05563da617a45dfe439063e6ef61198
REQUEST_READ: COMPLETE_INCLUDING_EMBEDDED_SOURCES
SOURCE_BASELINE_AS_SUPPLIED: 495fef27fbf7142ab452f3d2f8ac06debcbc671e
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: LITERAL_CCM_N_EQUALS_M_ORIGINAL_THREE_CONSTRAINT_SPARSE_BAND
TERMINAL_CONSUMER: SEPARATE_SPARSE_BAND_OFF_CRITICAL_WITNESS_RECEIVER
ADJUDICATION: INCONCLUSIVE_FOR_NEW_COMPLETE_EXPONENT
NEW_COMPLETE_PARAMETER_PROPORTIONAL_BOUND: NOT_PROVED
NEW_COMPLETE_FIXED_EXPONENT_IMPROVEMENT: NONE
NEW_PAID_RANGE: "Fourier harmonics h >= ceil(D^2*(1+log D)/T) on exact d,t tiles, all k already returned"
NEW_PAID_RANGE_BOUND: "||E_fast|| <= 32*(1+D1)*N_D*(1+log J); at J=m^2 and M=m^epsilon this is O_epsilon(m^epsilon log m)"
FOURIER_TRUNCATION_BOUND: "||E-E^(J)|| <= K2*sqrt(m)/(pi^2*J), K2=16/3+20*D1/9+4*D2/9"
NEW_PROVED_FACTS:
  - Controlled finite sawtooth expansion through the continuous periodic B2 primitive
  - Exact projected upper derivative A_m_prime(m)=0
  - Endpoint-exact mean-square bound for actual reciprocal sums, including d<=t
  - Entire fast reciprocal range paid uniformly in the actual spectral weight
  - Slow reciprocal prefix norms are equivalent up to fixed constants to local Mobius prefix norms
  - Full C_plus_E recombination preserves the original zeta log-derivative symbol
UNPAID_OBJECT: "C_{>R}+E_slow^(m^2), one-sided on the actual P"
MERTENS_OR_RH_STRENGTH_INPUT: NOT_ASSUMED
COEFFICIENT_REPLACEMENT: "Only |mu|<=1 in explicitly coefficient-blind valid estimates; no arbitrary-coefficient oscillation claimed in the slow range"
BEST_INHERITED_COMPLETE_BOUND: "O(m^(3/8)*(log m)^2*log(3 log m)), CONDITIONAL on supplied ZF78"
ZF78_USE: COMPARISON_ONLY_NOT_REPROVED_NOT_USED_TO_BOUND_MERTENS
COFINAL_IMPROVEMENT: NOT_OBTAINED
FULL_SP: OPEN_NOT_CLAIMED
G1_G3: OPEN_NOT_CLAIMED
RH: NOT_PROVED
PX_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
NEW_CCM_SPECTRAL_RUNS: 0
LEAN_RUNS: 0
ARB_RUNS: 0
EXACT_LOCAL_CHECKS: 1580
EXACT_LOCAL_CHECK_STATUS: PASS
SMALL_RECIPROCAL_NUMERICAL_DIAGNOSTICS: 6
NUMERICAL_DIAGNOSTIC_STATUS: AGREEMENT_NOT_INTERVAL_CERTIFICATION
INDEPENDENT_AUDIT: NOT_RUN
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: AUXILIARY_RECIPROCAL_RANGE_AND_IMPORT_BOUNDARY_ONLY
CONSUMER_PROGRESS: NO_NEW_COMPLETE_EXPONENT
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ACTUAL_ROUTE_KILL_SCOPE: NONE
```

Ы. **Q02 выполнен как проверка одного механизма.** Получено допустимое конечное раскрытие точной ошибки Эйлера с полностью оплаченной Fourier-ошибкой. После интегрирования по настоящей переменной `t` весь достаточно высокочастотный reciprocal-сектор имеет параметр-пропорциональную цену. Но малые гармоники на диапазоне `t` и `d` одного порядка не получают растущей осцилляции. Их независимое абсолютное оценивание снова требует непоставленной компенсации настоящих μ. Совместная сборка `C+E` не удаляет этот арифметический долг: ниже выполнен её точный возврат, без объявления отдельной оценки E необходимой.

**Главный результат не есть улучшение полного T.** Он локализует границу проверенного reciprocal-импорта: высокие гармоники и truncation не являются неоплаченным препятствием; оставшаяся совместная низкочастотная часть с C остаётся исходной арифметической задачей.

## 0. Источник, кванторы, границы проверки

**[ABSTRACT | PAPER — происхождение].** Авторитетен верх Q02 TXT, строки 1–38. Прочитан весь загруженный UTF-8, включая обновлённый Abel/floor тест, принятый Q01, sparse receiver и long-Mobius primitive test. Число байт и SHA-256 в заголовке вычислены по смонтированному файлу. Baseline указан как pin запроса; состояние ветки, Lean и Comparator заново не проверялись. Старые задания внутри приложений не исполнялись. Q01 и его 7021 проверки не повторялись как новая работа.

Используются принятые в Q02 определения и PAPER-входы, не усиливая их:

- буквальные `P,Q_M`, исходные частоты и `||Q_M||<=2`;
- Q01 `||C_m(d)||<=20/sqrt(d)` и исходные continuous identities;
- исходная малоделительная плата и архимедов возврат;
- условный adverse witness отдельного sparse receiver;
- Q10 с ZF78 только как прежняя граница сравнения.

Внешняя сверка ограничена Fourier-рядами полиномов Бернулли (NIST DLMF 24.8.1–24.8.3) и нормировкой Dirichlet-рядов (DLMF 27.4). Никакая внешняя оценка коротких сумм Мёбиуса, reciprocal Type-II, Mertens или zero-free-to-Mertens не импортируется. Новые оценки и все их цены выводятся ниже.

До локальных вычислений зарегистрированы: знак Euler-раскрытия; обязательность нижнего производного края; точная отмена C+E при отсутствии ненулевого k; сохранение k=2 оболочки. Новый полный показатель не предсказывался. Отдельно перед шестью небольшими численными контролями зарегистрировано согласие точной парной формулы интеграла с независимой покусочной квадратурой. Это не интервальные сертификаты.

## 1. Неизменённая CCM и точная ошибка

**[FINITE_CELL | PAPER].** Пусть `m>=4`, `1<=M<=m`, `2<=R<m`,
\[
 L=\log m,\qquad \omega_j=2\pi j/L,\qquad \Omega=2\pi M/L.
\]
`P` — первоначальный ортогональный проектор на три ограничения `b*c=v_+*c=v_-*c=0` внутри `|j|<=M`, с нулевым дополнением в исходный carrier `|j|<=m`. При данном m он фиксирован во всех интегралах по t.
\[
 Q_M(s)_{jk}=\begin{cases}
 2(1-s/L)\cos(\omega_js),&j=k,\\
 [\sin(\omega_ks)-\sin(\omega_js)]/[\pi(j-k)],&j\ne k,
 \end{cases}\quad 0\le s\le L.
 \tag{1}
\]
\[
 A_m(t)=t^{-1/2}P Q_M(\log t)P,\qquad
 B_{m,d}=\sum_{k\le m/d}\log k\,A_m(dk),
\]
\[
 C_m(d)=\frac1d\int_d^m\log(t/d)A_m(t)\,dt,\qquad
 E_{m,d}=B_{m,d}-C_m(d).
 \tag{2}
\]
Все d,k — **обычные целые**, не идеалы CF22. Сохраняются все произведения, в том числе степени простых; `k=1` имеет вес ноль, `dk=m` имеет `Q_M(L)=0`. Для `d=m` обе части (2) нулевые.

Обозначим
\[
 \mathcal C_{>R}=\sum_{R<d\le m}\mu(d)C_m(d),\qquad
 \mathcal E_{>R}=\sum_{R<d\le m}\mu(d)E_{m,d}.
\]
Тогда
\[
 \boxed{T_{>R}=\mathcal C_{>R}+\mathcal E_{>R}.}              \tag{3}
\]
Это C непрерывного возврата CCM, **не** прежняя центрированная C арифметической ветки CF22.

Для
\[
 F_d(t)=\log(t/d)A_m(t),\qquad
 \beta_d(t)=\lfloor t/d\rfloor-t/d
\]
буквальное Stieltjes-суммирование даёт
\[
 E_{m,d}=[\beta_d(t)F_d(t)]_d^m-\int_d^m\beta_d(t)F_d'(t)\,dt
       =-\int_d^m\beta_d(t)F_d'(t)\,dt.                    \tag{4}
\]
Оба произведения на краях нулевые: `log1=0` и `Q_M(L)=0`. Скачки floor не пропущены — именно они образуют дискретную сумму B.

Положим `b_1(x)={x}-1/2` вне целых, с Fourier-серединным значением 0 в целых. Почти всюду `beta_d=-b_1(t/d)-1/2`. Поэтому
\[
 \boxed{E_{m,d}=\int_d^m b_1(t/d)F_d'(t)\,dt.}              \tag{5}
\]
Постоянная часть равна `1/2(F_d(m)-F_d(d))=0`. Это интегральная отмена, **не** разрешение занулять её подынтегрально. Изменение значений b1 в целых точках не меняет dt-интеграл и не удаляет целочисленные атомы из (4).

## 2. Производные настоящего ядра и дополнительный верхний нуль

**Лемма 1 [COFINAL_FAMILY | PAPER; фактически для всех конечных m,M].** Введём
\[
 D_1=2/L+4\Omega,\qquad D_2=4\Omega/L+4\Omega^2.
\]
Тогда
\[
 \|Q_M'(s)\|\le D_1,\quad \|Q_M''(s)\|\le D_2,
\]
\[
 \|A_m'(t)\|\le(1+D_1)t^{-3/2},\qquad
 \|A_m''(t)\|\le(3/2+2D_1+D_2)t^{-5/2}.                 \tag{6}
\]
Кроме того,
\[
 \boxed{A_m(m)=A_m'(m)=0.}                               \tag{7}
\]

**Доказательство.** Пусть `H_jk=1/(j-k)` при `j!=k`, `H_jj=0`. Его норма не превосходит π: конечная матрица есть сжатие дискретного Hilbert-оператора, чей Fourier-множитель имеет модуль не больше π. Это также непосредственно следует из ряда `sum_{n!=0}e^{inθ}/n=i(π-θ)` и Parseval. Из (1)
\[
 Q_M(s)=\operatorname{diag}\bigl(2(1-s/L)\cos\omega_js\bigr)
       -\pi^{-1}[\operatorname{diag}(\sin\omega_js),H].
\]
Дифференцирование диагонали и оценка нормы коммутатора дают `2/L+2Omega+2Omega` и `4Omega/L+2Omega²+2Omega²`. Далее
\[
 A_m'=t^{-3/2}P(Q_M'-\tfrac12Q_M)P,
\]
\[
 A_m''=t^{-5/2}P(Q_M''-2Q_M'+\tfrac34Q_M)P.
\]
Здесь использовано `||Q_M||<=2`, а производная P не возникает.

На `s=L` все `sin(omega_j L)=0`, `cos(omega_j L)=1`, и **каждый** элемент `Q_M'(L)` равен `-2/L`. Значит,
\[
 Q_M'(L)=-\frac2L\mathbf1\mathbf1^*,\qquad
 P\mathbf1=0\quad\Longrightarrow\quad PQ_M'(L)P=0.
\]
Это доказывает (7). В частности `F_d'(m)=0`. Частоты `2πj/log M` вместо исходных частот не дали бы этого вывода. ∎

Из (6) получаем
\[
 \|F_d'(t)\|\le[2+(1+D_1)\log(t/d)]t^{-3/2},             \tag{8}
\]
\[
 \|F_d''(t)\|\le[4+2D_1+(3/2+2D_1+D_2)\log(t/d)]t^{-5/2}.
 \tag{9}
\]
У нижнего края
\[
 F_d'(d)=A_m(d)/d,
\]
и этот член, вообще говоря, **не нулевой**.

## 3. Допустимое Fourier-раскрытие с явной ошибкой

**Теорема 2 [COFINAL_FAMILY | PAPER].** Для целого `J>=1` положим
\[
 b_{1,J}(x)=-\sum_{h=1}^J\frac{\sin(2\pi h x)}{\pi h},
\]
\[
 E_{m,d}^{(J)}=-\sum_{h=1}^J\frac1{\pi h}
                   \int_d^m\sin(2\pi h t/d)F_d'(t)\,dt.
 \tag{10}
\]
При
\[
 \mathfrak K_2=\frac{16}{3}+\frac{20}{9}D_1+\frac49D_2
\]
имеем
\[
 \boxed{
 \|E_{m,d}-E_{m,d}^{(J)}\|
 \le\frac{\mathfrak K_2}{2\pi^2J\sqrt d},\qquad
 \|\mathcal E_{>R}-\mathcal E_{>R}^{(J)}\|
 \le\frac{\mathfrak K_2\sqrt m}{\pi^2J}.
 }                                                        \tag{11}
\]

**Доказательство.** Нельзя использовать равномерную точечную ошибку `O(1/J)` для скачкообразной b1. Вместо неё используем **непрерывную первообразную хвоста**:
\[
 R_J(x)=\sum_{h>J}\frac{\cos(2\pi h x)}{2\pi^2h^2},
 \qquad \|R_J\|_\infty\le\frac1{2\pi^2J}.
\]
Из Fourier-ряда периодического B2 следует `R_J'=b_1-b_{1,J}` почти всюду. Ряд самой первообразной сходится абсолютно и равномерно; функция абсолютно непрерывна на периоде. Поэтому строго
\[
 E_{m,d}-E_{m,d}^{(J)}
 =d[R_J(t/d)F_d'(t)]_d^m
  -d\int_d^m R_J(t/d)F_d''(t)\,dt.                       \tag{12}
\]
Верхний край исчезает по (7), нижний сохраняется. Из (9),
\[
 \|F_d'(d)\|+\int_d^m\|F_d''(t)\|dt
 \le d^{-3/2}
 \left[2+\frac23(4+2D_1)+\frac49(3/2+2D_1+D_2)\right]
 =\mathfrak K_2d^{-3/2}.
\]
Использованы точные интегралы `int_d^∞t^(-5/2)=2/(3d^(3/2))` и `int_d^∞log(t/d)t^(-5/2)=4/(9d^(3/2))`. Это доказывает первую часть (11); `sum_{d>R}d^(-1/2)<=2sqrt m` — вторую. Ни μ-погашение, ни оценка Мертенса здесь не нужны. ∎

### 3.1. Ненулевой нижний край в бесконечном ряде

Для `B_2({x})={x}²-{x}+1/6` формула (5) также даёт точное
\[
 \boxed{
 E_{m,d}=-\frac{A_m(d)}{12}
        -\frac d2\int_d^m B_2(\{t/d\})F_d''(t)\,dt.
 }                                                        \tag{13}
\]
Отсутствие постоянной Fourier-моды у b1 **не означает** отсутствия арифметического нижнего края. Но и (13) нельзя разрывать без оплаты: интеграл может компенсировать этот край.

### 3.2. Цена усечения на исходном расписании

Далее разрешено выбрать `J=m²`. Это **вспомогательная аналитическая длина ряда**, не новый production cutoff и не предписание численно суммировать m² гармоник. При `M=floor(m^epsilon)`
\[
 \mathfrak K_2=O\bigl(1+m^{2\epsilon}/L^2\bigr),\qquad
 \frac{\mathfrak K_2\sqrt m}{\pi^2J}
 =O\bigl(m^{-3/2}+m^{-3/2+2\epsilon}/L^2\bigr).
 \tag{14}
\]
Для фиксированного `0<epsilon<1/32` это убывающая плата. Fourier-truncation полностью оплачен, но ещё ничего не сказано о низких сохранённых гармониках.

## 4. Точный reciprocal-объект с настоящими μ

**[FINITE_CELL | PAPER].** При `e(x)=exp(2πix)` зададим
\[
 S_0(h,t)=\sum_{R<d\le t}\mu(d)e(ht/d),\qquad
 S_1(h,t)=\sum_{R<d\le t}\mu(d)\log(t/d)e(ht/d).
 \tag{15}
\]
Суммы конечны, поскольку `t<=m`. Из (8),(10), с точной перестановкой,
\[
 \boxed{
 \mathcal E_{>R}^{(J)}
 =-\frac1\pi\sum_{h=1}^J\frac1h
 \int_R^m\left[
 \frac{A_m(t)}t\Im S_0(h,t)+A_m'(t)\Im S_1(h,t)
 \right]dt.
 }                                                        \tag{16}
\]
Это и есть проверяемая reciprocal-фаза. Гиперболический край сохранён как `d<=t`, а все исходные k уже содержатся в точном Euler-переходе (4). Для actual `W=PWP>=0, Tr W=1` берётся след **того же** равенства; ни один удобный вектор вместо W не выбирается.

## 5. Количественный тест: весь быстрый reciprocal-диапазон оплачивается

Это не гипотеза об арифметической случайности μ. Следующая оценка доказывается непосредственно из расстояния частот `h/d` после интегрирования по t. Именно здесь допустим коэффициентно-универсальный bound: его полученная цена будет предъявлена полностью.

### 5.1. Средний квадрат с настоящим движущимся краем

**Лемма 3 [ABSTRACT | PAPER].** Пусть D — целое положительное, `T>=D`, `T<U<=2T`, `h>=1`, а `|a_d|<=B`. Положим
\[
 S_a(t)=\sum_{D<d\le\min(2D,t)}a_d e(ht/d).
\]
Тогда
\[
 \boxed{
 \int_T^U|S_a(t)|^2dt
 \le B^2\left[TD+\frac{3D^3(1+\log D)}h\right].
 }                                                        \tag{17}
\]
В частности это верно для **буквальных** `a_d=mu(d)` и `a_d=mu(d)log(d/D)` с B=1.

**Доказательство.** Сохраняя все смешанные члены,
\[
 \int_T^U|S_a(t)|^2dt
 =\sum_{D<d,e\le2D}a_d\overline{a_e}
 \int_{\max(T,d,e)}^U e\bigl(ht(1/d-1/e)\bigr)dt,
 \tag{18}
\]
где интеграл равен нулю, если нижний край не меньше верхнего. Это **не** замена треугольной области прямоугольником.

Диагональ не больше `B²TD`. При `d!=e`
\[
 \left|\int_a^b e\bigl(ht(1/d-1/e)\bigr)dt\right|
 \le\frac1{\pi h|1/d-1/e|}
 \le\frac{4D^2}{\pi h|d-e|}.
\]
А
\[
 \sum_{D<d,e\le2D,\ d\ne e}\frac1{|d-e|}
 =2\sum_{v=1}^{D-1}\frac{D-v}{v}
 \le2D(1+\log D).
\]
Так как `8/pi<3`, получаем (17). Нет предположения о знаке cross terms: они оплачены точным интегралом фаз. ∎

### 5.2. Полное разбиение d,t,h

Пусть
\[
 D_a=2^aR,\quad a=0,\ldots,N_D-1,\qquad
 N_D=\lceil\log_2(m/R)\rceil.
\]
Делители лежат в `(D,2D]`, с нулевым продолжением за m. Для каждого D разбиваем t на
\[
 [T,\min(2T,m)],\quad T=2^jD,\quad j\ge0,\ T<m.
\]
В каждом tile сохраняется `d<=t`. Введём **выведенный из (17)** порог
\[
 H_{D,T}=\max\left\{1,\left\lceil\frac{D^2(1+\log D)}T\right\rceil\right\}.
 \tag{19}
\]
Быстрый сектор: `H_{D,T}<=h<=J`. Медленный: `1<=h<min(H_{D,T},J+1)`. Это полное разбиение, не удаление маленьких h.

В d-блоке обозначим через `S_{0,D}` сумму (15) только по `(D,2D]`, и
\[
 S_{\log,D}(h,t)=\sum_{D<d\le\min(2D,t)}\mu(d)\log(d/D)e(ht/d).
\]
Точно
\[
 S_{1,D}(h,t)=\log(t/D)S_{0,D}(h,t)-S_{\log,D}(h,t).
 \tag{20}
\]
Слагаемые с d>m нулевые автоматически, поскольку `t<=m`.

Пусть `E_fast^(J)` и `E_slow^(J)` — правая сторона (16) с указанными быстрыми и медленными диапазонами **в каждом tile**, соответственно. Все эти матрицы самосопряжены и поддержаны на исходном P.
\[
 \boxed{\mathcal E_{>R}=E_{\rm fast}^{(J)}+E_{\rm slow}^{(J)}+\mathcal R_J,\quad
 \|\mathcal R_J\|\le\mathfrak K_2\sqrt m/(\pi^2J).}         \tag{21}
\]

### 5.3. Оплата всех быстрых h, t, d и матричного возврата

**Теорема 4 [COFINAL_FAMILY | PAPER; конечная оценка для всех m,M,R,J].**
\[
 \boxed{
 \|E_{\rm fast}^{(J)}\|
 \le 32(1+D_1)N_D(1+\log J).
 }                                                        \tag{22}
\]

**Доказательство.** При `h>=H_{D,T}` правая сторона (17) не больше `4TD` для обоих коэффициентных наборов из (20). По Cauchy только в переменной t,
\[
 \int_T^{\min(2T,m)}|S_{0,D}|dt\le2T\sqrt D,
\]
\[
 \int_T^{\min(2T,m)}|S_{1,D}|dt
 \le2T\sqrt D\,[\log(2T/D)+1].
\]
Следовательно, полная норма t-интеграла в (16) для данного h,D,T не больше
\[
 [4+2(1+D_1)(\log(2T/D)+1)]\sqrt{D/T}
 \le8(1+D_1)(j+1)2^{-j/2}.
 \tag{23}
\]
Использованы только (6), `||A_m||<=2/sqrt t` и неизменённый P. Ни размерность, ни скрытая сумма по матричным элементам не добавлены.

Сумма коэффициентов `1/h` не больше `1+log J`; коэффициент перед ней в (16) — `1/pi`. Суммирование по j даёт
\[
 \sum_{j\ge0}(j+1)2^{-j/2}=(1-2^{-1/2})^{-2}<12.
\]
Поэтому для каждого D цена не больше `(96/pi)(1+D1)(1+log J)`, что меньше `32(1+D1)(1+log J)`. Суммирование N_D блоков доказывает (22). ∎

**[COFINAL_FAMILY | PAPER].** На исходном расписании `M=R=floor(m^epsilon)`, `J=m²`, для каждого фиксированного `epsilon>0` на позднем хвосте `M>=L`, поэтому
\[
 \boxed{\|E_{\rm fast}^{(m^2)}\|=O_\epsilon(m^\epsilon\log m).} \tag{24}
\]
Усреднялся t внутри одной исходной ячейки, **не** m и не заранее выбранный W. После (22) bound уже действует на все W одновременно. Здесь нет запрещённого обмена `sup_W` с усреднением.

Это настоящий оплаченный диапазон reciprocal-представления. Но он не использует специальное взаимное расположение знаков μ: в (17) было достаточно `|mu|<=1`. Поэтому его нельзя продлевать на медленный сектор словами «та же осцилляция».

## 6. Что именно остаётся: малые h и сопоставимые d,t

### 6.1. Легальный диапазон, который не является пустым хвостом

Для достаточно больших m выберем один исходный диадический D с
\[
 m/16<D\le m/8,
\]
что возможно при `R=m^epsilon`, `epsilon<1/32`. Возьмём его tile
\[
 T=4D,\qquad 4D\le t\le8D\le m.
\]
Тогда при `D<d<=2D`, `h=1`
\[
 2\le t/d<8,\qquad H_{D,T}\asymp D\log D.
 \tag{25}
\]
Следовательно, h=1 принадлежит **медленному**, а не оплаченному диапазону. Число оборотов этой фазы по d ограничено абсолютной постоянной независимо от m. В исходной дискретной сумме здесь есть настоящие k>=2; это не область `d>m/2`, где вся B тождественно нулевая.

Даже для неограниченных комплексных коэффициентов по модулю 1 нельзя иметь универсальный степенной выигрыш только от такого reciprocal-символа: при `t=4D`, `a_d=e(-4D/d)` каждый член равен 1. Это **контроль ложного коэффициентно-универсального импорта**, не контрпример для настоящих μ или CCM.

### 6.2. Точный actual-mu тест обычного prefix/Abel-импорта

**Лемма 5 [ABSTRACT | PAPER].** Для целого D положим
\[
 \mathfrak M_D=\sup_{D\le y\le2D}\left|\sum_{D<d\le y}\mu(d)\right|,
\]
\[
 \mathfrak S_D=\sup_{D\le y\le2D}\left|\sum_{D<d\le y}\mu(d)e(4D/d)\right|.
\]
Тогда
\[
 \boxed{
 (1+4\pi)^{-1}\mathfrak M_D\le\mathfrak S_D
 \le(1+4\pi)\mathfrak M_D.
 }                                                        \tag{26}
\]

**Доказательство.** У множителя `w(x)=e(4D/x)` модуль 1 и
\[
 \int_D^{2D}|w'(x)|dx
 =8\pi D\int_D^{2D}x^{-2}dx=4\pi.
\]
Конечное частичное суммирование сначала для μ с весом w, затем для μw с весом `conj(w)` даёт обе стороны. Это точное утверждение о тех же μ, без предположения о Мертенсе. ∎

То есть **uniform-prefix оценка** reciprocal-суммы в этом диапазоне не является автоматически более слабой или более осциллирующей задачей, чем соответствующая локальная сумма μ. Она лишь умножена на гладкий невырожденный вес с ограниченной вариацией.

Это не утверждает, что prefix-контроль необходим для исходной one-sided CCM: там может сработать совместный знак полного интеграла. Оно проверяет именно стандартный переход через максимумы частичных сумм, который иначе незаметно вставил бы новый Mertens supplier.

### 6.3. Полная цена низкой гармоники в таком подходе

Для `t/D` в фиксированном компакте из (25) та же формула Абеля, включая логарифмический множитель (20), даёт
\[
 |S_{0,D}(1,t)|+|S_{1,D}(1,t)|\le C\mathfrak M_D.
\]
С (6) полный t-интеграл h=1 оплачивается лишь ценой
\[
 \boxed{C(1+D_1)D^{-1/2}\mathfrak M_D.}                   \tag{27}
\]
Предположения `M_D<=D^theta` здесь нет. Если использовать только действительно доступную элементарную `M_D<=D`, цена (27) равна `O((1+Omega)sqrt D)`. В диапазоне `D` порядка m это несёт степень `1/2+epsilon`.

Для аудита предлагаемого внешнего результата: поставленная степень `theta` в таком prefix-импорте дала бы `theta-1/2+epsilon`. Простое `D^(1-sigma)` с небольшим sigma оставляет `1/2-sigma+epsilon`; оно не становится `eta(epsilon)->0`. Показатель `theta` около `1/2` не получен и **не принимается**.

Ни (27), ни сравнение показателей не являются нижней границей actual T или доказательством его большого размера. Это стоимость выбранного достаточного способа оценивания. Отрицательный вклад низкой гармоники мог бы быть полезен, а с C возможна дальнейшая компенсация.

## 7. Совместная сборка C+E: не превращаем искусственный сектор в «стену»

### 7.1. Проверка области без k>=2

Для каждого целого `d>m/2` в B возможен только `k=1`, причём `log1=0`. Поэтому
\[
 \boxed{B_{m,d}=0,\qquad C_m(d)+E_{m,d}=0.}              \tag{28}
\]
При чётном m равенство B=0 остаётся и для `d=m/2`, потому что второй атом имеет аргумент m и `Q_M(L)=0`.

Значит, назначать отдельную большую цену этому хвосту C и E и объявлять её неизбежной арифметической потерей было бы ошибкой. Формула (21) сохраняет отмену, хотя отдельные fast/slow/truncation куски могут быть ненулевыми.

### 7.2. Ближайшая непустая оболочка сохраняется буквально

При `m/3<d<=m/2` единственный ненулевой логарифмический вес — k=2:
\[
 B_{m,d}=\log2\,A_m(2d).
\]
Поэтому совместный вклад этой оболочки **ровно**
\[
 \boxed{
 \log2\sum_{m/3<d\le m/2}\mu(d)(2d)^{-1/2}
       P Q_M(\log(2d))P.
 }                                                        \tag{29}
\]
Верхний атом с `2d=m` нулевой по исходному ядру, а не удалён по аналогии. Здесь нет быстрого reciprocal-параметра, хотя оба C,E допускают бесконечное Fourier-раскрытие. При отдельном модульном оценивании (29) остаётся цена O(sqrt m). **Эта оболочка не назначается обязательной отдельной леммой:** остальные d могут её компенсировать.

### 7.3. Изменение переменной показывает место возвращения логарифмических фаз

На скалярной Mellin-компоненте `A_s(t)=t^(-s)` положим `F_{s,d}(t)=log(t/d)t^(-s)`. Тогда каждая Fourier-гармоника после полного t-интегрирования равна точно
\[
 -\frac1{\pi h}\int_d^m\sin(2\pi ht/d)F_{s,d}'(t)dt
 =-\frac{d^{-s}}{\pi h}\int_1^{m/d}
       \sin(2\pi hu)u^{-s-1}(1-s\log u)\,du.
 \tag{30}
\]
Это подстановка `t=du`, с сохранённым верхним краем `m/d`.

Все элементы буквального Q выражаются через `t^(-1/2±i omega_j)` и их первые s-производные; диагональ содержит ещё линейный множитель log t. Поэтому (30) описывает и их составные части, после линейной сборки и того же P. В интегрированном выражении новая Fourier-фаза стала фазой по u, а в d снова стоит настоящий Mellin-вес и изменяющийся cutoff. Из (30) не следует отсутствие возможной компенсации μ; следует только, что «появилась неразделимая e(ht/d), значит готовая биллинейная теорема даёт выигрыш» не является доказанным переносом.

### 7.4. Точный совместный Mellin-символ

**[ABSTRACT | PAPER].** Для `Re s>1` положим
\[
 U_R(s)=\sum_{d\le R}\mu(d)d^{-s},\qquad
 a_R(s)=\frac1{\zeta(s)}-U_R(s).
\]
Непрерывная мера C имеет плотность
\[
 c_R(t)=\sum_{R<d\le t}\frac{\mu(d)}d\log(t/d),
\]
а дискретная B — атомы
\[
 \ell_R(n)=\sum_{d\mid n,\ d>R}\mu(d)\log(n/d).
\]
Абсолютная сходимость разрешает конечный-to-infinite diagnostic transfer и даёт
\[
 \boxed{\int_1^\infty c_R(t)t^{-s}dt=\frac{a_R(s)}{(s-1)^2},} \tag{31}
\]
\[
 \boxed{\sum_{n\ge1}\ell_R(n)n^{-s}=-\zeta'(s)a_R(s).}       \tag{32}
\]
Разность мер E имеет символ
\[
 \boxed{\left[-\zeta'(s)-\frac1{(s-1)^2}\right]a_R(s).}      \tag{33}
\]
Квадратная скобка целая: двойной полюс `-zeta'` в s=1 вычтен. Но после сборки C+E получаем
\[
 \boxed{-\frac{\zeta'}{\zeta}(s)+\zeta'(s)U_R(s),}          \tag{34}
\]
то есть исходный полный логарифмически взвешенный Möbius-объект с коэффициентом 1, а не его улучшенную версию.

Для сверки непосредственно с матрицей определим
\[
 v_\pm(z)_j=(z\pm i\omega_j)^{-1},\quad
 \mathsf S_P(z)=P\left[\frac1L\sum_{\pm}v_\pm(z)v_\pm(z)^{\mathsf T}\right]P.
\]
Обратное преобразование Лапласа двух простых резольвент, вычисленное в `L-log n`, даёт ровно (1); вне `n<=m` оно нулевое. Поэтому на правой прямой `Re z=c>1/2`
\[
 T_{>R}=\frac1{2\pi i}\int_{(c)}m^z
 \left[-\frac{\zeta'}{\zeta}(1/2+z)+\zeta'(1/2+z)U_R(1/2+z)\right]
 \mathsf S_P(z)\,dz.                                    \tag{35}
\]
Та же формула отдельно с (31),(33) даёт C,E. Это source-return на области абсолютной сходимости; **контур через неизвестные нули не сдвигался**. Транспонирование в `vv^T` не заменяется `vv*`, и положительность actual W не превращает аналитическое выражение `Tr(W S_P(z))` в неотрицательное.

У любого гипотетического нетривиального нуля ρ кратности k символ (34) имеет residue `-k`. При простом нуле residues отдельных C,E равны
\[
 \frac{1}{(\rho-1)^2\zeta'(\rho)},\qquad
 -1-\frac{1}{(\rho-1)^2\zeta'(\rho)},
\]
и складываются в -1. При кратном нуле высшие полюсные части отдельных слагаемых также сокращаются только совместно. Это не заявление о существовании внепрямого нуля и не запрет нового знакового аргумента. Это точная проверка: Fourier-раскрытие E не устраняет исходную нулевую арифметику автоматически.

## 8. Полный количественный возврат к CCM

### 8.1. Оплаченный результат новой репрезентации

Определим **совместный** остаток
\[
 \mathcal V_{m,R,J}=\mathcal C_{>R}+E_{\rm slow}^{(J)}.
\]
Из (21),(22) получено реальное, полностью оценённое сравнение
\[
 \boxed{T_{>R}=\mathcal V_{m,R,J}+E_{\rm fast}^{(J)}+\mathcal R_J,} \tag{36}
\]
\[
 \boxed{
 \|T_{>R}-\mathcal V_{m,R,J}\|
 \le 32(1+D_1)N_D(1+\log J)+\frac{\mathfrak K_2\sqrt m}{\pi^2J}.
 }                                                        \tag{37}
\]
Это не объявляется малостью V. При `J=m²` разность оплачена `O_epsilon(m^epsilon log m)`.

Для всех actual W одновременно:
\[
 \operatorname{Tr}(WT_{>R})\le\operatorname{Tr}(W\mathcal V_{m,R,m^2})
 +32(1+D_1)N_D(1+2L)+\frac{\mathfrak K_2}{\pi^2m^{3/2}}.
 \tag{38}
\]
Сохраняется полезная отрицательная часть V; не требуется малая норма V в качестве обязательного интерфейса.

### 8.2. Фактически получаемая полная граница без новых предпосылок

Из принятого `||C_m(d)||<=20/sqrt d`:
\[
 \|\mathcal C_{>R}\|\le40\sqrt m.
\]
Из (5),(8), `|b_1|<=1/2` и точных интегралов
\[
 \int_d^\infty t^{-3/2}dt=2/\sqrt d,\qquad
 \int_d^\infty\log(t/d)t^{-3/2}dt=4/\sqrt d
\]
следует
\[
 \|E_{m,d}\|\le(4+2D_1)/\sqrt d,\qquad
 \|\mathcal E_{>R}\|\le(8+4D_1)\sqrt m.
\]
Итак, без непоставленного μ-входа полный one-sided bound не лучше
\[
 \boxed{T_{>R}\preceq(48+4D_1)\sqrt m\,P.}              \tag{39}
\]
Он сохраняет степень `1/2+epsilon`, если считать производную через D1. Даже более грубое исходное оценивание до Euler даёт асимптотически лучшую для фиксированной epsilon альтернативу
\[
 \boxed{\|T_{>R}\|\le4\sqrt m\,L(1+L).}                \tag{40}
\]
Действительно,
\[
 2\sum_{d>R}d^{-1/2}\sum_{k\le m/d}\frac{\log k}{\sqrt k}
 \le4\sqrt m\sum_{d>R}\frac{\log(m/d)}d
 \le4\sqrt m\,L(1+L).
\]
Поэтому честный элементарный полный конверт — минимум (39),(40), а не рекламирование новой производной платы как улучшения. Его фиксированная степень 1/2 хуже сохранённой условной Q10 степени 3/8.

**Все высокие h и truncation можно сделать дешёвыми, но это не делает низкие h и C малыми.** В Q02 не получено ни smaller full exponent, ни `eta(epsilon)->0`.

### 8.3. Малые делители и архимедова часть

Пакет сохраняет
\[
 b_{\rm small}=(56+32\Omega)\sqrt R+12(1+\log R)^2,
\]
\[
 PK_mP=P(A_{\rm arch}-c_AI)P-(T_{\le R}+T_{>R}),\quad
 \|A_{\rm arch}-c_AI\|\le50L+8.
\]
Следовательно, если обозначить **действительно доказанную** полную цену из (39),(40) через a_m,
\[
 \boxed{PK_mP\succeq-[a_m+b_{\rm small}+50L+8]P.}        \tag{41}
\]
Малоделительная плата добавлена один раз. На `M=R=m^epsilon` её степень — `3epsilon/2`, fast-return — `epsilon` с логарифмом, truncation убывает. Но a_m сохраняет 1/2: (41) не закрывает sparse consumer.

Если в будущем будет **доказана**, а не предположена, верхняя оценка V с показателем `eta_0(epsilon)->0`, то (38),(41) дали бы полный показатель `max(eta_0(epsilon),3epsilon/2)+o(1)`. Это лишь чтение уже рассчитанного бюджета. **Ни одна часть результата Q02 не использует такую оценку V как предпосылку.**

Новый кофинальный по m результат тоже не получен. t-усреднение в (17) не выбирает хорошую m-ячейку и не заменяет доказательство необходимой неограниченной подпоследовательности.

## 9. Точная граница неудачи и разрешённый откат

**Неудачен прямой импорт:** «фаза e(ht/d) неразделима, поэтому можно применить осцилляторную оценку ко всей Euler-ошибке и получить полный выигрыш». Расчёт (17)–(25) показывает, где такой импорт действительно работает и где его собственный параметр перестаёт быть большим.

**Не опровергнуты:** actual one-sided T; возможность совместной компенсации C+E_slow; вся reciprocal-методология; RH. Ни пример с произвольными коэффициентами, ни сравнение верхних цен не дают lower bound для настоящей матрицы.

**Самая ранняя оставшаяся потеря:** модульное оценивание медленных d-сумм/их prefix maximum отдельно от C и от фактического матричного множителя. Точная отмена (28) показывает, почему этот разрыв может быть искусственным. Разложения (29),(34) показывают, что одна алгебраическая пересборка одновременно не устраняет все непустые арифметические вклады.

Перед новыми вычислениями оставляем ровно два источниковых представления, не два обязательных новых предположения:

| Представление | Что сохранено | Решающий тест / цена | Риск |
|---|---|---|---|
| **V=C+E_slow до модулей**, с уже оплаченной (37) | Все μ, t,d-края, actual P,W; только нужная верхняя сторона | Высокая диагностическая сила; низкая цена проверки (37), высокая/неизвестная цена нового signed bound | Объявить prefix-Mertens bound фактом либо потерять C |
| **Совместный Mellin-symbol (34)–(35)** | Все prime powers, log-вес, полный causal return и analytic square | Высокая сила против фиктивного исчезновения полюсов; низкая цена точной алгебры | Сдвинуть контур через нули без residue/горизонтальной оплаты |

Первое представление — точка отката выбранной попытки; второе — её независимая проверка. Не предлагается очередной момент, PySR или новая платформа. Само имя V не считается прогрессом; количественный результат здесь только (11),(22),(37) и граница применимости импорта.

## 10. Дискриминаторы, проверки и область сертификатов

**DISCRIMINATOR для полного источника.** Для закреплённых `K,eta,m0,epsilon` проверяем на `m>=m0` запас
\[
 K m^\eta-\lambda_{\max}(T_{>R}|_{\operatorname{ran}P}).
\]
Нижняя интервальная граница `>=0` принимает только законную конечную ячейку; верхняя `<0` отвергает только этот контракт. Интервал, содержащий ноль, требует более высокой точности или точного источникового аргумента. Ни eventual-старт, ни константа не подбираются после проверки.

**DISCRIMINATOR для нового fast-bound.** Первое проверяемое место — (18) с нижним концом `max(T,d,e)`, затем (12) с нижним производным краем. Удаление этих членов — намеренная ошибка контрольного стенда. Согласие нескольких чисел не заменяет общий вывод.

Выполнено 1580 точных рациональных контролей, описанных в приложении A. Они проверяют Euler/B2-алгебру на полиномиальных тестовых F, μ-сборку и **истинную целочисленную поддержку** k. Полиномы не выдаются за actual CCM-ядро. 63 ненулевых случая обнаруживают преднамеренную смену Euler-знака. Проверены ненулевые нижние края и отмена C+E на пустой k-области.

Отдельно выполнено шесть небольших **неинтервальных** 45-значных диагностик настоящих μ reciprocal-сумм: endpoint-exact парный интеграл (18) сравнен с независимой покусочной квадратурой. Максимальное расхождение в записанных случаях меньше `9e-44`; это численное согласие, не доказательство точного нуля и не Arb-сертификат. Все шесть значений лежат под (17). Доказательством (17) остаётся §5.1.

Новых вычислений спектра CCM, Lean, Arb и независимого внешнего аудита нет. Ничего в репозиторий не записывалось.

## 11. Ledger, зависимости и closeout

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| S | Буквальные P,Q, continuous и short/arch returns | COFINAL_FAMILY | PAPER | Приняты из Q02 в их области |
| F1 | Дополнительный projected endpoint A'_m(m)=0 и derivative bounds | COFINAL_FAMILY | PAPER | Доказаны по буквальным элементам |
| F2 | Конечный Fourier-return с полной ошибкой (11) | COFINAL_FAMILY | PAPER | Доказан |
| R1 | Mean-square reciprocal bound с движущимся cutoff (17) | ABSTRACT | PAPER | Доказан; generic coefficients allowed only in this bound |
| R2 | Весь fast-sector (22), цена (24) | COFINAL_FAMILY | PAPER | Доказан; auxiliary range only |
| L1 | Prefix comparability для настоящих μ (26) | ABSTRACT | PAPER | Доказана; не нижняя граница actual T |
| J1 | Точная сборка C+E, непустая оболочка и symbol (28)–(35) | ABSTRACT | PAPER | Доказаны; нового знака нет |
| C1 | Полный источник, новый parameter-proportional показатель | COFINAL_FAMILY | CONDITIONAL | OPEN; не предпосылка результата |
| C2 | Новая кофинальная m-оценка | COFINAL_FAMILY | CONDITIONAL | Не получена |
| Q10 | Лучший унаследованный полный показатель 3/8 | COFINAL_FAMILY | CONDITIONAL | ZF78, без улучшения и без нового Mertens импорта |
| T1 | Рациональные и небольшие numerical controls | FINITE_CELL | PAPER | Алгебра/диагностика, не actual spectral certificate |

**DOWNSTREAM_CONSUMER:** отдельный sparse-band off-critical witness receiver, исходная полная CCM с N=m. **ACTUAL_CONSUMER_REQUIREMENT:** одна верхняя оценка T с `eta(epsilon)->0`, eventual или доказанно cofinal. **ORIGINAL_REQUESTED_OBJECT:** количественная проверка reciprocal-фазы в exact Euler error с C+E return. **ORIGINAL_OBJECT_IS:** UNKNOWN как необходимый для любого решения; этот инструмент лишь кандидат. **KNOWN_WEAKER_INTERFACES:** прямая one-sided совместная оценка V или T без prefix maxima, без нормы E отдельно и без квадратного trace. **FAILURE_TYPE:** NO_DERIVATION для actual slow-plus-continuous estimate. **EPISTEMIC_STATUS:** RESEARCH_DEBT. **NOVELTY_AXIS:** оплаченный полный high-h sector и Fourier-tail; точный slow-range audit, не новая CF22/SP/RH степень. **REOPEN_TRIGGER:** настоящий upper sign для V на исходном P с показателем ниже прежнего полного 3/8 или стремящимся к нулю; доказанный другой совместный source mechanism с меньшим полным бюджетом. **MATHEMATICALLY_DEAD:** не заявлено ни для actual цели, ни для reciprocal-семейства.

**Что стало меньше:** весь быстро осциллирующий retained Fourier-range и хвост имеют явную малую цену, равномерную по actual W. **Что не стало меньше:** лучший доказанный полный показатель. **Что запрещено повторять:** переносить высокочастотный bound на h=1,t~d; занулять C; удалять нижний Bernoulli-край; объявлять Fourier zero-mode cancellation исчезновением исходного prime/log-derivative symbol; оплаченный быстрый сектор называть закрытием sparse receiver.

**Судьба прогнозов:** Euler/B2, lower boundary, empty-k cancellation и k=2 support подтверждены бумажными равенствами и exact controls. Независимая квадратура подтвердила численное согласие (18) в шести контрольных случаях, не универсальную μ-оценку. Прогноз нового полного показателя не регистрировался; показатель не получен.

```yaml
MEMORY_ENTRY:
  iteration: CCM_RECIPROCAL_ERROR_Q02_2026_10_20
  target: ACTUAL_LONG_DIVISOR_ONE_SIDED_SPARSE_BOUND
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  paid_range: h>=ceil(D^2*(1+log D)/T), plus controlled h>m^2 Fourier tail
  unpaid_object: C_gtR_plus_E_slow_on_actual_P
  failed_strategy: Treat reciprocal nonseparability as a uniform oscillation gain at low h and t comparable to d
  invariant_learned: C and Euler error cancel exactly on empty-k shells; low reciprocal prefix norms retain actual local Mobius difficulty
  forbidden_future_move: Replace the slow-range arithmetic by an assumed Mertens power or spend the fast-range bound on the whole source
  consumer_progress: NO_NEW_COMPLETE_EXPONENT
  route_family_death: NOT_ESTABLISHED
```

## 12. Одна CODEX DIRECTIVE

**Независимо проверить один пакет Q02:** (7),(11),(17),(22),(37), с буквальными частотами и P, нижним производным краем, движущимся `d<=t`, всеми h- и t-платами. Сверить конечные равенства (28)–(34), чтобы исключить ложный кредит от разделения C и E. Воспроизвести точный рациональный стенд и отдельно неинтервальную диагностику из приложений, не повышая их до спектрального сертификата. Приёмка означает только оплату fast-sector и законность Fourier-return. **Не принимать** оценку V, Mertens supplier, новый полный показатель или RH. Если в (17)/(22) дефект — вернуть первый неверный шаг и восстановленную цену; если дефекта нет — зафиксировать исходную медленную совместную форму, без автоматического нового широкого запуска.

## 13. Источники и воспроизведение

Основной источник: авторитетный Q02 TXT, SHA-256 из заголовка. В индексированной копии: строки 14–38 — новый контракт; 48–139 — собственный continuous/floor тест; 284–346 — ограниченная приёмка Q01; 430–496 — источник и возврат; 606–677 — принятый полный k-return; 1381–1451 — sparse receiver; 1454–1518 — границы усиленного scalar supplier. Нумерация индексированной копии и число LF сырого UTF-8 могут отличаться на одну завершающую пустую строку.

Первичные внешние ссылки, использованные только для нормировок:
```text
NIST DLMF 24.8, Fourier series for periodic Bernoulli B1 and B2:
https://dlmf.nist.gov/24.8
NIST DLMF 27.4, reciprocal zeta and Dirichlet series:
https://dlmf.nist.gov/27.4
```
Все источниковые и новые оценки, фактически использованные здесь, изложены в тексте. Эти ссылки не являются поставщиками требуемой low-h μ-компенсации.

## Приложение A. Точный локальный проверяющий

Сохранить следующий блок как `check_q02.py` и выполнить `python3 check_q02.py`. **Подстановок переменных или путей нет**: выходной JSON записывается рядом с самим скриптом. Стандартная библиотека Python; никакие файлы проекта не меняются. Полиномиальные F — только проверка Euler-алгебры, не замена CCM.

```python
"""Exact consistency checks for Q02. These are not CCM spectral certificates."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import hashlib
import json


def trim(a):
    a=list(map(F,a))
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return trim(c)

def scale(q,a): return trim([F(q)*x for x in a])

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)

def deriv(a):return trim([i*a[i] for i in range(1,len(a))] or [0])

def val(a,x):return sum(v*F(x)**i for i,v in enumerate(a))

def integ(a,lo,hi):return sum(x*(F(hi)**(i+1)-F(lo)**(i+1))/F(i+1) for i,x in enumerate(a))

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
        p+=1
    return -s if n>1 else s

stats=Counter();samples=[];rejected=0
for m in (6,9,12,17,24):
    rows={}
    for d in range(1,m+1):
        # Lower value and upper value/derivative vanish exactly.
        f=scale(F(1,m**3),mul([-d,1],mul([m,-1],[m,-1])))
        fp=deriv(f);fpp=deriv(fp)
        assert val(f,d)==val(f,m)==val(fp,m)==0
        stats['endpoint_contracts']+=1
        discrete=sum(val(f,d*k) for k in range(1,m//d+1))
        cont=integ(f,d,m)/d
        err=discrete-cont
        beta_int=F(0);center_int=F(0);b2_int=F(0)
        for k in range(1,m//d+1):
            lo=max(d,k*d);hi=min(m,(k+1)*d)
            if lo>=hi:continue
            beta=[F(k),-F(1,d)]
            b1=[-F(k)-F(1,2),F(1,d)]
            b2=[F(k*k+k)+F(1,6),-F(2*k+1,d),F(1,d*d)]
            beta_int-=integ(mul(beta,fp),lo,hi)
            center_int+=integ(mul(b1,fp),lo,hi)
            b2_int+=integ(mul(b2,fpp),lo,hi)
        bernoulli=-F(d,12)*val(fp,d)-F(d,2)*b2_int
        assert err==beta_int==center_int==bernoulli
        stats['euler_centered_bernoulli_equalities']+=1
        if err:
            assert -center_int!=err
            rejected+=1
        rows[d]=(discrete,cont,err)
        if m%d==0:
            assert b2_int==0
            assert err==-F(d,12)*val(fp,d)
            stats['lower_boundary_nonoscillatory_controls']+=1
    for R in (1,2,3):
        if R>=m:continue
        B=sum(mu(d)*rows[d][0] for d in range(R+1,m+1))
        C=sum(mu(d)*rows[d][1] for d in range(R+1,m+1))
        E=sum(mu(d)*rows[d][2] for d in range(R+1,m+1))
        assert B==C+E
        stats['actual_mu_signed_euler_reassemblies']+=1
        if len(samples)<3:samples.append({'m':m,'R':R,'B':str(B),'C':str(C),'E':str(E)})

# Actual source combinatorial support: k=1 carries log(1)=0.
for m in range(6,65):
    for d in range(1,m+1):
        nonzero_k=list(range(2,m//d+1))
        if 2*d>m:
            assert not nonzero_k
            stats['empty_full_k_shell']+=1
        if 3*d>m and 2*d<=m:
            assert nonzero_k==[2]
            stats['exact_k2_shell']+=1

# Endpoint derivative is -2/L times the all-ones matrix; P b = 0 kills it.
for M in range(1,7):
    n=2*M+1
    P=[[F(i==j)-F(1,n) for j in range(n)] for i in range(n)]
    one=[F(1)]*n
    assert all(sum(P[i][j]*one[j] for j in range(n))==0 for i in range(n))
    for j in range(-M,M+1):
        for k in range(-M,M+1):
            coefficient=F(-2) if j==k else F(2*(k-j),j-k)
            assert coefficient==-2
    stats['projected_upper_derivative_controls']+=1

# Exact coefficients in the second-derivative truncation budget.
for D1,D2 in ((F(0),F(0)),(F(1),F(3)),(F(7,2),F(23,4))):
    K2=F(3,2)+2*D1+D2
    derived=2+F(2,3)*(4+2*D1)+F(4,9)*K2
    stated=F(16,3)+F(20,9)*D1+F(4,9)*D2
    assert derived==stated
    stats['fourier_tail_constant_algebra']+=1

# The centered k-free reciprocal kernel for a scalar Mellin monomial.
# Euler identity alone does not permit erasing the continuous term.
assert any(c!=0 and e!=0 for _,c,e in rows.values())
stats['delete_continuous_term_rejected']+=1

out={
 'status':'PASS', 'scope':'finite exact algebra; synthetic smooth kernels and actual integer mu; not CCM sign certificates',
 'counts':dict(stats),'total_checks':sum(stats.values()),
 'wrong_euler_sign_detected_cases':rejected,'signed_reassembly_samples':samples,
 'new_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

### Фактический результат

```json
{
  "status": "PASS",
  "scope": "finite exact algebra; synthetic smooth kernels and actual integer mu; not CCM sign certificates",
  "counts": {
    "endpoint_contracts": 68,
    "euler_centered_bernoulli_equalities": 68,
    "lower_boundary_nonoscillatory_controls": 23,
    "actual_mu_signed_euler_reassemblies": 15,
    "exact_k2_shell": 349,
    "empty_full_k_shell": 1047,
    "projected_upper_derivative_controls": 6,
    "fourier_tail_constant_algebra": 3,
    "delete_continuous_term_rejected": 1
  },
  "total_checks": 1580,
  "wrong_euler_sign_detected_cases": 63,
  "signed_reassembly_samples": [
    {
      "m": 6,
      "R": 1,
      "B": "-1/27",
      "C": "-97/1620",
      "E": "37/1620"
    },
    {
      "m": 6,
      "R": 2,
      "B": "0",
      "C": "-17/1620",
      "E": "17/1620"
    },
    {
      "m": 6,
      "R": 3,
      "B": "0",
      "C": "-1/12960",
      "E": "1/12960"
    }
  ],
  "new_ccm_spectral_runs": 0,
  "arb_runs": 0,
  "lean_runs": 0,
  "script_sha256": "51b72bf2a6f278e9be86003105105fb0afd8798e9af9ffe426a6dd935d3bab2d"
}
```

## Приложение B. Малые неинтервальные reciprocal-диагностики

Следующий скрипт использует `mpmath` и 45 десятичных знаков. Он сравнивает парный интеграл с покусочной квадратурой; **не** сертифицирует интервальный знак и **не** вычисляет собственные значения CCM. Подстановок путей нет.

```python
"""Small non-interval diagnostics only: literal mu, not CCM spectral values."""
import mpmath as mp
from pathlib import Path
import json
mp.mp.dps=45

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
        p+=1
    return -s if n>1 else s

def exact_pair_integral(D,T,h,log_weight):
    out=mp.mpc(0)
    for d in range(D+1,2*D+1):
        a=mu(d)*(mp.log(mp.mpf(d)/D) if log_weight else 1)
        for e in range(D+1,2*D+1):
            b=mu(e)*(mp.log(mp.mpf(e)/D) if log_weight else 1)
            lo=max(T,d,e);hi=2*T
            if lo>=hi:continue
            if d==e:I=mp.mpf(hi-lo)
            else:
                w=2*mp.pi*h*(mp.mpf(1)/d-mp.mpf(1)/e)
                I=(mp.exp(1j*w*hi)-mp.exp(1j*w*lo))/(1j*w)
            out+=a*b*I
    assert abs(mp.im(out))<mp.mpf('1e-35')
    return mp.re(out)

rows=[]
for D,T,h,log_weight in [(4,4,1,False),(4,4,8,True),(8,8,3,False),(8,32,1,True),(12,24,20,False),(12,12,6,True)]:
    exact=exact_pair_integral(D,T,h,log_weight)
    def f(t):
        s=sum(mu(d)*(mp.log(mp.mpf(d)/D) if log_weight else 1)*mp.exp(2j*mp.pi*h*t/d)
              for d in range(D+1,2*D+1) if d<=t)
        return abs(s)**2
    cuts=sorted(set([T,2*T]+[d for d in range(D+1,2*D+1) if T<d<2*T]))
    numeric=sum(mp.quad(f,[a,b]) for a,b in zip(cuts,cuts[1:]))
    difference=abs(exact-numeric)
    bound=T*D+3*D**3*(1+mp.log(D))/h
    assert difference<mp.mpf('1e-30')
    assert exact<=bound
    rows.append({'D':D,'T':T,'h':h,'log_weight':log_weight,
                 'integral':mp.nstr(exact,22),'analytic_minus_quad_abs':mp.nstr(difference,5),
                 'proved_bound':mp.nstr(bound,22)})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'precision_decimal':45,'rows':rows}
Path(__file__).with_name('reciprocal_diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

### Фактический результат

```json
{
  "status": "PASS_DIAGNOSTIC_NOT_INTERVAL",
  "cases": 6,
  "precision_decimal": 45,
  "rows": [
    {
      "D": 4,
      "T": 4,
      "h": 1,
      "log_weight": false,
      "integral": "2.9257029669428583633",
      "analytic_minus_quad_abs": "2.4523e-45",
      "proved_bound": "474.1685173350189988162"
    },
    {
      "D": 4,
      "T": 4,
      "h": 8,
      "log_weight": true,
      "integral": "0.8772523427314543645841",
      "analytic_minus_quad_abs": "2.1019e-45",
      "proved_bound": "73.27106466687737485203"
    },
    {
      "D": 8,
      "T": 8,
      "h": 3,
      "log_weight": false,
      "integral": "8.804479516864968115895",
      "analytic_minus_quad_abs": "1.4013e-45",
      "proved_bound": "1640.674069340075995265"
    },
    {
      "D": 8,
      "T": 32,
      "h": 1,
      "log_weight": true,
      "integral": "47.47307450608847886945",
      "analytic_minus_quad_abs": "5.0447e-44",
      "proved_bound": "4986.022208020227985795"
    },
    {
      "D": 12,
      "T": 24,
      "h": 20,
      "log_weight": false,
      "integral": "191.3199226064480155972",
      "analytic_minus_quad_abs": "8.9683e-44",
      "proved_bound": "1191.287803625049680412"
    },
    {
      "D": 12,
      "T": 12,
      "h": 6,
      "log_weight": true,
      "integral": "4.608453009299622088598",
      "analytic_minus_quad_abs": "2.8026e-45",
      "proved_bound": "3154.959345416832268038"
    }
  ]
}
```

## Приложение C. Регистрация локальных проверок

```json
{
  "request": "PROSHKA_CCM_RECIPROCAL_ERROR_Q02_2026-10-20.txt",
  "request_sha256": "21893c097ed643fef7c99ff9dbd148c0e05563da617a45dfe439063e6ef61198",
  "scope": "paper feasibility attempt; no actual CCM numerical spectral claims",
  "predictions_before_local_checks": [
    "Euler discrepancy equals centered sawtooth integral with the stated sign and both endpoints.",
    "One integration by parts through the periodic Bernoulli B2 primitive retains the lower derivative boundary.",
    "Deleting C or its cancellation with E is detected on d>m/2; B is exactly zero there.",
    "The actual k=2 shell m/3<d<=m/2 survives the full C+E return.",
    "The full reciprocal expansion retains actual mu and a low-frequency range; no new full exponent is predicted."
  ],
  "computations_authorized": "finite rational/symbolic consistency checks only; no large scan, no PySR, no Lean or Arb claim",
  "additional_diagnostics_registered_before_run": [
    "For finitely many small reciprocal sums with literal mu, endpoint-exact pair integration equals independent piecewise quadrature.",
    "Their numerical squared integrals do not exceed the proved TD+3D^3(1+log D)/h upper bound; this is a diagnostic, not an interval certificate."
  ]
}
```
