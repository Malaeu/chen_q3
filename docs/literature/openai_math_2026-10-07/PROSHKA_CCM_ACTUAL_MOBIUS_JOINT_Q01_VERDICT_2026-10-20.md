# STATUS: TRY_CCM_ACTUAL_MOBIUS_JOINT_CANCELLATION
```yaml
OPERATIVE_CLASS: TRY_CCM_ACTUAL_MOBIUS_JOINT_CANCELLATION
VERDICT_CODE: FULL_K_RECOMBINATION_PAYS_CORRELATION_DIAGONAL_OFFDIAGONAL_OPEN
DATE: 2026-10-20
REQUEST_FILE: PROSHKA_CCM_ACTUAL_MOBIUS_JOINT_Q01_2026-10-20.txt
REQUEST_BYTES: 138159
REQUEST_RAW_LINES: 1823
REQUEST_SHA256: 6f6349f862f6aa450d8b2017ac010bed08f4860f14b10bcd5e455311d21f334d
REQUEST_READ: COMPLETE_INCLUDING_ALL_NINE_EMBEDDED_SOURCE_BLOCKS
SOURCE_COMMIT_AS_SUPPLIED: c6f9d2b79e9f660b604d7f83818807ff7dd824d9
BOOTSTRAP_REPOSITORY: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: LITERAL_FULL_CCM_N_EQUALS_M_WITH_ORIGINAL_CONSTRAINED_SPARSE_BAND
TERMINAL_CONSUMER: SEPARATE_SPARSE_BAND_OFF_CRITICAL_WITNESS_RECEIVER
ADJUDICATION: INCONCLUSIVE_FOR_NEW_ARITHMETIC_POWER_GAIN
NEW_PARAMETER_PROPORTIONAL_SOURCE_BOUND: NOT_PROVED
NEW_STRICTLY_BETTER_COMPLETE_EXPONENT: NOT_OBTAINED
NEW_PAPER_RESULTS:
  - Uniform full-k single-divisor bound ||B_m,d|| <= (40+16 Omega_M)/sqrt(d)
  - Exact noncommutative Fejer correlation with actual Mobius coefficients
  - All k,kprime and divisor cross terms retained before inequalities
  - Correlation diagonal paid at parameter-proportional cost
  - Calculated cofinal scalar averaged-correlation receiver with exponent 2 epsilon
UNPAID_ARITHMETIC:
  - Signed off-diagonal correlation with literal compressed kernels
  - Its stated cofinal averaged trace bound is a candidate, not an input
ZF78_USE: COMPARISON_ONLY_INHERITED_CONDITIONAL_Q10_BOUND
BEST_INHERITED_COMPLETE_BOUND: O(m^(3/8)*(log m)^2*log(3 log m)), conditional on supplied ZF78
FULL_SP: OPEN_NOT_CLAIMED
G1_G3: OPEN_NOT_CLAIMED
RH: NOT_PROVED
PX_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
LEAN_RUNS: 0
ARB_RUNS: 0
NEW_CCM_NUMERICAL_EVALUATIONS: 0
FINAL_EXACT_CONTROL_COUNT: 7021
FINAL_EXACT_CONTROL_STATUS: PASS
EXPLORATORY_EXTRA_ASSERTION: FAILED_AND_RECORDED_NOT_RETROACTIVELY_CERTIFIED
INDEPENDENT_REVIEW: NOT_RUN
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CONSUMER_PROGRESS: NO_NEW_EXPONENT
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE_FOR_ACTUAL_CCM_TARGET
```

Ы. **Попытка выполнена. Новый показатель для полной исходной матрицы не получен.** Получена более экономная корреляционная постановка: до возведения в квадрат надо собрать **все** внутренние индексы `k` при каждом делителе `d`. Исходные три ограничения тогда оплачивают весь отдельный `d`-оператор с ценой `(40+16 Omega_M)/sqrt(d)`. Поэтому диагональная часть последующего второго момента имеет параметр-пропорциональную цену. Неоценённой остаётся точно выписанная совместная корреляция разных настоящих коэффициентов Мёбиуса.

Расчёт не использует предполагаемую малость коротких корреляций, RH-эквивалентный all-prefix supplier или положительность сжатых произведений. Условная граница Q10 с показателем `3/8` не повышается до безусловного результата и не называется новой. Ниже дан полный возврат и один рассчитанный вариант отступления к кофинальному усреднению, в котором адаптивность максимального собственного значения сохранена.

## 0. Источник, граница чтения и зарегистрированные проверки

**[ABSTRACT | PAPER — происхождение].** Авторитетен верхний запрос, строки 1–23 приложенного TXT. Исторические директивы внутри девяти приложений не исполняются как новые задания. Прочитан весь UTF-8-файл, включая:

1. sparse-band receiver;
2. restricted-prime receiver;
3. fixed-prime compression test и Q1–Q3;
4. long-Mobius primitive test;
5. Q10 conclusion;
6. полный Q10 verdict;
7. weighted-LCM return;
8. C5 signed-core attempt;
9. cancellation-literature audit.

Контроль байтов, SHA-256 и число строк относятся к фактически смонтированному файлу, а не к предположению по его имени. Указанный commit принят как pin запроса; новое состояние репозитория, Comparator и транзитивные Lean-зависимости не пересертифицировались.

Зафиксированы до локальных тестов: точное совпадение диадической сборки; точное некоммутативное оконное тождество; gcd-формула для настоящих `mu(d)mu(e)`; обнаружение преднамеренно удалённого смешанного члена/общей маски. **Прогноз успешного нового показателя не регистрировался.**

Внешняя сверка ограничена DLMF §27.5 для `Lambda=mu*log` и авторским изложением принципа van der Corput/Cauchy у Tao. Нужная конечная матричная версия доказывается здесь, а не импортируется из теоремы для другой фазы. Ни один внешний результат об асимптотической малости корреляций Мёбиуса не принят.

## 1. Неизменённый источник и потребитель

**[FINITE_CELL | PAPER — определения из TXT, §§2,4 вложенного Q10].** Для целого `m>=4`:

\[
 L=\log m,\qquad \omega_j=2\pi j/L,\qquad
 \Omega=2\pi M/L,\qquad 1\le M\le m,
\]

\[
 Fe_j(t)=L^{-1/2}e^{i\omega_jt}\mathbf1_{[0,L]}(t).
\]

`P` — прежний ортогональный проектор в полосе `|j|<=M` на три условия `b*c=v_+*c=v_-*c=0`, с нулевым дополнением в исходное пространство `|j|<=m`. Для всех последующих преобразований при данном `m` он фиксирован. Частоты остаются `2 pi j/log m`, не `2 pi j/log M`.

\[
 Q_M(s)_{jk}=\begin{cases}
 2(1-s/L)\cos(\omega_js),&j=k,\\
 [\sin(\omega_ks)-\sin(\omega_js)]/[\pi(j-k)],&j\ne k,
 \end{cases}\quad 0\le s\le L.
\]

Сохраняются `Q_M(0)=2I`, `Q_M(L)=0`, `||Q_M(s)||<=2`. Положим

\[
 A_m(t)=t^{-1/2}P Q_M(\log t)P,
\]

\[
 T_{>R}=\sum_{\substack{d>R\\dk\le m}}
                \mu(d)\log k\,A_m(dk),\qquad 2\le R<m.       \tag{1}
\]

Все `d,k` — **обычные положительные целые**. Здесь нет идеалов или шестистепенных характеров CF22. `mu(d)=0` на квадратных делителях, но произведения `dk` могут быть любыми, включая все степени простых. `k=1` имеет точный вес ноль, верхний атом `dk=m` имеет точную матрицу ноль. В разложениях эти факты используются только как тождества, не как удаление неоплаченных границ.

Для actual weight

\[
 W=PWP\succeq0,\qquad\operatorname{Tr}W=1,
\]

исходная цель — верхняя оценка `Tr(W T_{>R})`, единая по всем таким W, с показателем `eta(epsilon)->0` при

\[
 M=R=\lfloor m^\epsilon\rfloor,
 \qquad 0<\epsilon<1/32\quad\text{фиксировано до }m\to\infty.  \tag{2}
\]

При нулевом пространстве `ran P` матричные оценки тривиальны; нормированный W рассматривается только когда это пространство ненулевое.

**[COFINAL_FAMILY | PAPER — принятые входы, не новая проверка].** Пакет предоставляет

\[
 \|T_{\le R}\|\le b_{\rm small}:=
 (56+32\Omega)\sqrt R+12(1+\log R)^2,                       \tag{3}
\]

\[
 PK_mP=P(A_{\rm arch}-c_AI)P-(T_{\le R}+T_{>R}),
 \qquad\|A_{\rm arch}-c_AI\|\le50L+8.                     \tag{4}
\]

Значит, любая новая верхняя цена `a_m` для **целой** `T_{>R}` даёт

\[
 PK_mP\succeq-[a_m+b_{\rm small}+50L+8]P.                  \tag{5}
\]

Малоделительная плата (3) возвращается **один раз**. Существующий weighted-LCM выигрыш не используется повторно и не кредитуется как знак.

## 2. Точное диадическое разбиение до какого-либо модуля

**[FINITE_CELL | PAPER].** Пусть

\[
 D_a=2^aR,\quad a=0,\ldots,J-1,\quad
 J=\lceil\log_2(m/R)\rceil,
\]

\[
 I_a=\{d\in\mathbb Z:D_a<d\le2D_a\},\qquad
 K_b=2^b,\quad k\in[K_b,2K_b).
\]

Продлим любое слагаемое с `d>m` нулём. Для `d<=m` определим

\[
 B_{m,d;b}:=
 \sum_{\substack{K_b\le k<2K_b\\dk\le m}}
                  \log k\,A_m(dk),
 \qquad
 B_{m,d}:=\sum_b B_{m,d;b}.                               \tag{6}
\]

Это конечная сумма; достаточно `K_b<=m`. Тогда

\[
 T_{>R}=\sum_{a,b}\sum_{d\in I_a}\mu(d)B_{m,d;b}
       =\sum_a\sum_{d\in I_a}\mu(d)B_{m,d}.               \tag{7}
\]

Ни один продукт не назначен двум блокам: нижние/верхние концы именно такие, как выписано. Внутренний `dk<=m` остаётся в каждом блоке. Это не замена гиперболического отсечения полным прямоугольником.

Если обозначить блочные операторы `T_{a,b}`, до всякого неравенства

\[
 T_{>R}^2=
 \sum_{a,b}T_{a,b}^2+
 \sum_{(a,b)<(a',b')}\{T_{a,b},T_{a',b'}\},                \tag{8}
\]

где `{X,Y}=XY+YX`. В частности, полный `k`-возврат содержит

\[
 B_{m,d}B_{m,e}=\sum_{b,b'}B_{m,d;b}B_{m,e;b'}.             \tag{9}
\]

Все члены `b!=b'` сохраняются. Произведения с промежуточным `P` не отождествляются со сдвигом без промежуточной проекции.

Для actual W положим `rho_W(s)=Tr(W P Q_M(s)P)`. Тогда `rho_W` вещественна, `|rho_W|<=2`, и каждая скалярная блоковая сумма имеет буквальные коэффициенты

\[
 \sum_{D<d\le2D}\mu(d)b_{d,K}(W),\qquad
 b_{d,K}(W)=\frac1{\sqrt d}
 \sum_{\substack{K\le k<2K\\dk\le m}}
 \frac{\log k}{\sqrt k}\rho_W(\log(dk)).                  \tag{10}
\]

## 3. Первый фильтр: почему нельзя сразу квадратить отдельные k-блоки

**[ABSTRACT | PAPER — аудит выбранной цены, не невозможность источниковой оценки].** Из (10) следует

\[
 |b_{d,K}(W)|\le2\sqrt{K/D}\log(2K),
\]

поэтому диагональ по d стоит не больше

\[
 \sum_{D<d\le2D}\mu(d)^2|b_{d,K}(W)|^2
       \le4K\log^2(2K).                                  \tag{11}
\]

Даже **гипотетическое** доказательство того, что соответствующие сдвиговые смешанные члены не увеличивают (11), дало бы через Cauchy/van der Corput всего цену `O(sqrt(K) log(2K))` для блока. Эта гипотеза здесь не используется как факт.

При `D` около исходного `R=m^epsilon`, `K` может иметь порядок `m/R`; у такого достаточного конверта остаётся степень `(1-epsilon)/2`. Он не проходит фильтр запроса.

Можно было бы поднять вспомогательную границу до `Y=m^theta`, сохранив точное

\[
 T_{>R}=T_{>Y}+T_{\le Y}-T_{\le R}.                       \tag{12}
\]

Цена короткой части тогда имеет степень `epsilon+theta/2`, а идеализированная диагональная цена длинной — `(1-theta)/2`. Минимизация их максимума даёт

\[
 \theta=\tfrac12-\epsilon,\qquad
 \min_\theta\max\{\epsilon+\theta/2,(1-\theta)/2\}
       =\tfrac14+\tfrac\epsilon2.                          \tag{13}
\]

Это расчёт возможностей **данной суммы верхних цен**, а не нижняя граница настоящего T. Даже идеализированный исход сохранял бы фиксированный четверть-степенной барьер. Ни (11), ни (13) не доказывают этот промежуточный bound: нужная off-diagonal оценка не поставлена.

**Отступление выполняется сразу:** собрать все k внутри (6) **до** квадратов. Нельзя превращать удобную прямоугольную сумму в обязательный потребитель.

## 4. Количественный шаг: полный k-оператор каждого делителя

**Лемма A [COFINAL_FAMILY | PAPER].** При принятых буквальных continuous/Hilbert identities пакета, для каждого `m>=4`, `1<=M<=m`, `1<=d<=m`:

\[
 \boxed{
 \|B_{m,d}\|\le\frac{\mathfrak b_m}{\sqrt d},
 \qquad\mathfrak b_m:=40+16\Omega.
 }                                                        \tag{14}
\]

Это оценка уже **суммы всех k**, не отдельных слагаемых. Она не предполагает RH, ZF78, коротких корреляций или вероятностных свойств μ.

### 4.1. Точная цена суммирования по целым k

Вложенный L1 даёт для любого `d<=y<=m`

\[
 e_d(\omega;y)=
 \sum_{k\le y/d}\frac{\log k}{(dk)^{1/2+i\omega}}
 -\frac1d\int_d^y\log(t/d)t^{-1/2-i\omega}\,dt,
\]

\[
 |e_d(\omega;y)|\le(5+4|\omega|)/\sqrt d.                   \tag{15}
\]

При `y<d` обе стороны определяющей разности нулевые. Верхняя скалярная граница не удаляется. Напомним вывод: при `F_d(t)=log(t/d)t^{-s}`, `s=1/2+i omega`, и `beta_d(t)=floor(t/d)-t/d`

\[
 e_d=\beta_d(y)F_d(y)-\int_d^y\beta_d(t)F'_d(t)\,dt.
\]

Используются `F_d(d)=0`, `|beta_d|<=1`, `|F_d(y)|<=2/(e sqrt d)` и интеграл `t^{-3/2}(1+|s|log(t/d))`. Это даёт `(2/e+2+4|s|)/sqrt d<=(5+4|omega|)/sqrt d`.

К буквальной матрице меры применяется уже данный в пакете Hilbert-return с коэффициентом 4; сжатие тем же P норму не увеличивает. Следовательно,

\[
 B_{m,d}=
 \frac1d\int_d^m\log(t/d)A_m(t)\,dt+E_{m,d},
\]

\[
 \|E_{m,d}\|\le(20+16\Omega)/\sqrt d.                     \tag{16}
\]

Это равномерно по **каждому d до m**. Никакого предположения `d<=m^epsilon` для (15)–(16) нет.

### 4.2. Именно исходные ограничения оплачивают непрерывную часть

Принятые identities из Q10:

\[
 \int_1^m A_m(t)dt=-H_P,\qquad
 \int_1^m\log t\,A_m(t)dt=J_P,
\]

\[
 0\preceq H_P\preceq4P,\qquad\|J_P\|\le8.                 \tag{17}
\]

Для каждого d точно

\[
 \frac1d\int_d^m\log(t/d)A_m(t)dt
 =\frac{J_P+\log d\,H_P}{d}
 -\frac1d\int_1^d\log(t/d)A_m(t)dt.                       \tag{18}
\]

Нижний возврат не исчезает. По `||A_m(t)||<=2/sqrt(t)`

\[
 \frac1d\int_1^d\log(d/t)\|A_m(t)\|dt
 \le\frac2d\int_1^d\frac{\log(d/t)}{\sqrt t}dt
 \le\frac8{\sqrt d}.                                      \tag{19}
\]

Поскольку `log d/sqrt d<=2/e<1` и `d>=1`,

\[
 \left\|\frac{J_P+\log d\,H_P}{d}\right\|
 \le\frac8d+\frac{4\log d}{d}\le\frac{12}{\sqrt d}.
\]

Вместе с (16),(19) это доказывает (14). Более острый постоянный коэффициент не нужен.

**Что действительно изменилось:** цена диагонали по d больше не содержит длинный K из (11). Все k-cross terms были собраны до применения оценки. Это реальное удешевление корреляционного сертификата, но не новая верхняя степень полного T.

### 4.3. Контроль, обнаруживающий потерю P

**[COFINAL_FAMILY | PAPER — planted failure, не контрпример CCM].** Без P взять нулевую Fourier-моду. Для фиксированного d и `m` достаточно большого, в диапазоне `m/(4d)<=k<=m/(2d)`:

\[
 \log k\ge L/2,\quad Q_M(\log(dk))_{00}\ge2\log2/L,
 \quad (dk)^{-1/2}\ge m^{-1/2}.
\]

Таких целых k не меньше `m/(8d)`, после увеличения фиксированного старта. Поэтому несжатый диагональный элемент удовлетворяет

\[
 (B^{\rm raw}_{m,d})_{00}\ge\frac{\log2}{8d}\sqrt m.        \tag{20}
\]

При фиксированном `epsilon<1/2` это не совместимо с ошибочной несжатой версией (14). Следовательно, P не декоративен: именно его исходные условия дают (17). Не разрешено применять (14) к raw-оператору.

## 5. Точная совместная корреляция настоящих μ — матричная, не случайная

**[FINITE_CELL | PAPER].** В d-блоке `(D,2D]` положим

\[
 X_i=\mu(D+i)B_{m,D+i},\quad i=1,\ldots,D,
\]

с нулевым продолжением за `d=m`. Все X_i самосопряжены и поддержаны на P. Для `j=2-D,...,D` определим полные окна

\[
 C_{D,j}=\sum_{i=1}^D\mathbf1_{j\le i\le j+D-1}X_i.
\]

Каждый X_i входит ровно в D окон, поэтому

\[
 \sum_j C_{D,j}=D T_D,\qquad T_D=\sum_iX_i.                \tag{21}
\]

Определим

\[
 G_D=\frac1D\sum_{j=2-D}^{D}C_{D,j}^2\succeq0.            \tag{22}
\]

Подсчёт общего числа окон двух индексов даёт **точно**

\[
 \boxed{
 G_D=\sum_{d,e\in I_D}
 \left(1-\frac{|d-e|}{D}\right)
 \mu(d)\mu(e)B_{m,d}B_{m,e}.
 }                                                        \tag{23}
\]

Это некоммутативное тождество: порядок матриц не переставляется. Симметричная пара даёт антикоммутатор, не произведение модулей. В частности,

\[
 G_D=\mathcal D_D+\mathcal O_D,
\]

\[
 \mathcal D_D=\sum_{d\in I_D}\mu(d)^2 B_{m,d}^2\succeq0,
\]

\[
 \boxed{
 \mathcal O_D=
 \sum_{h=1}^{D-1}\left(1-\frac hD\right)
 \sum_{d=D+1}^{2D-h}\mu(d)\mu(d+h)
       \{B_{m,d},B_{m,d+h}\}.
 }                                                        \tag{24}
\]

Знак O_D неизвестен. Для actual W:

\[
 \operatorname{Tr}(W\mathcal O_D)=
 2\sum_{h=1}^{D-1}\left(1-\frac hD\right)
 \sum_{d=D+1}^{2D-h}\mu(d)\mu(d+h)
 \Re\operatorname{Tr}(W B_{m,d}B_{m,d+h}).                 \tag{25}
\]

**Не** применяется неверное равенство `Tr(WB_d)Tr(WB_e)=Tr(WB_dB_e)`. Рабочий объект — матричные квадраты (22); passage к actual W делается как след доказанного операторного неравенства.

### 5.1. Полная формула с k,k'

Из определения B:

\[
 \begin{aligned}
 &\Re\operatorname{Tr}(W B_{m,d}B_{m,e})\\
 &=\frac1{\sqrt{de}}
 \sum_{\substack{dk\le m\\e\ell\le m}}
 \frac{\log k\log\ell}{\sqrt{k\ell}}
 \Re\operatorname{Tr}\!\left[
 W P Q_M(\log(dk))P Q_M(\log(e\ell))P\right].
 \end{aligned}                                           \tag{26}
\]

Сохраняются: все пары k,ell; `k=ell` и `k!=ell`; совпадения произведений `dk=e ell`; разные произведения; все prime powers; верхние атомы с их нулём; промежуточное P. Никакой факторизации сжатых сдвигов не введено, поэтому положительный Gram-дефект из прежнего q-теста не расходуется как бесплатный кредит.

### 5.2. Все межблочные члены оплачены, а не объявлены нулевыми

Для самосопряжённых `C_1,...,C_s`:

\[
 (\sum_i C_i)^2\preceq s\sum_i C_i^2.                      \tag{27}
\]

Доказательство: применить обычное Cauchy к векторам `C_i f` для каждого f. Это сохраняет направление Loewner-неравенства и не требует коммутирования.

Из (21),(22):

\[
 T_D^2\preceq\frac{2D-1}{D}G_D\preceq2G_D.
\]

Обозначая

\[
 G_m=\sum_{a=0}^{J-1}G_{D_a},\quad
 \mathcal D_m=\sum_a\mathcal D_{D_a},\quad
 \mathcal O_m=\sum_a\mathcal O_{D_a},
\]

получаем

\[
 \boxed{T_{>R}^2\preceq2J G_m,
 \qquad G_m=\mathcal D_m+\mathcal O_m\succeq0.}             \tag{28}
\]

Полная цена ограничения меж-d-блочных членов — J, то есть `O(log m)`. Они не удалены из (8); они ограничены (27). Внутренние k-блоки, напротив, не разделялись при оценивании B.

Для любого actual W с trace 1:

\[
 |\operatorname{Tr}(WT_{>R})|^2
 \le\operatorname{Tr}(WT_{>R}^2)
 \le2J\operatorname{Tr}(WG_m).                            \tag{29}
\]

Первое неравенство — Cauchy в скалярном произведении `Tr(W X*Y)`. Поэтому тот же W сохраняется, а максимум не заменяется произвольным удобным вектором.

**Первое усиление задачи:** (28)–(29) контролируют абсолютную величину, тогда как потребитель просит только верхнюю сторону. Неудача этого достаточного сертификата не опровергает потребитель. Также (27) может потерять полезную компенсацию между d-блоками. Эти потери явно локализованы.

## 6. Что оплачено для всех масштабов

**Теорема B [COFINAL_FAMILY | PAPER].** Из (14), с тем же P,

\[
 \boxed{
 0\preceq\mathcal D_m
 \preceq\mathfrak b_m^2\log(m/R)P.
 }                                                        \tag{30}
\]

Действительно, `B_d^2<=||B_d||^2P`, а

\[
 \sum_{d=R+1}^{m}\frac{\mu(d)^2}{d}
 \le\sum_{d=R+1}^{m}\frac1d\le\log(m/R).
\]

Это верхняя оценка диагонали, не утверждение, что off-diagonal можно выкинуть.

Для каждой фиксированной epsilon на позднем диапазоне `M>=L` и

\[
 \mathfrak b_m=40+32\pi M/L
 \le C_b M/L,\qquad C_b=40+32\pi.
\]

Поскольку `J<=1+L/log2`, (30) показывает: **диагональная доля правой стороны (28)** имеет цену

\[
 2J\mathcal D_m\preceq C M^2P.                            \tag{31}
\]

Её квадратный корень имел бы порядок `m^epsilon`. Малоделительный возврат (3) затем стоил бы `m^(3epsilon/2)`.

Но действительная (29) содержит также `Tr(W O_m)`. Положительность G_m не означает `O_m<=0`.

## 7. Попытка использовать именно арифметику μ

**[FINITE_CELL | PAPER].** Для `d=ga,e=gb,(a,b)=1` точно

\[
 \boxed{
 \mu(d)\mu(e)
 =\mu(g)^2\mu(a)\mu(b)\mathbf1_{(g,ab)=1}.
 }                                                        \tag{32}
\]

Если g имеет квадрат, обе стороны нулевые. При бесквадратном g пересечение g с a или b создаёт квадрат в d или e и также зануляет обе стороны. В остальных случаях это мультипликативность μ.

Поэтому для `h>0` каждая действительная сдвиговая корреляция допускает перепись

\[
 \begin{aligned}
 &\sum_{d=D+1}^{2D-h}\mu(d)\mu(d+h)\,\Xi_W(d,d+h)\\
 &=\sum_{g\mid h}\mu(g)^2
 \sum_{\substack{D<ga\le2D-h\\(a,h/g)=1\\(g,a(a+h/g))=1}}
 \mu(a)\mu(a+h/g)\,\Xi_W(ga,g(a+h/g)),
 \end{aligned}                                           \tag{33}
\]

где `Xi_W(d,e)=Re Tr(W B_dB_e)` — **настоящий** вес из (26).

Это выполненная арифметическая перестановка, сохраняющая общий squarefree фактор и все маски. Она **не превращает** внутреннюю корреляцию в сумму `mu` по делителям одного числа. Уже при `h=1` остаётся единственный `g=1` и исходная взвешенная корреляция соседних μ. Вложенные источники не поставляют нужную равномерную оценку; в этой попытке она не выведена.

Заменить `mu(a)mu(a+h/g)` на его модуль допустимо как грубую оценку, но это уничтожает искомую компенсацию. Для демонстрации полной цены ниже этот ход доведён до конца, не скрыт словом «осцилляция».

### 7.1. Что даёт доступная оценка без недоказанных корреляций

Оконный Cauchy даёт

\[
 G_D\preceq D\sum_{d\in I_D}\mu(d)^2B_d^2
       \preceq D\mathfrak b_m^2P.
\]

Так как `sum_a D_a<2m`,

\[
 G_m\preceq2m\mathfrak b_m^2P.                            \tag{34}
\]

Через (28) это даёт `O(b_m sqrt(m log m))`. Лучше непосредственный полный возврат (14):

\[
 \boxed{\|T_{>R}\|\le
 \mathfrak b_m\sum_{R<d\le m}d^{-1/2}
 \le2\mathfrak b_m\sqrt m.}                              \tag{35}
\]

На (2) это не лучше степени `1/2+epsilon`. Совсем грубое исходное оценивание до regrouping даже даёт

\[
 \|T_{>R}\|
 \le2\sum_{d>R}d^{-1/2}\sum_{k\le m/d}\frac{\log k}{\sqrt k}
 \le4\sqrt m L(1+L).                                      \tag{36}
\]

Поэтому (35) не объявляется улучшением полной прежней цены. Условный Q10

\[
 T_{>R}\preceq
 [4C_{\rm cl}m^{3/8}L^2\log(3L)+b_{\rm small}]P-2H_P      \tag{37}
\]

остаётся сильнее полученных здесь полных элементарных конвертов. **Его показатель 3/8 не улучшен.** (37) наследует ровно ZF78 из запроса и не передоказывается.

### 7.2. Почему нельзя бесплатно выбросить off-diagonal

**[ABSTRACT | PAPER — контроль общей импликации, не источник CCM].** В блоке `D=4` настоящие коэффициенты имеют `mu(5)=-1,mu(6)=1`. Возьмём для контрольной модели `B_5=-I,B_6=I,B_7=B_8=0`. Тогда `X_1=X_2=I`, остальные X нулевые:

\[
 \mathcal D_D=2I,\qquad
 \mathcal O_D=\tfrac32I,\qquad G_D=\tfrac72I.
\]

Если вместо этого взять `B_5=B_6=I`, off-diagonal меняет знак. Значит, реальность μ, boundedness коэффициентов и положительность оконных квадратов **не доказывают** нужного знака O. Это специально выбранные B, не фактические CCM-матрицы; они опровергают только автоматическое правило вывода.

Точно так же `gcd`-маску нельзя удалить: `d=2,e=4` даёт `mu(2)mu(4)=0`, но правая часть (32) без `1_(g,ab)=1` равна `-1`.

## 8. Полный every-cell возврат и точное место остановки

Если бы для настоящего `O_m` было доказано, например,

\[
 \operatorname{Tr}(W\mathcal O_m)
 \le C_\epsilon\mathfrak b_m^2 L^b m^{\sigma(\epsilon)}
 \quad\text{для каждого actual W},                         \tag{38}
\]

с `sigma(epsilon)->0` и фиксированным b, то (29),(30) дали бы верхнюю цену с показателем `epsilon+sigma(epsilon)/2`, плюс поглощаемые логарифмы. После (3) появился бы показатель

\[
 \max\{\epsilon+\sigma(\epsilon)/2,\,3\epsilon/2\}+o(1).
\]

**(38) не используется как предпосылка выполненного доказательства. Она не доказана.** Это показывает точную численную цену missing correlation, а не поставляет её.

Фактически доступны только (35)–(37). По (5) новый элементарный возврат не даёт sparse-band supplier. Не доказаны ни every-cell `eta(epsilon)->0`, ни улучшенный полный фиксированный показатель.

**Самая ранняя исправленная потеря:** квадраты отдельных k-блоков до исходной continuous-компенсации. Её устранила (14).

**Самая ранняя оставшаяся потеря:** Cauchy по d превращает одностороннюю исходную форму в контроль квадратов; следующая неоценённая часть — O_m из (24)–(26), а не ошибка округления или quadrature. Возврат к `sum |mu|`, общему PNT или all-prefix примитиву новой степени не даёт и не предпринимается повторно.

## 9. Один рассчитанный альтернативный механизм: кофинальный средний след G

Это не утверждение о новом арифметическом результате. Это более точная разрешённая точка отката: вместо uniform-in-W оценки корреляции (38) попытаться доказать **одну скалярную усреднённую оценку** для уже определённого положительного G. Адаптивный максимум контролируется **до** выбора масштаба.

### 9.1. Явная арифметическая сумма, которую пришлось бы ограничить

**[FINITE_CELL | PAPER].** Положим

\[
 \Gamma_m(n,n')=
 \operatorname{Tr}\!\left[
 P Q_M(\log n)P Q_M(\log n')P\right]\in\mathbb R.
\]

Вещественность следует из самосопряжённости двух сжатых Q и цикличности trace; положительность каждого значения не утверждается.

Тогда

\[
 \begin{aligned}
 \operatorname{Tr}\mathcal O_m
 ={}&2\sum_{a=0}^{J-1}\sum_{h=1}^{D_a-1}
       \left(1-\frac h{D_a}\right)
 \sum_{d=D_a+1}^{2D_a-h}\frac{\mu(d)\mu(d+h)}{\sqrt{d(d+h)}}\\
 &\quad\times
 \sum_{\substack{dk\le m\\(d+h)\ell\le m}}
 \frac{\log k\log\ell}{\sqrt{k\ell}}
 \Gamma_m(dk,(d+h)\ell).
 \end{aligned}                                           \tag{39}
\]

Нулевое продолжение при `d>m` понимается как раньше. В (39) остаются все межмодовые члены, исходный проектор при текущем m и все product coincidences. Это не среднее одной фиксированной формы и не скалярная prime-discrepancy гипотеза.

### 9.2. Оплаченная диагональ с размерностью

**[COFINAL_FAMILY | PAPER].** Для каждого фиксированного epsilon на достаточно позднем хвосте

\[
 \operatorname{rank}P\le2M+1\le3m^\epsilon,
\]

\[
 \operatorname{Tr}\mathcal D_m
 \le3m^\epsilon\mathfrak b_m^2L
 \le3C_b^2\frac{m^{3\epsilon}}L.                           \tag{40}
\]

Для целого `X` достаточно большого и `m=X,...,2X-1`:

\[
 \sum_{m=X}^{2X-1}\operatorname{Tr}\mathcal D_m
 \le6C_b^2\frac{X^{1+3\epsilon}}{\log X},                 \tag{41}
\]

где использовано `epsilon<1/32`. Здесь цена размерности `m^epsilon` выставлена явно.

### 9.3. Одна открытая арифметическая лемма — ровно её бюджет

**[COFINAL_FAMILY | CONDITIONAL — OPEN, не вход результата].** Рассмотреть утверждение:

> Для каждого достаточно малого фиксированного `epsilon>0` существуют `C_epsilon` и неограниченная последовательность целых `X` такие, что для literal `M=R=floor(m^epsilon)`
>
> \[
> \boxed{
> \sum_{m=X}^{2X-1}\operatorname{Tr}\mathcal O_m
> \le C_\epsilon X^{1+3\epsilon}(\log(2X))^2.
> }                                                       \tag{AV}
> \]
>
> В сумму входят все m и все члены (39); оценка односторонняя, без модуля внешней signed суммы.

Степень `3epsilon` здесь — **допустимый бюджет**, рассчитанный из (40) и цены trace, а не найденный закон. Ни независимость μ, ни (AV) не предполагаются. Эта попытка **не доказала (AV)**.

### 9.4. Доказанный условный возврат (AV) к тому же sparse-band receiver

**Лемма C [ABSTRACT | PAPER: импликация, не доказательство AV].** Из (41),(AV), поскольку `G_m>=0`,

\[
 \sum_{m=X}^{2X-1}\operatorname{Tr}G_m
 \le C'_\epsilon X^{1+3\epsilon}(\log(2X))^2.
\]

Следовательно, существует **один общий** `m_X` в этом окне с

\[
 \operatorname{Tr}G_{m_X}
 \le C'_\epsilon X^{3\epsilon}(\log(2X))^2.
\]

Для каждого m заранее доказано, независимо от W,

\[
 \|T_{>R}\|^2\le2J\|G_m\|\le2J\operatorname{Tr}G_m.       \tag{42}
\]

Поэтому в выбранном `m_X` оценка действует **одновременно для всех W**:

\[
 \|T_{>R}\|\le
 C''_\epsilon m_X^{3\epsilon/2}(\log m_X)^{3/2}.           \tag{43}
\]

Нет перестановки `sup_W` со средним. Мы сначала использовали положительный trace как детерминированный контроль максимума на каждой ячейке, затем выбрали ячейку. Разный m означает свой первоначально определённый P, M, R — никаких отождествлений проекторов между ячейками.

Вернув (3),(4),

\[
 \lambda_{\min}(K_{m_X}|_{\operatorname{ran}P})
 \ge-C'''_\epsilon m_X^{3\epsilon/2}(\log m_X)^{3/2}
       -b_{\rm small}-50\log m_X-8.
\]

В конце можно увеличить константу и старт, используя `log^B m<=m^(epsilon/2)` при фиксированном epsilon:

\[
 \boxed{
 \lambda_{\min}(K_{m_X}|_{\operatorname{ran}P})
 \ge-C''''_\epsilon m_X^{2\epsilon}.
 }                                                        \tag{44}
\]

Это был бы нужный кофинальный bound для **отдельного** sparse receiver: гипотетический нуль с `delta>0` даёт отрицательный свидетель `-c m^delta/(log m)^(2delta)` на каждой поздней ячейке. Выбор одного фиксированного `epsilon<delta/4` сделал бы (44) несовместимым с ним вдоль неограниченных `m_X`. Сам witness принимается только в области, записанной в приложении.

**Никакое противоречие не активировано: AV открыта.** Полный SP, G1/G3 и дополнение к P этим не закрываются даже условным объявлением.

### 9.5. Полная проверка цены при отсутствии нового знака

Из (34), `rank P<=3m^epsilon` и `b_m=O(m^epsilon/L)`:

\[
 \operatorname{Tr}G_m
 \le C\frac{m^{1+3\epsilon}}{L^2},
\]

\[
 \sum_{m=X}^{2X-1}\operatorname{Tr}G_m
 \le C\frac{X^{2+3\epsilon}}{(\log X)^2}.                  \tag{45}
\]

По сравнению с бюджетом AV здесь остаётся **лишняя степень X**, с точностью до логарифмов. Простое усреднение эту степень не убрало. Это вычисленный дефицит достаточного метода, не lower bound для actual G.

Нельзя подставить Q10-bound для T как bound для G: G содержит квадратные префиксные окна делителей, а из малого полного T малость этих окон не следует. Тем более нельзя заменить (AV) усреднением заранее выбранного вектора W.

## 10. Почему этот сертификат не объявляется необходимым

**[ABSTRACT | PAPER].** У исходной задачи верхняя сторона. Матрица `T=-NI` имеет хорошую верхнюю границу 0, но квадрат `T^2=N^2I` велик. Два блока `T_1=NI,T_2=-NI` дают суммарный ноль, хотя сумма их квадратов велика. Это абстрактные контроли, не фактическая CCM.

Поэтому:

- failure оценки G не опровергает исходный signed T;
- failure AV не опровергает существование другой кофинальной оценки;
- даже uniform scalar H_mu не назначается обязательным интерфейсом;
- все source sign claims требуют собственного доказательства, не «положительного Gram» по названию.

Два представления этого же фронта, до новых тяжёлых запусков:

| Представление | Что сохраняет | Диагностическая сила / стоимость | Риск |
|---|---|---|---|
| Прямая actual-W сумма (1),(7), до Cauchy | Только нужную верхнюю сторону, все d-блоковые компенсации | Высокая; низкая алгебраическая, высокая цена нового знака | Возврат к scalar абсолютному примитиву, равносильному прежней стене |
| Полная k-сборка + оконный Gram + средний trace (14),(39),(AV) | Все k-cross, μ-пары, P и право адаптивного спектрального выбора | Высокая для точного бюджета; средняя для конечной алгебры, неизвестная для AV | Квадрат и trace требуют больше, чем потребитель; потеря направления |

Выбранная попытка выполнена во втором представлении. При отсутствии оценки (39) её дальнейшее разбиение/вычисление без нового математического входа останавливается. Отступление — перед Cauchy по d, не к очередному большему моменту и не в CF22.

## 11. Дискриминаторы и что могло бы изменить план

Для конкретно заявленного конечного `K,eta,m0`, на `m>=m0` проверяется **запас**

\[
 K m^\eta-\lambda_{\max}(T_{>R}|_{\operatorname{ran}P}).
\]

Нижняя интервальная граница `>=0` принимает только эту конечную ячейку; верхняя `<0` опровергает только этот контракт. Интервал через ноль требует более высокой точности/точной структуры, не округления.

Для конкретной оконной гипотезы с порогом B проверяется `B-Tr(W O_m)` на том же actual W; для AV — весь `C_epsilon X^(1+3epsilon)log²(2X)-sum Tr O_m`, с зафиксированным стартом и C. Конечный провал не опровергает утверждение с неизвестным eventual-стартом.

**Изменило бы план:** новое источниковое неравенство для weighted μ-пар (25)/(39), которое уменьшает полную степень после (42), либо прямое однонаправленное сравнение (1), сохраняющее отрицательный вклад. Само наличие большого числа нулевых/малых интервалов, растущий объём данных и очередная точная перестановка — не такой вход.

## 12. Выполненные проверки и их честная область

**[FINITE_CELL | PAPER — точная рациональная алгебра, не Lean/Arb].** Финальный локальный проверяющий выполнил 7021 сравнение:

| Проверка | Число |
|---|---:|
| Полные atom-by-atom dyadic Mobius-log reassemblies | 588 |
| Gcd identity (32) на d,e<=80 | 6400 |
| Число включений каждого индекса в окна | 9 |
| Некоммутативное тождество (23) на рациональных симметричных матрицах | 9 |
| Матричный Cauchy, проверка рациональной PSD-разности 2x2 | 9 |
| Преднамеренное удаление cross или gcd-маски | 2 |
| Настоящая степень 27 при R=2: коэффициент -2 log3 | 1 |
| Точный баланс идеализированной цены (13) | 3 |

Доказательства для всех параметров — текст выше; конечные проверки лишь ловят ошибки реализации и знаков. Матрицы в рациональном стенде **не выдаются за actual CCM**. Логарифмы в coefficient checks представлены целыми коэффициентами при логарифмах простых.

**Неудачный дополнительный контроль записан, а не скрыт.** В первом запуске после основных проверок была добавлена неподкреплённая проверка, ожидавшая оба знака off-diagonal у постоянного скалярного веса B_d=1 при D=2,...,79. Положительный знак не встретился, и assertion остановил запуск. Это не гипотеза, принятая из источника, и не одно из четырёх зарегистрированных ожиданий. Требование «обязательно увидеть оба знака» удалено; сам результат поиска сохранён: первый отрицательный пример D=3, значение -4/3; положительного в этом диапазоне нет. Никакого общего знака отсюда не выведено. Для опровержения автоматического sign rule используется **явный точный weighted-control §7.2**, а не эта неудачная догадка.

`python-flint` в доступной среде не найден; попытка установки в отдельный локальный target завершилась ошибкой DNS. Поэтому новых Arb-расчётов нет, и никакие точные/численные проверки не названы Arb-сертификатами. Lean, Comparator и независимый внешний обзор не запускались.

## 13. Ledger, зависимости и closeout

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| S0 | Literal P,Q и sparse adverse witness | COFINAL_FAMILY | PAPER | Приняты из TXT в их заявленной области |
| A1 | Полная диадическая сборка с гиперболическим cutoff | FINITE_CELL | PAPER | Доказана точно |
| A2 | Single-divisor full-k bound (14), все lower/upper returns | COFINAL_FAMILY | PAPER | Выведен из принятых Hilbert/continuous inputs |
| A3 | Необходимость сохранения P, контроль (20) | COFINAL_FAMILY | PAPER | Доказана для испорченной uncompressed формы |
| B1 | Некоммутативный Fejer Gram, все cross (23)–(29) | ABSTRACT | PAPER | Доказан |
| B2 | Оплата correlation diagonal (30)–(31) | COFINAL_FAMILY | PAPER | Доказана; не bound полного T |
| M1 | Actual mu gcd correlation reduction (32)–(33) | FINITE_CELL | PAPER | Доказана; нужного верхнего знака не даёт |
| M2 | Actual signed off-diagonal estimate | COFINAL_FAMILY | CONDITIONAL | OPEN, не использована как факт |
| C1 | AV -> cofinal exponent 2epsilon with same adaptive source | ABSTRACT | PAPER | Импликация доказана |
| C2 | AV для настоящих coefficients | COFINAL_FAMILY | CONDITIONAL | Не доказана |
| R1 | Лучший наследуемый полный 3/8 bound | COFINAL_FAMILY | CONDITIONAL | ZF78; сохранён, не улучшен |
| R2 | Sparse supplier/full SP/G1/G3/RH | COFINAL_FAMILY | CONDITIONAL | Не закрыты |
| T1 | 7021 локальный exact control | FINITE_CELL | PAPER | Пройден; не universal source sign |

**DOWNSTREAM_CONSUMER:** отдельный sparse-band off-critical witness receiver. **ACTUAL_CONSUMER_REQUIREMENT:** одна верхняя оценка полной T с показателем, стремящимся к нулю, возможно на неограниченной исходной подпоследовательности при каждом фиксированном epsilon. **ORIGINAL_REQUESTED_OBJECT:** направленная совместная корреляция μ в exact d,k blocks. **ORIGINAL_OBJECT_IS:** UNKNOWN как необходимый интерфейс; squared-Gram и AV доказаны только достаточными. **KNOWN_WEAKER_INTERFACES:** прямой one-sided actual-W bound; прямой prime upper bound без long-divisor split; источникозависимый cofinal bound без trace square. **FAILURE_TYPE:** NO_DERIVATION для actual O. **EPISTEMIC_STATUS:** RESEARCH_DEBT. **NOVELTY_AXIS:** полная k-сборка до квадрата удаляет искусственный K из диагонального бюджета и даёт явный adaptivity-safe cofinal correlation contract; не новый полный арифметический показатель.

**Что стало меньше:** стоимость диагонального сертификата — из цены, несущей длинный K, в параметр-пропорциональную цену B_m² log(m/R). **Что не стало меньше:** доказанный полный показатель источника. **Что убито:** только общие автоматические shortcuts «выбросить cross», «удалить общий gcd-фактор», «применить projected cancellation без P»; actual target не опровергнут. **Что не повторять:** называть эти проверки закрытием sparse supplier; брать μ-модули и ждать нового степенного выигрыша; объявлять среднее фиксированного вектора контролем adaptive max.

**Prediction fates:** P1–P3 подтверждены конечной точной алгеброй и полными бумажными выводами; P4 обнаруживает planted failures. Глобальный выигрыш не предсказывался и не получен. Дополнительное ошибочное ожидание двух знаков на constant-weight scan не подтверждено и явно отделено от P1–P4.

```yaml
MEMORY_ENTRY:
  iteration: CCM_ACTUAL_MOBIUS_JOINT_Q01_2026_10_20
  target: ACTUAL_LONG_DIVISOR_ONE_SIDED_SPARSE_BOUND
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: Separately square k-blocks or estimate remaining actual mu-pairs by magnitudes
  invariant_learned: Sum every k with the original P before squaring in d; retain all intermediate P and all cross terms
  smallest_unpaid_input: Signed off-diagonal (25), or the explicitly stronger cofinal averaged-trace (AV) with kernel (39)
  forbidden_future_move: Promote paid diagonal or conditional implication to a new exponent for full T
  next_decisive_test: Audit Lemma A and the exact adaptivity-safe AV return; further arithmetic work must estimate (39), not just regroup it
  consumer_progress: NONE
  route_family_death: NOT_ESTABLISHED
  reopen_trigger: A quantitative source-specific mu-pair bound that beats the full displayed budget
```

## 14. Одна CODEX DIRECTIVE

**Независимо проверить один пакет лемм A–C:** full-k bound (14) с настоящими (17) и всеми границами; некоммутативную оконную сборку (23)–(29) без удаления промежуточного P; диагональный бюджет (40)–(41); импликацию AV -> (44) с полной ценой размерности, окон и short return. Отдельно подтвердить, что AV не доказана и не поставляется никаким из вложенных источников. Выполнить встроенный exact-check ниже как контроль реализации, не как сертификат actual sign. Вернуть первый дефект либо приёмку ровно этих утверждений. **Не** запускать очередной широкий численный scan, PySR, формализацию или новую ветку; **не** принимать оценку O_m, новый спектральный показатель, SP или RH по результату проверки этой импликации.

Репозиторий в этой сессии не изменён. Архивный файл — PAPER-вывод и проверяемая локальная алгебра; не Lean-certified result.

## 15. Первичные и внутренние источники

Основной источник: приложенный TXT с SHA-256 из заголовка. Ключевые диапазоны индексированной копии: 8–23 (контракт), 82–144 (sparse receiver), 422–474 (L1/L2 и границы scalar supplier), 621–836 (literal Q,P,short-return), 1009–1105 (Hilbert/Q10), 1334–1632 (weighted-LCM и C5), 1635–1823 (предыдущий mechanism audit). Эти входы не заменялись новым рассказом о библиотеке или маршруте.

Внешние definitional/method ссылки, не поставщики target:

```text
https://dlmf.nist.gov/27.5
https://terrytao.wordpress.com/2021/02/27/boosting-the-van-der-corput-inequality-using-the-tensor-power-trick/
```

DLMF фиксирует свёрточное тождество; Tao иллюстрирует принцип Cauchy/Gram. Ни одна страница не утверждает нужную взвешенную μ-корреляцию. Все конечные constants и source returns, фактически использованные здесь, выписаны в доказательствах.

## Приложение A. Воспроизводимый exact-check

Сохранить приведённый ниже код как `check_exact.py` в отдельном рабочем каталоге и запустить `python3 check_exact.py`. Никаких подстановок пути репозитория или установки зависимостей не требуется. Код использует только стандартную библиотеку. Его проверки не заменяют бумажные доказательства и не вычисляют actual CCM.

```python
from fractions import Fraction as Q
from collections import Counter
from math import gcd
from pathlib import Path
import json, hashlib

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    return -s if n>1 else s

def faclog(n):
    out=Counter();p=2
    while p*p<=n:
        while n%p==0:out[p]+=1;n//=p
        p+=1
    if n>1:out[n]+=1
    return out

def normc(x):return {k:v for k,v in x.items() if v}
def smat(A,B):return tuple(tuple(a+b for a,b in zip(x,y)) for x,y in zip(A,B))
def cmat(s,A):return tuple(tuple(s*a for a in row) for row in A)
def mmat(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(len(A))) for j in range(len(A))) for i in range(len(A)))
def zmat(n=2):return tuple(tuple(Q(0) for _ in range(n)) for _ in range(n))
def summ(A):
    out=zmat()
    for a in A:out=smat(out,a)
    return out

def psd2(A):
    return A[0][1]==A[1][0] and A[0][0]>=0 and A[1][1]>=0 and A[0][0]*A[1][1]-A[0][1]**2>=0

stats=Counter()
# Exact log coefficients: each atom carries log(p) as formal independent symbol.
for m in (12,17,24,31,48,64):
 for R in (2,3,5):
  if R>=m:continue
  direct={n:Counter() for n in range(1,m+1)}
  blocked={n:Counter() for n in range(1,m+1)}
  for d in range(R+1,m+1):
   for k in range(1,m//d+1):
    for p,e in faclog(k).items():direct[d*k][p]+=mu(d)*e
  D=R
  while D<m:
   K=1
   while K<=m:
    for d in range(D+1,min(2*D,m)+1):
     for k in range(K,min(2*K-1,m//d)+1):
      for p,e in faclog(k).items():blocked[d*k][p]+=mu(d)*e
    K*=2
   D*=2
  for n in range(1,m+1):
   assert normc(direct[n])==normc(blocked[n]);stats['atom_reassemblies']+=1
# Actual mu gcd identity including all common-prime square obstructions.
for d in range(1,81):
 for e in range(1,81):
  g=gcd(d,e);a=d//g;b=e//g
  rhs=mu(g)**2*mu(a)*mu(b)*(gcd(g,a*b)==1)
  assert mu(d)*mu(e)==rhs;stats['mu_gcd_checks']+=1
# Noncommuting symmetric matrix Fejer identity for all endpoints.
for D in range(1,10):
 X=[]
 for i in range(1,D+1):
  B=((Q(i, i+2),Q((-1)**i, i+1)),(Q((-1)**i,i+1),Q(2*i-3,i+3)))
  X.append(cmat(mu(D+i),B))
 windows=[]
 for j in range(2-D,D+1):
  windows.append(summ(X[n-1] for n in range(1,D+1) if j<=n<=j+D-1))
 assert summ(windows)==cmat(D,summ(X));stats['window_sum_checks']+=1
 G=cmat(Q(1,D),summ(mmat(C,C) for C in windows))
 expanded=summ(cmat(Q(D-abs(i-j),D),mmat(X[i],X[j])) for i in range(D) for j in range(D))
 assert G==expanded;stats['matrix_fejer_identities']+=1
 T=summ(X);bound=smat(cmat(Q(2*D-1,D),G),cmat(-1,mmat(T,T)))
 assert psd2(bound);stats['matrix_cs_psd_controls']+=1
# A concrete generic diagonal-discard failure: uses actual mu but not CCM B_d.
# D=4: mu(5)=-1, mu(6)=1; choose B5=-1, B6=1, B7=B8=0 -> both X=1.
D=4;a=[Q(1),Q(1),Q(0),Q(0)]
c0=sum(x*x for x in a)
G=c0+2*sum(Q(D-h,D)*sum(a[i]*a[i+h] for i in range(D-h)) for h in range(1,D))
assert G==Q(7,2) and c0==2 and G>c0
assert mu(2)*mu(4)==0 and mu(2)**2*mu(1)*mu(2)==-1
stats['planted_failures_detected']=2
# Original source proper-power coefficient: n=27,R=2 -> -2log3, not zero.
ell=Counter()
for d in range(3,28):
 if 27%d==0:
  for p,e in faclog(27//d).items():ell[p]+=mu(d)*e
assert normc(ell)=={3:-2};stats['proper_power_control']=1
# The naive-k diagonal cost balancing is algebraic, not a proved source estimate.
for eps in (Q(1,1000),Q(1,100),Q(1,32)):
 theta=Q(1,2)-eps
 assert eps+theta/2==(1-theta)/2==Q(1,4)+eps/2
 stats['conditional_exponent_controls']+=1
# Actual Mu does not force off-diagonal Fejer sign for a general positive weight.
positive_generic=[];negative_generic=[]
for D in range(2,80):
 a=[Q(mu(d)) for d in range(D+1,2*D+1)]
 off=2*sum(Q(D-h,D)*sum(a[i]*a[i+h] for i in range(D-h)) for h in range(1,D))
 if off>0 and not positive_generic:positive_generic=[D,str(off)]
 if off<0 and not negative_generic:negative_generic=[D,str(off)]
# Exploration is reported as observed; no sign is imposed as a passing test.
# The deliberately weighted exact control above is the only generic sign refutation.

out={"status":"PASS", "counts":dict(stats),"total_checks":sum(stats.values()),
     "generic_mu_constant_weight_first_positive":positive_generic,
     "generic_mu_constant_weight_first_negative":negative_generic,
     "not_ccm_sign_certificates":True,"arb_runs":0,"lean_runs":0,
     "exploratory_constant_weight_note":"No positive off-diagonal was found for D=2..79; a first run wrongly asserted both signs and stopped. That unsupported assertion is removed, not counted as a theorem or test.",
     "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

## Приложение B. Фактический результат финального локального запуска

```json
{
  "status": "PASS",
  "counts": {
    "atom_reassemblies": 588,
    "mu_gcd_checks": 6400,
    "window_sum_checks": 9,
    "matrix_fejer_identities": 9,
    "matrix_cs_psd_controls": 9,
    "planted_failures_detected": 2,
    "proper_power_control": 1,
    "conditional_exponent_controls": 3
  },
  "total_checks": 7021,
  "generic_mu_constant_weight_first_positive": [],
  "generic_mu_constant_weight_first_negative": [
    3,
    "-4/3"
  ],
  "not_ccm_sign_certificates": true,
  "arb_runs": 0,
  "lean_runs": 0,
  "exploratory_constant_weight_note": "No positive off-diagonal was found for D=2..79; a first run wrongly asserted both signs and stopped. That unsupported assertion is removed, not counted as a theorem or test.",
  "script_sha256": "23d4939d6a9d37be05cd033482c772e1d97bb8c435341a02760f365ab7db5f20"
}

```
