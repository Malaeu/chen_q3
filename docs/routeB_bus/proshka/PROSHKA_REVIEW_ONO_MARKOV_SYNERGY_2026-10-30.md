# STATUS: RUN_ONO_MARKOV_SOURCE_CROSSWALK

```yaml
OPERATIVE_CLASS: RUN_ONO_MARKOV_SOURCE_CROSSWALK
DOCUMENT_ROLE: OWNER_REQUESTED_LITERATURE_REVIEW_NOT_A_NEW_BUS_ADJUDICATION
DATE: 2026-10-30
REQUEST_ID: null
OWNER_REQUEST: VERIFY_MORNING_BRIEF_AND_SELECT_A_USEFUL_NEXT_CHECK
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AXIOM_REPOSITORY: AxiomMath/RiemannJensen
AXIOM_COMMIT: c1e023fa3ae7161219dde3dcb73f0c28ff972be2
AXIOM_MAIN_STATEMENT: VERIFIED_IN_PRIMARY_SOURCE_CODE
AXIOM_COMPARATOR_CONFIGURATION: READ_NOT_EXECUTED
AXIOM_TRANSITIVE_AXIOM_AUDIT: NOT_EXECUTED
ARXIV_2610_38870_PDF: NOT_RETRIEVED
ARXIV_TO_REPOSITORY_BYTE_VERSION_MATCH: NOT_VERIFIED
ARTIN_2610_40267_THEOREMS: NOT_VERIFIED_PRIMARY_MANUSCRIPT_UNAVAILABLE
MEDICAL_ARTICLES: THREE_PUBLISHER_RECORDS_VERIFIED_WITH_SCOPE_CORRECTIONS
SHARED_THETA_KERNEL: EXACT_PAPER_IDENTITY_H_EQUALS_4_THETA_PHI
COUNTING_WINDOW_TO_FIXED_COMPACT: DOES_NOT_COVER_THE_REQUIRED_SCALE
COFINAL_G1A: OPEN
COFINAL_G3: OPEN
COFINAL_WEIL_SIGN: OPEN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
ROUTE_SCORE: 3
REPOSITORY_WRITTEN: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NEW_LITERAL_CCM_NUMERICAL_SCAN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **Результат Оно полезен нам прежде всего как источник проверяемой аналитики того же theta-ядра, а не как поставщик недостающего знака.** В проверенной формализации механизм подсчёта корней работает в масштабе, который после естественной нормировки уходит из любого фиксированного компакта. Именно фиксированные компакты нужны нашей цепочке с Гурвицем.

Это исследовательская записка по прямому вопросу владельца, не новая транзакция adjudication для прежнего TXT, не изменение состояния репозитория и не независимое подтверждение всех утверждений MARKOV.

## 1. Что действительно проверено

### 1.1 Оно: найден первичный математический исходник, но не прочитан PDF препринта

**[ABSTRACT | PAPER — аудит формулировок исходника]** В публичном `AxiomMath/RiemannJensen` найдено утверждение именно обсуждаемого типа. Репозиторий зафиксирован на коммите `c1e023fa3ae7161219dde3dcb73f0c28ff972be2`.

`Solution/Basic.lean` содержит без дополнительных RH-предпосылок в видимой сигнатуре:

- для каждого числового поля K существуют C>0 и d₀, так что при d≥d₀ соответствующий Jensen-полином ненулевой и имеет не менее d−C√(d log d) различных отрицательных действительных корней;
- для риманова случая существует C>0, для всех d≥2 одновременно действуют верхняя оценка числа недействительных корней с кратностями и нижняя оценка числа различных отрицательных действительных корней.

Константа в римановом утверждении существующая, не выданная в прочитанной сигнатуре численно. Формулировка для всех d≥2 поэтому не означает practically usable границу для каждого малого d.

`Challenge/Basic.lean` задаёт целевой контракт над Mathlib. Его `sorry` — заглушки challenge, а не обнаруженный дефект опубликованного solution. `Solution/Basic.lean` ссылается на реализующие теоремы. В `Comparator/comparator.json` перечислены четыре проверяемых экспорта и разрешены только `propext`, `Quot.sound`, `Classical.choice`; включён `enable_nanoda`.

**Граница проверки:** я прочитал контракт, solution-wrapper, настройки comparator и целевые аналитические модули. Я не запускал Lean/comparator и не проверил весь транзитивный граф зависимостей. Утверждение README об успешной проверке — сообщение авторов, не наш собственный результат выполнения.

PDF/HTML по `arXiv:2610.38870` инструмент не вернул. Это не доказательство отсутствия статьи. Первичный код подтверждает содержательное утверждение, но я не выдаю это за построчный аудит Theorem 1/3 PDF или за byte-exact совпадение его версии с кодом. В `CITATION.cff` заголовок отличается от заголовка дайджеста и стоит `date-released: 2026-10-21`; это метаданные software, не самостоятельно подтверждённая дата подачи препринта.

### 1.2 Остальные четыре пункта дайджеста

**[FINITE_CELL | PAPER — чтение опубликованных отчётов, не воспроизведение исследований]**

| Пункт | Проверка | Существенная поправка |
|---|---|---|
| Nature Cancer, irAE-agent | Публикация от 29.10.2026 и основные числа подтверждены | 316 временных наблюдений — задания 17 участников на 20 уникальных заметках. 43,5% — сокращение медианного времени разметки, не всей клинической документации. Общая точность градации не дала значимого улучшения; это отдельный endpoint от complete-match и согласия аннотаторов. |
| Nature Communications, AIMS-LDR | Подтверждены заявленные >34% дополнительных ложных диагнозов и приблизительно −40% reproducibility | Сравнение ретроспективное; на странице — принятая peer-reviewed ранняя версия. «Больше ложных диагнозов» нельзя автоматически читать как изменение specificity на 34 процентных пункта. |
| Nature Medicine, EVLF-FM | Подтверждены публикация, 8B, 1,3 млн samples и внешняя проверка | Авторы прямо ограничивают вход статическими 2D-изображениями. Это не готовый volumetric CT- или whole-slide-агент. |
| Zaman–Zhao, Artin L-functions | Авторская страница подтверждает работу с этим названием и авторами | Там она обозначена `In preparation`; текст arXiv:2610.40267 получить не удалось. Дата подачи и Theorems 1.2–1.4 в этом обзоре не подтверждены. Страница могла отстать от подачи; фальсификация не утверждается. |

Ничего из этих медицинских исследований не импортируется как математическая предпосылка. Неустановленные детали Artin-препринта не используются для выбора маршрута.

## 2. Где мы находимся после MARKOV

**[ABSTRACT | CONDITIONAL — статус последнего PAPER-артефакта]** Последний локально прочитанный файл `PROSHKA_VERDICT_MARKOV_2026-10-29.md` различает три задачи:

1. **Markov/Perron–Frobenius для pole-free bulk G на полном непрерывном окне.** В нём дано PAPER-доказательство положительно улучшающей полугруппы и простого чётного основного состояния. Это не автоматический результат для конечной Fourier-компрессии с N=m.
2. **G1a для исходного K.** Нужна строгая очередность нижних чётного и нечётного уровней. Source displacement algebra связывает её с простотой и ненулевым eta-парингом. Нового кофинального знака нет.
3. **G3 / глобальный знак.** Compact-uniform tracking и нужные sharp inequalities остаются открытыми.

Особенно важно: §4 MARKOV заявляет новое source-specific следствие

\[
\rho\notin\{\Re s=1/2\}\quad\Longrightarrow\quad
n_-(G_{m,m,E})\ge2,\quad n_-(G_{m,m,O})\ge1
\]

на всех достаточно поздних исходных ячейках. Сам файл заканчивается требованием **независимого PAPER-аудита** этого построения и возврата на N=m. Я не нашёл в текущем разговоре результата такого независимого аудита. Поэтому не повышаю этот фрагмент до независимо принятого факта.

Это не повод отступать от математической задачи. Это точное место, где новый внешний поставщик должен помочь проверке, а не скрыть её.

## 3. Точное пересечение с Оно: один и тот же theta-источник

### 3.1 Не аналогия, а равенство

**[ABSTRACT | PAPER]** В MARKOV, (4.3), определено

\[
h(x)=\sum_{n\ge1}
(16\pi^2n^4e^{9x/2}-24\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}}.
\]

В `RiemannJensen/Theta.lean` определено

\[
\Phi(x)=\sum_{n\ge1}
(4\pi^2n^4e^{9x/2}-6\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}}.
\]

Следовательно, непосредственно по определениям и абсолютной сходимости,

\[
\boxed{h(x)=4\Phi(x).}                                      \tag{S1}
\]

Никакой замены арифметического семейства здесь нет. Это тождество функций, не тождество спектральных задач.

### 3.2 Что действительно можно переиспользовать

**[ABSTRACT | PAPER — source review, не выполненная kernel-проверка]** В прочитанных файлах присутствуют:

- `summable_thetaTerm` и `thetaPhi_pos`;
- `expMoments_thetaPhi` — все экспоненциальные моменты на положительной полуоси;
- `gammaCoeff_eq_thetaGammaCoeff` — связь Taylor-коэффициентов с моментами;
- `gammaCoeff_pos`;
- использование `xiThetaIntegral_eq_centeredXi` в доказательстве моментной формулы.

Это подходящие кандидаты для сокращения нашей analytic/formalization debt: сходимость, положительность ядра, дифференцирование под интегралом, моментная нормировка. Перед импортом обязательны совпадение версии Mathlib и проверка точного типа каждого расходуемого утверждения.

По нашим Fourier-конвенциям

\[
\widehat h(z)=4\xi(1/2-iz),
\]

а в Axiom-определениях `centeredXi(w)=ξ(1/2+w)`. Поэтому

\[
\boxed{w=-iz.}                                            \tag{S2}
\]

Совпадение имени `centeredXi` не разрешает отождествлять переменные без этого поворота.

Для их коэффициентов

\[
\xi(1/2+w)=\sum_{j\ge0}\frac{\gamma_j}{j!}w^{2j}
\]

получаем

\[
\boxed{\gamma_j=\frac{j!}{4(2j)!}\int_{\mathbb R}h(x)x^{2j}\,dx.}       \tag{S3}
\]

Это вывод из (S1), чётности и нормированной интегральной формулы. Факторы 4 и j!/(2j)! существенны.

### 3.3 Чего эти леммы не дают

В MARKOV остаётся неравенство

\[
\mathcal E_h[F]\ge
8\operatorname{Var}_{\mu}(F)+8\left|\int\tanh(x/2)F(x)\,d\mu(x)\right|^2,
\quad d\mu=\tfrac12\cosh(x/2)h(x)\,dx.                    \tag{S4}
\]

В \(\mathcal E_h\) входят **парные значения h в арифметических сдвигах** и все prime powers. Положительность отдельных моментов \(\int h x^{2j}\) не доказывает sharp domination (S4). Точно так же она не доказывает знак secular scalars или ground parity у K.

**Вывод:** общий theta-источник даёт реальный аналитический импорт; утверждение «почти все Jensen-корни действительны» не является поставщиком (S4).

## 4. Решающий аудит масштаба: какие корни на самом деле контролируются

### 4.1 Полиномы и фиксированные нули ζ

**[ABSTRACT | PAPER]** Зафиксируем именно определения из репозитория:

\[
J_d(X)=\sum_{j=0}^d\binom dj\gamma_jX^j,
\qquad
A(Y)=\sum_{j\ge0}\frac{\gamma_j}{j!}Y^j.
\]

Чётность entire-функции ξ вокруг 1/2 означает, что A — entire и

\[
A(w^2)=\xi(1/2+w).
\]

Запись через ряд избегает выбора ветви квадратного корня. Из неё следует

\[
\boxed{J_d(Y/d)\longrightarrow A(Y)}
\]

локально равномерно. Здесь d→∞, а Y остаётся в фиксированном компакте.

Есть простой количественный бюджет, который не использует RH. Положим

\[
r_{d,j}=\begin{cases}
\prod_{k=0}^{j-1}(1-k/d),&j\le d,\\
0,&j>d.
\end{cases}
\]

Для d≥1 и всех j≥0:

\[
0\le1-r_{d,j}\le\frac{j(j-1)}{2d}.                        \tag{S5}
\]

При j≤d это неравенство \(1-\prod(1-a_k)\le\sum a_k\), где 0≤a_k≤1; при j>d правая часть уже ≥1. Используя \(\gamma_j>0\), получаем для R>0

\[
\boxed{
\sup_{|Y|\le R}|J_d(Y/d)-A(Y)|
\le\frac{R^2A''(R)}{2d}.}                                \tag{S6}
\]

Это собственный элементарный PAPER-вывод из точных определений и положительности коэффициентов, а не приписанная Оно новая теорема. Положительность коэффициентов можно заменить абсолютной мажорантой, если рассматривать другой entire-источник.

Теперь предположим для теста, что у ζ есть ноль

\[
\rho=\tfrac12+\delta+i\gamma,\qquad \delta>0.
\]

Тогда

\[
Y_\rho=(\rho-1/2)^2
=\delta^2-\gamma^2+2i\delta\gamma
\]

является недействительным нулём A. Нет нетривиальных действительных нулей ζ в критической полосе, поэтому \(\gamma\ne0\). Ненулевая производная локальной карты w↦w² сохраняет кратность.

Возьмём малый диск D вокруг \(Y_\rho\), не пересекающий действительную ось и другие нули, и положим b=min∂D|A|>0. При достаточно большом d, например когда правая часть (S6) меньше b для содержащего D радиуса R, Руше даёт столько же нулей \(J_d(Y/d)\) внутри D, сколько имеет A.

Следовательно, для простого нуля существует ветвь корней

\[
\boxed{X_d=\frac{Y_\rho+o(1)}{d}.}                        \tag{S7}
\]

При кратности r получается r корней в каждом из двух сопряжённых малых дисков. Итак, одна off-line quartet ζ требует не менее 2r недействительных Jensen-корней при всех больших d. Это совместимо с верхней оценкой C√(d log d), растущей до бесконечности.

Важно: (S7) — не утверждение о существовании внелинейного нуля. Это условный falsifier того, что может или не может исключить новый count bound.

### 4.2 Реальное окно доказательства в исходном коде

**[ABSTRACT | PAPER — точный перенос прочитанных определений]** В `Analysis/Scale.lean` масштаб T_d задаётся уравнением

\[
\frac{T_d}{2\pi}\left(\log\frac{T_d}{2\pi}-1\right)=d,
\qquad T_d>2\pi e.
\]

Также записаны \(T_d\Lambda_d=4\pi d\) и \(\Lambda_d\asymp\log d\). Поэтому \(T_d\asymp d/\log d\) и \(T_d\to\infty\).

В `MainTheorem/Counting.lean` транспорт отрицательных корней имеет вид

\[
\boxed{X=-\frac{T_d^2}{d q}.}                            \tag{S8}
\]

В `MainTheorem/CountingAssembly.lean` верхний конец используемого oscillation window есть

\[
q\le c_0T_d,
\]

где c₀=`oscillationC0` — фиксированная положительная константа. Значит **каждый корень, полученный этим контролируемым механизмом**, удовлетворяет

\[
\boxed{|dX|=\frac{T_d^2}{q}\ge\frac{T_d}{c_0}\longrightarrow\infty.}    \tag{S9}
\]

В исходной X-плоскости это \(|X|\gtrsim1/\log d\), в то время как фиксированный ноль ζ из (S7) лежит при \(|X|=O(1/d)\).

**Это и есть точный несовпадающий масштаб.** В нормировке Y=dX те корни, которые построены для массового подсчёта, уходят за любой фиксированный компакт. Корни, кодирующие фиксированную точку ζ, остаются в фиксированном компакте.

Отсюда нельзя делать более сильный вывод, будто все исключения лежат у нуля или что вся saddle-point методология принципиально не может туда добраться. Проверено более узкое утверждение: **прочитанное основное counting-window доказательство не даёт нужного нам контроля на фиксированном Y-компакте**. Расширение окна потребовало бы новой, реально оплаченной оценки.

### 4.3 Почему «удалить оставшиеся корни» не ремонтирует Гурвица

**[ABSTRACT | PAPER]** Количество исключений само по себе не контролирует их аналитический вклад. Для d≥3 рассмотрим

\[
P_d(z)=(1+z^2)\prod_{k=1}^{d-2}\left(1+\frac{z}{d+k}\right).
\]

Здесь d−2 различных отрицательных корня и два постоянных недействительных корня ±i. На компактах

\[
P_d(z)\longrightarrow(1+z^2)e^{z\log2}.
\]

Доказательство: сумма \(\sum_{k=1}^{d-2}(d+k)^{-1}\to\log2\), а сумма квадратов обратных знаменателей — O(1/d), поэтому логарифм произведения сходится равномерно на компактах.

Таким образом, доля различных действительных корней стремится к 1 и имеется compact-uniform предел, но у предела остаются ±i. После удаления этих двух корней предел меняется. Это synthetic контроль абстрактного перехода, не модель ζ и не опровержение результата Оно.

## 5. Как это сочетается с нашей архитектурой

| Наш потребитель | Что потребовалось бы | Что реально дал просмотр нового источника |
|---|---|---|
| G1a, строгий порядок parity bottoms исходного K_m | Коффинальная source-specific нижняя/верхняя граница или secular bracket | Не дано: Jensen-полином не characteristic polynomial K_m |
| G3, tracked ground transform → Xi на компактах | Норма именно разности исходной ground-семьи и Xi | Дана другая аппроксимирующая семья; отсутствует оценка связи с ground-семьёй |
| Sharp theta-weighted inequality MARKOV (6.9) | Доминирование variance/covariance с коэффициентом 8 | Совпало h, но знак арифметических парных вкладов не установлен |
| Аналитические поставщики для h | Положительность, moments, integrability, Mellin/Taylor-normalization | Найдены конкретные Lean-модули, заслуживающие локального воспроизведения |
| Исключение фиксированного off-line zero | Контроль микроскопического режима X=O(1/d), то есть фиксированного Y=dX | В основном counting-window механизме этот режим отсутствует |

**[ABSTRACT | PAPER]** То, что обе программы используют xi и theta, не делает их конечные матрицы унитарно эквивалентными. Не найдено равенства форм, интертвинера или теоремы, переносящей число недействительных Jensen-корней в отрицательный индекс именно нашего G_m или parity gap K_m.

Простой контроль масштаба спектральных требований: матрица diag(−1,1,…,1) имеет долю положительных собственных значений, стремящуюся к 1, но её минимум всегда отрицателен. Это не source counterexample, а напоминание о различии доли и крайнего уровня.

Результат об экстремумах Artin L(1,χ), даже в заявленной дайджестом форме, относится к существованию расширений и величине L-значений. Без отдельного uniform transfer к фиксированному source-семейству он не поставляет ни G1a, ни G3, ни (S4). До получения текста не назначаю ему более конкретную роль.

## 6. Следующий ход: один приоритет, две проверяемые альтернативы

### Приоритет

**Не запускать новую кампанию вычисления real-root percentages. Выполнить уже поставленный независимый аудит MARKOV §4, используя общий theta-источник для сокращения проверяемого аналитического основания.**

Причина выбора: исход аудита определяет, являются ли bulk-index условия самостоятельными промежуточными леммами или уже полным zero-exclusion обязательством. В любом случае это меняет выбор дальнейшей стратегии. Ещё одна таблица почти действительных Jensen-корней этого не меняет.

### Один CODEX DIRECTIVE

```text
TARGET: MARKOV_SECTION4_OFFLINE_ZERO_PARITY_WITNESS_DIAGONAL_RETURN
MODE: READ_ONLY_INDEPENDENT_PAPER_AUDIT
INPUT_A: retained PROSHKA_VERDICT_MARKOV_2026-10-29.md, section 4
INPUT_B: its source pin ab6394323c40ed2c1b0a720778f0fb09662dc0bb
INPUT_C: AxiomMath/RiemannJensen at c1e023fa3ae7161219dde3dcb73f0c28ff972be2

Claim to check:
An off-critical zeta zero gives n_-(G_{m,m,E}) >= 2 and
n_-(G_{m,m,O}) >= 1 for every sufficiently large ORIGINAL m,
with L=log(m), N=m.

First lock h=4*thetaPhi and w=-i*z. Reuse only exact, inspected
source statements about h; do not import the Jensen root-count
conclusion as an energy inequality.
Then check pole annihilation, parity/reality, the quartet values,
the even mixed pairing, and the complete expanding-window
Fourier return with all prime powers and both endpoints.

PASS: negative upper envelopes on both constructed source subspaces,
with an explicit vanishing return budget and the unchanged schedule.
FAIL: the first incorrect or unpaid analytic estimate, its exact
location, and the weakest repaired statement.

No repository edits, no broad eigensolver scan, no replacement
N=N(L) chosen after the window, no RH/index/tracking premise.
Outputs:
INDEX_WITNESS_DIAGONAL_RETURN_CONFIRMED_PAPER
or INDEX_WITNESS_FIRST_UNPAID_TERM.
```

Чтение чужих Lean-лемм не заменяет независимый PAPER-аудит нашего нового вывода. Отдельный runtime-gate для внешнего пакета, если он включается в этот аудит: команда, указанная авторами, `lake env comparator Comparator/comparator.json` в зафиксированном checkout с установленным comparator. Такой запуск здесь не выполнялся. Ожидаемый axiom profile — ровно три стандартных аксиомы из manifest; соответствие математического объекта проверяется отдельно.

### Две альтернативные репрезентации незакрытого фронта

| Репрезентация | Что должно закрыть задачу | Decision power / стоимость | Stop/discriminator |
|---|---|---|---|
| **Theta-weighted jump defect** \(\mathcal D_h[F]=\mathcal E_h[F]-8\operatorname{Var}_\mu(F)-8|\int\tau Fd\mu|^2\) | Строгая source-specific нижняя оболочка на нужном классе | Высокая / высокая аналитическая; kernel-import умеренный | Положительные моменты без контроля парных prime-shifts не считаются продвижением. DISCRIMINATOR: сертифицированный знак полного defect с exterior terms. |
| **Microscopic Jensen divisor** \(J_d(Y/d)\) на фиксированных Y-контурах | Отсутствие недействительных нулей в нужных компактах с явным remainder | Высокая / высокая; тест масштаба дешёвый | Основной count window уже не проходит область. DISCRIMINATOR: winding number на nonreal диске, а не доля real roots. |

Ни одна альтернатива не разрешает эскалировать вычисления без нового источникового неравенства. Для G1a сохраняется более слабый путь через guarded secular bracket самого K; он не требует подменять G1a всей Weil-положительностью.

## 7. Клиническая синергия: взять устройство проверки, а не рекламный процент

Это предложения по дизайну нашего исследования, а не результаты перечисленных статей.

Для хирургического консил-агента я бы разделил **генерацию дифференциала** и **принятие клинического утверждения**. Каждая принимаемая находка должна иметь проверяемую привязку к записи/изображению, temporality и статус неопределённости. Рекомендация к действию — отдельный объект от гипотезы.

Практическая схема: development на ретроспективном корпусе; затем silent-проверка на временно и организационно отделённой выборке; затем рандомизированное сравнение человека и человека с агентом. В анализе учитывать перекрёстную зависимость doctor×case, перенос обучения между периодами, распространённость событий и неоднозначность gold standard.

Три приоритетных результата: время до клинически принятого решения, клинически значимые ошибки/ложные действия, стабильность повторных запусков. На этом фоне отдельно измерять согласие врачей. Высокое согласие с одним AI-предложением может отражать общую якорную ошибку, поэтому оно не заменяет независимую accuracy/safety-оценку.

Для изображений сначала определить наш реальный unit of analysis: срез, 3D-исследование, patch или целое стекло. Результат на 2D-изображениях не переносить на 3D/WSI без собственного адаптера и проверки. Проверять не красоту объяснения, а его согласованность с маркированным свидетельством и поведение при удалении/изменении релевантной области; такое возмущение тоже должно оставаться клинически осмысленным.

Общая инженерная идея для AI-медицины и AI-математики: генератор предлагает, независимый контур проверяет. Но 34% из клинического benchmark не переносится числом на частоту ложных математических доказательств; это лишь архитектурная аналогия.

## 8. Леджер утверждений и dependency epistemics

| ID | Scope | Verifier | Результат | Ограничение |
|---|---|---|---|---|
| L1 | ABSTRACT | PAPER | Точная формулировка main exports найдена в первичном коде | Не воспроизведён kernel/comparator |
| L2 | ABSTRACT | PAPER | h=4thetaPhi и w=−iz | Не равенство Jensen- и CCM-операторов |
| L3 | ABSTRACT | PAPER | Количественная compact-оценка (S6) | Не утверждает real-rootedness |
| L4 | COFINAL_FAMILY | PAPER | Гипотетический off-line zero порождает микроскопические Jensen-корни (S7) | Никакой actual off-line zero не предъявлен |
| L5 | COFINAL_FAMILY | PAPER | Подсчитанные посредством прочитанного окна корни удовлетворяют (S9) | Не классифицирует все корни и все возможные варианты метода |
| L6 | ABSTRACT | PAPER | Density-one plus local convergence не даёт real-zero limit | Synthetic контроль, не контрпример ζ |
| L7 | COFINAL_FAMILY | CONDITIONAL | MARKOV index-witness theorem — источник для аудита | Новая независимая проверка не завершена здесь |
| L8 | FINITE_CELL | PAPER | Проверены три publisher reports и их ограничения | Не выполнена независимая репликация клинических результатов |

```yaml
DOWNSTREAM_CONSUMER: SAME_FAMILY_G2_G3_HURWITZ_ROOF_OR_EXPLICIT_WEIL_SIGN
ACTUAL_CONSUMER_REQUIREMENT:
  - REAL_ZERO_GROUND_FAMILY_WITH_COMPACT_UNIFORM_TRACKING
  - OR_PROVED_NONNEGATIVE_FULL_WEIL_FORM_WITH_AN_EXHAUSTION_RETURN
ORIGINAL_REQUESTED_OBJECT: SYNERGY_OF_NEW_LITERATURE_WITH_THE_ACTIVE_ROUTE
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - EXACT_THETA_MOMENT_ANALYTIC_SUPPLIERS_FOR_EXISTING_SOURCE_LEMMAS
  - GUARDED_PARITY_BRACKET_FOR_K_PLUS_DIRECT_G3
  - MICROSCOPIC_DIVISOR_CONTROL_RATHER_THAN_GLOBAL_ROOT_PERCENTAGE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: EXACT_THETA_CROSSWALK_AND_SCALE_SEPARATION
REOPEN_TRIGGER:
  - NEW_SOURCE_BOUND_IN_THE_MICROSCOPIC_JENSEN_REGIME
  - ACTUAL_INTERTWINER_OR_FORM_IDENTITY_TO_THE_UNCHANGED_CCM_CONSUMER
  - NEW_SIGNED_ARITHMETIC_BOUND_FOR_THE_FULL_THETA_WEIGHTED_DEFECT
KILL_SCOPE: null
ROUTE_FAMILY_DEATH: NOT_ASSERTED
```

## 9. Сильнейшая атака на предлагаемый вывод

«Ты увидел одно counting-window доказательство и объявил весь метод Оно бесполезным». Это было бы неправильно. Я не объявляю метод бесполезным. (S9) ограничивает **проверенный импорт**: из него нельзя получать compact zero control. Новая оценка для другого окна могла бы изменить заключение.

«Общий theta-источник — просто ещё один мост без выигрыша». Для знака это верно: никакой новый знак не получен. Практическая ценность строго уже — не заново формализовать интегральное представление и моменты, если они уже доступны в проверяемом пакете. Именно поэтому основной следующий target — аудит существующего source-specific witness, а не строительство нового слоя абстракций.

«INDEX_RH_GRADED из прошлого ответа уже можно считать установленным». Нет: в нашем provenance это PAPER-артефакт, чей автор сам запросил независимую проверку. Новая статья не выдаёт такую проверку автоматически.

## 10. Прогнозы, closeout и память стратегии

До чтения counting-window файлов был явно поставлен тест охвата масштаба X=O(1/d). Количественная вероятность исхода не регистрировалась; задним числом HIT не начисляется. Само равенство h=4thetaPhi найдено при чтении определений, а не предсказано экспериментом.

**Результат теста:** (S8) и верхняя граница q дают (S9), поэтому в проверенном основном counting window нужный компактный режим отсутствует. Это exact PAPER-проверка масштаба, не численный эксперимент.

Прогноз для следующего аудита: внешний theta-пакет может закрыть часть аналитических оснований, но не заменяет проверку pole-annihilation и N=m projection-return. Статус — PENDING; никаких вероятностей или исходов прежнего MARKOV не переписано.

Что стало точнее: теперь названы и точный общий объект, и точный несовпадающий масштаб. Что не изменилось: G1a, G3, secular signs и sharp constant 8 остаются открытыми. Чего не делать снова: считать high-degree real-root percentage доказательством compact zero exclusion; принимать общий xi-источник за unitary equivalence конечных операторов; платить формализацию повторно без проверки существующих экспортов.

```yaml
iteration:
  target: EXTERNAL_ONO_SUPPLIER_TO_CURRENT_CCM_ROUTE
  status: OPEN
  failed_strategy: IMPORT_GLOBAL_DENSITY_ONE_ROOT_COUNT_AS_COMPACT_ZERO_CONTROL
  cognitive_operator_used: LITERATURE_BRIDGE
  new_gap_name: MICROSCOPIC_JENSEN_CONTROL_OR_ACTUAL_CCM_SIGN_SUPPLIER
  invariant_learned: H_EQUALS_4_THETA_PHI_BUT_JENSEN_DEGREE_IS_NOT_CCM_CUTOFF
  forbidden_future_move: DROP_THE_EXCEPTIONAL_FACTOR_WITHOUT_COMPACT_ERROR_CONTROL
  next_decisive_test: INDEPENDENT_MARKOV_SECTION4_DIAGONAL_RETURN_AUDIT
```

## 11. Источники и точные границы чтения

### Первичный внешний код

Все следующие файлы READ через GitHub connector на `AxiomMath/RiemannJensen`, commit `c1e023fa3ae7161219dde3dcb73f0c28ff972be2`:

| Файл | Что прочитано / использовано |
|---|---|
| `README.md` | Описание результата и команда comparator; авторское сообщение об успешной проверке |
| `CITATION.cff` | Автор, альтернативный software-title, дата и URL из метаданных |
| `Challenge/Basic.lean` | Определения и четыре challenge-утверждения |
| `Solution/Basic.lean` | Точные solution-wrapper signatures |
| `Comparator/comparator.json` | Четыре exports, три разрешённые аксиомы, nanoda flag |
| `RiemannJensen.lean` | Список импортируемых модулей; не аудит всех их тел |
| `RiemannJensen/Definitions.lean` | Коэффициенты, Jensen-полиномы, root counts, xi-normalization |
| `RiemannJensen/Theta.lean` | Полные определения thetaPhi и базовые леммы |
| `RiemannJensen/Analysis/XiThetaMoments.lean` | Показанные определения и доказательства моментной связи, завершающий фрагмент positivity; без заявления об audit всего import graph |
| `RiemannJensen/Analysis/Scale.lean`, строки 1–220 | scaleT, scaleLambda, точное уравнение и logarithmic bounds |
| `RiemannJensen/MainTheorem/Counting.lean` | Точный reciprocal transport и условный phase-span root counter |
| `RiemannJensen/MainTheorem/CountingAssembly.lean`, строки 1–210 | Верхний endpoint q=c₀T_d и используемая oscillation formula |

Локатор: `https://github.com/AxiomMath/RiemannJensen/tree/c1e023fa3ae7161219dde3dcb73f0c28ff972be2`.

### Наши источники

- READ: bootstrap `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` на `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`.
- READ: локально сохранённый `PROSHKA_VERDICT_MARKOV_2026-10-29.md`, введение, §4, §6, §8, последняя директива. Использован для точного текущего объекта и границы доказанного; не выдан за независимый аудит самого себя.
- Предшествующие ответы в истории — контекст. Новые утверждения не выводились из пересказа их результатов без чтения соответствующих формул MARKOV.

### Внешние клинические первоисточники

- READ, publisher text, Gallifant et al., Nature Cancer, 29.10.2026, DOI `10.1038/s43018-026-01264-6`: abstract, Fig. 3 caption, randomized-workflow и prospective-silent sections в возвращённом поиском тексте. Прямое открытие страницы не удалось; точные фрагменты получены из индексированного текста самого издателя.
- READ, publisher abstract/record, Wu et al., Nature Communications, 29.10.2026, DOI `10.1038/s41467-026-78520-x`: граница controlled retrospective, модельные и physician-study эффекты, accepted early version. Полный supplementary/statistical reanalysis не проводился.
- READ, publisher text, Bai et al., Nature Medicine, 29.10.2026, DOI `10.1038/s41591-026-04655-5`: abstract, results, limitation о 2D, основные methods sections. Прямое открытие страницы не удалось; использован текст самого издателя, возвращённый поиском.
- READ, авторская страница `https://kristopherz.net/`: название Zaman–Zhao и статус `In preparation` в доступном снимке. Это не аудит нового препринта.

### Не импортировано

- PDF/HTML `arXiv:2610.38870` и `arXiv:2610.40267`: попытки открытия не дали содержимого. Не помечаются READ.
- Secondary arXiv-агрегатор: помог подтвердить обсуждаемую запись для поиска; не расходуется как доказательство.
- Случайные результаты поиска о Jensen/RH: не использованы как поставщики теорем.
- Архивы публичных публикаций авторов: использованы только для поиска, не для утверждения отсутствия новых работ.

**Итог:** общий theta-код найден, точный масштабный барьер установлен, новый кофинальный знак не получен. Не меняем математический маршрут из-за заголовка; используем найденный первичный пакет там, где он действительно совпадает с нашим объектом.
