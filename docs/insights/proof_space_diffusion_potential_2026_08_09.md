# Диффузионный потенциал на пространстве доказательства — адъюдикация и первый probe

```yaml
status: exploratory, ADVISORY_ONLY
authority: не proof-source, не route-selection, не theorem note
date: 2026-08-09
body: CLAUDE_CODE_LINUX
branch: claude/ricci-flows-proof-search-emucjh
instrument: scripts/proof_potential.py (read-only)
```

```text
SEARCH_FLAGS (ask.sh, 2026-08-09):
  ricci        -> 1 hit: litreview ZOTERO_MASTER.md [30][34][35][37]
                  «Perelman Ricci-flow trilogy -> unrelated (methodology/analogy only)»
  diffusion    -> НЕ НАЙДЕНО НИГДЕ
  kontorovich  -> НЕ НАЙДЕНО НИГДЕ
  pagerank     -> НЕ НАЙДЕНО НИГДЕ
  proof graph / laplacian / harmonic / heat kernel
               -> хиты только про математику самого Q3 (RKHS, prime graph SOS,
                  HeatKernel в Lean), не про поисковую методологию
RELAY: атрибуция идеи Конторовичу — relay, не верифицировано; премиссой не является.
```

## 1. Идея (как пришла от владельца)

Лабиринт: холод (T=0) на вход, жар (T=1) на выход, уравнение теплопроводности,
стационарное T, идти по градиенту. Перенос: пространство утверждений как граф,
холод на доказанное, жар на RH, штраф на тупики, диффузия/Лаплас, градиент
показывает перспективное направление. Максимальная версия: «настоящий
геометрический поток типа Риччи на пространстве метрик доказательств».

## 2. Вердикт по частям

### 2.1 Что честно выживает

На **известном конечном графе** идея корректна и имеет стандартные имена:
стационарное T с граничными условиями = задача Дирихле; T(v) = вероятность,
что случайное блуждание из v поглотится на «жаре» раньше, чем на «холоде»
(harmonic measure / absorbing Markov chain); «штраф на тупики» = поглощающие
холодные узлы. Это **value-функция поиска**, т.е. prioritization-эвристика.
Место такого сигнала в проекте — уровень `COGNITIVE_KERNEL.md` (выбор
оператора мышления при стагнации), не уровень математики.

Kills с AUTOPSY-тегами — буквально готовое «холодное множество» из идеи:
проект уже годами дисциплинированно копит то, что в лабиринтной картинке
называется «посещённые тупики».

### 2.2 Что умирает

1. **«Диффузия на пространстве всех утверждений».** В лабиринте уравнение
   решается на *данном* графе коридоров. Граф утверждений не дан: он локально
   бесконечно ветвится и открывается только генерацией ходов. Диффузия не
   порождает новых узлов — она только перевзвешивает уже исследованное.
   Значит метод в принципе не заменяет генерацию, а лишь ранжирует фронты
   исследованной части; вся информация о неисследованном сидит на границе.

2. **Категориальная ошибка OR vs AND.** Лабиринт — чисто OR-объект: достаточно
   одного пути, локальная связность = глобальная достижимость. Доказательство —
   AND/OR-объект: лемме нужны *все* посылки; цепочка с одним разорванным звеном
   стоит ноль. Диффузия считает средние по соседям, т.е. систематически
   награждает «много слабых почти-связей» и штрафует «одну точную цепочку» —
   ровно противоположно семантике доказательства. Честный дискретный аналог для
   AND/OR-графов давно существует: proof-number search (PN): вместо среднего —
   min по OR-веткам и sum по AND-посылкам. Если строить сигнал на goal-слое,
   строить надо PN-подобный, а диффузионный держать как OR-релаксацию.

3. **«Настоящий поток Риччи на метриках доказательств».** Объект не определён:
   нет ни метрики, ни кривизны на «пространстве метрик доказательств». В
   лабиринтном примере геометрия фиксирована и уравнение линейно; у Перельмана
   эволюционирует сама метрика нелинейным потоком — это другой механизм, из
   аналогии он не следует. Максимальный честный родственник — дискретная
   кривизна Олливье/Формана на графе как детектор bottleneck-рёбер:
   диагностика, не поиск. Litreview уже квалифицировал трилогию Перельмана как
   «methodology/analogy only» — подтверждаю эту квалификацию.

### 2.3 Риск, из-за которого ADVISORY_ONLY

Граф, на котором мы можем решать задачу Дирихле, — наш собственный,
кураторский: его топология кодирует наши приоритеты. Потенциал на нём — это
отмывка собственных приоров через PDE. Читать его как evidence о математике =
surrogate (CODEX_CONTROL §13); поэтому инструмент печатает `ADVISORY_ONLY` и
никогда не входит в премиссы.

## 3. Что показал диск (probe, 2026-08-09)

### 3.1 Lean-слой: лабиринт уже решён, диффузия отвечает тривиально

Замыкание обоих корней (`Q3.Main.RH_of_Weil_and_Q3`, 66 файлов;
`Q3.RH_of_shifted_atom_route`, 65) — **0 sorry, 0 taint**; вся недоказанность
сжата в две аксиомы-двери: `Q3.Weil_criterion` (Q3/Axioms.lean, цитированный
критерий) и `Q3.prime_term_le_at_t_critical_axiom`
(Q3/Proofs/Q_nonneg_t_critical.lean, собственный математический долг).

Числа потенциала (равномерный спуск по зависимостям из корня):

```text
entry exposure = 0.4416       (вероятность упереться в открытую аксиому)
  via Q3/Axioms.lean                        0.3098
  via Q3/Proofs/Q_nonneg_t_critical.lean    0.1318
ground mass    = 0.5584       (поглощено в полностью доказанном полу)
8 файлов с температурой 1.0000 — чисто условная зона
  (off_diag_exp_sum_integrated, node_spacing_integrated, Rayleigh_utils,
   Rayleigh_basis0, Rayleigh_Fourier, Q_nonneg_lemmas, FloorCert/Defs,
   A3_bridge_rayleigh_first)
```

Оба корня дают идентичные числа — atom-route делит весь конус с Main. На этом
слое градиент не сообщает ничего, чего не сообщал `#print axioms`: это
negative control, и он важен — идея имеет содержание только там, где лабиринт
ещё не решён.

### 3.2 Goal-слой: единственное место, где идея может заработать — и он ill-posed

Граничные условия существуют: **71 kill** в knowledge.db (структурированные:
track, stop_code, forbidden_future_move), 5 walls, 8 AUTOPSY-событий. Но:

```text
fronts:    все walls в UNCLASSIFIED_FRONT  -> нет пути front->target
link rows: 6 на 76 холодных узлов          -> у графа есть граница, но нет
                                              внутренности; диффузии не через
                                              что течь
well_posed: False
```

Чтобы слой стал well-posed, нужно ровно три вещи (это измеренная цена идеи):

1. классифицировать walls/kills по фронтам (уйти от UNCLASSIFIED_FRONT);
2. дать goal->front и front->target рёбра (DAG фронтов, хотя бы для живых:
   H1^f ladder, Route B bus, PSD-pd);
3. после этого потенциал считается тем же инструментом, но семантику брать
   PN-подобную (min/sum), а не чисто диффузионную (среднее) — §2.2.

Пока рёбер нет, любой «глобальный сигнал» на goal-слое был бы выдумкой.

## 4. Decision record (§13.1)

Рассмотрено и отвергнуто:

- **A. Диффузия на пространстве утверждений** — граф не дан, метод не
  порождает узлов (§2.2.1);
- **B. Поток Риччи на «метриках доказательств»** — объект не определён,
  из аналогии не следует (§2.2.3);
- **C. Кривизна Олливье на goal-графе прямо сейчас** — рёбер нет (link=6),
  диагностика без носителя.

Выбрано: **D. Минимальный read-only probe** — точный потенциал на Lean-слое
(negative control, exact solve по DAG) + измерение ill-posedness goal-слоя с
конкретным списком недостающей структуры. `ARSENAL_USED: none` (по ask.sh
карты с этой сигнатурой механизма нет).

## 5. Запуск

```bash
python3 scripts/proof_potential.py            # Main root, текстовый отчёт
python3 scripts/proof_potential.py --root atom
python3 scripts/proof_potential.py --json     # машиночитаемый дамп
```

Строго read-only; ничего не пишет в tracked-состояние; не входит ни в какой
route и не меняет mainline.

## 5.1 Q3_PROOF_GEOMETRY_V0_BACKTEST — вердикт (2026-08-09, той же сессией)

По директиве владельца построен V0 heat-navigator и прогнан **слепой
исторический бэктест** на коридоре `GOAL056_S2_WALL__GOAL057_B3_0_LADDER`
(25 узлов B3.0A…Q, AND-входы из Lean-импортов, 10 убитых веток GOAL056,
синтетический plant; веса заморожены в `flow.PRECOMMIT` и закоммичены до
прогона — `cad078e`). Один прогон, без тюнинга. Результат:

```text
top-3 rate: flow 0.240 | shortest_path 0.120 | pagerank 0.240 |
            topo_depth 0.400 | random 0.080
plant: выше правильного узла на 15/25 чекпоинтов, в top-3 на cp23,24
SUCCESS: False
FAILURE_CODE: Q3_PROOF_GEOMETRY_NO_PREDICTIVE_GAIN
FAILURE_CODE: Q3_PROOF_GEOMETRY_FAKE_SHORTCUT_ACCEPTED
```

Механизм провала виден в таблице по чекпоинтам (`results_057.json`):
потенциал ранжирует кандидатов по близости к крыше (`M,Q,B3,L` — соседи
target'а), а исторический процесс строил **снизу вверх** — правильный
следующий узел почти всегда глубокий, только что ставший готовым. Поле
ориентировано к цели, а строительство идёт от пола: для вопроса «что строить
дальше» нужен объект типа расстояния-от-пола / PN-readiness
(eikonal-семейство), не harmonic-потенциал близости к цели. Это ровно
KEY_CORRECTION из адъюдикации владельца, теперь с числом. И plant показал
второе: мультипликативный штраф проводимости `0.55·e^{-3}≈0.027` не
выдерживает экспоненциального спада потенциала с глубиной — глубокие честные
узлы имеют `u~10^{-2..-3}`, и сосед цели с крошечной проводимостью всё равно
выигрывает. Доверие должно быть hard gate, не soft penalty.

```text
AUTOPSY: dropped=ORIENTATION; note=goal-ward harmonic field ranks roof-adjacent nodes while construction is floor-ward; correct object is distance-from-floor / PN-readiness
AUTOPSY: dropped=TRUST; note=multiplicative conductance penalty exp(-beta*risk) loses to exponential depth-decay of u; conditional shortcut must be hard-gated
AUTOPSY: dropped=NORMALIZATION; note=score c*(u(out)-mean u(in)) not depth-normalized; potential magnitude dominates readiness signal
```

Положительное: убитые ветки легли на дно (kill в top-3 только на вырожденном
cp24, где живых кандидатов два), AND-структура сохранена (factor-graph guard
не сработал), и `topo_depth=0.40` подтверждает, что порядок строительства —
основной сигнал. Коридор 057 как held-out **сожжён** (данные просмотрены):
любая V0.1 (PN-семантика min/sum, readiness-gate, eikonal-поле) — это новый
прекоммит на свежем коридоре (кандидаты: 040→046 Müntz-цепь, Step32).

Кандидат-запись для knowledge.db (не вносил — canonical store под
write-lock Mac-тела; поля готовы к `kb.py add`):
`subject=V0 goal-ward harmonic potential as next-lemma ranker;
status=KILLED; stop_code=Q3_PROOF_GEOMETRY_NO_PREDICTIVE_GAIN+FAKE_SHORTCUT_ACCEPTED;
forbidden_future_move=rank construction frontier by goal-adjacent harmonic
potential or soft-penalize conditional shortcuts; scope=corridor_057 backtest;
evidence=proof_geometry/results_057.json@<commit>`.

## 6. Побочное наблюдение (записано в момент обнаружения)

`q3.lean.aristotle/ACTIVE/graphs/` и `full/q3.lean.aristotle/ACTIVE/graphs/` —
два байт-идентичных набора графовых JSON в одном дереве; `scripts/build_proof_graph.py`
указывает ROOT на `full/`, ask.sh и Lean-проверки — на верхний. Два чтения:
(а) намеренное зеркало manuscript-дерева; (б) случайная дупликация, которая
разойдётся при первом же несинхронном пересборе. Различитель: один пересбор
генераторов и diff обоих деревьев. Здесь не решаю — probe читает верхний.

## 7. GOAL057_SOURCE_WEIL_EVEN_SECTOR_SPECTRAL_CUT_PREFLIGHT — вердикт

```yaml
status: FAILED at (13,60), stop-rule fired, N=90/120 not evaluated
mode: READ_ONLY_EXPERIMENTAL — не proof-source, не route-selection
directive_source: owner Proshka-format verdict 2026-08-09 (V0 FATAL; RUN selected)
instrument: proof_geometry/spectral_cut/{ccm_source,preflight}.py
precommit: proof_geometry/spectral_cut/PRECOMMIT.md, коммит 22a4575 —
  ДО первого запуска на реальной матрице (проверяемо git-историей)
result_file: proof_geometry/spectral_cut/results_spectral_cut.json
```

```text
SEARCH_FLAGS (ask.sh, 2026-08-09):
  sourceCCMFiniteRayleigh          -> 1 хит: определение в Lean, не значение
  ccmWeilMatFinite null vector     -> НЕ НАЙДЕНО НИГДЕ
  trial nullity kernel spectral    -> НЕ НАЙДЕНО НИГДЕ
```

### 7.1 Протокол выполнен буквально

Все планты прошли **до** интерпретации реальной матрицы: block-diagonal
recovery, one-bridge control, prime-sign mutation (гейт отверг мутацию),
label permutation и ±1 diagonal conjugation на самой K⁺(13,60) — все PASS.
Фаза-0 hard gates — все PASS: sha256-пин восьми Lean-файлов, порядок мод
−N..N, симметрия и `JK=KJ` на полу 10⁻¹⁵, литеральный spot-check
`τ = W02 − WR − Prime` против формулы Lean (12 пар, rel diff ~6e-33),
PSWF-ODE-невязка ψ₀/ψ₄ ~5e-13/5e-14, ортогональность ψ₀⊥ψ₄ ~1e-32,
`∫hTrial=0` точно, `‖kTrial‖=1` точно.

### 7.2 Результат на (13,60)

```text
candidate (Fiedler min-conductance sweep, even sector, dim=61):
  phi (conductance)  = 0.03129     (<= 0.25 порог "meaningful": PASS)
  mu (retained mass) = 1.0         (>= 0.95: PASS)
  epsilon = ||E||_op  = 0.6955
  delta = dist(a,specB) = 0.4940
  rho = epsilon/delta = 1.408      (<= 0.25 required: FAIL, превышение ~5.6x)
  s = epsilon^2/delta  = 0.9793

frozen baselines:
  contiguous_half:  s = 1.3415
  lowhigh_split:    s = 2,133,885  (delta~4.9e-7 — вырожденный разрез)

criteria: not_parity_only=T, mass=T, rho=F, schur_2x=F, phi_meaningful=T
STOP: GOAL057_SPECTRAL_CUT_LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER
```

Fiedler-кандидат направленно бьёт обе замороженные базовые линии
(`s=0.979` против `1.342` и против вырожденных `2·10⁶`), но не дотягивает
до требуемого 2× барьера (нужно `s ≤ 0.671`, получили `0.979`). Важнее:
`rho=1.41 > 1` — перекрёстная связь блоков **превышает** спектральный
зазор, то есть даже пертурбативный/Schur-ряд первого порядка здесь не
гарантированно сходится. Это ровно тот failure mode, который директива
предсказала заранее как наиболее вероятный («graph conductance is a
surrogate without theorem power»), с точным кодом
`LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER`, а не `NO_STABLE_LOW_CONDUCTANCE_CUT`:
граф нашёл структурно осмысленный (низкая проводимость, не голая чётность)
разрез, но оператор его не подтвердил. Registered prediction сбылась
буквально.

Стоп-правило исполнено: N=90,120 не считались.

### 7.3 Замеченное и не объяснённое — записано в момент обнаружения

`a = <q_even, K⁺ q_even> = 2.89·10⁻³²` — Rayleigh-значение source-trial
относительно полного even-sector оператора K⁺ численно **ноль** (на полу
точности dps=30), при том что спектр дополнительного блока B лежит
целиком в `[0.494, 5.019]` — нигде рядом с нулём. Для юнит-вектора это
нетипично: если бы `a` было generic Rayleigh-значением, ожидался бы
порядок величины спектра (~1), а не 32 нуля после запятой. Именно эта
близость к нулю и делает `delta = dist(a, specB) = specB_min` маленьким
относительно `epsilon`, то есть управляет провалом `rho`.

Два прочтения, оба открыты:

1. **Структурное.** Каноническая комбинация `hTrial = (I4·h0 − I0·h4)/‖·‖`
   построена как *единственная* (с точностью до скаляра) комбинация с
   нулевым интегралом (`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`) — если это
   обнуление транспортируется через `E*`/проекцию в почти-точную
   ортогональность к ведущей моде K⁺, тогда trial-вектор *по конструкции*
   близок к null-вектору конечного CCM-оператора. Если так, это не баг, а
   потенциально полезный факт о самом источнике.
2. **Инструментальное.** Вся числовая цепочка (PSWF через диагонализацию
   в базисе Лежандра, `E*`-суммирование, координаты Фурье) — независимая
   Python-транскрипция, не экспортирована из Lean. Структурные гейты
   (симметрия, `J`-коммутация, ODE-невязка, ортогональность ψ₀/ψ₄,
   `∫hTrial=0`, литеральный spot-check τ) — все необходимые условия
   корректности, ни одно не достаточное: они ловят рассинхрон между двумя
   моими путями кода, но не сверяют результат с независимым вторым
   источником. Систематическая ошибка в самой формуле (знак, порядок пары
   `chi0`/`chi4`, диапазон суммирования `E*`), одинаково повторённая в обоих
   моих путях, прошла бы все текущие гейты.

Различитель (дешёвый, не выполнен): независимая вторая численная реализация
PSWF (например, shooting-метод по ОДУ вместо диагонализации в базисе
Лежандра) на маленькой ячейке `(m=3, N=4)` — если `a` там тоже аномально
мало относительно спектра своего блока B, это говорит в пользу (1); если
нет — в пользу (2). Не запускал: протокол директивы — один прогон, без
дотюнивания после результата, и различитель уже относится к следующему
шагу, а не к текущему preflight.

```text
AUTOPSY: dropped=COUPLING; note=cross-block operator norm epsilon exceeds spectral gap delta (rho=1.41>1); graph min-conductance cut is not a Schur-safe decomposition here
AUTOPSY: dropped=SPECTRAL_ORDERING; note=conductance-optimal cut and gap-optimal cut disagree; low graph conductance (0.031) coexists with rho>1
```

### 7.4 Кандидат-запись для knowledge.db (не внесена — см. §5 про write-lock)

`subject=GOAL057 even-sector Fiedler spectral cut at (13,60);
status=KILLED_AT_PREFLIGHT;
stop_code=GOAL057_SPECTRAL_CUT_LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER;
forbidden_future_move=trust graph conductance alone as a Schur-decomposition
signal without checking rho=epsilon/delta<=0.25 on the actual signed block
operator; scope=cell (13,60), even sector only, N=90/120 not reached;
evidence=proof_geometry/spectral_cut/results_spectral_cut.json@<commit>;
open_question=a_N near-zero anomaly, see §7.3, unresolved`.

### 7.5 Что дальше не делаю без решения владельца

Директива запрещает: тюнинг порогов после просмотра результата (не делал —
все пороги и пины в `PRECOMMIT.md`, закоммичены в `22a4575` до прогона),
работу над V0.1, finite-to-global или H4a1b заявления, продвижение маршрута.
Это честно read-only experimental result: конечная ячейка, even sector,
один разрез, без claim про continuum decomposition.
