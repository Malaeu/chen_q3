# STATUS: CONDITIONAL — TYPED I/O PROOF SYNTHESIS RATIFIED; PORT MATCHER AND GAP ALGEBRA ARE THE MISSING ENGINE

```yaml
PRIMARY: TRY_Q3_TYPED_IO_MEET_IN_THE_MIDDLE
OPERATIVE_CLASS: TRY_Q3_TYPED_IO_MEET_IN_THE_MIDDLE
DOCUMENT_ROLE: ARCHITECTURE_VERDICT_AND_FUTURE_CODEX_DIRECTIVE

REPO: Malaeu/chen_q3
BRANCH: rh_clean
REVIEW_HEAD: 7609b5f45955823d4c385cb0ee6f4a4a94d56e97
DATE: 2026-08-23

OWNER_INTENT:
  mathematical_objects_as_typed_io_modules: RATIFIED
  bidirectional_meet_in_the_middle: RATIFIED
  gap_meter_then_cheapest_closure: RATIFIED
  arsenal_needles_after_gap_lock: RATIFIED
  fixed_pruning_percentage_99_99: NOT_YET_AUTHORIZED_MEASURE_FIRST

FORMAL_MODEL:
  semantic_view: DEPENDENT_TYPED_MULTICATEGORY
  operational_view: DIRECTED_AND_HYPERGRAPH_WITH_REFINEMENT_PORTS
  kernel_truth: LEAN_PROOF_TERM
  semantic_firewall: KERNEL_GREEN_NE_SEMANTICALLY_ADMITTED

CURRENT_REPO_FACTS:
  chain_gap_phase_0_k_metric: BUILT
  chain_gap_phase_1_weak_candidates: BUILT
  capability_catalog: BUILT_PROSE_SHADOW
  exact_consumer_first_discipline: BUILT_MANUAL
  bridge_kind_schema: BUILT
  insight_state_machine: BUILT
  bounded_exploration_phase: BUILT
  exact_port_unification: OPEN
  adapter_registry_with_loss_ledger: OPEN
  typed_gap_vector: OPEN
  bidirectional_route_search: OPEN
  constructor_task_distribution: OPEN

SEQUENCE_REPAIR:
  previous_failure: RANKING_BEFORE_TYPED_PORT_MATCHING
  selected_order:
    - T2_PORT_MATCHER_LOCAL_PLANTS
    - T3_TYPED_GAP_VECTOR_IN_CHEAP
    - R6A_PROCESS_CALIBRATION_CAN_RUN_IN_PARALLEL
    - T4_BIDIRECTIONAL_MEET_IN_THE_MIDDLE
    - R6B_BLINDED_BACKTEST_WITH_DUAL_SCORING

GEMINI_QUESTIONS:
  exploration_vs_validation: ANSWERED_BY_QUARANTINED_HEURISTIC_STAGE
  io_composition_rule: ANSWERED_BY_EXPLICIT_ADAPTER_UNIFICATION
  alternative_valid_backtest: ANSWERED_BY_DUAL_SCORE
  unconnected_external_needles: ALLOWED_ONLY_ON_COLD_SHELF

CLOSES:
  - TYPE_DIRECTED_SEARCH_ARCHITECTURE_AMBIGUITY
  - EXPLORATION_VALIDATION_BOUNDARY_AMBIGUITY
  - PORT_COMPOSITION_RULE_AMBIGUITY
  - HISTORICAL_BACKTEST_ALTERNATIVE_ROUTE_BIAS
  - UNCONNECTED_ARCHAEOLOGY_ADMISSION_AMBIGUITY
  - GAP_METER_SCALARIZATION_ERROR

OPENS:
  - T2_PORT_MATCHER_LOCAL_PLANTS
  - T3_TYPED_GAP_VECTOR_IN_CHEAP
  - T4_BIDIRECTIONAL_MEET_IN_THE_MIDDLE

SCOPE: ABSTRACT
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

EXECUTION_AUTHORIZED_BY_THIS_FILE: false
OWNER_GOAL_SCOPED_GRANT_REQUIRED: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Вердикт по исходному замыслу

Замысел верен:

```text
математическая теорема или инструмент
= модуль с типизированными входами и выходами;

доказательство
= композиция модулей;

открытая проблема
= несовпадение выходных портов левой стены
  и входных портов правой стены;

поиск
= bidirectional meet-in-the-middle;

новая математика
= минимальный адаптер или модуль,
  закрывающий измеренный типовой разрыв.
```

Это не просто метафора электронной схемы. Это рабочая семантика Curry–Howard:
proof term является программой, proposition является типом, theorem является
типизированным преобразованием.

Однако выражение «чистая теория категорий» требует ремонта.

Для недепендентных утверждений можно думать о категории, где объекты — типы, а
морфизмы — доказательства. Production Lean содержит зависимые входы, typeclass
arguments, subtypes, coercions, scopes и свидетелей, от которых зависят
последующие порты. Поэтому точная семантика ближе к:

```text
category with families / contextual category
+ dependent type theory
+ multicategory for multi-input inference.
```

Для инженерной реализации эта абстракция сжимается до:

```text
DIRECTED AND-HYPERGRAPH
+ exact Lean types
+ semantic refinement ports.
```

Переход

```text
A ∧ B ∧ C → D
```

хранится одной hyperedge с тремя обязательными входами. Обычный DAG создаёт
ложные ребра `A→D`, `B→D`, `C→D` и фабрику фальшивых shortcuts.

`[ABSTRACT][PAPER]`

### 2. Почему система до сих пор не работала именно так

Репозиторий уже содержит Shelf, assembly-граф, `cheap.py`, карты Arsenal,
consumer-first дисциплину и Lean kernel. Не хватало не идеи, а четырёх машинных
слоёв.

#### 2.1. Порты хранились именами, не типами

`capability.requires/provides` является быстрым прозаическим индексом. Он не
кодирует и не проверяет автоматически:

```text
carrier;
source family;
domain/support;
normalization;
quantifier order;
scope FINITE_CELL/COFINAL_FAMILY;
topology;
representative;
summation method;
basis/Gram geometry.
```

Поэтому похожие объекты соединялись глазами, а C04-аудит приходил позже.
Реальные ночные дефекты показывают нужные refinement-типы:

```text
tsum != conditional reflection sum;
L2 isometry != actual pointwise Fourier integral;
full endpoint != midpoint representative;
Hilbert density != form core.
```

#### 2.2. Много проводов действительно отсутствуют

Type search может показать точный отсутствующий тип. Он не создаёт theorem,
которого нет ни в Mathlib, ни в Q3, ни в источнике. После фильтрации большая
часть оставшихся gaps будет настоящей новой математикой.

Это успех системы, а не её провал:

```text
route search failure
→ named missing theorem.
```

#### 2.3. Взрыв вариантов пока убивает судья вручную

Proshka выполняет hard eligibility gates, source-object audit, normalization
check и falsifiers вручную. Поэтому ветви не разрастаются, но появляется
судейская латентность. Port matcher должен автоматизировать только очевидные
объектные несовместимости, не заменять математическое решение.

#### 2.4. Нет comparator и adapter algebra

`exact?` и `apply?` — неполные локальные поисковики. Они могут не увидеть
живой supplier под projection wrapper или из-за локальной нотации. Совпадение
слов тоже не доказывает применимость.

Нужен собственный слой:

```text
candidate generation
→ explicit Lean harness
→ negative control
→ semantic refinement audit
→ PortMatchResult.
```

#### 2.5. Порядок работ был перевёрнут

Пытаться оценивать next-node navigator до exact port matching — всё равно что
ранжировать электрические маршруты до проверки напряжения и разъёмов.

Правильный порядок теперь:

```text
port schema
→ port matcher
→ gap algebra
→ meet-in-the-middle
→ historical backtest.
```

## TYPED I/O OBJECT MODEL

### 3. Двухслойный тип порта

Lean type является единственным kernel-level источником истины. Но часть
семантики не выражена в theorem type напрямую. Поэтому каждый порт имеет два
слоя.

```yaml
PORT_SPEC_V1:
  PORT_ID:
  POLARITY: REQUIRE | PROVIDE
  PORT_ROLE: DATA | PROP | WITNESS | MAP | BOUND | RATE | CERTIFICATE

  KERNEL:
    exact_type:        # byte/source-derived `#check`, не реконструкция
    local_environment: # namespace, open, scoped notation, instances
    source_decl:
    source_commit:

  REFINEMENTS:
    carrier:
    source_family:
    domain:
    support:
    normalization:
    units:
    quantifier_spine:
    scope: ABSTRACT | FINITE_CELL | COFINAL_FAMILY
    topology:
    representative:
    summation_method:
    symmetry:
    basis_or_Gram:

  TRUST:
    verifier: LEAN | ARB_INTERVAL | PAPER | CONDITIONAL
    axiom_profile:
    provenance:
```

Правило:

```text
KERNEL.exact_type копируется из consumer/provider.
REFINEMENTS добавляют только то, чего kernel type не различает.
```

Metadata никогда не имеет права переписать Lean type.

### 4. Математический модуль

```yaml
MODULE_SPEC_V1:
  MODULE_ID:
  THEOREM_REF:
  INPUT_PORTS: [...]
  OUTPUT_PORTS: [...]
  BRIDGE_KIND:
  SIDE_CONDITIONS:
  PRESERVES:
  DROPS:
  CLOSES:
  OPENS:
  COST_CLASS:
  FAILURE_ATLAS_GUARDS:
```

Один theorem может иметь несколько логических consequences только тогда, когда
существуют отдельные projection theorems или структура с доказанными полями.
Нельзя расщеплять prose-summary на несуществующие output-порты.

### 5. Адаптер

**Adapter** — явная теорема, которая преобразует один порт в другой.

```yaml
ADAPTER_SPEC_V1:
  ADAPTER_ID:
  FROM_PORT:
  TO_PORT:
  THEOREM_REF:
  DIRECTION:
  PRESERVES:
  DROPS:
  LOSS_LEDGER:
  SCOPE:
  VERIFIER:
  COST:
```

Примеры законных адаптеров:

```text
finite-measure L2 → L1 via Hölder;
real matrix → complex matrix via scalar extension;
nonorthogonal coordinates → Gram-corrected form;
a.e. representative equality → Lp-class equality;
source finite row → function transform via exact synthesis theorem.
```

Примеры запрещённых «адаптеров» без отдельного theorem:

```text
finite cell → cofinal family;
trial family → ground family;
L2 isometry → pointwise Fourier transform;
full endpoint → midpoint pointwise identity;
small Rayleigh value → small residual;
prolate gap → true Weil gap.
```

## FORMAL COMPOSITION RULE

### 6. Смыкание модулей

Пусть:

```text
M1 : Γ → Δ
M2 : Σ → Θ
```

где `Γ, Δ, Σ, Θ` — типизированные contexts портов.

Композиция разрешена, если для каждого required-порта `σ_i ∈ Σ` существует:

1. output-порт `δ_j ∈ Δ`;
2. либо exact/definitional match;
3. либо source-locked adapter chain
   
   ```text
   δ_j → A1 → ... → Ak → σ_i
   ```

   с согласованными refinements.

Оставшиеся required-порты становятся точным gap context. Они не исчезают из-за
того, что большинство входов уже найдено.

### 7. Закрытое правило `PORT_MATCH_RESULT_V1`

```text
EXACT_MATCH
DEFINITIONAL_MATCH
EXPLICIT_ADAPTER_MATCH
ADAPTER_REQUIRED
REFINEMENT_LOSS
HARD_MISMATCH
UNVERIFIED
```

Hard mismatch возникает минимум при:

```text
different source family without crosswalk;
FINITE_CELL offered to COFINAL_FAMILY consumer;
weaker quantifier offered to stronger consumer;
wrong normalization or units;
pointwise object offered where only an Lp class exists;
conditional sum offered as tsum;
surrogate functional offered to exact consumer;
verifier below the task trust floor.
```

Сильный output может удовлетворить слабый input. Обратное направление
запрещено. Это refinement preorder, а не симметричное «похожи».

## GAP ALGEBRA

### 8. Gap не является одним вещественным расстоянием

Нельзя компенсировать wrong object дешёвой формализацией. Поэтому Gap Meter
сначала применяет hard eligibility gates, затем ранжирует только допустимое.

```yaml
GAP_SIGNATURE_V1:
  exact_consumer:
  left_available_outputs:
  right_required_inputs:

  hard_mismatches: [...]
  missing_ports: [...]
  adapter_gaps: [...]
  scope_deficits: [...]
  quantifier_deficits: [...]
  object_identity_deficits: [...]
  normalization_unit_deficits: [...]
  topology_representative_deficits: [...]
  trust_deficits: [...]

  current_k:
  residual_arity:
  minimum_adapter_depth:
  expected_closes:
  expected_opens:
  proof_cost_estimate:
  kill_power_estimate:
  decisive_test:
```

### 9. Порядок сравнения gaps

Сначала:

```text
hard_mismatches == []
source object exact
consumer exact
scope direction legal
trust threshold passed.
```

Только затем используется лексикографический ranking:

```text
1. меньше missing_ports / k;
2. меньше residual arity;
3. меньше adapter depth;
4. выше CLOSES-OPENS;
5. ниже proof cost;
6. выше kill-power / information gain.
```

Не использовать один weighted score для hard и soft факторов.

### 10. Измерение обещанного сокращения вариантов

Процент `99.99%` не объявляется заранее.

Для каждого search depth фиксируются:

```text
syntactic_candidates;
kernel_type_eligible;
refinement_eligible;
falsifier_survivors;
final_top3.
```

И считается:

\[
\operatorname{PruneRate}
=
1-
\frac{\#\text{refinement-eligible candidates}}
     {\#\text{syntactic candidates}}.
\]

Зарегистрированная цель V0:

```text
>=95% rejection before theorem invention;
wrong-object escape exactly zero.
```

Если получится 99.99%, это измеренный результат, не рекламный input.

## BIDIRECTIONAL MEET-IN-THE-MIDDLE

### 11. Алгоритм

```text
A. BACKWARD WALL
   exact consumer theorem
   → required ports
   → expand known provider hyperedges to bounded depth.

B. FORWARD WALL
   kernel-green / semantically admitted shelf
   → available output ports
   → apply only explicit adapters to bounded depth.

C. MEET
   exact or adapter-backed port unification.

D. GAP
   unmatched required ports produce GAP_SIGNATURE_V1.

E. SHELF QUERY
   ask.sh / capability / Mathlib / litreview.

F. NEEDLE ROUND
   only after shelf exhaustion:
   Arsenal scan by gap signature;
   2–5 representations in bounded exploration;
   cheapest falsifier first.

G. ONE PACKET
   one selected theorem target to Codex.
```

Начальная глубина остаётся `d=3`. Ограничение глубины — не слабость: цель V0
не найти длиннейшее доказательство, а обнаружить тончайший измеримый разрыв.

### 12. Роль Arsenal needles

Arsenal не перебирает всю математику. Он получает typed gap.

Примеры:

```text
location information dropped
  → C01 localization;

same coordinates / different law
  → C04 object-category audit;

post-hoc witness
  → C09 precommit;

surrogate functional
  → C10 exact consumer;

broken exact symmetry with explicit finite defect
  → C13 completion by shadow.
```

Card предлагает re-representation и falsifier. Card не является theorem и не
создаёт proof edge без source/Lean evidence.

## ANSWERS TO GEMINI

### 13. Вопрос 1 — Exploration vs Validation

Эвристический поиск разрешён только в quarantined pre-composability zone:

```text
RAW_INSIGHT / HEURISTIC_ANALOGY
→ BRIDGE_STUB
→ ALIGNMENT_PROBE
→ CROSSWALK_TYPED
→ FALSIFIER_PASSED.
```

Правила:

- В `RAW_INSIGHT` разрешены широкие analogies и I/O matching.
- Кандидат не входит в active proof graph и ничего не блокирует.
- `BRIDGE_STUB` обязан назвать exact consumer, source/target objects и cheapest
  killer.
- `ALIGNMENT_PROBE` перечисляет несовпадающие порты; отсутствие theorem ещё не
  является kill.
- Proshka убивает candidate до `CROSSWALK_TYPED` только за structural
  contradiction: wrong carrier, impossible rank, forbidden source switch,
  circular target, incompatible units.
- После заявления composability включается полный Inquisitor.

Таким образом HEURISTIC_ANALOGY не убивается за то, что она ещё не theorem. Она
карантинируется. Убивается ложное заявление, что она уже является bridge.

### 14. Вопрос 2 — цепочка из 2–3 adapters

Да, цепочка разрешена. Formal rule — explicit adapter composition выше.

Каждый adapter обязан иметь theorem ref и loss ledger. Compose допускается
только если loss после каждого шага всё ещё удовлетворяет следующему input.

Пример:

```text
H_m vector
→ logWindowL2Equiv.symm
→ finite-window L2 representative
→ L2-to-L1 Hölder adapter
→ ordinary Fourier integral
→ a.e. equality with synthesized isometry.
```

Здесь каждый провод имеет свой тип. Фраза «оба являются Fourier transform» не
является правилом объединения.

### 15. Вопрос 3 — alternative valid solution в backtest

Один exact-history score действительно наказал бы систему за новое валидное
решение. Поэтому R6B получает две независимые метрики.

```yaml
HISTORICAL_REPLAY_SCORE:
  question: actual historical next node ranked where?
  metrics: top_k, MRR

CONTRACT_CLOSURE_SCORE:
  question: candidate independently closes the same exact consumer contract?
  requirements:
    - frozen before reveal
    - source available at checkpoint or genuinely new theorem marked separately
    - no stronger hidden assumptions
    - same source object/scope/normalization
    - Lean/PAPER verification
```

Исходы:

```text
REPLAY_MATCH
INDEPENDENT_VALID_ALTERNATIVE
UNVERIFIED_ALTERNATIVE
HISTORICAL_LEAKAGE
INVALID_SURROGATE
```

Новая альтернативная theorem получает discovery credit только после независимой
проверки. До проверки она не считается ни успехом, ни провалом.

### 16. Вопрос 4 — внешний Археолог и «про запас»

Разрешены две полки.

```text
ACTIVE CAPABILITY SHELF:
  typed supplier с известным consumer или reusable contract.

COLD MECHANISM SHELF:
  source-locked historical decomposition без текущего GAP_ID.
```

Термин `UNCONNECTED_SUPPLIER` запрещён: без consumer это ещё не supplier.
Использовать:

```text
UNCONNECTED_MECHANISM
UNVERIFIED_DECOMPOSITION
QUARANTINED_ANALOGY.
```

Promotion cold → active разрешён, если выполнено хотя бы одно:

1. exact match с текущим GAP_ID;
2. NAMEWATCH: минимум два разных goals и два разных fronts, coverage audit и
   discriminator;
3. отдельная owner-ratified стратегическая библиотека.

Так Археолог может копить потенциальные механизмы без загрязнения active graph.

## IMPLEMENTATION LADDER

### 17. Что уже существует

```text
T1 schema foundation:
  BRIDGE_KIND_V1;
  BRIDGE_STUB_V1;
  ATOMIC_INVARIANT_CONTRACT_V1;
  INSIGHT_STATE_V1.

Gap meter V0:
  cheap.py k-count;
  structural cost classes;
  weak capability candidates.

Constructor foundations:
  translation dictionary;
  atom descriptions;
  foreign Lean bridge;
  exact consumer-first rule.
```

### 18. Следующий порядок

#### T2 — `PORT_MATCHER_V0`

Минимальный matcher:

```text
exact `#check` consumer/provider types;
temporary Lean harness;
semantic refinement comparison;
explicit mismatch class;
negative controls.
```

Обязательные plants:

```text
P1 same interface / wrong source family          → HARD_MISMATCH
P2 FINITE_CELL offered to COFINAL_FAMILY         → HARD_MISMATCH
P3 L2 isometry offered as pointwise Fourier      → ADAPTER_REQUIRED
P4 midpoint vs full endpoint pointwise identity → REFINEMENT_LOSS
P5 small Rayleigh value offered as residual      → HARD_MISMATCH
```

#### T3 — `GAP_SIGNATURE_V1` in `cheap.py`

Добавить к текущей цене:

```text
exact missing port types;
mismatch vector;
minimum adapter depth;
CLOSES/OPENS yield;
decisive test.
```

#### R6A — process calibration

Может идти параллельно после freeze схемы. Он не блокирует T2, потому что T2
имеет собственные exact plants.

#### T4 — bidirectional search

Запускается только после T2/T3 PASS.

#### R6B — dual-score blinded backtest

Оценивает и historical replay, и independently verified contract closure.

## REGISTERED PREDICTIONS

```yaml
P_TIO_1:
  prediction: hard kernel/refinement gates reject at least 95 percent of naive depth_2 candidate edges
  probability: 0.74
  fate: UNTESTED

P_TIO_2:
  prediction: after exact matching most surviving gaps are genuinely missing theorem modules rather than search failures
  probability: 0.83
  fate: UNTESTED

P_TIO_3:
  prediction: explicit adapter registry closes a material fraction of low-cost bridges currently adjudicated manually
  probability: 0.72
  fate: UNTESTED

P_TIO_4:
  prediction: historical-only scoring undercounts mathematically valid alternative routes
  probability: 0.91
  fate: UNTESTED
```

## STRONGEST ATTACK

Самое сильное возражение:

> Система превратит математику в обслуживание metadata, а schema сама начнёт
> расходиться с Lean.

Это FATAL, если metadata становится вторым источником theorem type.

Guards:

```text
exact type always copied from #check;
metadata only refines facts absent from kernel type;
every proposed edge emits a tiny Lean harness;
every matcher release carries negative plants;
no mass manual retrofit;
no active capability without provenance;
no single weighted score hiding hard mismatch.
```

Второе возражение:

> После идеальной типизации останется одна настоящая новая теорема, и engine её
> не докажет.

Да. Это ожидаемый и полезный результат. Цель Discovery Compiler — не отменить
математическое творчество, а перестать тратить его на wrong objects, повторные
suppliers и незаконные compositions.

## CODEX DIRECTIVE — FUTURE GOAL-SCOPED EXECUTION

Этот блок не разрешает запуск. Нужна отдельная owner goal-scoped команда.

```text
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_V0

OBJECTIVE:
  Build and falsify the minimal typed port matcher before any global route ranker.

AUTHORITATIVE_SOURCE:
  docs/routeB_bus/proshka/
  PROSHKA_VERDICT_TYPED_IO_MEET_IN_THE_MIDDLE_GAP_ALGEBRA_2026-08-23.md

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/cartographer/CHAIN_GAP_DESIGN.md
  docs/cartographer/CONSTRUCTOR_SPEC.md
  docs/cartographer/HOWTO.md
  docs/AGENT_OS_MAP_AND_REFACTORING_2026-08-23.md
  q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md

MODE:
  BOUNDED_EXPLORATION
  NO_LIVE_ROUTE_MUTATION

DO_NOT_EDIT:
  AGENTS.md
  docs/CODEX_CONTROL.md
  SESSION_ENTRY.md
  CLAUDE.md
  ROUTE_B_STATE.md
  STATE.json
  any Lean production theorem
  any current goal or answer

PHASE_1_SCHEMA:
  Define PORT_SPEC_V1, ADAPTER_SPEC_V1 and PORT_MATCH_RESULT_V1 in one
  docs/cartographer schema file or one report attachment.
  Kernel types must be extracted from exact declarations.

PHASE_2_PLANTS:
  Run P1-P5 from section 18 using temporary Lean harnesses outside tracked
  production source.

PHASE_3_REPORT:
  For every plant report:
    kernel match result;
    refinement match result;
    required adapter;
    expected vs actual classification;
    exact command and output.

PASS:
  all five plants classified exactly;
  wrong-object escape = 0;
  no candidate is called a supplier without a verified edge;
  schema does not duplicate theorem statements manually.

STOP:
  first wrong-object acceptance;
  or one report after all plants.

OUTPUT_ONE_FILE:
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_V0_2026-08-23.md

NEXT_IF_PASS:
  T3_TYPED_GAP_VECTOR_IN_CHEAP

FAILURE_CODES:
  TIO_KERNEL_TYPE_RECONSTRUCTED_NOT_COPIED
  TIO_WRONG_OBJECT_ACCEPTED
  TIO_FINITE_AS_COFINAL_ACCEPTED
  TIO_POINTWISE_LP_CLASS_CONFLATION
  TIO_RAYLEIGH_RESIDUAL_CONFLATION
  TIO_METADATA_SECOND_KERNEL
```

## META CLOSEOUT

**Что стало меньше?**

Широкая мечта «математика как микросхемы» сжата до трёх отсутствующих модулей:

```text
T2 port matcher;
T3 gap algebra;
T4 bidirectional search.
```

**Что убито?**

```text
обычный DAG;
порты только по именам;
одна скалярная gap-метрика;
исторический next node как единственная мера успеха;
UNCONNECTED_SUPPLIER в active shelf;
99.99 percent как непроверенный лозунг;
ranker before type checker.
```

**Что нельзя пробовать снова?**

Нельзя запускать глобальный navigator, пока local port matcher принимает
wrong-object plant или путает finite/cofinal scope.

**Текущий smallest named gap:**

```text
T2_PORT_MATCHER_LOCAL_PLANTS
```

**Следующий дешёвый решающий тест:**

Пять exact mismatch plants на temporary Lean harnesses.

```yaml
iteration:
  target: typed_io_proof_synthesis
  status: OPEN
  failed_strategy: ranking_before_typed_port_matching
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: T2_PORT_MATCHER_LOCAL_PLANTS
  invariant_learned: kernel type is source of truth and semantic refinements may only narrow composability
  forbidden_future_move: global_path_ranking_before_wrong_object_escape_is_zero
  next_decisive_test: five_port_matcher_plants
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
