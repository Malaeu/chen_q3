# STATUS: CONDITIONAL — Q3 DISCOVERY COMPILER IS A SIDECAR PROGRAM; SHADOW BACKTEST SELECTED

```yaml
PRIMARY: RUN_Q3_AMDL_V0_SHADOW_BACKTEST
OPERATIVE_CLASS: RUN_Q3_AMDL_V0_SHADOW_BACKTEST
DOCUMENT_ROLE: OWNER_MANDATE_AND_CODEX_DIRECTIVE

BASE_HEAD: ff47f300e93fc6d5c6869b40b420cbea717fb125
DATE: 2026-08-23

PROJECT_CLASSIFICATION:
  mathematical_route: NOT_A_NEW_RH_ROUTE
  scientific_method: EXTENSION_OF_CURRENT_Q3_DISCIPLINE
  engineering_workstream: SEPARATE_SIDECAR_SUBPROJECT
  initial_home: SAME_REPOSITORY_SHADOW_MODE
  future_extraction_to_separate_repository: CONDITIONAL_ON_V0_VALUE

LIVE_ROUTE:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal058_state: UNCHANGED
  route_promotion: false
  rh_claim: false
  live_lean_edits_authorized: false

SELECTED_ARCHITECTURE:
  name: Q3_DISCOVERY_COMPILER
  full_name: Modular Invariant-Driven Mathematical Discovery Compiler
  proof_space: TYPED_DIRECTED_AND_HYPERGRAPH
  historical_layer: HISTORICAL_LEAP_DECOMPILER
  contract_layer: ATOMIC_INVARIANT_CONTRACT
  assembly_layer: CONSUMER_FIRST_PROOF_ASSEMBLER
  adversarial_layer: FALSIFIER_AND_FAILURE_ATLAS
  final_verifiers:
    - LEAN
    - ARB_INTERVAL
    - PAPER
    - CONDITIONAL

CORE_RULES:
  agent_consensus_proves_nothing: true
  analogy_is_not_a_bridge: true
  isomorphism_requires_inverse_maps: true
  reverse_math_term_reserved_for_actual_logical_strength_analysis: true
  ordinary_use_name: DEPENDENCY_SLICE
  smt_without_checked_certificate_is_not_a_verifier: true
  finite_result_does_not_occupy_cofinal_quantifier: true
  one_active_theorem_target: true

CLOSES:
  - AMDL_PROJECT_BOUNDARY_AMBIGUITY
  - UNVERSIONED_CODEX_DIRECTIVE
  - FREE_FORM_AGENT_SWARM_AS_DEFAULT

OPENS:
  - Q3_AMDL_V0_SHADOW_BACKTEST

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

EXECUTION_AUTHORIZED_BY_THIS_FILE: false
OWNER_GOAL_SCOPED_GRANT_REQUIRED: true
```

## ROUTE MAP

### 1. Это не новая математическая ветка RH

Проект не создаёт ещё один способ доказать RH. Он создаёт **мета-инструмент** для
поиска, проверки и сборки локальных математических мостов внутри уже выбранного
маршрута.

Правильная граница:

```text
Q3 / Route B:
  математические объекты, теоремы, certificates, Lean proofs.

Q3 Discovery Compiler:
  поиск существующего supplier;
  извлечение proof mechanism;
  типизация cross-domain bridge;
  построение falsifier;
  выбор следующего theorem-sized target.
```

Поэтому это:

```text
same scientific ecosystem;
separate engineering workstream;
no separate live proof route;
no second control kernel.
```

На первой стадии sidecar обязан жить в **shadow mode** — теневом режиме. Он
наблюдает исторические решения, но не меняет живой Route B, не минтит goal и не
пишет Lean.

Если V0 покажет измеримый выигрыш, реализация может стать отдельным модулем
репозитория. Если появится независимая пользовательская ценность вне Q3, тогда
разрешается вынести её в отдельный repository/package. Делать отдельный проект
до подтверждения predictive gain — преждевременная инфраструктура.

`[ABSTRACT][PAPER]`

### 2. Что реально новое в предложении

Не новы:

- формальные доказательства;
- базы теорем;
- proof search;
- reverse mathematics;
- theorem provers;
- библиотеки механизмов.

Потенциально новое для нашего pipeline — их жёсткая композиция:

```text
historical proof source
→ mechanism decomposition
→ typed invariant contract
→ source/target crosswalk
→ planted falsifier
→ theorem-sized packet
→ kernel or paper verification
→ reusable capability node.
```

Ценность не в слове «атомный». Ценность в том, что каждый атом хранит не только
утверждение, но и **условия легального переноса**.

## ARCHITECTURE

### A. Historical Leap Decompiler

**Historical Leap Decompiler** — декомпилятор исторических скачков. Он не
«объясняет гения» и не объявляет одну ретроспективную историю канонической.
Он извлекает из source-locked proof:

```text
exact obstacle before the leap;
minimal object changed by the leap;
new invariant or representation;
forward theorem;
dual failure test;
structures preserved and dropped;
smallest reusable contract.
```

Каждый результат сначала имеет статус:

```text
UNVERIFIED_DECOMPOSITION
```

Он становится reusable card только после независимого source audit.

Обязательный guard против hindsight bias:

```text
hide the later theorem;
expose only information available before the historical step;
ask whether the extracted mechanism ranks the actual next move;
score before any repair.
```

Исторический narrative без blind replay не является доказательством, что
механизм способен находить новые шаги.

### B. Atomic Invariant Contract

**Atomic Invariant Contract** — атомный контракт инварианта. Это минимальная
машинно-читаемая единица, которую Proof Assembler имеет право соединять.

```yaml
ATOMIC_INVARIANT_CONTRACT_V1:
  CARD_ID:
  SOURCE_LOCK:
    source:
    theorem_or_section:
    commit_or_bibliographic_pin:
  TARGET_OBSTACLE:
  SOURCE_OBJECT:
  TARGET_OBJECT:
  BRIDGE_KIND:
  INPUT_SIGNATURE:
  OUTPUT_SIGNATURE:
  QUANTIFIERS:
  DOMAIN:
  NORMALIZATION:
  UNITS:
  TOPOLOGY:
  SUPPORT_AND_CONE:
  SYMMETRY:
  BASIS_OR_GRAM_DATA:
  PRESERVES:
  DROPS:
  DEPENDENCY_SLICE:
  PRINCIPLE_P:
  COMPUTABLE_STATEMENT_X:
  FORWARD_THEOREM:
  DUAL_FALSIFIER:
  BOUNDARY_PLANTS:
  DISCRIMINATOR:
  CLOSES:
  OPENS:
  SCOPE: ABSTRACT | FINITE_CELL | COFINAL_FAMILY
  VERIFIER: LEAN | ARB_INTERVAL | PAPER | CONDITIONAL
  KILL_POWER_ESTIMATE:
  PROOF_COST_ESTIMATE:
  FORMALIZATION_COST_ESTIMATE:
  STATUS:
  EVIDENCE:
```

`BRIDGE_KIND` принимает только одно значение:

```text
EXACT_ISOMORPHISM
UNITARY_INTERTWINER
FORM_IDENTITY
ONE_WAY_TRANSFER
ASYMPTOTIC_EQUIVALENCE
STRUCTURAL_ANALOGY
HEURISTIC_ANALOGY
```

`EXACT_ISOMORPHISM` разрешён только при записанных прямой и обратной картах и
проверке сохраняемой структуры. Иначе карточка автоматически понижается.

### C. Consumer-First Proof Assembler

**Proof Assembler** — сборщик доказательств. Он не комбинирует красивые идеи
произвольно. Он начинает с точного consumer:

```text
TARGET THEOREM
→ exact missing input
→ internal capability lookup
→ at most three matching mechanism cards
→ type/normalization/quantifier gates
→ falsifier before proof
→ one selected theorem packet
→ Codex execution
→ semantic admission after kernel gate.
```

Proof-space является **directed AND-hypergraph**, а не обычным DAG. Переход

```text
A ∧ B ∧ C → D
```

нельзя разложить на три ложных ребра `A→D`, `B→D`, `C→D`.

Assembler обязан сначала спросить существующий capability catalog. Новый node
не создаётся, пока `./ask.sh` не исключил готового supplier или синоним.

### D. Adversarial Sentry

До формализации кандидат проходит:

```text
wrong-object plant;
wrong-normalization plant;
boundary plant;
rank-collapse plant;
finite-to-global counterfeit;
post-hoc witness plant;
circularity audit;
source-target type audit.
```

Карточки C04, C09 и C10 являются standing guards:

```text
C04: equal in which category; what was forgotten?
C09: was the object fixed before outcomes were inspected?
C10: is the theorem about the consumer's functional or a surrogate?
```

### E. Knowledge Shelf

На Shelf попадает не «сырая мысль», а один из объектов:

```text
VERIFIED_SUPPLIER
CONDITIONAL_SUPPLIER
KILLED_MECHANISM_WITH_AUTOPSY
UNVERIFIED_DECOMPOSITION
QUARANTINED_ANALOGY
```

Каждая запись versioned, source-locked и append-only.

## EFFICIENCY MODEL

Система оценивается не числом идей.

Обязательные метрики:

```text
SUPPLIER_REUSE_RATE
WRONG_OBJECT_ESCAPE_RATE
SEMANTIC_KILL_LATENCY
THEOREM_PACKET_TO_KERNEL_RATE
CLOSES_TO_OPENS_RATIO
PREDICTION_CALIBRATION
NO_PROGRESS_LOOP_RATE
```

Главная ожидаемая польза:

```text
reuse existing theorems sooner;
kill wrong-object bridges earlier;
compress analogies into exact local contracts;
reduce duplicated literature and Lean work;
make negative results reusable.
```

Не обещается:

```text
automatic invention of a true spectral gap;
automatic finite-to-global theorem;
automatic discovery of hidden cancellation;
automatic RH proof.
```

## STRONGEST ATTACK

Самое сильное возражение:

> Система станет ещё одним мета-слоем, который пишет карточки, но не закрывает
> theorem gaps.

Это считается подтверждённым, если выполняется хотя бы одно:

```text
actual next theorem is not top-3 often enough;
wrong-object plant survives once;
CLOSES/OPENS <= 1;
manual maintenance exceeds saved proof work;
new vocabulary grows faster than verified suppliers;
ranking needs repair after holdout inspection.
```

В этом случае проект получает статус:

```text
Q3_AMDL_IDEA_INFLATION_FATAL
```

и не внедряется в живой pipeline.

Вторая атака:

> Historical decompiler просто описывает известное задним числом.

Ремонт только один: blind historical replay. Красивые walkthroughs без blinded
ranking остаются учебным corpus, а не discovery engine.

## REGISTERED PREDICTIONS

```yaml
P_AMDL_1:
  prediction: typed contracts plus hard object gates outperform free-form agent swarm
  probability: 0.78
  fate: UNTESTED

P_AMDL_2:
  prediction: largest gain comes from supplier reuse and early wrong-object kills
  probability: 0.82
  fate: UNTESTED

P_AMDL_3:
  prediction: historical decompiler without blind replay shows severe hindsight bias
  probability: 0.88
  fate: UNTESTED

P_AMDL_4:
  prediction: live RH frontier is a bad validation set because the correct next node is unknown
  probability: 0.95
  fate: UNTESTED
```

## CODEX DIRECTIVE — FUTURE GOAL-SCOPED EXECUTION

This directive is source text only. It is not executable until the Owner issues
an explicit goal-scoped operational grant naming this file and task ID.

```text
TASK_ID: Q3_AMDL_V0_SHADOW_BACKTEST

MODE:
  SHADOW_READ_ONLY_ON_LIVE_ROUTE

OBJECTIVE:
  Determine whether a typed Historical-Leap / Atomic-Invariant / Proof-Assembler
  pipeline predicts useful next theorem nodes and rejects semantic counterfeits
  better than simple baselines.

AUTHORITATIVE_SOURCE:
  docs/routeB_bus/proshka/
  ARSENAL_MANDATE_2026-08-23_MODULAR_DISCOVERY_COMPILER_SHADOW.md

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md
  docs/routeB_bus/PROSHKA_QUEUE.md
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/

DO_NOT_EDIT:
  AGENTS.md
  docs/CODEX_CONTROL.md
  SESSION_ENTRY.md
  CLAUDE.md
  ROUTE_B_STATE.md
  STATE.json
  any Lean source
  any current goal or answer
  any live runtime state

NO_EXTERNAL_EXECUTION:
  no Aristotle
  no paid calls
  no Proshka call
  no new browser research

BUILD_DATASET:
  Select 12 timestamped checkpoints from at least three closed historical
  corridors. At each checkpoint expose only files and facts available at that
  time. Include at least:

    Corridor A:
      Goal044 -> Goal046 exact-v3 supplier transition.

    Corridor B:
      Step32/Step33 matrix-identification and finite-to-global work.

    Corridor C:
      Goal058 same-family residual/gap/transform/tail work.

  Freeze checkpoint list before scoring.

FOR_EACH_CHECKPOINT:
  1. Lock the exact consumer and smallest named gap.
  2. Query the internal capability catalog before minting a new node.
  3. Produce at most three AtomicInvariantContract candidates.
  4. Build a typed AND-hypergraph; do not flatten conjunctions.
  5. Register one predicted next node before revealing history.
  6. Run mandatory plants.
  7. Reveal the actual next load-bearing historical node.
  8. Score without retroactive repair.

MANDATORY_PLANTS:
  P1_WRONG_OBJECT_SAME_INTERFACE:
    Same surface type, different source family or normalization.

  P2_POST_HOC_WITNESS:
    Candidate chosen after the finite cell or failure pattern was inspected.

  P3_FINITE_AS_COFINAL:
    Finite-cell certificate relabeled as a cofinal theorem.

  P4_AND_EDGE_FLATTENING:
    A conjunctive theorem represented as independent one-premise edges.

  P5_SURROGATE_FUNCTIONAL:
    Positivity or convergence proved for a convenient surrogate rather than the
    consumer's exact object.

BASELINES:
  B1 shortest dependency path
  B2 plain capability search ranking
  B3 most recently touched open node
  B4 random eligible node

PASS_CRITERIA:
  actual next load-bearing node is top-3 at >= 70 percent of checkpoints;
  typed method beats every baseline on mean reciprocal rank;
  every mandatory semantic plant is rejected;
  wrong-object escape rate is exactly zero;
  median semantic kill latency improves over plain capability search;
  aggregate proposed CLOSES/OPENS ratio is > 1;
  no rule, weight, or schema changes after holdout reveal.

FAILURE_CODES:
  Q3_AMDL_NO_PREDICTIVE_GAIN
  Q3_AMDL_WRONG_OBJECT_ACCEPTED
  Q3_AMDL_HISTORICAL_LEAKAGE
  Q3_AMDL_AND_STRUCTURE_LOST
  Q3_AMDL_IDEA_INFLATION_FATAL
  Q3_AMDL_BASELINE_NOT_BEATEN

OUTPUT_ONE_FILE:
  docs/routeB_bus/CODEX_REPORT_Q3_AMDL_V0_SHADOW_2026-08-23.md

OUTPUT_HEADER:
  STATUS: PASS | REPAIR | FATAL
  TASK_ID: Q3_AMDL_V0_SHADOW_BACKTEST
  BASE_HEAD:
  CHECKPOINT_MANIFEST_SHA256:
  SCHEMA_SHA256:
  RESULTS:
  PLANT_FATES:
  PREDICTION_FATES:
  CLOSES:
  OPENS:
  RECOMMENDATION: PROMOTE_TO_V1 | ONE_REPAIR_ONLY | KILL

STOP_CONDITION:
  Stop after the single report is committed and pushed, or earlier on the first
  wrong-object plant escape.

FORBIDDEN:
  Do not implement a production discovery engine.
  Do not tune after holdout reveal.
  Do not change the live RH route.
  Do not mint a new mathematical theorem.
  Do not claim this system discovers mathematics until the backtest passes.
```

## FUTURE V1 — NOT AUTHORIZED

V1 may be proposed only after V0 PASS. Its smallest acceptable implementation:

```text
historical source ingester;
AtomicInvariantContract schema validator;
typed hypergraph builder;
capability-catalog adapter;
falsifier registry;
ranker;
report generator.
```

No autonomous Lean writer belongs in V1. Codex remains the single theorem
executor under the existing control plane.

## META CLOSEOUT

**Что стало меньше?**

Широкая идея «новой математики» сжата до одного проверяемого sidecar:

```text
Q3_AMDL_V0_SHADOW_BACKTEST.
```

**Что убито?**

```text
free-form swarm;
analogy relabeled as isomorphism;
simple DAG that destroys AND logic;
SMT answer without checked certificate;
live-route deployment before backtest;
separate repository before evidence of value.
```

**Что нельзя пробовать снова?**

Нельзя оценивать discovery navigator на открытом RH-фронте и затем объявлять
неизвестный правильный ответ подтверждением собственной модели.

**Текущий smallest named gap:**

```text
Q3_AMDL_V0_SHADOW_BACKTEST
```

**Следующий дешёвый решающий тест:**

Blinded historical replay against four baselines and five semantic plants.

```yaml
iteration:
  target: modular_invariant_discovery_compiler
  status: OPEN
  failed_strategy: free_form_multi_agent_swarm
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: Q3_AMDL_V0_SHADOW_BACKTEST
  invariant_learned: every reusable mechanism carries exact object normalization quantifiers and a dual falsifier
  forbidden_future_move: deploy_or_tune_on_live_RH_frontier
  next_decisive_test: blinded_historical_shadow_backtest
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
