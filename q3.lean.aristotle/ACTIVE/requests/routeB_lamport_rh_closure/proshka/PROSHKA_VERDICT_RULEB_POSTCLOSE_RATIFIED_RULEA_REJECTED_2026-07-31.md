# PROSHKA VERDICT — RULE_B_AND_POSTCLOSE_PIN_RATIFIED; RULE_A_EQUIVALENCE_REJECTED
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Consumed by: relation repair in proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md
(target RuleA_RelationRepair, success code RULE_A_CANONICAL_WITH_A2_COROLLARY_PINNED)
Transport artifacts note: payload verbatim as pasted by the owner from the
Proshka browser chat; escaping/rendering artifacts preserved unmodified
(square-bracket display-math fences, ```yaml/```text fences as received).
Semantic content untouched; no editing performed. NOTE: the payload below
quotes the rejected biconditional as historical text; the zero-occurrence
grep gate applies to the disambiguation file, not to this verbatim record.

--- VERBATIM PAYLOAD BEGINS ---

# STATUS: OPEN — RULE_B_AND_POSTCLOSE_PIN_RATIFIED; RULE_A_EQUIVALENCE_REJECTED

```yaml
primary_verdict: RULE_A_EXACT_EQUIVALENCE_REJECTED

secondary_verdicts:
  - RULE_B_EXACT_EQUIVALENCE_RATIFIED
  - GOAL040_POSTCLOSE_VERSIONING_RATIFIED
  - GOAL040_IMMUTABILITY_RESTORED
  - PROSHKA_VERDICTS_MATERIALIZED
  - COMMIT_PIN_RESOLVED

requested_gap:
  name: RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
  closed: false
  closed_components:
    - RULE_B
    - VERSION_SAFE_POSTCLOSE_PIN
    - GOAL040_BYTE_RESTORATION
  remaining_component:
    - RULE_A_A1_A2_BICONDITIONAL

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
rh_claimed: false

pin:
  branch: rh_clean
  commit: de9f056028c12cc6757627329cfda26971dd370c
  commit_resolves: true

goal_040:
  sha256: 48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300
  canonical_mirror_byte_identity: verified
  retroactive_amendment_present: false
  interim_mutation_disclosed: true

rule_A:
  A1_implies_A2: true
  A2_implies_A1: false
  exact_equivalence: false
  repair: classify_A2_as_operational_corollary_of_A1

rule_B:
  live_implies_R0_1_to_R0_3: true
  R0_1_to_R0_3_imply_live: true
  exact_operational_equivalence: ratified

execution_directive:
  code_changes: forbidden
  goal040_changes: forbidden
  docs_only_relation_repair: required
```

## ROUTE MAP

| Объект              | Результат                                                                                                                                                                                                                                              | Tags                |
| ------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------- |
| Commit pin          | `de9f056028c12cc6757627329cfda26971dd370c` существует; его commit message прямо фиксирует откат A1, восстановление SHA Goal 040, отдельный post-close audit и материализацию двух вердиктов.                                                           | `[ABSTRACT][PAPER]` |
| Два вердикта Прошки | Оба файла существуют и помечены как owner-relayed verbatim payload с сохранением transport artifacts, без semantic editing.                                                                                                                            | `[ABSTRACT][PAPER]` |
| Goal 040            | Manifest фиксирует исходный SHA-256 `48172cdb…89300`. Канонная и зеркальная копии на pinned commit имеют одинаковый Git blob SHA и одинаковый текст.                                                                                                   | `[ABSTRACT][PAPER]` |
| Post-close audit    | Header ровно non-normative: `POSTCLOSE_REVIEWER_REQUIREMENTS`, `normative_for_goal_040_execution: false`, `modifies_goal_040_contract: false`. Файл сохраняет A1.1–A1.3, exact witness (-1/12) и открытую историю ошибочного commit `19a4dcbf`.        | `[ABSTRACT][PAPER]` |
| Rule B              | Live-формулировка разложена на `DEFAULT_SHOW`, `EXPLICIT_SEND_AUTHORITY`, `RECIPIENT_AND_CHANNEL_LOCK`; обратная сборка восстанавливает live-правило без дополнительного содержательного требования.                                                   | `[ABSTRACT][PAPER]` |
| Rule A              | A1 требует **до каждого запуска** инвентаризацию собственного репозитория **и pinned Mathlib**. A2 запрещает конкретный повторный cloud-submit, когда exact local theorem уже закрывает интерфейс. Это следствие A1, но не эквивалентная формулировка. | `[ABSTRACT][PAPER]` |

### Rule B — ратифицирована

Live-текст утверждает три вещи:

1. подготовленный текст по умолчанию только показывается владельцу;
2. отправка требует явного текущего разрешения;
3. адресат и канал должны быть названы однозначно.

`R0.1–R0.3` утверждают те же три вещи, лишь раскрывая два пограничных случая: старое общее `go` не является текущим разрешением, а готовность goal не является dispatch authority. Это корректная operational expansion, а не усиление другого типа. `[ABSTRACT][PAPER]`

Фактическая duty map также совместима с mapping: владелец передаёт Прошке через браузер и отправляет Aristotle-контракты через браузер; Codex работает по явно запущенному goal.  `[ABSTRACT][PAPER]`

[
\boxed{
\texttt{RULE_SEND_DISCIPLINE_EXACT_TEXT_RATIFIED}
}
]

### Version-safe Goal 040 — ратифицирован

Требования выполнены правильно:

* закрытый Goal 040 восстановлен;
* поздние guards вынесены в отдельный объект;
* этот объект прямо запрещает трактовать guards как условия, якобы исполненные доказательством 040;
* историческая ошибка не скрыта;
* фактический quadratic witness отделён от sound-but-superseded tent route. `[ABSTRACT][PAPER]`

[
\boxed{
\texttt{GOAL040_VERSION_SAFE_POSTCLOSE_PIN_RATIFIED}
}
]

## FINAL PROPOSAL

### Rule A нельзя ратифицировать как (A1\equiv A2)

Точная логическая связь:

[
\boxed{A1\Longrightarrow A2}
]

но

[
\boxed{A2\not\Longrightarrow A1}.
]

Причина не стилистическая.

A1 содержит обязательную процедуру:

```text
до любого Aristotle/cloud run:
  inventory own repository;
  inventory pinned Mathlib.
```

A2 содержит stop-condition:

```text
если exact local theorem уже закрывает interface:
  не отправлять дублирующий Aristotle theorem.
```

Можно выполнить A2 и нарушить A1. Например:

```text
- агент не проверил pinned Mathlib;
- в canon exact theorem отсутствует;
- он отправил cloud task;
- A2 формально не нарушена;
- A1 нарушена, потому что inventory не проводилась.
```

Ещё более прямой случай:

```text
- theorem уже существует в pinned Mathlib;
- theorem отсутствует в project canon;
- A1 запрещает запуск после inventory;
- A2, ограниченная "proved in canon / exact local theorem", этого случая
  дословно не покрывает.
```

`[ABSTRACT][PAPER]`

### Минимальный ремонт без переписывания истории

Не менять цитаты A1 и A2. Изменить только классификацию в disambiguation-файле:

```text
Rule A — RULE_INVENTORY_FIRST

Canonical rule:
  A1.

A2 status:
  operational corollary and T4a precedent of A1.

Logical relation:
  A1 ⇒ A2.
  No claim A2 ⇒ A1.
```

И финальную строку:

```text
Ratification requests are separate:
  Rule A: A1 is canonical; A2 is its cloud-duplication corollary.
  Rule B: live text ≡ R0.1–R0.3.
```

Это сохраняет provenance, не редактирует слова Прошки задним числом и делает правило логически точным. `[ABSTRACT][PAPER]`

После такого ремонта новый закрывающий код:

```text
RULE_A_CANONICAL_WITH_A2_COROLLARY_RATIFIED
```

Не следует пытаться сохранить символ `≡` ценой расширительного толкования.

## STRONGEST ATTACK

Самое сильное возражение:

> Вы называете две формулировки эквивалентными, хотя одна задаёт обязательный pre-flight audit, а другая лишь запрещает один результат этого audit — дублирующую отправку.

Это точный semantic mismatch.

Аналогия:

```text
A1:
  перед каждым рейсом проверить топливо и двигатель;
  не взлетать, если самолёт уже неисправен.

A2:
  не взлетать, если уже известно, что двигатель неисправен.
```

A1 обеспечивает A2, но A2 не требует самой проверки. Называть их эквивалентными нельзя.

Это не возвращает двусмысленный `Rule 0`: разделение Rule A / Rule B остаётся правильным. Убит только лишний biconditional внутри Rule A. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
TARGET:
  RuleA_RelationRepair

FILES:
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md

  docs/routeB_bus/proshka/
    RULE_NAMING_DISAMBIGUATION_2026-07-31.md

MAKE EXACTLY ONE SEMANTIC CHANGE:
  replace the claim A1 ≡ A2 by:
    A1 is canonical;
    A2 is an operational corollary / T4a precedent;
    A1 ⇒ A2;
    no converse is claimed.

DO NOT CHANGE:
  - quoted A1 text;
  - quoted A2 text;
  - Rule B;
  - Goal 040;
  - Goal 040 answer;
  - post-close audit;
  - either materialized Proshka verdict;
  - git history.

VALIDATION:
  1. canonical and mirror copies byte-identical;
  2. old label "Rule 0" remains retired;
  3. no `A1 ≡ A2` remains;
  4. Rule B still states live ≡ R0.1–R0.3;
  5. Goal 040 SHA-256 remains
     48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300;
  6. rebuild MANIFEST.

SUCCESS:
  RULE_A_CANONICAL_WITH_A2_COROLLARY_PINNED

FAILURE:
  RULE_A_PROVENANCE_TEXT_MUTATED
  RULE_B_SEMANTICS_DRIFT
  GOAL040_SHA_DRIFT
  RULE_A_CANON_MIRROR_DRIFT
```

## META CLOSEOUT

**Что стало меньше:** пять запрошенных pin-gates сведены к одной логической надписи в одном файле. Goal 040, post-close audit, материализация вердиктов и Rule B закрыты. `[ABSTRACT][PAPER]`

**Что убито:** двусмысленный ярлык `Rule 0`; ретроактивная правка Goal 040; ложный тезис (A1\equiv A2). `[ABSTRACT][PAPER]`

**Что нельзя повторять:** нельзя объявлять процедуру предварительной проверки эквивалентной одному из её stop-cases. `[ABSTRACT][PAPER]`

**Текущий smallest named gap:**

[
\boxed{
\texttt{RuleA_A2CorollaryClassification}
}
]

`[ABSTRACT][CONDITIONAL]`

**Следующий решающий тест:** после минимального docs-only diff поиск по двум pinned копиям должен вернуть `A1 ⇒ A2` и ноль вхождений `A1 ≡ A2`. `[ABSTRACT][CONDITIONAL]`

**Fate of requested ratifications:**

```text
Rule A exact equivalence: REFUTED.
Rule B exact equivalence: RATIFIED.
Version-safe post-close pin: RATIFIED.
Goal 040 immutability: RESTORED_AND_RATIFIED.
Full combined gap: ONE-LINE_REPAIR_REMAINS.
```

```yaml
iteration:
  target: RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
  status: OPEN
  failed_strategy: treat_preflight_protocol_as_equivalent_to_one_stop_condition
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: RuleA_A2CorollaryClassification
  invariant_learned: quoted historical formulations may be related asymmetrically
  forbidden_future_move: preserve a false biconditional for naming convenience
  next_decisive_test: pin A1_as_canonical_and_A2_as_corollary
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
