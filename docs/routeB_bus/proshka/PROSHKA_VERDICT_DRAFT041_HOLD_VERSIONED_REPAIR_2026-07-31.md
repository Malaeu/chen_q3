# PROSHKA VERDICT — DRAFT_041_HOLD_FOR_VERSIONED_REPAIR
Date received: 2026-07-31 (chat timestamp "Today 7:12 AM" preceded this message)
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Consumed by: revert of goal-040 AMENDMENT A1 (goal restored to pinned SHA
48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300);
docs/routeB_bus/041_goal040_postclose_requirements_audit.md
Transport artifacts note: payload is verbatim as pasted by the owner from the
Proshka browser chat; copy-paste escaping artifacts preserved unmodified
(backslash-escaped underscores, "## STATUS" heading level, fences rendered as
```markdown). Semantic content untouched; no editing performed.

--- VERBATIM PAYLOAD BEGINS ---

## STATUS: OPEN — DRAFT\_041\_HOLD\_FOR\_VERSIONED\_REPAIR

```markdown
primary_verdict: DRAFT_NOT_SENDABLE_AS_WRITTEN
draft_is_send_authority: false
direct_send_authorized: false

rule_disambiguation:
  conceptual_split_A_vs_B: RATIFIABLE
  exact_text_equivalence_A: PENDING
  exact_text_equivalence_B: PENDING
  proposed_file_in_current_rh_clean: ABSENT

goal_040:
  current_status: PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
  current_goal_mutation_after_answer: FORBIDDEN
  postclose_amendment_required_location: SEPARATE_VERSIONED_ARTIFACT
  proof_used_tent_log_moment_route: false
  proof_used_cheaper_exact_mellin_witness: true

goal_041:
  current_status: CONDUCTOR_HANDOVER_COMPLETE
  currently_states_goal_040_unchanged: true

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
```

## ROUTE MAP

Черновик **не отправлять пока**. Разделение двух разных «Rule 0» на:

```markdown
Rule A = RULE_INVENTORY_FIRST
Rule B = RULE_SEND_DISCIPLINE
```

концептуально правильное. Ратификация должна быть раздельной:

```markdown
A: A1 ≡ A2
B: live formulation ≡ R0.1–R0.3
```

`[ABSTRACT][PAPER]`

Но в текущем `rh_clean` файл

```markdown
docs/routeB_bus/proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md
```

ещё отсутствует. Поэтому draft сейчас описывает будущий объект как уже материализованный. `[ABSTRACT][CONDITIONAL]`

Есть более серьёзная проблема. Текущий ответ 041 уже закрыт как `CONDUCTOR_HANDOVER_COMPLETE` и прямо фиксирует, что Goal 040 был **не изменён** и завершён отдельным ответом.

Сам Goal 040 уже закрыт:

```markdown
PL2_RAW_POLE_MISMATCH_WITNESS_PROVED
```

с Lean-проверенным theorem `exists_rawZetaMellin_not_continuousAt_one`, зелёной сборкой, нулевым taint и стандартной тройкой аксиом.

## FINAL PROPOSAL

### Rule A / Rule B

Оставить предложенное именование. После sync предоставить один commit-pinned файл, содержащий:

```markdown
Rule A:
  обе точные формулировки A1 и A2;
  явное утверждение эквивалентности только внутри этой пары.

Rule B:
  live formulation;
  R0.1 DEFAULT_SHOW;
  R0.2 EXPLICIT_SEND_AUTHORITY;
  R0.3 RECIPIENT_AND_CHANNEL_LOCK;
  mapping между ними.
```

Тогда A и B можно ратифицировать независимо. `[ABSTRACT][PAPER]`

### Goal 040

**Не вставлять `AMENDMENT A1` задним числом в уже закрытый goal-файл.**

Исходный Goal 040 и его ответ образуют source-locked транзакцию. Ответ 040 пинит конкретный SHA goal-файла и сообщает, что theorem уже доказан. Изменение goal после результата превратит контракт в ретроактивно отредактированный.

Правильный объект:

```markdown
docs/routeB_bus/041_goal040_postclose_requirements_audit.md
```

или следующий нумерованный audit-goal. Его header:

```markdown
status: POSTCLOSE_REVIEWER_REQUIREMENTS
normative_for_goal_040_execution: false
modifies_goal_040_contract: false
```

В нём можно дословно сохранить:

```markdown
A1.1:
  bump_mass > 0
  right_support_lower > left_support_upper

A1.2:
  log-moment without derivative-identification theorem
  ⇒ PL2_DERIV_IDENTIFICATION_API_GAP

A1.3:
  P040-PL2 registered prediction
```

Но это будут **post-close reviewer guards**, а не условия, которые будто бы были исполнены доказательством 040.

### Исправление пункта (2) в черновике

Заменить его на:

> «Оба STRONGEST-ATTACK требования сохранены в отдельном post-close audit; исходный Goal 040 и его source hash не изменялись. Goal 040 уже закрыт более дешёвым точным свидетелем: компактной квадратичной функцией с явной Mellin-формулой и $\operatorname{deriv}(\operatorname{Mellin}h)(1)=-1/12$. Поэтому tent/translation/log-bound маршрут классифицирован как sound but superseded, а не как фактически использованный proof route.»

Это соответствует реальному ответу 040: вместо двух translated tents была использована функция

$$
h(u)=1_{(0,1]}(u)\,u-\frac32\,1_{(0,1]}(u)\,u^2,
$$

для которой Mellin transform вычислен точно, масса равна нулю, а производная в единице равна $-1/12$.

## STRONGEST ATTACK

Главное возражение к текущему draft:

> После закрытия theorem вы изменили текст goal так, чтобы выполненная работа выглядела как исполнение новых требований.

Это ретроактивный ремонт контракта. Он ломает:

```markdown
registration-before-test;
source-hash provenance;
prediction scoring;
answer-to-goal correspondence.
```

`[ABSTRACT][PAPER]`

Второе возражение:

> Draft утверждает, что требования про translated tents, translation invariance и constant log bounds были внесены и исполнены, хотя фактическое доказательство выбрало другой witness.

Фактический маршрут был дешевле и сильнее: exact Mellin formula. Прогноз `P040-M3` в ответе 040 честно оценён как `SUPERSEDED_BY_CHEAPER_EXACT_WITNESS`, а не как подтверждённый использованный путь.

## CODEX DIRECTIVE

```markdown
NO EXECUTION DIRECTIVE.

Do not send the browser message.
Do not mutate the closed Goal 040.
Do not replace placeholders yet.

After mirror-sync, provide:
  1. exact HEAD;
  2. SHA-256 of the materialized Proshka verdict;
  3. pinned Rule A/B disambiguation file;
  4. separate post-close requirements audit;
  5. confirmation that original Goal 040 SHA remains unchanged.
```

## META CLOSEOUT

**Что стало меньше?**

Запрос распался на две независимые проверки:

```markdown
Rule naming/equivalence audit;
version-safe Goal 040 post-close audit.
```

**Что убито?**

```markdown
единый неоднозначный ярлык "Rule 0";
ретроактивное изменение закрытого Goal 040;
утверждение, что tent/log-moment route был фактическим proof route.
```

**Что нельзя повторять?**

Нельзя менять зарегистрированный goal после появления matching answer. Новые требования оформляются отдельным versioned audit или новым goal.

**Current smallest named gap:**

```markdown
RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
```

**Следующий решающий тест:**

```markdown
original Goal 040 SHA before/after 041 sync must be identical.
```
```markdown
iteration:
  target: draft_reply_after_goal_041
  status: OPEN
  failed_strategy: retroactive_goal_amendment
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: RULE_A_B_EXACT_TEXT_AND_VERSION_SAFE_POSTCLOSE_PIN
  invariant_learned: a closed goal is immutable; later reviewer requirements need a separate artifact
  forbidden_future_move: rewrite a proved contract to match later feedback
  next_decisive_test: compare original_goal_040_sha_across_sync
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
