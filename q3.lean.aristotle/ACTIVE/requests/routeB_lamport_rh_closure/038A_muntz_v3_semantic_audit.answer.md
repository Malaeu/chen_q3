# STATUS: MUNTZ_V3_CONDITIONAL_SHELL_SEMANTICALLY_VERIFIED
```yaml
PRIMARY_VERDICT: MUNTZ_V3_CONDITIONAL_SHELL_SEMANTICALLY_VERIFIED
PRIMARY_VERDICT_COUNT: 1
ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
STATE_PROMOTION: false
RH_CLAIMED: false

AUTHOR: conductor
AUTHOR_NOTE: >
  Транспортный аудит, не математический ответ. Кондуктор проверял только то,
  что проверяется сравнением: знаки, определения, отсутствие taint, профиль
  аксиом. Математическое содержание не оценивалось — это не его зона.

SOURCE:
  ARISTOTLE_PROJECT: 987ff124-3032-42e5-aa9f-24ceef69f62a
  ARISTOTLE_TASK: 472e126c-759f-4c69-8816-fa013ff740b2
  TASK_STATUS: COMPLETE_WITH_ERRORS
  HARVEST_PATH: q3.lean.aristotle/aristotle_output/987ff124_MUNTZ_V3_POLESUBTRACTED_2026-07-30/
  AUDITED_FILE: RequestProject/Main.lean
  LINES: 239

RPLUS_SIGN_CHECK:
  VERDICT: RPLUS_SIGN_MINUS_CONFIRMED
  OCCURRENCES_CHECKED: 7
  ALL_MINUS: true
  ANY_PLUS_RPLUS: false
  LINES: [161, 163, 165, 211, 214, 234, 235]
  FORM: "ZetaMellinPoleSub h (s + 1/2) - Rminus h Λ s - Rplus h Λ s"

DEFINITIONS_MATCH_CONTRACT:
  RMINUS: "∫ u in Set.Ioo 0 Λ⁻¹, Estar h u * u^(s-1)"
  RPLUS: "∫ u in Set.Ioi Λ, Estar h u * u^(s-1)"
  RPLUS_IS_POSITIVE_TAIL_INTEGRAL: true

POLE_VALUE_CHECK:
  VERDICT: POLE_VALUE_CLEAN
  ZETA_MELLIN_POLE_SUB_AT_1: "deriv (Mellin h) 1"        # строка 125
  MELLIN_DIV_ONE_AT_1: "deriv (Mellin h) 1"              # строка 49
  EQUATED_WITH_RAW_ZETA_ONE: false
  RIEMANN_ZETA_ONE_PRESENT_IN_FILE: false

TAINT_SCAN:
  PATTERN: "sorry|admit|native_decide|exact?"
  MATCHES: 0

AXIOMS:
  DECLARED: [propext, Classical.choice, Quot.sound]
  NEW_AXIOMS: false

STOP_CODES:
  MUNTZ_V3_SOURCE_NOT_HARVESTED: false
  MUNTZ_V3_TAINT_FOUND: false
  MUNTZ_V3_RPLUS_SIGN_DRIFT: false
  MUNTZ_V3_POLE_VALUE_DRIFT: false
  MUNTZ_V3_AXIOM_PROFILE_DRIFT: false

NOT_VERIFIED_BY_CONDUCTOR:
  - MUNTZ_V3_BUILD_FAIL          # lake build кондуктором не запускался
  - MUNTZ_V3_EXTRA_HIDDEN_PREMISE # требует чтения дерева зависимостей
```

## Что проверялось и как

Гейт поставлен судьёй в директиве 038: до этого аудита свежий результат v3
импортировать было нельзя. Причина — исторический дрейф знака: в R6-файле
`Rplus` определён как положительный интеграл хвоста, но условное продолжение
было записано с `− Rminus + Rplus`. Одно успешно собравшееся Lean-утверждение
с неверным знаком является доказательством не той теоремы.

### Знак — семь вхождений, все с минусом

```
161: (hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane)
163: Gwin h Λ s = ZetaMellinPoleSub h (s + 1/2) - Rminus h Λ s - Rplus h Λ s
165: let F := fun s => ZetaMellinPoleSub h (s + 1/2) - Rminus h Λ s - Rplus h Λ s
211: ... - Rminus h Λ s - Rplus h Λ s
214: ... - Rminus h Λ s - Rplus h Λ s
234: ... - Rminus h Λ s - Rplus h Λ s
235: Gwin h Λ (1/2) = deriv (Mellin h) 1 - Rminus h Λ (1/2) - Rplus h Λ (1/2)
```

Ни одного `+ Rplus`. Дрейф R6 в свежем проекте не повторён.

### Определения совпадают с контрактом v3

```lean
noncomputable def Rminus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (0 : ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rplus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)
```

`Rplus` — именно положительный интеграл по `(Λ, ∞)`, как требует контракт.

### Значение в полюсе

`ZetaMellinPoleSub h 1 = deriv (Mellin h) 1` (строка 125), `MellinDivOne h 1 =
deriv (Mellin h) 1` (строка 49). Приравнивания к сырому `ζ(1)·Mellin h 1` нет;
`riemannZeta 1` в файле не встречается вовсе.

## Границы этого аудита

Кондуктор — транспорт. Проверено только то, что решается сравнением: знаки,
формы определений, отсутствие taint, заявленный профиль аксиом. **Не
проверялось:** `lake build` (не запускался), полное дерево зависимостей на
скрытые посылки, математическая корректность рассуждения. Эти пункты
директивы остаются за исполнителем и судьёй.

## Следствие

Условная оболочка `T4a ⟹ pole-subtracted T4c–T4g ⟹ T5` семантически
верифицирована и может быть заморожена. Стоп-коды по знаку, значению в полюсе,
taint и аксиомам не срабатывают.
