# Aristotle Sandbox Challenge

## Проблема

Мы хотим дать Aristotle "песочницу" — набор готовых фактов, чтобы он только соединил их в доказательство. Но наши эксперименты показали ограничения:

### Что НЕ работает:

1. **Project imports** (`import Q3.Axioms`)
   - Aristotle не имеет доступа к нашему проекту
   - Ошибка: `object file does not exist`

2. **Custom axioms** (`axiom my_fact : ...`)
   - Aristotle ОТВЕРГАЕТ файлы с пользовательскими axioms
   - Ошибка: `Unexpected axioms were added during verification`

### Что работает:

1. **Pure informal** — всё как текст в .md, Aristotle формализует сам
2. **Mathlib imports** — стандартная библиотека доступна

## Гипотеза: Mathlib-based Sandbox

Если нельзя добавлять свои axioms, можно ли:
- Использовать СУЩЕСТВУЮЩИЕ факты из Mathlib как "данность"
- Дать Aristotle hint: "используй вот эти леммы из Mathlib"
- Он соединяет их в доказательство

## Ключевой вопрос для исследования

**Как построить sandbox, который Aristotle примет?**

### Вариант A: Mathlib hints в informal input
```markdown
## Dependencies from Mathlib
Use these lemmas:
- `Nat.add_comm : ∀ n m, n + m = m + n`
- `Real.tendsto_atTop_atTop_of_lt : ...`
```

### Вариант B: Self-contained .lean с Mathlib only
```lean
import Mathlib

-- Нет своих axioms! Только Mathlib.
-- Просим доказать используя существующие факты.

theorem foo : ... := by sorry
```

### Вариант C: Какой-то хак?
- Может быть, можно как-то "замаскировать" axioms?
- Или использовать `opaque` вместо `axiom`?
- Или `constant`?

## Aristotle Architecture (что мы знаем)

1. **Verification step**: проверяет что proof не добавляет новых axioms
2. **Allowed axioms**: только `propext`, `Classical.choice`, `Quot.sound`
3. **Mathlib**: полностью доступен (v4.24.0, Oct 2025)
4. **formal_input_context**: .lean файл передаётся в solver
5. **auto_add_imports**: автоматически собирает imports

## API Details

```python
from aristotlelib import Project, ProjectInputType

# Power combo (если бы работало)
project = await Project.create(project_input_type=ProjectInputType.INFORMAL)
await project.solve(
    input_file_path="problem.md",
    formal_input_context="sandbox.lean"  # <- Как сделать этот файл?
)
```

## Эксперименты для проведения

### Test 1: Pure Mathlib sandbox
```lean
import Mathlib
-- Без axioms, только Mathlib
theorem two_plus_two : 2 + 2 = 4 := by sorry
```

### Test 2: Hint existing lemmas
```markdown
Prove: For all x > 0, x + x > x
Use: `add_pos` from Mathlib
```

### Test 3: opaque/constant вместо axiom
```lean
import Mathlib
opaque my_type : Type  -- вместо axiom?
constant my_fact : P   -- вместо axiom?
```

## Success Criteria

Sandbox работает если:
1. Aristotle ПРИНИМАЕТ formal_input_context файл
2. НЕ выдаёт "Unexpected axioms" ошибку
3. ИСПОЛЬЗУЕТ предоставленные факты в proof
4. Возвращает COMPLETE статус с валидным доказательством

---

# ✅ РЕШЕНИЕ НАЙДЕНО!

## Working Sandbox Approach

**Эксперимент:** `sandbox_test.lean` + `sandbox_test.md`
**Результат:** COMPLETE с валидными доказательствами!

### Что работает:

```lean
import Mathlib  -- ТОЛЬКО Mathlib, ничего своего

-- Definitions как def (НЕ axiom!)
def my_function (x : ℝ) : ℝ := x * x

-- Теоремы с sorry (Aristotle заполнит)
theorem my_theorem : ... := by sorry
```

### Что Aristotle делает:

1. Принимает .lean файл с `import Mathlib` only
2. НЕ модифицирует оригинальные `sorry`
3. СОЗДАЁТ НОВЫЕ теоремы с суффиксом `_proof`:
   - `theorem X : ... := by sorry` → `theorem X_proof : ... := by actual_proof`

### Пример результата:

```lean
-- Оригинал (оставляет как есть)
theorem two_plus_two : (2 : ℕ) + 2 = 4 := by sorry

-- Aristotle добавляет:
theorem two_plus_two_proof : (2 : ℕ) + 2 = 4 := by
  norm_num

theorem add_self_gt_proof (x : ℝ) (hx : x > 0) : x + x > x := by
  linarith

theorem inv_tendsto_zero_proof : Filter.Tendsto ... := by
  exact tendsto_one_div_atTop_nhds_zero_nat
```

### Ключевые правила sandbox:

| Можно | Нельзя |
|-------|--------|
| `import Mathlib` | `import MyProject.xxx` |
| `def X := ...` | `axiom X : ...` |
| `theorem X := by sorry` | `opaque X : ...` |
| Mathlib lemmas в hints | Custom axioms |

## Цель

Если найдём рабочий sandbox approach:
- Можем давать Aristotle "подсказки" в виде Mathlib lemmas
- Ускоряем search space (меньше вариантов искать)
- Можем "направлять" proof в нужную сторону

## Контакты

- API: https://aristotle.harmonic.fun
- PyPI: `aristotlelib` v0.6.0
- Lean: v4.24.0, Mathlib v4.24.0
