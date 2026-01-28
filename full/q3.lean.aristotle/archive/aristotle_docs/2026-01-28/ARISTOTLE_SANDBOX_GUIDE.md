# Aristotle Sandbox Guide

**Полный гайд по созданию sandbox для Aristotle**

Дата: 2026-01-14
Автор: Claude + Ылша

---

## TL;DR

```lean
-- sandbox.lean
import Mathlib

def my_type := ...           -- ✅ OK
theorem X := by sorry        -- ✅ Aristotle создаст X_proof
-- axiom Y : ...             -- ❌ ЗАПРЕЩЕНО!
```

---

## Глава 1: Проблема

### Что мы хотели
Дать Aristotle "песочницу" с готовыми фактами, чтобы он только соединил их в доказательство.

### Почему это важно
- Ускорение поиска (меньше вариантов)
- Направление proof в нужную сторону
- Использование уже доказанных лемм

---

## Глава 2: Эксперименты

### Эксперимент 1: Project imports
```python
formal_input_context="Q3/Proofs/A1_density.lean"
```

**Результат:** ❌ FAILED
```
object file 'Q3/Basic/Defs.olean' does not exist
```

**Причина:** Aristotle не имеет доступа к нашему проекту.

---

### Эксперимент 2: Custom axioms (Stub approach)
```lean
import Mathlib

axiom W_K : ℝ → Set (ℝ → ℝ)              -- Свой тип
axiom hat_interpolation_approx : ...     -- Свой факт

theorem my_theorem := by sorry           -- Доказать это
```

**Результат:** ❌ FAILED
```
Unexpected axioms were added during verification:
['W_K', 'hat_interpolation_approx', ...]
```

**Причина:** Aristotle ОТВЕРГАЕТ пользовательские axioms при verification.

---

### Эксперимент 3: Pure Mathlib (УСПЕХ!)
```lean
import Mathlib

-- НЕТ axioms! Только def + theorem с sorry
def FejerKernel (B x : ℝ) : ℝ := max 0 (1 - |x| / B)

theorem two_plus_two : (2 : ℕ) + 2 = 4 := by sorry
theorem add_self_gt (x : ℝ) (hx : x > 0) : x + x > x := by sorry
```

**Результат:** ✅ SUCCESS!

Aristotle создал:
```lean
theorem two_plus_two_proof : (2 : ℕ) + 2 = 4 := by
  norm_num

theorem add_self_gt_proof (x : ℝ) (hx : x > 0) : x + x > x := by
  linarith
```

---

## Глава 3: Правила Sandbox

### ✅ Можно

| Элемент | Пример |
|---------|--------|
| Mathlib import | `import Mathlib` |
| Definitions | `def my_func (x : ℝ) := x * x` |
| Structures | `structure MyType where ...` |
| Theorems с sorry | `theorem X := by sorry` |
| Mathlib lemmas в hints | "Use `linarith` from Mathlib" |

### ❌ Нельзя

| Элемент | Пример | Ошибка |
|---------|--------|--------|
| Custom imports | `import MyProject.xxx` | "does not exist" |
| axiom | `axiom X : Type` | "Unexpected axioms" |
| opaque | `opaque X : Type` | Не проверено, вероятно тоже |
| constant | `constant X : P` | Не проверено |

---

## Глава 4: Как Aristotle обрабатывает sandbox

1. **Принимает** .lean файл с `import Mathlib`
2. **Парсит** все `def` и `theorem ... := by sorry`
3. **НЕ модифицирует** оригинальные `sorry`
4. **Создаёт НОВЫЕ** теоремы с суффиксом `_proof`
5. **Использует** Mathlib для доказательств

---

## Глава 5: Практическое применение

### Шаблон sandbox файла

```lean
/-
Sandbox for Aristotle
Project: [название]
Goal: [что доказать]
-/

import Mathlib

open [нужные namespaces]

/-! ## Definitions -/

-- Все типы и функции как def (НЕ axiom!)
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {f | Continuous f ∧ Function.support f ⊆ Set.Icc (-K) K}

def FejerKernel (B x : ℝ) : ℝ := max 0 (1 - |x| / B)

/-! ## Known facts (hints for Aristotle) -/

-- Факты которые "известны" — Aristotle может доказать их сам
-- или использовать как подсказки
theorem fejer_nonneg (B x : ℝ) : 0 ≤ FejerKernel B x := by sorry

theorem fejer_le_one (B x : ℝ) (hB : B > 0) : FejerKernel B x ≤ 1 := by sorry

/-! ## Main theorem to prove -/

theorem main_result : [statement] := by sorry
```

### Шаблон informal input

```markdown
# [Название теоремы]

## What to Prove
[Описание задачи]

## Definitions
See formal_input_context for:
- W_K: test function space
- FejerKernel: hat function

## Proof Sketch
1. First, use fejer_nonneg to show...
2. Then, apply fejer_le_one...
3. Finally, conclude...

## Hints
- Use `linarith` for linear arithmetic
- Use `norm_num` for numeric computations
- The key lemma is [X] from Mathlib
```

---

## Глава 6: API код

```python
import asyncio
from pathlib import Path
from aristotlelib import Project, ProjectInputType

async def sandbox_workflow(
    sandbox_lean: str,
    informal_md: str,
    output_path: str
):
    """
    Submit sandbox to Aristotle.

    Args:
        sandbox_lean: Path to self-contained .lean file (Mathlib only!)
        informal_md: Path to informal description
        output_path: Where to save result
    """
    print(f"Creating project...", flush=True)

    project = await Project.create(
        project_input_type=ProjectInputType.INFORMAL
    )
    print(f"Project ID: {project.project_id}", flush=True)

    # ВАЖНО: sandbox_lean должен быть self-contained!
    await project.solve(
        input_file_path=informal_md,
        formal_input_context=sandbox_lean
    )

    print(f"Submitted! Waiting...", flush=True)

    # Poll until complete
    from aristotlelib import ProjectStatus
    while project.status not in [ProjectStatus.COMPLETE, ProjectStatus.FAILED]:
        print(f"[{project.percent_complete}%] {project.status}", flush=True)
        await asyncio.sleep(30)
        await project.refresh()

    if project.status == ProjectStatus.COMPLETE:
        path = await project.get_solution(output_path)
        print(f"SUCCESS! Saved to: {path}")
        return str(path)
    else:
        print(f"FAILED: {project.status}")
        return None

# Использование:
# asyncio.run(sandbox_workflow(
#     "sandbox.lean",
#     "problem.md",
#     "result.lean"
# ))
```

---

## Глава 7: Ограничения

### Что Aristotle НЕ может с sandbox:

1. **Использовать ваши axioms** — он их отвергнет
2. **Импортировать ваш проект** — нет доступа к .olean файлам
3. **Модифицировать sorry** — создаёт новые `_proof` версии
4. **Гарантировать использование hints** — он сам решает как доказывать

### Что требует дополнительной работы:

1. **Перенос `_proof` теорем** обратно в проект
2. **Адаптация namespaces** если они отличаются
3. **Проверка совместимости** версий Mathlib

---

## Глава 8: FAQ

### Q: Почему axiom не работает?
**A:** Aristotle проверяет, что результат "чистый" — без новых axioms кроме стандартных (propext, Classical.choice, Quot.sound).

### Q: Можно ли использовать opaque?
**A:** Не тестировано. Вероятно тоже нет — Lean4 считает opaque близким к axiom.

### Q: Как дать Aristotle уже доказанную лемму?
**A:** Напишите её как `theorem X := by sorry`. Если она тривиальна — Aristotle сам докажет. Если сложна — он создаст `X_proof` с реальным доказательством.

### Q: Какая версия Mathlib?
**A:** v4.24.0 (October 2025) — смотрите в результате файла.

---

## Глава 9: Примеры

### Пример 1: Простая арифметика

**sandbox.lean:**
```lean
import Mathlib
theorem two_plus_two : (2 : ℕ) + 2 = 4 := by sorry
```

**Результат:**
```lean
theorem two_plus_two_proof : (2 : ℕ) + 2 = 4 := by
  norm_num
```

### Пример 2: Анализ

**sandbox.lean:**
```lean
import Mathlib
theorem inv_tendsto : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0) := by sorry
```

**Результат:**
```lean
theorem inv_tendsto_proof : ... := by
  exact tendsto_one_div_atTop_nhds_zero_nat
```

---

## Глава 10: Чеклист

Перед отправкой sandbox проверь:

- [ ] Файл содержит ТОЛЬКО `import Mathlib`
- [ ] НЕТ `axiom` declarations
- [ ] НЕТ `import MyProject.xxx`
- [ ] Все типы определены через `def` или `structure`
- [ ] Теоремы для доказательства имеют `by sorry`
- [ ] Informal input описывает что доказать и даёт hints
- [ ] Project ID записан в `project_ids.txt`

---

## Файлы проекта

```
aristotle_input/
├── project_ids.txt          # Все UUID проектов
├── sandbox_test.lean        # Тестовый sandbox (УСПЕХ!)
├── sandbox_test.md          # Informal input для теста
└── A1_density_stub.lean     # Неудачный stub (axioms)

aristotle_output/
├── sandbox_test_result.lean # Результат теста (УСПЕХ!)
└── ...

~/.claude/skills/aristotle/
├── skill.yaml               # Регистрация скилла
├── skill.md                 # Основная документация
└── DEEP_DIVE.md             # Визуальные диаграммы
```

---

## Контакты и ресурсы

- **API:** https://aristotle.harmonic.fun
- **PyPI:** `aristotlelib` v0.6.0
- **Lean:** v4.24.0
- **Mathlib:** v4.24.0 (Oct 2025)

---

*Этот документ создан на основе экспериментов 2026-01-14*
