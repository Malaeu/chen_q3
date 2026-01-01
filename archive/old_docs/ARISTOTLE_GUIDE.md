# 🏛️ ARISTOTLE WORKFLOW GUIDE
## Инструкции для Claude по работе с Harmonic Aristotle

**Версия:** 2.0
**Последнее обновление:** 2025-12-22
**Проверено на:** Q3 Twin Primes формализация

---

## 🚨 КРИТИЧЕСКИЕ ОШИБКИ (НЕ ПОВТОРЯТЬ!)

### 1. Неправильный UUID
```python
# ❌ НЕПРАВИЛЬНО - копипастил UUID с ошибкой
pid = '2647ad4e-8c3f-4be8-9a4d-fc7d4c5c8a2c'  # 403 Forbidden!

# ✅ ПРАВИЛЬНО - брать из project_ids.txt
pid = '2647ad4e-a3ce-42e5-8bca-6b1ca80bdca4'  # Работает!
```

### 2. Несуществующий атрибут `progress`
```python
# ❌ НЕПРАВИЛЬНО
print(p.progress)  # AttributeError!

# ✅ ПРАВИЛЬНО
print(p.percent_complete)  # 0-100
print(p.status)  # ProjectStatus enum
```

### 3. Неправильный тип ввода для .md файлов
```python
# ❌ НЕПРАВИЛЬНО - Aristotle ожидает .lean по умолчанию
await Project.prove_from_file(input_file_path="problem.md")

# ✅ ПРАВИЛЬНО - указать INFORMAL для .md/.txt/.tex
from aristotlelib import ProjectInputType
await Project.prove_from_file(
    input_file_path="problem.md",
    project_input_type=ProjectInputType.INFORMAL,
    validate_lean_project=False,
)
```

---

## 📦 УСТАНОВКА И НАСТРОЙКА

### venv находится здесь:
```bash
/Users/emalam/Documents/GitHub/chen_q3/.venv
```

### Активация:
```bash
cd /Users/emalam/Documents/GitHub/chen_q3
source .venv/bin/activate
```

### Проверка API ключа:
```bash
echo $ARISTOTLE_API_KEY
# Должен быть установлен в ~/.zshrc
```

---

## 🔧 ARISTOTLELIB API REFERENCE

### Основные классы
```python
from aristotlelib import Project, ProjectInputType, ProjectStatus
```

### ProjectStatus enum
```python
ProjectStatus.NOT_STARTED
ProjectStatus.QUEUED
ProjectStatus.IN_PROGRESS
ProjectStatus.COMPLETE
ProjectStatus.FAILED
ProjectStatus.PENDING_RETRY
```

### ProjectInputType enum
```python
ProjectInputType.FORMAL_LEAN = 2   # Для .lean файлов
ProjectInputType.INFORMAL = 3      # Для .md, .txt, .tex файлов
```

### Project атрибуты
```python
p.project_id         # str: UUID проекта
p.status             # ProjectStatus enum
p.percent_complete   # int | None: 0-100
p.file_name          # str | None: путь к входному файлу
p.created_at         # datetime
p.last_updated_at    # datetime
```

### Project методы
```python
# Создать/получить проект
p = await Project.from_id(project_id)
p = await Project.create(context_file_paths=[...])

# Отправить на решение
await p.solve(input_file_path="problem.lean")
await p.solve(input_content="theorem ...")

# Получить решение (скачивает файл!)
solution_path = await p.get_solution(output_path="result.lean")

# Обновить статус
await p.refresh()

# Дождаться завершения
await p.wait_for_completion()

# Добавить контекст
await p.add_context(context_file_paths=["helper.lean"])
```

---

## 📤 ОТПРАВКА ПРОЕКТА

### Вариант 1: prove_from_file (всё в одном)
```python
import asyncio
from aristotlelib import Project, ProjectInputType

async def submit():
    project_id = await Project.prove_from_file(
        input_file_path="problem.md",
        project_input_type=ProjectInputType.INFORMAL,
        validate_lean_project=False,
        wait_for_completion=False,  # Не ждать
    )
    print(f"Submitted: {project_id}")
    return project_id

asyncio.run(submit())
```

### Вариант 2: create + solve (с контекстом)
```python
async def submit_with_context():
    # Создать проект с контекстом
    p = await Project.create(
        context_file_paths=["Twins/Defs.lean", "proven_lemma.lean"],
        validate_lean_project_root=False,
        project_input_type=ProjectInputType.INFORMAL,
    )

    # Добавить ещё контекст
    await p.add_context(
        context_file_paths=["more_context.md"],
        validate_lean_project_root=False,
        project_root=Path("."),
    )

    # Отправить задачу
    await p.solve(input_file_path="main_problem.md")

    return p.project_id
```

---

## 📥 ПОЛУЧЕНИЕ РЕЗУЛЬТАТА

```python
async def download_solution(project_id: str, output_path: str):
    p = await Project.from_id(project_id)

    if p.status == ProjectStatus.COMPLETE:
        result = await p.get_solution(output_path)
        print(f"Downloaded: {result}")
        print(result.read_text())
    elif p.status == ProjectStatus.FAILED:
        print("FAILED - need to retry")
    else:
        print(f"Still working: {p.percent_complete}%")
```

---

## 📊 МОНИТОРИНГ СТАТУСА

```python
async def monitor(project_ids: dict[str, str]):
    for name, pid in project_ids.items():
        try:
            p = await Project.from_id(pid)
            status = f"{p.status.name:15} {p.percent_complete}%"
            print(f"{name}: {status}")
        except Exception as e:
            print(f"{name}: ERROR - {e}")
```

---

## 🎯 ТАКТИКА ФОРМАЛИЗАЦИИ (OEDT)

### OEDT = Outline, Examples, Definitions, Theorems

### Структура входного .md файла:
```markdown
# Theorem Name

## Setup (Definitions)
- Define key objects
- Import statements (suggestive)

## Theorem Statement
```lean
theorem my_theorem ... := by
  sorry
```

## Proof Outline
**Step 1:** ...
**Step 2:** ...

## Key Lemmas Needed
1. Lemma A: ...
2. Lemma B: ...

## Numerical Evidence (optional)
- Experimental data supporting the theorem
```

---

## 🏗️ TIERED AXIOM SYSTEM

### Tier-1: Elementary (PROVABLE)
- Mathlib lemmas
- Basic number theory
- Should be provable by Aristotle

### Tier-2: Research-level (AXIOMS/THEOREMS)
- T2.1-style theorems Aristotle CAN prove
- T2.2+ axioms based on numerical evidence
- Conjectural results (Hardy-Littlewood, etc.)

### Правило: Если Aristotle застревает — разбей на Tier-1 леммы!

---

## 📁 СТРУКТУРА ПРОЕКТА

```
project_aristotle/
├── ProjectName/           # Lean 4 source
│   ├── Defs.lean          # Definitions
│   ├── Axioms.lean        # Tiered axioms
│   ├── Lemmas.lean        # Helper lemmas
│   └── Main.lean          # Main theorems
├── aristotle_input/       # .md files для Aristotle
│   ├── Problem1.md
│   └── Problem2_v2.md     # V2 с контекстом
├── aristotle_output/      # Сгенерированные .lean
├── submit.py              # Submission script
├── project_ids.txt        # UUID'ы проектов
├── lakefile.toml          # Lake config
└── lean-toolchain         # Lean version
```

---

## 🔄 WORKFLOW

### 1. Подготовка
```bash
mkdir project_aristotle && cd project_aristotle
mkdir -p ProjectName aristotle_input aristotle_output
```

### 2. Написать определения (Defs.lean)
```lean
import Mathlib
def MyObject (x : ℕ) : Prop := ...
```

### 3. Создать входной .md файл
Следовать OEDT структуре (см. выше)

### 4. Отправить в Aristotle
```python
project_id = await Project.prove_from_file(
    input_file_path="aristotle_input/Problem.md",
    project_input_type=ProjectInputType.INFORMAL,
    wait_for_completion=False,
)
# Сохранить UUID!
with open("project_ids.txt", "a") as f:
    f.write(f"Problem.md: {project_id}\n")
```

### 5. Мониторить прогресс
```python
p = await Project.from_id(project_id)
print(f"{p.status.name} {p.percent_complete}%")
```

### 6. Скачать результат
```python
if p.status == ProjectStatus.COMPLETE:
    await p.get_solution("aristotle_output/Problem_aristotle.lean")
```

### 7. Если FAILED — создать V2 с контекстом
- Добавить доказанные леммы
- Упростить формулировку
- Разбить на под-задачи

---

## 🆚 OPUS vs ARISTOTLE

| Критерий | Opus (ручной код) | Aristotle |
|----------|-------------------|-----------|
| Скорость | Минуты | Минуты-часы |
| Компактность | ~60 строк | ~10 строк |
| Читаемость | Высокая | Низкая |
| Надёжность | Зависит от меня | Проверено |
| Подход | Леммы + структура | Brute-force тактики |

### Когда что использовать:
- **Opus**: Педагогические доказательства, понимание
- **Aristotle**: Продакшен код, сложные случаи

---

## 📋 ЧЕКЛИСТ ПЕРЕД ОТПРАВКОЙ

- [ ] `.md` файл использует `ProjectInputType.INFORMAL`
- [ ] `validate_lean_project=False` для неформальных входов
- [ ] UUID сохранён в `project_ids.txt`
- [ ] Определения корректны (проверены в Lean)
- [ ] Theorem statement имеет `sorry`
- [ ] Proof outline понятен
- [ ] Численные данные (если есть) включены

---

## 🐛 TROUBLESHOOTING

### 403 Forbidden
- Неправильный UUID (опечатка)
- Проект не принадлежит твоему API ключу
- Проверь `project_ids.txt`

### "File is not a Lean file"
- Добавь `project_input_type=ProjectInputType.INFORMAL`

### AttributeError: 'progress'
- Используй `percent_complete` вместо `progress`

### FAILED status
- Задача слишком сложная
- Создай V2 с контекстом
- Разбей на под-леммы

---

## 📚 ПРИМЕРЫ ИЗ Q3

### Успешный проект: Q3_twins_mod6
- Вход: 40 строк .md с OEDT структурой
- Выход: 10 строк Lean с `interval_cases`
- Время: ~5 минут

### Сложный проект: Q3_twins_exp_sum
- Вход: 98 строк .md
- Статус: IN_PROGRESS (требует больше времени)
- Backup: V2 с контекстом готов

---

## 🔄 ИТЕРАТИВНАЯ ТАКТИКА (КРИТИЧЕСКИ ВАЖНО!)

### Принцип: V1 → V2 → V3 → ... → SUCCESS

Aristotle может не решить сложную задачу с первого раза. Но каждая попытка даёт **контекст для следующей**!

### Алгоритм итераций:

```
1. V1: Отправить базовую задачу
   ↓
2. Aristotle возвращает результат (даже частичный/FAILED)
   ↓
3. ИЗУЧИТЬ что он сделал:
   - Какие леммы доказал?
   - Где застрял?
   - Какие тактики использовал?
   ↓
4. V2: Добавить в контекст:
   - Доказанные леммы из V1
   - Подсказки где он застрял
   - Разбиение на под-задачи
   ↓
5. Повторять пока не SUCCESS (обычно 3-6 итераций)
```

### Пример структуры V2:

```markdown
# Problem V2

## PROVEN CONTEXT (from V1)

Aristotle уже доказал следующее (можно использовать):

```lean
-- Из предыдущей попытки
lemma helper1 : ... := by ...
lemma helper2 : ... := by ...
```

## HINT: Where V1 got stuck

V1 застрял на шаге 3 потому что не знал про X.
Подсказка: использовать теорему Y из Mathlib.

## Main theorem (simplified)

Теперь доказать только оставшуюся часть...
```

### Реальный пример из Q3:

| Итерация | Что сделали | Результат |
|----------|-------------|-----------|
| V1 | Базовая задача | FAILED на шаге 5 |
| V2 | + леммы из V1, + hint | 60% done |
| V3 | + больше контекста | 85% done |
| V4 | + разбиение на 2 части | Part 1 ✅ |
| V5 | + Part 1 как контекст | Part 2 ✅ |
| V6 | Склеить | **COMPLETE** ✅ |

### Ключевые правила:

1. **НИКОГДА не выбрасывай частичные результаты** — они становятся контекстом
2. **Читай ВСЁ что Aristotle сделал** — даже если FAILED
3. **Разбивай большие задачи** — проще доказать 5 маленьких
4. **Добавляй HINTS** — где он застрял и как обойти
5. **Используй доказанные леммы** — они уже проверены Lean

### Как скачать частичный результат:

```python
# Даже если status == FAILED, может быть частичный код
p = await Project.from_id(project_id)
if p.status in [ProjectStatus.COMPLETE, ProjectStatus.FAILED]:
    try:
        result = await p.get_solution("partial_result.lean")
        # Изучить что он успел сделать
        print(result.read_text())
    except:
        print("Нет даже частичного результата")
```

### Шаблон для V(N+1):

```markdown
# Problem V{N+1}

## Previously Proven (from V1...V{N})

{Вставить все доказанные леммы}

## Current Goal

{Упрощённая/оставшаяся часть задачи}

## Hints

1. {Где застревал раньше}
2. {Какие тактики работают}
3. {Какие теоремы из Mathlib использовать}
```

---

**ПОМНИ:** Aristotle мощный, но ему нужен правильный input! Итерации — ключ к успеху!
