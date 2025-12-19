# Aristotle - Полная Документация

## Что такое Aristotle?

**Aristotle** — AI theorem prover от [Harmonic](https://harmonic.fun/), достигший уровня золотой медали IMO 2025 (5/6 задач). Конвертирует неформальную математику (English/LaTeX) в формальные Lean4 доказательства.

**Достижения:**
- IMO 2025: 5/6 задач (Gold Medal level)
- Erdos Problem #124: решена за 6 часов автономно
- 200B+ параметров, Monte Carlo tree search + reinforcement learning

---

## API Reference

### Base URL
```
https://aristotle.harmonic.fun/api/v1
```

### Аутентификация
```
Header: X-API-Key: {your_api_key}
```

Получить ключ: https://aristotle.harmonic.fun (Early Access)

---

## API Endpoints

| Endpoint | Метод | Описание |
|----------|-------|----------|
| `/project?project_type={2\|3}` | POST | Создать проект |
| `/project/{id}` | GET | Получить статус проекта |
| `/project/{id}/result` | GET | Скачать Lean solution |
| `/project` | GET | Список всех проектов |
| `/project/{id}/solve` | POST | Запустить решение |
| `/project/{id}/context` | POST | Добавить context файлы |

---

## ВАЖНО: Лимиты API

### Max Concurrent Projects: 5

**Что это значит:**
- Одновременно можно иметь максимум **5 активных проектов** (со статусом `IN_PROGRESS` или `QUEUED`)
- Завершённые проекты (`COMPLETE`, `FAILED`) не считаются
- При превышении: HTTP 429 "Too Many Requests"

**Что делать при 429:**
1. Дождаться завершения одного из текущих проектов
2. Или отменить неактуальный проект (если API поддерживает)

### Pagination Limit: 100

**Что это значит:**
- GET `/project` возвращает максимум **100 проектов за запрос**
- Для получения остальных использовать `pagination_key`

**Пример пагинации:**
```python
# Первый запрос
response = await Project.list_projects(limit=100)
projects, next_key = response

# Следующая страница
if next_key:
    response = await Project.list_projects(limit=100, pagination_key=next_key)
```

---

## Project Types

| Type | Значение | Описание |
|------|----------|----------|
| `2` | FORMAL_LEAN | Входной файл уже в Lean4 синтаксисе |
| `3` | INFORMAL | Входной файл в English/LaTeX (автоформализация) |

**Когда использовать:**
- `type=3 (INFORMAL)` — когда пишешь на английском с LaTeX формулами. Aristotle сам переведёт в Lean4.
- `type=2 (FORMAL)` — когда уже есть Lean4 код и нужна помощь с тактиками/доказательствами.

---

## Project Statuses

| Status | Описание |
|--------|----------|
| `NOT_STARTED` | Создан, но solve не вызван |
| `QUEUED` | В очереди на обработку |
| `IN_PROGRESS` | Aristotle работает над ним |
| `COMPLETE` | Готово! Solution доступен |
| `FAILED` | Не смог доказать |
| `PENDING_RETRY` | Ошибка, будет повторная попытка |

---

## Response Format

**GET /project/{id}:**
```json
{
  "project_id": "uuid",
  "status": "IN_PROGRESS",
  "percent_complete": 42,
  "file_name": "input.md",
  "description": "Prove theorem X",
  "created_at": "2025-12-14T10:00:00",
  "last_updated_at": "2025-12-14T10:30:00"
}
```

**GET /project (list):**
```json
{
  "projects": [...],
  "pagination_key": "next_page_key_or_null"
}
```

---

## CLI Usage

```bash
# Установка
uv pip install aristotlelib  # или pip install aristotlelib

# API Key
export ARISTOTLE_API_KEY="arstl_..."

# Запуск доказательства (informal mode)
aristotle prove-from-file --informal --no-validate-lean-project theorem.md

# Не ждать завершения
aristotle prove-from-file --informal --no-validate-lean-project theorem.md --no-wait

# С context файлами
aristotle prove-from-file --informal theorem.md --context-folder ./helpers/
```

### CLI Flags

| Flag | Описание |
|------|----------|
| `--informal` | Использовать INFORMAL mode (English/LaTeX -> Lean4) |
| `--no-validate-lean-project` | Не проверять что файлы в Lean project |
| `--no-wait` | Вернуть project_id сразу, не ждать завершения |
| `--polling-interval N` | Проверять статус каждые N секунд (default: 30) |
| `--output-file FILE` | Куда сохранить результат |
| `--context-folder DIR` | Папка с дополнительными .lean/.md/.tex файлами |

---

## Python API

```python
import asyncio
from aristotlelib import Project, ProjectStatus

# Создать и запустить проект
async def run_proof():
    project = await Project.prove_from_file(
        input_file_path="theorem.md",
        auto_add_imports=False,
        validate_lean_project=False,
    )
    print(f"Status: {project.status}")

    # Дождаться завершения
    await project.wait_for_completion()

    # Скачать solution
    path = await project.get_solution("output.lean")
    print(f"Downloaded: {path}")

# Проверить статус существующего
async def check_status(project_id):
    p = await Project.from_id(project_id)
    print(f"Status: {p.status}, Progress: {p.percent_complete}%")

# Список всех проектов
async def list_all():
    projects, next_key = await Project.list_projects(limit=50)
    for p in projects:
        print(f"{p.file_name}: {p.status}")

asyncio.run(run_proof())
```

---

## Input File Format (Informal Mode)

```markdown
# Theorem Name

## Setup (definitions, notation)
Let $X$ be a set...
Define $f: X \to Y$ by...

## Theorem (statement to prove)
Prove that $f$ is continuous.

## Proof Sketch (ВАЖНО! Помогает Aristotle найти путь)
By definition of continuity...
Consider any open set U...
```

**Tips:**
- Proof Sketch значительно ускоряет поиск
- Используй стандартные обозначения (Mathlib-style)
- Разбивай сложные теоремы на леммы

---

## Timing Expectations

| Сложность | Время | Пример |
|-----------|-------|--------|
| Simple lemma | 5-15 min | Арифметика, простые неравенства |
| Medium theorem | 15-60 min | Топология, линейная алгебра |
| Complex (IMO-level) | 1-8 hours | Комбинаторика, number theory |
| Very hard | 8-24 hours | Нестандартные подходы |

---

## Local Monitoring

### Запуск monitor сервера
```bash
cd /path/to/q3.lean.aristotle
export ARISTOTLE_API_KEY="your_key"
python3 monitor_server.py

# Открыть в браузере
open http://localhost:8080/monitor_local.html
```

### Monitor features
- Real-time status updates
- Progress bars
- Configurable auto-refresh (0.5-60 min)
- Download completed solutions
- View input files inline (click on project name)
- Timestamps for each update

---

## Troubleshooting

### HTTP 429 "Too Many Requests"
У тебя уже 5 активных проектов. Дождись завершения одного.

### "API key not set"
```bash
export ARISTOTLE_API_KEY="arstl_..."
# или добавь в ~/.zshrc
```

### Solution не скачивается
Проект ещё не COMPLETE. Проверь статус.

### percent_complete > 100%
Это бывает при множественных попытках. Игнорируй, жди COMPLETE.

### Input file 404 в мониторе
Убедись что файлы в папке `input/` с правильными именами (например `01_T0_normalization.md`).

---

## Lean4 Integration

### Mathlib Version
Aristotle использует конкретную версию Mathlib:
```
f897ebcf72cd16f89ab4577d0c826cd14afaafc7
```

### Настройка проекта
```toml
# lakefile.toml
name = "my_project"
version = "0.1.0"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

[[lean_lib]]
name = "MyLib"
```

### Известные проблемы

**`open scoped Nat` конфликтует с φ:**
Aristotle иногда генерирует `open scoped Nat`, что делает φ (phi) зарезервированным символом (Euler's totient function).

**Фикс:** Закомментировать `open scoped Nat` в сгенерированном файле:
```lean
-- open scoped Nat  -- commented: conflicts with φ notation
```

---

## Links

- Website: https://harmonic.fun
- API: https://aristotle.harmonic.fun
- Paper: https://arxiv.org/abs/2510.01346
- GitHub (IMO 2025): https://github.com/harmonic-ai/IMO2025

---

## Q3 Project IDs (текущая сессия)

| Name | Project ID | Status |
|------|------------|--------|
| 01_T0_normalization | 98c4ed76-fce8-4e58-b3ca-46f8c6d3f6e6 | COMPLETE |
| 02_A1prime_local_density | 098c51d6-908e-4a65-a15a-65e9060e6358 | IN_PROGRESS |
| 03_A2_lipschitz | 8337e17d-d2ca-4231-adb9-929e45e3fc8f | COMPLETE |
| 04_A3_toeplitz_main | f62e1767-5adb-4d52-99cc-58831c8201c6 | IN_PROGRESS |
| 05_RKHS_prime_cap | 34be4dc5-7272-42a8-9be8-59f4be0d90f8 | IN_PROGRESS |
| 06_T5_transfer | f3991944-86d5-4667-93d4-d7d19dc15dab | IN_PROGRESS |
| 07_Main_closure | 6e8bdd2f-2503-471e-a132-b81a36a31b1f | COMPLETE |
