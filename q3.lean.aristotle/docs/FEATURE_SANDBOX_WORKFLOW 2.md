# Feature Sandbox Workflow

**Дата создания**: 2026-01-16
**Статус**: Production-ready
**Skill**: `/x-sandbox`

---

## Философия

> "Эта структура освобождает мои мысли. Мне не нужно думать, что я что-то запортачу."

Полная изоляция через clone **внутри** chen_q3. Каждый sandbox:
- Имеет свой git, свой lake cache
- Содержит `TASK.md` с описанием задачи
- Можно удалить без последствий

---

## Архитектура

```
chen_q3/
├── sandboxes/              ← ВСЕ sandbox'ы тут (в .gitignore)
│   ├── arch_prime/
│   │   ├── full/           ← clone с КОПИРОВАННЫМ .lake (быстро!)
│   │   ├── .venv → ../../../.venv  ← symlink на главный venv
│   │   └── TASK.md         ← что делать агенту
│   ├── carleson/
│   └── P_A_cont/
├── full/
│   └── q3.lean.aristotle/
│       └── .lake/          ← исходный кэш (копируем в sandbox'ы)
├── .venv/                  ← главный venv (symlink'ится)
└── .gitignore              ← содержит "sandboxes/"
```

---

## Команды

| Command | Description |
|---------|-------------|
| `/x-sandbox create <name> "<desc>"` | Создать sandbox с TASK.md |
| `/x-sandbox list` | Показать все sandbox'ы |
| `/x-sandbox delete <name>` | Удалить sandbox |
| `/x-sandbox merge <name>` | Merge sandbox в main |
| `/x-sandbox-work` | Начать работу (автоматом читает TASK.md) |

---

## Workflow

### Phase 1: Создание Sandbox (~30 сек вместо ~5 мин)

```bash
cd ~/Documents/GitHub/chen_q3
/x-sandbox create arch_prime "Prove arch >= prime via localization"
```

Скрипт:
1. Клонирует с `--local` (hardlinks, быстро)
2. **КОПИРУЕТ .lake/** вместо rebuild (~10 сек вместо ~5 мин)
3. **Symlink'ит .venv/** (мгновенно)
4. Создаёт TASK.md с описанием

### Phase 2: Запуск Агента

В **НОВОМ терминале**:

```bash
cd ~/Documents/GitHub/chen_q3/sandboxes/arch_prime
claude "/x-sandbox-work"
```

Агент:
1. Читает TASK.md автоматически
2. Работает над задачей
3. Коммитит когда готово

### Phase 3: Merge (если успех)

```bash
cd ~/Documents/GitHub/chen_q3
/x-sandbox merge arch_prime
/x-sandbox delete arch_prime
```

### Phase 4: Abort (если фейл)

```bash
/x-sandbox delete arch_prime
# Main остался чистым
```

---

## Оптимизации

| Что | Старый способ | Новый способ | Экономия |
|-----|---------------|--------------|----------|
| Lake cache | `lake build` (~5 мин) | `cp -r .lake/` (~10 сек) | **~5 мин** |
| Venv | новый (~1 мин) | symlink (~1 сек) | **~1 мин** |
| Git | `git clone` | `git clone --local` | **~50%** |

**Создание sandbox: ~30 секунд вместо ~6 минут**

---

## TASK.md

Каждый sandbox имеет TASK.md в корне:

```markdown
# Sandbox Task: arch_prime

**Created:** 2026-01-16T22:30:00Z
**Branch:** sandbox/arch_prime
**Status:** IN PROGRESS

## Task Description

Prove arch_term >= prime_term via localization

## Aristotle Reference

2026-01-16 arch_ge_prime_rigorous_v1.md 4b483ef3-eb90-4317-a690-b55981a0b73e

## Success Criteria

- [ ] Task completed
- [ ] `lake build Q3.Main` passes
- [ ] Changes committed
```

Агент при `/x-sandbox-work` читает этот файл и знает что делать.

---

## Текущие задачи для sandbox'ов

| Task | Aristotle UUID | Description |
|------|----------------|-------------|
| `P_A_cont` | b2145057 | Prove P_A_continuous via tsum lemmas |
| `arch_prime` | 4b483ef3 | Prove arch >= prime via localization |
| `carleson` | 427880cd | Prove prime sampling is Carleson |
| `measure_dom` | d7bf9689 | Prove measure domination bound |

---

## См. также

- `PROJECT_ORCHESTRATOR.md` — какие axiom'ы закрывать
- `PHILOSOPHY_OF_PROOF.md` — что такое axiom closure
- `/x-sandbox` — skill documentation
