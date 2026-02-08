---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: high
last_updated: 2026-02-08
---

# KB INDEX — ЧИТАЙ ЭТО ПЕРВЫМ В КАЖДОЙ СЕССИИ

Ты — Aristotle 5.3. Всегда начинай с этого файла + `KB/SESSION_STATE.md`.

Доступные разделы:
- `orchestrator.md` → как делегировать sub-агентам
- `philosophy.md` → стиль, запреты, аксиомы
- `ERRORS_DESTROYER.md` → критические ошибки, которых избегать
- `skills/` → конкретные навыки и процессы
- `maps/` → LaTeX ↔ Lean карта и список открытых лемм
- `axioms/` → реестр аксиом и план закрытия
- `playbooks/` → шаблоны для долгоживущих задач, steering, delegation
- `insights/` → свежие находки (смотри `insights/INDEX.md`)
- `SESSION_STATE.md` → текущий статус цепочки, blockers, next steps
- `search.md` → быстрый recall и команды поиска
- `playbooks/self_improvement_loop.md` → полуавтоматический цикл обновления знаний

Frontmatter в каждом `.md` (добавляй при создании/обновлении):
```
---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: high | medium | low
last_updated: YYYY-MM-DD
---
```

После каждой значимой итерации или когда я скажу "summarize learnings / update kb":
1. Запиши 5–15 строк synthesis в `KB/insights/YYYY-MM-DD_краткое_название.md`
2. Запусти `python3 q3.lean.aristotle/scripts/kb_refresh.py` (обновит `KB/insights/INDEX.md` и auto‑scan в `KB/maps/open_lemmas.md`)
3. Если база запуталась, предложи `run self-diagnosis`.

## Self-diagnosis trigger

Запускай предложение `run self-diagnosis`, если видишь хотя бы один триггер:
- дубли (например, файлы с суффиксами ` 2`, ` 3`) мешают retrieval
- больше 5 сломанных ссылок внутри `KB/`
- противоречия в `KB/SESSION_STATE.md` против факта из `Q3/CheckAxioms.lean`
- больше 150 файлов в `KB/insights/`

После команды `run self-diagnosis`:
1. Проведи структурный аудит `KB/`.
2. Выдели 3–5 самых болезненных проблем.
3. Предложи план: prune / rename / merge / move to `KB/archive/`.
