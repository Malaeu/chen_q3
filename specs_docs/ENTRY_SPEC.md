# ENTRY_SPEC — что читается при старте сессии и чем это пишется

Одна карта входов вместо реконструкции по памяти каждый раз. Собрано 2026-08-06 машинной
проверкой (`git log` по каждому файлу), а не по документации — поэтому колонка «последняя
правка» отражает факт, а не намерение.

Адресат: владелец и Linux-тело. Это **навигация, не политика**: поведение исполнителя задаёт
`docs/CODEX_CONTROL.md`, здесь только карта того, что он читает и что чем обновляется.

---

## 1. Безусловный порядок старта

| # | Файл | Последняя правка | Кто пишет | Тип | Состояние |
|---|---|---|---|---|---|
| 1 | `AGENTS.md` | 2026-08-06 | Codex | ручной | тонкий указатель на (2) |
| 2 | `docs/CODEX_CONTROL.md` | 2026-08-06 | оба | ручной | **живой**, канонический кернел |
| 3 | `SESSION_ENTRY.md` | **2026-07-10** | Codex | ручной | ⚠️ протух на 27 дней, 34 КБ — см. ниже |
| 4 | task-specific state | см. §2 | Codex | — | зависит от ветки |
| 5.1 | `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` | 2026-07-10 | Codex | ручной | подстыл |
| 5.2 | `IMPLEMENTATION_PLAN.md` | **2026-04-27** | — | ручной | ⚠️ мёртв |
| 5.3 | `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md` | **2026-03-15** | — | ручной | ⚠️ мёртв |
| 5.4 | `q3.lean.aristotle/docs/INSIGHTS.md` | 2026-08-06 | Codex | ручной | **живой**, 170 правок/30 дней |
| 6 | `orchestrator/state/SPINE_VIEW.md` | 2026-08-06 | `spine.py` | **генерируется** | живой |
| 7 | `python3 orchestrator/spine.py --strict --reason session-start --stdout` | — | — | проверка | без записи |
| 8 | `orchestrator/state/CHANNEL_RUNTIME.json` + `git branch` / `git status` | 2026-08-06 | Codex | ручной | живой |

> **Поправка 2026-08-06.** Строка 3 раньше читалась «2026-01-29, мёртв 6 месяцев». Это была
> дата **симлинка** `SESSION_ENTRY.md` → `q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
> (единственный коммит симлинка, `9034a86d`). Настоящий файл правился **2026-07-10 `99acf3ff`**,
> тем же коммитом, что и `PROJECT_ORCHESTRATOR.md`. Не мёртв — протух и врёт по содержанию:
> 21 macOS-путь, два противоречащих «текущих фронтира», указатель на замороженную шину.
> Полный разбор: `specs_docs/SESSION_START_AUDIT_2026-08-06.md` §1.3.

## 2. Условные ветки

**Route B** — читать до generic-мониторов:

| Файл | Последняя правка | Активность |
|---|---|---|
| `…/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json` | 2026-08-05 | 57 правок/30 дней |
| `…/ROUTE_B_EXECUTION_CONTROL.md` | 2026-08-04 | 5 |
| `…/ROUTE_B_STATE.md` | 2026-08-06 | 31 |
| `…/bus/BUS_PROTOCOL.md` | 2026-07-12 | 5 |
| физическая папка `…/bus/` | — | шина решает, что исполнимо |
| `routeb_status.py --check` | — | нет открытой цели → `NO_OPEN_BUS_GOAL / STOP` |

**PSD/Step33** — ⚠️ вся ветка заморожена с июня: `PSD_STEP33_MONITOR.md` (2026-06-25),
`step33_bootstrap/node.md` (06-24), `report.md` (06-25). Монитор при этом всё ещё
самообъявляется `ACTIVE`. Отдельно проверено 2026-08-05: 143 072 строки корпуса, **ноль**
пересечений с живыми фронтами.

**H1/PO3/H-bridge** — `ACTIVE/PHASE_MONITOR.md` (2026-08-06, живой), но статус
`PARKED_CLOSED`, работой не управляет.

**Generic sprint** — `ACTIVE/SPRINT_MONITOR.md` (2026-08-06), статус `DONE_CLOSED`.

**Cognitive (stalled loop / route review)** — `COGNITIVE_KERNEL.md` и `COGNITIVE_OPERATORS.md`
⚠️ мертвы с 2026-06-25; `ACTIVE/COGNITIVE_GOVERNOR.md` — 2026-07-31.

**Embeddings** — `docs/EMBEDDING_INGEST_WORKFLOW.md` ⚠️ 2026-03-08.

**Oracle** — `ACTIVE/pipeline/RESEARCH_ORACLE.md` ⚠️ 2026-04-12; но
`oracle_questions/INDEX.md` и `BY_ADDRESS.md` (2026-08-05) **генерируются**.

**Aristotle** — `ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md` ⚠️ 2026-04-11,
`aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md` ⚠️ 2026-03-07.

---

## 3. Триггеры записи — главный ответ

**Автоматически пишутся ровно пять файлов:**

| Файл | Генератор | Чем триггерится |
|---|---|---|
| `orchestrator/state/SPINE_VIEW.md` | `orchestrator/spine.py` | запуск вручную |
| `orchestrator/state/SPINE_STATE.json` | `orchestrator/spine.py` | запуск вручную |
| `orchestrator/state/META_CORPUS.json` | `orchestrator/spine.py` | запуск вручную |
| `…/oracle_questions/INDEX.md` + `BY_ADDRESS.md` | `q3.lean.aristotle/scripts/oracle_questions.py` | запуск вручную |
| `q3.lean.aristotle/docs/insights/INDEX.md` | `q3.lean.aristotle/scripts/kb_refresh.py` | запуск вручную |

**Всё остальное пишется руками.** В репозитории нет ни хуков, ни cron, ни CI — проверено
2026-08-05: `.claude/` содержит только `skills/`, `settings.json` отсутствует.

**Важное недоразумение:** `q3.lean.aristotle/scripts/refresh_q3_docs.py` упоминает
`SESSION_ENTRY.md` и `IMPLEMENTATION_PLAN.md`, но **не пишет их** — он их читает, чтобы
скормить эмбеддингам. Эти доки для него вход, а не выход.

**Базы данных:**

| База | Пишется | В git |
|---|---|---|
| `aristotle_db/aristotle_proofs.db` | `aristotle_db/parse_lean.py`, `orchestrator/backfill_db.py` | да |
| `aristotle_db/knowledge.db` | `orchestrator/kb.py`, `kb_migrate_*.py` | да |
| `aristotle_db/observability.db` | `orchestrator/observability.py rebuild` | **нет**, локальная |

---

## 4. Что из этого следует

**Из 27 документов порядка чтения одиннадцать не менялись месяцами.** Читаются обязательно,
не пишутся никогда — та же болезнь, что была у атласов, но на уровне точек входа.

Самый острый случай — **`SESSION_ENTRY.md`**: третий пункт обязательного старта, 34 КБ,
последняя правка 29 января. Каждая сессия начинается с чтения январского состояния проекта,
и авторитет позиции в списке заставляет верить ему больше, чем он заслуживает.

Ни одно из этих замечаний не означает «удалить». Означает: **пометить дату и читать как
исторический документ, а не как текущее состояние**.

---

## 5. Как обновить эту таблицу

```bash
bash specs_docs/entry_audit.sh          # печатает свежую таблицу дат и активности
```

Скрипт read-only, ничего не переписывает. После прогона колонки «последняя правка» и
«активность» в §1–2 обновляются вручную — или, если это станет частым, вносится в `spine.py`
как ещё один генерируемый раздел.

**Правило единственного писателя (`CODEX_CONTROL` §18) действует и здесь:** пока write-lock у
Кодекса, Linux-тело приносит текст, а применяет его он.
