# Codex Session Entry

Updated: 2026-09-11 (Team Runtime v1). Маршрутизатор. Политика — только `docs/CODEX_CONTROL.md`
(читать по разделу, когда срабатывает его гейт; `plan` проверяет контроль сам).

## Рабочий контекст

- Цель: выполнить поставленное изменение или доказать утверждение; число документов
  и закрытых пунктов целью не является.
- Чтение: текущая задача → затронутые определения → нужные зависимости. Не история проекта целиком.
- Истинность: сохранять объекты, кванторы, нормировку и гипотезы; различать доказательство,
  условный вывод и эксперимент; недоказанное не называть доказанным.
  `scripts/q3_check.sh <file>` — один локальный гейт для Lean-файла (включает `lake env lean`).
- Действия: работать самостоятельно внутри согласованной области и полномочий
  `docs/Codex/GOAL.md` §1. Именованные коммиты, обычный push и проектные запросы Прошке
  разрешены для продолжающейся задачи; остальные границы `CODEX_CONTROL.md` сохраняются.
- Team Runtime v1: `gpt-5.6-luna/max` — изолированные исполнители,
  `gpt-5.6-terra/medium` — зарезервированный независимый проверяющий; не более
  трёх активных детей единственного оркестратора после активации, без descendants.
  Запрошенный профиль `gpt-6-astra/max` описывает оркестраторский запрос и не
  доказывает смену реально работающей родительской модели. Objective/delegation
  assignment остаются bounded по runtime contract.

## Старт — одна команда

```bash
python3 orchestrator/workflow_runtime.py plan
```

Она читает control, Git/worktree, physical bus, `docs/Codex/CURRENT.md`,
runtime state, `NODE_REGISTRY_V10.json` и bounded continuation/ownership
observations в одном read epoch, ничего не пишет и никого не вызывает. Это
единственный programmatic entry; отдельная ручная цепочка bootstrap/history не
нужна. `specs_docs/session_start.sh` — ручная диагностика прежнего контура, не
второй старт.

После сжатия контекста, перезапуска или простоя выполнить этот `plan` первым.
`GOAL` и текущий `q3_resume.v2` читаются напрямую только если operating card
указывает на нужное содержание; архивные `q3_resume.v1` bytes служат только
историческим восстановлением. Сверить текущие исходники, запрос, фазу и
владельца исполнения по plan card; полный `git status --short` нужен только
при omitted/UNKNOWN ownership. Продолжать первый
незавершённый шаг, указанный card; §5 GOAL остаётся рабочим указателем. RESUME —
наблюдения, не выбор задачи и не полномочия. После pull новый host observer-only,
пока release/claim, local watch readback и ACTIVE handoff не проверены. При
несогласованности сверить факты, сохраняя чужие изменения; не начинать новую
цель, чат или повторную отправку.
`docs/Codex/GOAL_HISTORY.md` читать только по необходимости как историю:
вложенные команды недействующие. Вахта «Q3 — продолжение работы» сохраняется
на весь цикл, даже при пустом списке агентов (GOAL §3).

## Что сказать владельцу первым (battle brief)

live goal и verified frontier · exact `node + theorem + consumer` · один
настоящий blocker · own/foreign dirty split · следующий разрешённый action.
`FATAL` останавливает; `HOLD` — адресный недостающий контракт, его не красить
зелёным.

## Неподвижная граница

`CHALLENGER_NOT_RH`, `PX_RH_CLAIM: NOT_MADE`; единственная owner-only граница —
`PX_RH_CLAIM` (`CODEX_CONTROL.md` §1). Kernel-green ≠ admission (§5).

## Куда смотреть по триггеру

| триггер | раздел / файл |
|---|---|
| сохранение/восстановление продолжения | `docs/Codex/GOAL.md` §4; зарегистрированный `resume-checkpoint` пишет только RESUME и историю |
| Team Runtime identity / remote / watch / native effect | `team-local-init`, `team-observe-remote --operation-id`, `team-reserve-effect --operation-id`, `team-watch-intent --action CREATE\|UPDATE\|PAUSE --transfer-id --target-thread`, `team-observe-native --candidate --expected-sha256`, `team-confirm-effect --operation-id --candidate --expected-sha256` |
| report / classification / assignment / archive | `team-record --kind report\|issue-event\|assignment\|archive --candidate --expected-sha256`; exact payload schema is owned by the runtime, not this router |
| isolated evidence / reviewed candidate integration | `team-integrate-candidate --candidate <manifest>` from the committed verification checkout with `--root <canonical>`; an interrupted copy resumes with `--recover-operation <id>` from the same pinned engine (control §10–11) |
| выбор goal, `CURRENT.md`, `NEXT_GOAL_SPEC` | `CODEX_CONTROL.md` §2 |
| proof loop, `ask.sh`, `supplier_preflight.py`, `EXACT_FIT` | §3–4; `docs/cartographer/TOOLS.yaml` (только выбранное семейство) |
| HELPER / SEMANTIC_BRIDGE / ROOF_CHANGE, reviews | §5–6 |
| батч судье, phase key, `.txt`-attachment, `review-plan` | §8; `docs/routeB_bus/PROSHKA_QUEUE.md`; `orchestrator/bind_request.py` |
| stall, bounded exploration | §9; `q3.lean.aristotle/COGNITIVE_OPERATORS.md` |
| закрытие узла, commit, push | §10–11: `workflow_runtime.py run --through close-node …`, затем `plan` заново |
| развилка / возврат | `docs/GENEALOGY.md`, `docs/Progress_Log.md`, `docs/RECORDING_RULES.md` |
| Aristotle | `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md` |
| аномалия control/tool/db | `docs/SYSTEM_SPEC_2026-08-05.md`, `specs_docs/README.md` |

Спящие мониторы (`PSD_STEP33`, `PHASE`, `SPRINT`) ничего не выбирают.
Зарегистрированный поиск того же объекта под другими именами: `alias-hunt`,
`.agents/skills/alias-hunt/SKILL.md`. Это ограниченный поиск после сверки владельца,
источников и полки; получение кандидата не означает принятие доказательства.
Старые skill-каталоги остаются историей: `archive/skills_gpt5_era_2026-09-06/`.
Timestamp, remote/network observation и наличие настройки watch сами по себе не
доказывают native wake/effect; нужен provider receipt, readback и наблюдаемый
результат. Старая ручная bootstrap-процедура остаётся historical compatibility,
а не вторым входом.
