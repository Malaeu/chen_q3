# Codex Session Entry

Updated: 2026-09-06 (audit v2). Маршрутизатор. Политика — только `docs/CODEX_CONTROL.md`
(читать по разделу, когда срабатывает его гейт; `plan` проверяет контроль сам).

## Рабочий контекст

- Цель: выполнить поставленное изменение или доказать утверждение; число документов
  и закрытых пунктов целью не является.
- Чтение: текущая задача → затронутые определения → нужные зависимости. Не история проекта целиком.
- Истинность: сохранять объекты, кванторы, нормировку и гипотезы; различать доказательство,
  условный вывод и эксперимент; недоказанное не называть доказанным.
  `scripts/q3_check.sh <file>` — один локальный гейт для Lean-файла (включает `lake env lean`).
- Действия: работать самостоятельно внутри согласованной области; отдельное разрешение — только
  на расширение области, платные вызовы, публикацию, разрушительные операции и смену политики.

## Старт — одна команда

```bash
python3 orchestrator/workflow_runtime.py plan
```

Она читает control, Git/worktree, physical bus, `docs/Codex/CURRENT.md`,
runtime state и `NODE_REGISTRY_V10.json` в одном read epoch, ничего не пишет и
никого не вызывает. `specs_docs/session_start.sh` — ручная диагностика, не
второй старт.

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
Проектных skill-каталогов нет (архив: `archive/skills_gpt5_era_2026-09-06/`).
