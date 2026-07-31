# KNOWLEDGE SPINE — единый механизм памяти проекта

Date: 2026-07-31 · Owner zone: conductor (`orchestrator/`) · Status: v1, live

Задача: у проекта ≥13 поверхностей памяти (kills, стратегии, инсайты, трюки,
работа над ошибками), но они разрознены, частично протухли и не читаются перед
прыжком. Spine НЕ переписывает источники (зоны записи неприкосновенны) —
он агрегирует их adapter-паттерном (ScientistOne, §5: unify artifacts, then
audit) в один генерируемый вид.

## Механизм

```
sources (canonical, чужие зоны)          adapter (моя зона)         readers
─────────────────────────────────        ──────────────────         ───────
FAILURE_ATLAS.json      (object kills) ┐
FAILED_STRATEGIES.yaml  (strategy)     │
bus verdicts: M3 iteration blocks      ├─→ orchestrator/spine.py ─→ orchestrator/state/SPINE_VIEW.md
ERRORS_DESTROYER.md     (process)      │        (read-only)             ↑ читается Mythos'ом перед
RH_TRICK_ATLAS.md       (K9 arsenal)   │                                  JUMP-ROUND (K10 SENSE LEDGER)
INSIGHTS.md             (решения)      │                                ↑ включается в goal-преамбулы
COGNITIVE_GOVERNOR.md   (staleness) ───┘                                ↑ читается Прошкой при аудите
```

- `spine.py` запускается кондуктором **после каждого закрытого гола / вердикта**
  (тот же момент, что пересборка зеркала) и на session start.
- `SPINE_VIEW.md` — не источник истины, а взгляд. Править только источники.
- Staleness warnings в шапке — это сигналы на обслуживание, не декорация:
  просроченный governor или неслитые M3-блоки = разомкнутая петля памяти.

## Роли и обязанности записи (без изменений зон)

| Слой | Канонический файл | Кто пишет | Когда |
|---|---|---|---|
| Object-kills | `ACTIVE/pipeline/FAILURE_ATLAS.json` | Codex | при route-kill с Lean-декларацией |
| Strategy-kills | `ACTIVE/FAILED_STRATEGIES.yaml` | Codex | при `EscapeLoop`/`RouteKill`; **соль из M3-блоков Прошки — переносить сюда** |
| M3 iteration blocks | вердикты на шине | Прошка | каждый вердикт (уже делает) |
| Process errors | `docs/ERRORS_DESTROYER.md` | любой + owner | после ошибки процесса |
| Trick cards (K9) | `docs/RH_TRICK_ATLAS.md` | Mythos | новый переносимый приём |
| Insights / деревья | `docs/INSIGHTS.md` | Codex/CC | по Branching Protocol |
| Aristotle failure harvest | answers на шине → M3/atlas | Codex | каждый ран, удачный или нет |

## Связь с синтезом (SYNTHESIS_JUMPS_COE_2026-07-31.md)

- SPINE_VIEW = материализация **SENSE LEDGER** (K10 draft): прыжок Mythos
  обязан якориться в зарегистрированной аномалии — теперь все аномалии в одном
  файле, а не в 13.
- Замыкание CoE-цепочки: `forbidden_future_move` из вердиктов теперь виден
  всем головам автоматически, а не тонет в истории шины.
- I1-аналог (score verification): staleness-таблица = проверка, что память
  вообще обновляется.

## Быстрый старт

```bash
python3 orchestrator/spine.py            # regenerate view
python3 orchestrator/spine.py --stdout   # print to terminal
```

## TODO (не в зоне кондуктора — требует владельца/голов)

1. Слить 3 постфактум-найденных M3-блока (038 supplier, microscope, T4a/PL2)
   в `FAILED_STRATEGIES.yaml` — задача Codex-гола, не кондуктора.
2. Регенерировать `COGNITIVE_GOVERNOR.md` под Route B PL2 (сейчас смотрит на
   PSD Step33, 36 дней давности).
3. `ERRORS_DESTROYER.md` не пополнялся с января — но классы ошибок с тех пор
   были (например, дубликат-сабмит T4a остановлен только вердиктом). Вносить.
4. Ратификация K10/K11 у Прошки (см. synthesis, §5) — тогда SENSE LEDGER
   станет обязательным входом JUMP-ROUND, а не опцией.
