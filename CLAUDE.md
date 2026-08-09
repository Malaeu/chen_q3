# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.
Read it completely, then enter through `SESSION_ENTRY.md`.
Review questions accumulate in `docs/routeB_bus/PROSHKA_QUEUE.md`.
Before external search or object creation, run `./ask.sh <term>`.

## Карта проекта — читать при входе

```
docs/Progress_Log.md             развилки: что происходило и ПОЧЕМУ
docs/GENEALOGY.md                откуда взялась каждая линия (A / PSD / Route B)
docs/cartographer/TOOLS.yaml     реестр инструментов: включено / снято / сломано
docs/RECORDING_RULES.md          как писать: 4 правила, 8 граф записи
docs/GLOSSARY.md                 словарь обозначений для не-математика
docs/cartographer/brief.py       состояние графа из базы   (python3)
docs/cartographer/cheap.py       очередь незакрытых шагов по цене
```

Правило реестра: инструмент без записи в `TOOLS.yaml` считается несуществующим.
Правило записи: развилку писать в момент выбора, не постфактум.

This file is a thin pointer and contains no independent executor policy.
