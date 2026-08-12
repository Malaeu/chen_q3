# Lean environment index

`envdump.py` строит gitignored derived-индекс elaborated Lean-деклараций из уже
собранных RouteB `.olean`; `atom_describe.py` читает этот индекс только на чтение и
для RouteB заменяет исходную текстовую сигнатуру полным elaborated-типом.

## Knowledge preflight

Перед исправлением выполнен:

```text
./ask.sh "EnvDump atom_describe env_index import collision sourceArchimedeanSesquilinearForm"
```

Receipt: найден канонический `Q3.RouteB.D0Pstar.sourceArchimedeanSesquilinearForm`
в `D0PstarArchSesquilinearFormIntegral.lean`; отдельного готового EnvDump→describer
переходника в индексах нет.

## Запуск

```bash
python3 docs/cartographer/lean_env/envdump.py
python3 docs/cartographer/atom_describe.py --chain REALZERO_GROUND_DIAGONAL_TO_XI \
  --json docs/cartographer/route058_objects.json
python3 -m unittest docs/cartographer/lean_env/test_env_wiring.py
```

Build-кэш может содержать `.olean` удалённых файлов. Такие сироты не принадлежат
текущему дереву и никогда не импортируются. Это устраняет воспроизведённый collision:
удалённый `D0PstarShiftedArchSesquilinearFormScratch.olean` устанавливал то же имя,
что канонический `D0PstarArchSesquilinearFormIntegral.lean`.

Оба конца fail closed. `envdump.py` публикует индекс атомарно только после exit 0,
непустого и структурно корректного JSONL. `atom_describe.py` загружает индекс лениво:
Mathlib-only и foreign-only запрос от него не зависит, но первая RouteB-декларация делает
его обязательным. Для RouteB инструмент не публикует `--json`,
если индекс отсутствует/повреждён, модуль не совпадает, исходник новее индекса или
RouteB-декларация отсутствует в собранном окружении. Исходный текст при таком отказе
остаётся только явно маркированной диагностикой, а не заменой elaborated-типа.

Индекс не судит применимость и не пишет в канонические данные. Непокрытые исходники
остаются честно непокрытыми до их явной сборки.

## Проверенный прогон 2026-08-12

Declared invocation `python3 docs/cartographer/lean_env/envdump.py` завершился с
кодом `0` и атомарно опубликовал gitignored `env_index.jsonl`: 1139 уникальных
деклараций из 154 актуальных source-backed модулей, `sorryAx = 0`, прочих аксиом
вне стандартного списка `= 0`. Из denominator coverage исключены и названы 6
orphan `.olean`, 30 stale `.olean`; ещё 21 исходный модуль не был собран.

Реальный smoke-test получил `Q3.RouteB.ccmModeFinite` из environment с точным
module identity и elaborated-типом. Полная цепь
`REALZERO_GROUND_DIAGONAL_TO_XI` честно завершилась с кодом `1`: десять её
деклараций лежат в stale-excluded модулях, поэтому запрошенный JSON не был
опубликован. Это граница покрытия текущего build cache, а не ошибка подменённая
текстовой сигнатурой.
