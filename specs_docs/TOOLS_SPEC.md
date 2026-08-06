# TOOLS_SPEC — инструменты пайплайна: запуск, триггеры, выход

Пайплайн эволюционировал месяцами и ни разу не пересматривался целиком после августовских
изменений в промптах и правилах. Здесь собрано, что каждый инструмент делает, чем
запускается, что читает и что пишет — измерено с диска 2026-08-06 (`--help`, `argparse`,
`write_text`, `git log`), а не по документации.

Отдельно помечено, что **мертво**: инструмент может быть исправным и при этом не
запускаться месяцами — это разные вещи, и обе важны для оркестрации.

---

## 1. Кто кого вызывает

```
spine.py  ← единственная полная точка входа
├── import observability        (читает observability.db)
├── import sensors              (проверяет свежесть сенсорного пучка)
└── упоминает kb.py             (knowledge.db как durable memory host)

sensors.py refresh
├── scripts/q3_sensor_scan.py       общий быстрый скан дерева
├── scripts/build_taint_graph.py    дыры/границы импорта → observability.db
└── scripts/build_proof_graph.py    root→axiom проекция → observability.db

observability.py rebuild            ← база собирается отдельно, из схемы

kb.py                               ← независимая ветка (knowledge.db)
tools_census.py                     ← независимая (docs/TOOLS.md)
```

Ключевое: **`spine.py` наверху, но он не запускает `sensors refresh` сам.** Если пучок
сенсоров не обновлён, Spine покажет устаревшее состояние и честно об этом предупредит —
но не починит.

---

## 2. Спеки инструментов

### 2.1 Живые, входят в цикл

| Инструмент | Команды | Пишет | Когда запускать |
|---|---|---|---|
| `orchestrator/spine.py` | `--strict --reason <r> --stdout` · `--refresh` | `SPINE_VIEW.md`, `SPINE_STATE.json`, `META_CORPUS.json` | старт сессии (строго, без записи); после закрытия цели (с записью) |
| `orchestrator/observability.py` | `rebuild` · `summary` · `sources` | `observability.db` (**не в git**) | после свежего клона; перед доверием сенсорам |
| `orchestrator/sensors.py` | `refresh` · `status` · `--dry-run` | дескрипторы пучка | перед `spine --strict`, если сенсоры устарели |
| `orchestrator/kb.py` | `ask` · `search` · `show` · `list` · `add` · `census` · `excluded` · `export` · `init` · `record-exploration-close` | `knowledge.db`, `docs/KILLS.md` | **перед созданием любого объекта** (pre-flight); при записи kill/move; при закрытии exploration |
| `orchestrator/packet.py` | `build` · `ingest` · `--head` | пакеты для каналов | подготовка/приём пакета Прошки |
| `routeb_status.py` | `--check` · `--json` | ничего (read-only) | всегда, если задача про Route B |
| `orchestrator/tools_census.py` | `--markdown` | `docs/TOOLS.md` | при ревизии инструментария |
| `scripts/q3_sensor_scan.py` | — | общий скан для генераторов | внутри `sensors refresh` |
| `scripts/build_taint_graph.py` | `--json --numeric --out --sorry --sources-json --sources-out` | taint-проекция | внутри `sensors refresh` |
| `scripts/build_proof_graph.py` | `--alternatives --deps --json --out --taint` | root→axiom проекция | внутри `sensors refresh` |
| `q3.lean.aristotle/scripts/refresh_q3_docs.py` | `--no-embed --print-files` | манифест корпуса эмбеддингов | при переиндексации семантики |

### 2.2 Исправны, но не запускались месяцами

| Инструмент | Последний коммит | Что делает | Решение |
|---|---|---|---|
| `scripts/oracle_questions.py` | 2026-04-12 | журнал oracle-вопросов по адресам; пишет `INDEX.md`, `BY_ADDRESS.md`, шаблон, словарь | генерируемые им файлы правились 2026-08-05 — значит запускается, но редко |
| `q3.lean.aristotle/scripts/kb_refresh.py` | 2026-02-09 | пишет `AXIOM_REGISTRY`, `OPEN_LEMMAS`, `SESSION_STATE`, `insights/INDEX.md` | ⚠️ KB-контур ERA-1, заморожен |
| `q3.lean.aristotle/scripts/research_oracle.py` | 2026-03-07 | семантический поиск по `q3_docs` | ⚠️ был мёртв (корпус пуст); P5 заявлен переиндексированным — проверить |
| `aristotle_db/parse_lean.py` | 2026-01-29 | парсер Lean → `aristotle_proofs.db` | жив по факту (мы гоняли 2026-08-05), но сам файл не менялся |
| `orchestrator/relay.py` | 2026-07-30 | транспорт сообщений по адресам (`aristotle`/`codex`/`file`/`route`) | контур кондуктора ретайрнут |
| `orchestrator/sense.py` | 2026-07-30 | read-only детекция фазы | ⚠️ **сирота**: ноль входящих ссылок, пережил ретайр кондуктора |

---

## 3. Логика запуска — старт сессии

Безусловная последовательность (порядок из `CODEX_CONTROL`, инструменты — отсюда):

1. `AGENTS.md` → `docs/CODEX_CONTROL.md` (полностью, проверить `STATUS: ACTIVE`)
2. `SESSION_ENTRY.md` ⚠️ **последняя правка 2026-01-29** — читать как исторический
3. task-specific state (Route B / PSD / H1 — см. `ENTRY_SPEC.md` §2)
4. общий project state: `PROJECT_ORCHESTRATOR` → `IMPLEMENTATION_PLAN` ⚠️ → `PAPER_MAINLINE_TRACKER` ⚠️ → `INSIGHTS.md`
5. `orchestrator/state/SPINE_VIEW.md`
6. **строгая валидация без записи:**
   ```bash
   python3 orchestrator/spine.py --strict --reason session-start --stdout
   ```
7. `CHANNEL_RUNTIME.json`, `git branch --show-current`, `git status --short --branch`, site baton

Если сенсоры показывают stale/degraded — до доверия им:

```bash
python3 orchestrator/observability.py rebuild     # если базы нет (свежий клон)
python3 orchestrator/sensors.py refresh           # если пучок устарел
```

**На Linux любой вызов lake/lean — только через `env -u LD_LIBRARY_PATH`** (`CODEX_CONTROL` §16.3).

---

## 4. Триггеры

**Автоматических триггеров в репозитории нет.** Ни хуков, ни cron, ни CI. Всё ниже —
процедурные триггеры: условие, при котором исполнитель обязан запустить инструмент.

| Событие | Что запустить | Что записать |
|---|---|---|
| старт сессии | `spine.py --strict … --stdout`, `routeb_status.py --check` (если Route B) | ничего |
| свежий клон | `observability.py rebuild` | локальная база |
| сенсоры stale/degraded | `sensors.py refresh` → затем `spine.py` | дескрипторы + Spine |
| **рождение объекта** (Lean-файл, вход Аристотеля, goal, бриф) | `kb.py ask "<термины>"` | квитанция поиска в артефакте |
| маршрут/объект/стратегия убиты | `kb.py add --unit-type …` | строка в `knowledge.db` |
| закрытие exploration | `kb.py record-exploration-close` | запись в базе |
| закрытая цель / вердикт | `spine.py` (с записью) | `SPINE_VIEW`, `SPINE_STATE`, `META_CORPUS` |
| граница фазы | перезалить зеркала: `kb_migrate_journal.py`, `_dossiers`, `_moves` | `knowledge.db` |
| ревизия инструментария | `tools_census.py --markdown` | `docs/TOOLS.md` |
| переиндексация семантики | `refresh_q3_docs.py` | манифест корпуса |

---

## 5. Выход из сессии

Минимум, без которого следующая сессия начнётся вслепую:

1. **Состояние маршрута** — `ROUTE_B_STATE.md` / `ROUTE_B_EXECUTION_STATE.json`: что закрыто,
   какой следующий обязательный шаг, какой stop-code.
2. **Журнал** — запись в `docs/INSIGHTS.md`: датированная, с `Target:`, строкой валидации и
   **`Boundary:`** (что явно НЕ заявлено). Поле boundary — самое ценное при перечитывании.
3. **Убитое** — через `kb.py add`, не правкой атласов (они заморожены).
4. **Spine** — перегенерировать, чтобы вид соответствовал диску.
5. **Протокол сессии** — `SESSION_PROTOKOLL_<дата>.md` в рабочей папке.
6. **Память проекта** — resume-указатель с абсолютным путём к протоколу.
7. **Чистое дерево** — всё закоммичено и запушено, `git status` пуст.

---

## 6. Дыры, найденные при сборке этой спеки

1. **`spine.py` не запускает `sensors refresh`.** Верхний инструмент показывает состояние
   пучка, но не обновляет его: рассинхрон возможен и виден только по предупреждению.
2. **`observability.db` не в git** и её нет у свежего клона — сенсоры деградированы, пока
   не выполнить `rebuild`. Записано в `CODEX_CONTROL` §16.7.
3. **`sense.py` — сирота:** ноль входящих ссылок, пережил ретайр кондуктора. При этом
   реализует ровно детекцию фазы, которой сейчас не хватает картографу.
4. **Три инструмента заморожены с ERA-1** (`kb_refresh`, `research_oracle`, `relay`) и при
   этом упомянуты в порядке чтения или в правилах.
5. **`kb.py` расширен Кодексом** (`record-exploration-close`, коммит `7e319bdc`) — то есть
   инструмент стал общим для обоих тел; менять его теперь надо с оглядкой.

---

## 7. Границы

Это **спека, не политика**. Поведение исполнителя задаёт `docs/CODEX_CONTROL.md`; порядок
чтения — `specs_docs/ENTRY_SPEC.md`; здесь только инструменты и их запуск.

Таблицы дат обновляются `bash specs_docs/entry_audit.sh` (read-only).

---

# ЧАСТЬ II — операционный каталог (вынесен из кернела 2026-08-06)

`docs/CODEX_CONTROL.md` держит **политику** (обязан ли исполнитель искать перед действием).
Конкретные команды живут здесь, чтобы кернел не пух. Один источник, одна строка-ссылка там.

## 9. Шпаргалка команд

```bash
# ── ПАМЯТЬ: что уже пробовали, убили, доказали
./orchestrator/kb.py ask "<термины>"        # все слои сразу: kills · moves · journal · dossiers
./orchestrator/kb.py flags <адрес|термин>   # где уже искали: сильные / ЛОЖНЫЕ / пустые слова
./orchestrator/kb.py flags --vocab          # весь накопленный словарь поиска
./orchestrator/kb.py list --unit-type wall  # стоячие стены
./orchestrator/kb.py show <id>              # одна запись целиком
./orchestrator/kb.py add --unit-type route --subject "…" --reason "…"   # записать убитое
./orchestrator/kb.py census                 # судья: источники против базы
./orchestrator/kb.py excluded               # что НЕ мигрировано и почему

# ── СОСТОЯНИЕ
python3 orchestrator/spine.py --strict --reason session-start --stdout   # старт, без записи
./orchestrator/spine.py                                                  # с записью, после закрытия цели
python3 orchestrator/observability.py rebuild|summary|sources            # сенсорная база (локальная)
python3 orchestrator/sensors.py refresh|status                           # пучок сенсоров
python3 …/routeB_twolevel_spectral_ladder/routeb_status.py --check       # шина Route B

# ── ПОИСК ПО ТЕКСТАМ
./scripts/research_oracle.py query "<kw>" -c q3_docs     # семантика по докам
rg -n "<pattern>" Q3/ -t lean                            # точный поиск, всегда rg вместо grep

# ── ИНВЕНТАРЬ
./orchestrator/tools_census.py --markdown    # перегенерировать docs/TOOLS.md
bash specs_docs/entry_audit.sh               # свежесть точек входа (read-only)
```

**На Linux любой вызов lake/lean — только `env -u LD_LIBRARY_PATH lake …`**

## 10. Когда ЧИТАТЬ — четыре наблюдаемых повода

Формулировка «перед нетривиальной проблемой» не работает: нетривиальность субъективна.
Поводы объективные:

| Повод | Команда | Что ищем |
|---|---|---|
| открывается новый адрес или фронт | `kb.py flags <адрес>` | ходили ли здесь и с каким блокером |
| **рождается объект** — Lean-файл, вход Аристотеля, goal, бриф | `kb.py ask "<термины>"` | не существует ли уже |
| первая попытка не сработала | `kb.py flags <термины>` | ложные друзья: `global order17 constant` помечен **9 раз** |
| **перед обращением к Прошке** | `kb.py flags` + `kb.py ask` | её ответ стоит ~18 минут рассуждения и кусок месячного бюджета |

Четвёртый — самый ценный: он экономит единственный ресурс, который реально ограничен.

## 11. Когда ПИСАТЬ — врезано в существующий артефакт

**Отдельный шаг «не забудь записать» умирает.** Доказано трижды: `docs/insights` — последнее
новое досье в марте; карточки оракула 44 → 13 → 2 → 1 по месяцам; `ERRORS_DESTROYER` — одна
запись за семь месяцев, при том что правило требовало читать его перед каждым PR.

Поэтому запись идёт туда, где пишут **и так обязательно** — в шапку `answer.md` закрываемой
цели (и в блок `iteration:` вердикта Прошки):

```yaml
SEARCH_FLAGS:
  address: RouteB.G5.Mode4.RegularRow
  strong:       [термины, которые сработали]
  empty:        [дали пустоту]
  false_friend: [выглядели верными и увели]
  opens_branch: [открыли новую ветку]
```

Пустые поля — норма. Заполненный `false_friend` — то, ради чего контур существует.
Сбор в `search_session` — отдельным проходом, как `spine.py` собирает kills; исполнителю
дополнительных шагов не добавляется.

**Что записывается по другим поводам:**

| Событие | Куда |
|---|---|
| маршрут/объект/стратегия убиты | `kb.py add` — **не** правкой атласов, они заморожены |
| нетривиальная развилка | датированная запись в `INSIGHTS.md` с классом (`insight`/`synthesis`) и `Boundary:` |
| закрытие exploration | `kb.py record-exploration-close` |
| ошибка процесса | постмортем (корневая причина + правило) |

## 12. Что уже есть в базе (2026-08-06)

| Слой | Записей |
|---|---|
| kills: маршруты, объекты, стратегии, стены, критерии | 59 |
| moves: атлас + арсенал + tricks | 26 |
| journal (`INSIGHTS.md`) | 1784 |
| dossiers | 168 |
| **search_session** (карточки поиска) | **60** |
| **search_term** (размеченный словарь) | **321** над 117 узлами дерева |
| excluded_source (что не мигрировано и почему) | 113 |

Ответ за 44 мс. Пример реальной пользы: `kb.py flags PSWF` отдаёт карточку от 2026-08-05 с
источником коэффициентов **DLMF 30.8.3 / 30.8.7**, помечает `abstract recurrence row without
source eigenfunction` как пустое и `finite tridiagonal approximation alone` как ложного друга —
знание, которого не было ни у одного из трёх каналов при обсуждении `XW.0a`.
