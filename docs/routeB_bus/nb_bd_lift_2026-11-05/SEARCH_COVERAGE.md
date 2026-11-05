# Поиск NB–BD: охват и provenance

Дата: 2026-11-05. Репозиторий `Malaeu/chen_q3`. Поиск завершён по перечисленным ниже неподвижным снимкам; при доставке новых изменений эти снимки не переименовываются в «latest».

## Полный список веток и дополнительных snapshots

`git ls-remote --heads` обнаружил 12 веток; все 12 fetched через `refs/heads/*:refs/remotes/origin/*`. Это все remote heads на момент наблюдения, не выборка. Символический `origin/HEAD` не считался второй веткой. Два дополнительных снимка — task base и заданный inbox pin.

| Ветка / snapshot | Commit |
|---|---|
| `refs/remotes/origin/claude/greeting-a95gzh` | `83d3cc95594e9c9847be987beb1a72ec6b0bebbd` |
| `refs/remotes/origin/claude/phase-2b-n480-aitken-jlic1a` | `57f316c8f82c38e1db1b35f465e5a423b1c1be6e` |
| `refs/remotes/origin/claude/ricci-flows-proof-search-emucjh` | `bdaadcf2c650d100c15a29d02451f6884f4df712` |
| `refs/remotes/origin/codex_linux_app/goal058-curvature-second-jet` | `e6fdf040432b2eb91ecae862700787eb8dcfb342` |
| `refs/remotes/origin/codex_mac/anchored-contraction-20260914` | `e6b9b3d30fe378ed51311129e2afe02716ba2ba5` |
| `refs/remotes/origin/codex_mac/gamma-reciprocity-20260914` | `39a4d553ac48ee149cd5c8a8fcffa919f5951c28` |
| `refs/remotes/origin/codex_mac/math-proshka-20260912` | `3ac8c4eb7e3cf4ca86ec4fed2b0d73495b0fbe7d` |
| `refs/remotes/origin/main` | `388b1936f18be460df063ad3265f8fb48b4fac81` |
| `refs/remotes/origin/projekt_2` | `e899c62fcb4d1115b28e18810f4bd0bc7a244db2` |
| `refs/remotes/origin/proshka_inbox_2026-10-31` | `f862994a32a7cf8e5ddf5aee1e1e656b3fd6b1c4` |
| `refs/remotes/origin/rh_clean` | `967a2315e1f06e2815d5ac1244fb1d1dad5bc7c0` |
| `refs/remotes/origin/upgrade/lean-4.28-pilot` | `5f978caa4439dfaff746bf6e5b015eaee4571d1e` |
| `task-base` | `198c68e645f9b14591ee658712325f2410d49af1` |
| `inbox-task-pin` | `3d3ba2e60785408063c9aee70657ee0a0cf0e1dc` |

## Обычные текстовые blobs

Поиск выполнен потоковым `rg --pcre2` по Unicode NFC тексту; номера строк считаются после `splitlines()` исходного текста.

Проверено 135308 пар «путь / снимок», 14869 уникальных Git blobs. Все недостающие text blobs были fetched перед чтением через `git cat-file --batch`; ошибок чтения в завершённом проходе нет. Найдено 496 matching blobs, 3790 строк «путь / снимок» в [TEXT_HITS.tsv](TEXT_HITS.tsv). Каждая строка содержит branch/snapshot, полный commit, path, полный blob и все matching line numbers. Один blob читался один раз, затем результат развёрнут на **все** его пути/ветки.

Перечень расширений: `.md .txt .tex .bib .lean .py .json .yaml .yml .rst .html .csv .tsv .sh .toml .log`; также extensionless `README TASK NEXT GOAL`. Включены `docs`, `q3.lean.aristotle`, `full`, `archive`, `paper`, `sandboxes` и прочие деревья — без path-фильтра по текущей ветке. Это поиск содержимого, а не совпадений в имени файла.

Искомые выражения (case-insensitive, Unicode NFC для поиска):

```text
Nyman | Beurling | B[aá]ez | Burnol | Bettin | Н[аеию]й?ман | Б[еёэ]рлинг | Ба[эе]з | Бюрнол
\bd_\{?N\}? | NB[-–— ]BD | fractional\s+part
ρ_θ | rho_?theta | transfer[ -]node | узл\w*\s+перенос | \{[θϑ]\/x\}
```

Индекс намеренно широкий: `Beurling` может означать Beurling–Selberg или generalized primes, `d_N` — чужую величину, а случайные буквенные совпадения встречаются внутри embedded base64. Наличие строки в TSV не объявляет файл источником NB-теоремы. Такие ложные друзья не удалены из списка совпадений; математически использованные источники отделены в основном отчёте. В частности, поздняя формулировка задачи с памятью о «4/3» не считается независимым подтверждением этой памяти.

## Контейнеры и старые Q3-деревья

Проверено 40 уникальных ZIP/SQLite blobs (310 пар «контейнер / снимок»), все со статусом `SCANNED`: [CONTAINER_COVERAGE.tsv](CONTAINER_COVERAGE.tsv). Это все ZIP в путях `chats_prowka`, старых `*/docs/*`, bootstrap ZIP, а также все варианты `knowledge.db` в перечисленных snapshots. Численные matrix ZIP вне doc trees не использовались как корпус исторических чатов.

Для ZIP читались члены с расширениями `.md .txt .json .html .tex .bib .rst .csv .tsv`. Для SQLite — содержимое строк обычных таблиц, без FTS shadow tables. Поиск использовал имена Nyman/Beurling/Báez/Baez/Burnol/Bettin, Cyrillic варианты, `d_N`, fractional part, rho_theta, transfer node и NB-Schur. Исключений или LFS-pointer вместо контейнера в этом проходе не было.

[CONTAINER_HITS.tsv](CONTAINER_HITS.tsv) содержит 2291 строк: branch/snapshot + commit + container path + **container Git blob**, затем имя члена, его SHA-256 и линии; для SQLite — table/row locator и `source_file`, когда он записан в строке. `-` означает неприменимое/отсутствующее поле (например member hash у SQLite-строки). Member SHA-256 вычислен по исходным bytes до Unicode normalization. SQLite locator не притворяется отдельным Git blob; при повторяющемся первом поле таблицы контейнерный pin остаётся определяющим, а `source_file` помогает различать записи.

Исходный четырёхобъектный аудит найден в `docs/chats_prowka/RH_März_2026.zip`:

- container blob `2852202754e7fb5f7b48585fbbc548b3dd7de7a4`;
- member `2026-4-30 16-48-50-Goblin_Mode_Unleashed.md`;
- member SHA-256 `e28fb233381692f41f7809ba6255b873ce04ad89d3db59ae49622fa60dbc92cd`.

Восстановление нужного исходника из immutable snapshot:

```bash
git show '198c68e645f9b14591ee658712325f2410d49af1:docs/chats_prowka/RH_März_2026.zip' > /tmp/nb_source.zip
python3 - <<'PY'
from zipfile import ZipFile
from hashlib import sha256
with ZipFile('/tmp/nb_source.zip') as z:
    raw = z.read('2026-4-30 16-48-50-Goblin_Mode_Unleashed.md')
assert sha256(raw).hexdigest() == 'e28fb233381692f41f7809ba6255b873ce04ad89d3db59ae49622fa60dbc92cd'
lines = raw.decode('utf-8').splitlines()
print('\n'.join(lines[11989:12044]))
PY
```

[ORIGINAL_EXCERPTS.txt](ORIGINAL_EXCERPTS.txt) содержит четыре дословных диапазона из этого члена; заголовки `ARCHIVE MEMBER LINES ...` добавлены для навигации. Переводы строк вывода — LF. Это фрагменты, не новый самостоятельный первоисточник.

## Дополнительная разведка и пределы

- До широкого blob-прохода выполнен `rg` по доступным файлам docs; GitHub search использовался как предварительный локатор. Его default-branch индекс не подменял all-branch проход.
- Просмотрены commit messages по Nyman/Beurling/Báez/Burnol/transfer; история выбранного Q3 insight показала введение краткой записи 01.05 в `53624c45876fd18371c8de1c89b1e35f5d01fe26`. История контейнера на rh_clean ведёт к `4a908bbe26da0267075ff50121c4c79284e02491`. Это дополнительные locator checks, не полный content-scan каждого исторического commit.
- Отдельный `rh_lean_01_2026` не обнаружен в доступных `/workspace`, `/home/agent`, `/tmp`, `/opt`; Mac checkout из NEXT.md здесь не смонтирован. Исходник всё же найден в доступном chen_q3.
- В доступном через connector `Malaeu/RH_2025` выполнены дополнительные default-branch GitHub searches `Nyman`, `Baez`, `Burnol`: все без результатов. Это индексный negative search, не доказательство отсутствия текста во всей истории того репозитория.
- Проход не OCR-ил изображения/PDF, не сканировал все binary payloads и не заявляет проверку внешних дисков, недоступных локальных репозиториев, удалённых веток вне remote heads или каждого прошлого commit. Литература NB сверялась с тремя заданными локальными извлечёнными `.txt`, а не с выдуманным содержимым PDF.

## Проверки доставки

Проверены task blob, pins A/B и литературных `.txt`; SHA-256 source member, дословность quoted blocks и исходных line ranges; immutable branch/commit/blob provenance в TSV. Независимый bounded PAPER review основного отчёта не нашёл существенных ошибок. Проверка индекса: все строки TSV выводятся из прочитанного blob/контейнера на указанном snapshot; одинаковые blobs не объединены ценой потери branch/path provenance. `git diff --check` выполнен перед коммитом. Lean/build не запускались: изменены только отчёт и поисковые приложения, без Lean-кода, verdicts и route-state.
