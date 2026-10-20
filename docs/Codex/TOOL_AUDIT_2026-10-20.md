# Фактическая проверка инструментов Q3 — 20.10.2026

Scope: архивирование CF22 и возвращение к исходной CCM. Это операционный аудит,
не математическая верификация. Реестр: docs/cartographer/TOOLS.yaml.
Root выполнил сетевой smoke литературы; read-only агент archive_tools_audit
выполнил остальные проверки. Никаких установок, платных вызовов, отправок Прошке,
Lean-сборки, изменения аксиом или ремонта runtime в этом задании не было.

| Инструмент | Что реально проверено | Результат |
|---|---|---|
| ask.sh | `./ask.sh --defer-external 'CF22 PySR'`, системное и repo-venv окружения |exit2, ASK_STATUS INCOMPLETE; SEMANTIC_INDEX_CORPUS_STALE; Bash3.2: пустой LOCAL_CANDIDATE_RECORDS массив на строке514. System Python также без yaml; venv с yaml|
| kb.py | `./orchestrator/kb.py ask 'CF22 PySR'` |exit1, no hits в этом слое БД; это не отсутствие в репозитории, где файлы заведомо есть|
| supplier_preflight.py |только --help |CLI доступен; полный query/EXACT_FIT не проверен, точного Lean candidate/target в этом архиве нет|
| literature_discovery.py |одна общая metadata query к arXiv/Crossref, timeout8,max-results2 |CANDIDATES,4 записи, errors=[]; сырой JSON рядом|
| scripts/check_axioms.sh |обычный текстовый режим |exit0,3625 Q3 Lean файлов,35 текстовых sorry и72 axiom declarations; включает лексические совпадения, не kernel certificate|
| kernel axiom closure |--print-axioms для точной теоремы |не запускался; архив не меняет Lean и не заявляет новую теорему|
| phase_end.sh |прочитан полный вызываемый phase_end.py |не запущен: широкий git add -u и каталоги захватывают чужие изменения; даже --dry-run пишет статистику NEXT|

Сохранённый raw literature receipt: [TOOL_AUDIT_2026-10-20_literature.json](TOOL_AUDIT_2026-10-20_literature.json).
Запрос проверяет транспорт и метаданные, не даёт пригодного поставщика теоремы.
Фактические статусы выше не заменены оптимистическими ENABLED из реестра.

## Почему наличие автоматизации не означало выполнение

ask-shelf и supplier-preflight зарегистрированы MANUAL с определёнными триггерами.
Литература запускается при LITERATURE_DISCOVERY или из phase_end; scite/Consensus
в phase_end помечены MCP-only и автоматически самим Python-скриптом не вызываются.
X-поиск запускается только при xurl; в этом задании не запускался.
Проверка аксиом относится к Lean-изменению/допуску доказательства, не к Python-fit.
Обычный phase_end считает gates и текстовые совпадения, не проверяет истинность
нового математического выигрыша. Пропуск или nonfatal ошибка поиска не есть успех.
До архивации NEXT содержал прежние Ferrers/Fokas lit-запросы; они заменены двумя
запросами по форме Вейля/CCM и composite-shift оператору.

## Состояние восстановления и минимальные следующие действия

Архив уже доступен через README, NEXT, PAPER_CHAIN, GENEALOGY и Progress_Log;
Git и SHA-манифест сохраняют точные данные. Автоматическая семантическая индексация
этого архива НЕ подтверждена. Поиск через rg и прямые ссылки работает независимо.
Для восстановления семантической полки валидатор называет существующий вызов:
`.venv/bin/python orchestrator/spine.py --refresh --reason semantic-index-refresh`.
Он пишет производные данные; здесь не выполнялся и не исправит Bash-дефект.
Нужны отдельное узкое исправление пустого массива ask.sh, обновление индекса и
повтор того же запроса; до этого INCOMPLETE сохраняется. Не запускать полный
перестроитель ради видимости автоматизма и не считать no hits глобальным отсутствием.

Безопасное закрытие этого задания: проверить106 SHA, ссылки и diff, stage только
архивные пути и только нашу вставку Progress_Log, один commit/push и remote readback.
Чужая вставка Progress_Log, CLAUDE.md и все прежние untracked файлы сохраняются.
Это scoped замена опасного широкого staging при данном состоянии рабочего дерева,
не объявление phase_end починенным. Нет нового proof/CF22/SP/RH результата.
