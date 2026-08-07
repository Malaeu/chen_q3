#!/usr/bin/env bash
# q3-toolbelt.sh — SessionStart hook для репозитория chen_q3_rh_clean.
#
# Зачем. В контекст без действия попадают ровно три вещи: CLAUDE.md, память проекта и вывод
# SessionStart-хуков. Всё остальное — карта, спеки, база, литобзор — надо пойти и взять,
# а «не забудь пойти» умирает: 6–7 августа трижды подряд инструмент существовал, знание
# лежало внутри, никто не посмотрел. Этот хук кладёт пояс с инструментами прямо в контекст.
#
# Быстрый по построению: никаких lake/spine/сборок, только дешёвые запросы. Цель — < 2 с.

REPO="/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean"

# Молчать вне Q3.  Хук стоит в глобальном settings.json, поэтому запускается на старте
# ЛЮБОЙ сессии; печатать пояс Q3 в чужом проекте — мусор в чужом контексте.
# Проверять существование каталога недостаточно: он существует всегда.
case "$PWD/" in
  "$REPO"/*) ;;
  *) exit 0 ;;
esac
cd "$REPO" || exit 0

KB="q3.lean.aristotle/aristotle_db/knowledge.db"

echo "🧰 Q3 — пояс с инструментами (спрашивать ДО внешнего поиска и ДО создания чего-либо)"
echo
echo "   ./ask.sh <термин>          ← ОДИН вход: база + литобзор + Lean + спеки; печатает"
echo "                                 «НЕ НАЙДЕНО НИГДЕ», если правда нигде нет"
echo "   ./specs_docs/session_start.sh   состояние сессии; выходит с 1 при противоречиях"
echo "   ./orchestrator/kb.py ask|flags  знание точечно · где уже искали и что ложный друг"

if [ -f "$KB" ]; then
  ROWS="$(sqlite3 "file:$KB?mode=ro" \
    "SELECT (SELECT COUNT(*) FROM kill) || ' убитых · ' ||
            (SELECT COUNT(*) FROM journal_entry) || ' журнал · ' ||
            (SELECT COUNT(*) FROM dossier) || ' досье · ' ||
            (SELECT COUNT(*) FROM search_session) || ' карточек поиска';" 2>/dev/null)"
  [ -n "$ROWS" ] && echo "   база: $ROWS"
fi

PDFS="$(ls docs/routeB_bus/litreview/pdfs/*.pdf 2>/dev/null | wc -l)"
CARDS="$(ls docs/routeB_bus/litreview/*_CARDS.md 2>/dev/null | wc -l)"
echo "   литобзор: $PDFS PDF, $CARDS карточек — ./paper.sh <arxiv|doi> тянет PDF+bib+Zotero"

# Публикации, затянутые механикой, но не разобранные человеком.  Карточку автомат сделать
# не может — она суждение; поэтому долг светится здесь, пока не закрыт.
# grep -c печатает 0 И возвращает код 1, поэтому `|| echo 0` давал бы «0\n0».
NEED="$(grep -c 'NEEDS_CARDS' docs/routeB_bus/litreview/REFERENCES.md 2>/dev/null)"
[ "${NEED:-0}" -gt 0 ] 2>/dev/null && \
  echo "   ⚠ $NEED публикаций без карточки разбора — grep NEEDS_CARDS в REFERENCES.md"

echo
echo "   карта Route B      docs/routeB_bus/MAP.md"
echo "   как пришли к идее  docs/CHAT_DIGESTS.md"
echo "   задания Codex      docs/Codex/TASK_*.md"

# Копим вопросы к судье и отправляем батчем: он думает 20+ мин, поштучные вопросы
# тратят этот ресурс на мелочи. Порог — 2..4 блокирующих вопроса.
QF="docs/routeB_bus/PROSHKA_QUEUE.md"
if [ -f "$QF" ]; then
  # ^## Q<цифра> — иначе grep ловит строку-шаблон «## Q<n> · … OPEN | …» в шапке файла
  QN="$(grep -cE '^## Q[0-9]+ .*· OPEN' "$QF" 2>/dev/null)"
  if [ "${QN:-0}" -ge 2 ] 2>/dev/null; then
    echo "   ⚑ $QN открытых вопросов в очереди к Прошке — порог батча достигнут ($QF)"
  elif [ "${QN:-0}" -gt 0 ] 2>/dev/null; then
    echo "   очередь к Прошке: $QN — копим до 2–4, потом батч"
  fi
fi

BR="$(git branch --show-current 2>/dev/null)"
DIRTY="$(git status --porcelain 2>/dev/null | wc -l)"
echo
echo "   ветка $BR · $([ "$DIRTY" -eq 0 ] && echo 'дерево чисто' || echo "$DIRTY изменённых")"

# Мониторы, которые лгут о своём статусе — самая дорогая из известных ловушек
for f in q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md; do
  [ -f "$f" ] || continue
  ST="$(grep -m1 '^status:' "$f" 2>/dev/null | sed 's/^status:[[:space:]]*//')"
  TS="$(git log -1 --format=%ct -- "$f" 2>/dev/null)"
  if [ -n "$TS" ] && [ -n "$ST" ]; then
    DAYS=$(( ( $(date +%s) - TS ) / 86400 ))
    case "$ST" in ACTIVE*) [ "$DAYS" -gt 30 ] && \
      echo "   ⚠ $(basename "$f") заявляет '$ST', правился $DAYS дней назад — статус ложный";; esac
  fi
done

echo
echo "   Правило: перед «у нас этого нет» и перед созданием нового — ./ask.sh"
