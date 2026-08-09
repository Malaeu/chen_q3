#!/usr/bin/env bash
# session_start.sh — один вход в сессию.
#
# Печатает СОСТОЯНИЕ (не пересказывает правила) и падает, когда источники противоречат
# друг другу. Смысл: то, что протухает, не должно лежать в прозе — оно вычисляется здесь.
#
# Строго read-only: ни одной записи. `spine.py` вызывается с --stdout (ветка без записи),
# базы открываются только на чтение, git — только опросные команды.
#
# Коды возврата:
#   0 — состояние согласовано
#   1 — найдено противоречие между источниками (детали в разделе РАСХОЖДЕНИЯ)
#   2 — не удалось прочитать обязательный источник
#
# Правила старта живут в docs/CODEX_CONTROL.md. Этот скрипт их не дублирует.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO" || exit 2

RUNTIME="orchestrator/state/CHANNEL_RUNTIME.json"
RB_STATE="q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
LIVE_BUS="docs/routeB_bus"
KB="q3.lean.aristotle/aristotle_db/knowledge.db"

DIVERGENCE=()
note() { DIVERGENCE+=("$1"); }

hr() { printf '%s\n' "────────────────────────────────────────────────────────────────"; }

# ── 1. Площадка ────────────────────────────────────────────────────────────────
hr
echo "ПЛОЩАДКА"
echo "  repo    : $REPO"
echo "  branch  : $(git branch --show-current 2>/dev/null || echo '?')"
dirty="$(git status --porcelain=v1 -uall 2>/dev/null | wc -l)"
echo "  worktree: $([ "$dirty" -eq 0 ] && echo 'чисто' || echo "$dirty изменённых файлов")"
echo "  HEAD    : $(git log -1 --format='%h %ad %s' --date=short 2>/dev/null | cut -c1-90)"
ahead="$(git rev-list --count '@{u}..HEAD' 2>/dev/null || echo '?')"
behind="$(git rev-list --count 'HEAD..@{u}' 2>/dev/null || echo '?')"
echo "  vs origin: ahead $ahead / behind $behind"
[ "$behind" != "?" ] && [ "$behind" -gt 0 ] && note "локальная ветка отстаёт от origin на $behind коммитов — сперва подтянуть"

# ── 2. Рантайм канала ──────────────────────────────────────────────────────────
hr
echo "РАНТАЙМ КАНАЛА"
if [ ! -f "$RUNTIME" ]; then
  echo "  ОТСУТСТВУЕТ $RUNTIME"
  echo "  Без него умирает любой запуск spine.py (валидация безусловна)."
  exit 2
fi
python3 - "$RUNTIME" <<'PY'
import json, sys, datetime, os
p = sys.argv[1]
d = json.load(open(p))
print(f"  control : {d.get('control_status','?')}")
print(f"  authority: {d.get('mathematical_authority_mode','?')}")
print(f"  PX_RH   : {d.get('px_rh_claim_state','?')}")
ph = d.get('active_proshka_phase') or {}
if ph:
    print(f"  фаза    : {ph.get('phase_id','?')}")
    print(f"  чат     : {ph.get('conversation_id','—')}  вызовов к Прошке: {ph.get('proshka_calls','?')}")
    op = ph.get('opened_at')
    if op:
        try:
            t = datetime.datetime.fromisoformat(op.replace('Z','+00:00'))
            now = datetime.datetime.now(t.tzinfo) if t.tzinfo else datetime.datetime.now()
            hrs = (now - t).total_seconds()/3600
            mark = "  ← старше суток, проверь, та ли это фаза" if hrs > 24 else ""
            print(f"  открыта : {op}  ({hrs:.1f} ч назад){mark}")
            if hrs > 24:
                open(os.environ.get('DIV_FILE','/dev/null'),'a').write(
                    f"фаза Прошки открыта {hrs:.0f} ч назад — протухание рантайма ничем не проверяется\n")
        except Exception:
            print(f"  открыта : {op} (дату разобрать не удалось)")
else:
    print("  фаза    : нет активной")
PY

# ── 3. Мониторы: заявленный статус против git-активности ───────────────────────
hr
echo "МОНИТОРЫ  (заявляет / последняя правка / возраст)"
now_ts="$(date +%s)"
# git log -1 останавливается на первом попадании — в отличие от --since, который
# обходит всю историю и на файле в 1,4 МБ висит минутами
check_monitor() {
  local f="$1" name="$2"
  [ -f "$f" ] || { echo "  $name: файла нет"; return; }
  local st ts days d
  st="$(grep -m1 -E '^status:' "$f" | sed 's/^status:[[:space:]]*//' | tr -d '\r')"
  ts="$(git log -1 --format=%ct -- "$f" 2>/dev/null)"
  if [ -n "$ts" ]; then
    days=$(( (now_ts - ts) / 86400 ))
    d="$(date -d "@$ts" +%F 2>/dev/null)"
  else
    days=-1; d="—"
  fi
  printf '  %-16s %-24s %s  (%s дн назад)\n' "$name" "${st:-—}" "$d" "$days"
  if [[ "$st" == ACTIVE* ]] && [ "$days" -gt 30 ]; then
    note "$name заявляет '$st', но правился $d — $days дней назад. Статус ложный"
  fi
}
check_monitor "q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md" "PSD_STEP33"
check_monitor "q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md"      "PHASE (H1/PO3)"
check_monitor "q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md"     "SPRINT"

# ── 4. Route B: живая шина против того, что говорит арбитр ─────────────────────
hr
echo "ROUTE B"
if [ -d "$LIVE_BUS" ]; then
  last_goal="$(ls "$LIVE_BUS"/*.goal.md 2>/dev/null | sed 's#.*/##' | sort | tail -1)"
  n_goal="$(ls "$LIVE_BUS"/*.goal.md 2>/dev/null | wc -l)"
  n_ans="$(ls "$LIVE_BUS"/*.answer.md 2>/dev/null | wc -l)"
  echo "  живая шина  : $LIVE_BUS — целей $n_goal, ответов $n_ans"
  echo "  последняя   : ${last_goal:-—}"
  # цель без ответа = то, что исполнимо
  open_goals=""
  for g in "$LIVE_BUS"/*.goal.md; do
    [ -e "$g" ] || continue
    a="${g%.goal.md}.answer.md"
    [ -f "$a" ] || open_goals="$open_goals $(basename "$g")"
  done
  if [ -n "$open_goals" ]; then
    echo "  БЕЗ ОТВЕТА  :$open_goals"
  else
    echo "  без ответа  : нет — открытой цели в живой шине нет"
  fi
else
  echo "  живой шины $LIVE_BUS нет"
  note "живая шина не найдена по ожидаемому пути"
fi

if [ -f "$RB_STATE" ]; then
  addr="$(python3 -c "
import json,sys
d=json.load(open('$RB_STATE'))
for k in ('current_goal','goal_id','address','current_address'):
    if k in d: print(d[k]); break
else:
    print(json.dumps(d)[:120])
" 2>/dev/null)"
  echo "  адрес в state: ${addr:0:100}"
  st_date="$(git log -1 --format=%ad --date=short -- "$RB_STATE" 2>/dev/null)"
  echo "  state правился: $st_date"
  today="$(date +%F)"
  [ "$st_date" != "$today" ] && [ -n "$last_goal" ] && \
    note "ROUTE_B_EXECUTION_STATE.json правился $st_date, а последняя цель шины — $last_goal (проверь, не отстаёт ли адрес)"
fi

# ── 5. База знаний ─────────────────────────────────────────────────────────────
hr
echo "БАЗА ЗНАНИЙ"
if [ -f "$KB" ]; then
  python3 - "$KB" <<'PY'
import sqlite3, sys
c = sqlite3.connect(f"file:{sys.argv[1]}?mode=ro", uri=True)
parts = []
for t in ("kill","move","journal_entry","dossier","search_session","search_term"):
    try:
        parts.append(f"{t} {c.execute(f'SELECT COUNT(*) FROM {t}').fetchone()[0]}")
    except sqlite3.Error:
        pass
print("  " + " · ".join(parts))
PY
  echo "  спросить: ./orchestrator/kb.py ask \"<термин>\"   ·   флаги поиска: ./orchestrator/kb.py flags <адрес>"
else
  echo "  базы нет по пути $KB"
  note "knowledge.db отсутствует — поиск по накопленному знанию недоступен"
fi

# ── 6. Манифест инструментов ───────────────────────────────────────────────────
hr
echo "МАНИФЕСТ ИНСТРУМЕНТОВ"
manifest_out="$(python3 - <<'PY' 2>&1
from orchestrator import spine

data = spine.validate_tool_manifest()
print(
    f"  schema {data['schema']} · families {data['family_count']} · "
    f"tools {data['tool_count']} · writers {data['writer_count']}"
)
print(f"  mirror  : BYTE_IDENTICAL · sha256 {data['sha256']}")
PY
)"
manifest_rc=$?
if [ "$manifest_rc" -eq 0 ]; then
  printf '%s\n' "$manifest_out"
else
  echo "  ПРОВАЛ (код $manifest_rc):"
  printf '%s\n' "$manifest_out" | tail -5 | sed 's/^/    /'
  note "TOOLS.yaml не прошёл schema/contract/mirror validation"
fi

# ── 7. Строгая валидация контроля ──────────────────────────────────────────────
hr
echo "ВАЛИДАЦИЯ КОНТРОЛЯ"
if [ -f orchestrator/spine.py ]; then
  # --stdout = ветка без записи; --refresh здесь НЕ используем, он пишет
  out="$(python3 orchestrator/spine.py --strict --reason session-start --stdout 2>&1)"
  rc=$?
  if [ $rc -eq 0 ]; then
    echo "  $(printf '%s\n' "$out" | grep -m1 'P9_STRICT_PASS' || echo 'прошла')"
  else
    echo "  ПРОВАЛ (код $rc):"
    printf '%s\n' "$out" | tail -5 | sed 's/^/    /'
    note "strict-валидация контроля не прошла — работа не начинается"
  fi
else
  note "orchestrator/spine.py не найден"
fi

# ── 8. Расхождения ─────────────────────────────────────────────────────────────
hr
if [ ${#DIVERGENCE[@]} -eq 0 ]; then
  echo "РАСХОЖДЕНИЙ НЕТ — источники согласованы."
  exit 0
fi
echo "РАСХОЖДЕНИЯ (${#DIVERGENCE[@]}):"
for d in "${DIVERGENCE[@]}"; do echo "  · $d"; done
echo
echo "Разбор известных расхождений: specs_docs/SESSION_START_AUDIT_2026-08-06.md"
exit 1
