#!/usr/bin/env bash
# session_start.sh — manual legacy diagnostic wrapper.
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
# Правила старта живут в docs/CODEX_CONTROL.md. Канонический production front
# door — `python3 orchestrator/workflow_runtime.py plan`; этот wrapper никогда
# не вызывает его и не участвует в production workflow.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [ "${1:-}" = "--legacy-v9-maintenance" ]; then
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "usage: $0 [--legacy-v9-maintenance]" >&2
  exit 2
fi
echo "DEPRECATED_LEGACY_V9_MAINTENANCE" >&2

cd "$REPO" || exit 2

RUNTIME="orchestrator/state/CHANNEL_RUNTIME.json"
RB_STATE="q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
LIVE_BUS="docs/routeB_bus"
KB="q3.lean.aristotle/aristotle_db/knowledge.db"
CURRENT_TASK="docs/Codex/CURRENT.md"
PYTHON="python3"
[ -x .venv/bin/python ] && PYTHON=".venv/bin/python"

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

# ── 2a. Репозиторный указатель текущего задания Codex ─────────────────────────
hr
echo "ТЕКУЩЕЕ ЗАДАНИЕ CODEX"
task_out="$(python3 - <<'PY' 2>&1
from orchestrator import spine

data = spine.validate_current_codex_task()
print(f"  status  : {data['status']}")
print(f"  task    : {data['task_file'] or '—'}")
print(f"  source  : {data['source_commit'] or '—'}")
PY
)"
task_rc=$?
if [ "$task_rc" -eq 0 ]; then
  printf '%s\n' "$task_out"
else
  echo "  ПРОВАЛ (код $task_rc):"
  printf '%s\n' "$task_out" | tail -5 | sed 's/^/    /'
  note "$CURRENT_TASK не прошёл validation"
fi

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
  # PAUSED_RESTORABLE остаётся физическим goal, но не является исполнимым.
  goal_scan="$(python3 - "$LIVE_BUS" <<'PY'
import sys
from pathlib import Path

from orchestrator.routeb_goal_state import is_paused_goal

bus = Path(sys.argv[1])
open_goals = []
paused_goals = []
for goal in sorted(bus.glob("*.goal.md")):
    answer = goal.with_name(goal.name.removesuffix(".goal.md") + ".answer.md")
    if answer.is_file():
        continue
    (paused_goals if is_paused_goal(goal) else open_goals).append(goal.name)
print("OPEN=" + " ".join(open_goals))
print("PAUSED=" + " ".join(paused_goals))
PY
)"
  open_goals="$(printf '%s\n' "$goal_scan" | sed -n 's/^OPEN=//p')"
  paused_goals="$(printf '%s\n' "$goal_scan" | sed -n 's/^PAUSED=//p')"
  if [ -n "$open_goals" ]; then
    echo "  БЕЗ ОТВЕТА  : $open_goals"
  else
    echo "  без ответа  : нет — открытой цели в живой шине нет"
  fi
  if [ -n "$paused_goals" ]; then
    echo "  НА ПАУЗЕ    : $paused_goals"
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
  status_script="q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py"
  if status_out="$(python3 "$status_script" --check 2>&1)"; then
    echo "  арбитр      : $(printf '%s\n' "$status_out" | tail -1)"
  else
    status_rc=$?
    echo "  арбитр      : ПРОВАЛ (код $status_rc)"
    printf '%s\n' "$status_out" | tail -8 | sed 's/^/    /'
    note "Route B physical bus/execution state/source pins не прошли routeb_status.py --check"
  fi
fi

# ── 4a. Delta-aware Route B briefing ─────────────────────────────────────────
# Read-only: the small local checkpoint is written only by close-session.
hr
if briefing_out="$("$PYTHON" orchestrator/session_briefing.py brief 2>&1)"; then
  printf '%s\n' "$briefing_out"
  if printf '%s\n' "$briefing_out" | grep -q '^  BRIEFING_BLOCKER: CONTROL_PLANE_DRIFT$'; then
    note "Route B briefing: CONTROL_PLANE_DRIFT — state address is older than the latest authorized closeout"
  fi
else
  briefing_rc=$?
  echo "ROUTE B — SESSION BRIEF: ПРОВАЛ (код $briefing_rc)"
  printf '%s\n' "$briefing_out" | tail -8 | sed 's/^/  /'
  note "Route B session briefing registry/checkpoint/state validation failed"
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
print(f"  authority: REPO_CANONICAL · sha256 {data['sha256']}")
PY
)"
manifest_rc=$?
if [ "$manifest_rc" -eq 0 ]; then
  printf '%s\n' "$manifest_out"
else
  echo "  ПРОВАЛ (код $manifest_rc):"
  printf '%s\n' "$manifest_out" | tail -5 | sed 's/^/    /'
  note "TOOLS.yaml не прошёл schema/contract/path validation"
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

# ── 8. Границы, которые нельзя нарушать ────────────────────────────────────────
# Не пересказ чужого кернела, а вычисление из состояния: инварианты берутся с диска,
# поэтому не могут протухнуть в прозе.
hr
echo "ГРАНИЦЫ"
newest_ans="$(ls -t "$LIVE_BUS"/*.answer.md 2>/dev/null | head -1)"
if [ -n "$newest_ans" ]; then
  for k in ROUTE BUS_010 GOAL_055 ARISTOTLE_SUBMISSION ROUTE_PROMOTION PX_RH_CLAIM; do
    v="$(grep -m1 "^$k:" "$newest_ans" 2>/dev/null | sed "s/^$k:[[:space:]]*//")"
    [ -n "$v" ] && printf '  %-22s %s\n' "$k" "$v"
  done
  echo "  (из $(basename "$newest_ans"))"
else
  note "не удалось прочитать границы — нет ни одного answer.md в живой шине"
fi

# ── 9. Разделение цепей: Codex ↔ AGENTS.md, я ↔ CLAUDE.md ──────────────────────
# 2026-08-10 цепи разведены: Codex стартует через AGENTS.md, наблюдатель — через
# CLAUDE.md, и ни один не читает файл другого.  Слипание обратно ловится здесь:
# spine.py проверяет только свою сторону (validate_codex_bootstrap + защёлка
# BEHAVIOR_BODY_MULTIROLE на YAML-шапке контроля), нашу сторону не проверяет никто.
hr
echo "РАЗДЕЛЕНИЕ ЦЕПЕЙ"
leak=0
if grep -q "CLAUDE\.md" AGENTS.md 2>/dev/null; then
  note "AGENTS.md ссылается на CLAUDE.md — цепи слиплись"; leak=1
fi
# Ищем ВХОД, а не упоминание: вход стоял бы в шапке.  Ниже файл вправе называть чужую
# цепь как предмет наблюдения — первая версия проверки этого не различала и ругалась на
# собственный раздел «чего в этом файле нет».
if head -20 CLAUDE.md 2>/dev/null | grep -qE "enter through|CODEX_CONTROL_UNAVAILABLE|Read it completely"; then
  note "в шапке CLAUDE.md стоит вход Codex — цепи слиплись"; leak=1
fi
if [ -f docs/CODEX_CONTROL.md ] && \
   sed -n '/^```yaml/,/^```/p' docs/CODEX_CONTROL.md | grep -q "CLAUDE\.md"; then
  note "CLAUDE.md просочился в YAML-шапку CODEX_CONTROL — spine это тоже поймает"; leak=1
fi
[ "$leak" -eq 0 ] && echo "  чисто: AGENTS.md ↛ CLAUDE.md, CLAUDE.md ↛ вход Codex"

# ── 10. Картограф: не протух ли инвентарь относительно дерева ──────────────────
# inventory_RouteB.json порождён из .lean в RouteB, но связи между ними git не хранит:
# файл не менялся — дерево чистое, и молчание ничего не доказывает.  Спрашиваем прямо:
# когда инвентарь обновляли и что случилось с деревом после.  Даты файлов для этого
# не годятся — git не хранит mtime, после клона он у всех файлов одинаковый.
hr
echo "КАРТОГРАФ"
DEP_STATUS="$(python3 orchestrator/dependency_registry.py status --consumer session-start 2>&1)"
DEP_RC=$?
if [ "$DEP_RC" -eq 0 ]; then
  echo "  $DEP_STATUS"
else
  note "derived registry: $DEP_STATUS — repair: python3 orchestrator/workflow_runtime.py close-session --repair"
fi

# The old G1-G7/assembly count surface was removed here.  It duplicated the
# battle brief and incorrectly made legacy READY rows look like jointly bound
# roof premises.  session_briefing.py now owns the source-locked six-slot /
# seven-input dependent roof ledger and labels assembly totals as bookkeeping.

# ── 10a1. Запросы судье: что висит без ответа ──────────────────────────────────
hr
echo "ЗАПРОСЫ СУДЬЕ (PROSHKA_QUEUE)"
REQ_STATUS="$($PYTHON - docs/routeB_bus/PROSHKA_QUEUE.md <<'PYEOF'
import re, sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8")
for match in re.finditer(r"(?ms)^##\s+(REQ-[0-9A-Za-z-]+)\b(.*?)(?=^##\s+|\Z)", text):
    request_id, body = match.groups()
    status = re.search(r"(?m)^-?\s*\x60?STATUS:\s*(OPEN|IN_REVIEW|ANSWERED|DROPPED)\b", body)
    if status and status.group(1) in {"OPEN", "IN_REVIEW"}:
        print(f"{status.group(1)} {request_id}")
PYEOF
)"
OPEN_LIST="$(printf '%s\n' "$REQ_STATUS" | awk '$1 == "OPEN" {print $2}' | paste -sd' ' -)"
REVIEW_LIST="$(printf '%s\n' "$REQ_STATUS" | awk '$1 == "IN_REVIEW" {print $2}' | paste -sd' ' -)"
if [ -n "$REVIEW_LIST" ]; then
  echo "  В РАБОТЕ У СУДЬИ: $REVIEW_LIST — same-chat delivery уже выполнена; ждём natural verdict"
fi
if [ -n "$OPEN_LIST" ]; then
  echo "  НЕ ОТПРАВЛЕНЫ: $OPEN_LIST — текущий Codex-body должен выполнить review-plan и same-chat send сам"
fi
if [ -z "$OPEN_LIST" ] && [ -z "$REVIEW_LIST" ]; then
  echo "  все запросы отвечены"
fi

# ── 10a2. Непрожатые вердикты: мигратор отстал от шины? ────────────────────────
# Дыра найдена 2026-08-20: шаг «прогнать мигратор» вшит в петлю кондуктора
# (когда шину коммитим МЫ), но Прошка пушит вердикты сам — на pull-стороне
# триггера не было, и два вердикта пролежали непрожатыми. Детектор read-only:
# кричит; боевой прогон разрешён только действующим goal scope/lifecycle grant
# (knowledge.db бинарник в git), без повторного per-action OK внутри гранта.
hr
echo "МИГРАТОР ПРОТИВ ШИНЫ"
MIG_RAW="$("$PYTHON" orchestrator/kb_migrate_verdicts.py --dry-run 2>&1)"
MIG_RC=$?
MIG_OUT="$(printf '%s\n' "$MIG_RAW" | rg 'new strategy rows|new verdict-kill' || true)"
printf '%s\n' "$MIG_OUT" | sed 's/^/  /'
if [ "$MIG_RC" -ne 0 ]; then
  note "мигратор вердиктов не отработал (код $MIG_RC)"
elif printf '%s' "$MIG_OUT" | rg -q ': *[1-9]'; then
  note "мигратор отстал от шины — есть непрожатые вердикты: python3 orchestrator/workflow_runtime.py close-phase --repair (в активном goal scope)"
fi

# ── 10b. Записи журнала: обязательные графы заполнены? ─────────────────────────
# Валидатор существовал с самого начала (kb_migrate_progress_log.parse_entries
# требует все 8 граф), но жил только внутри pytest, который никто не гоняет на
# старте, — и запись без «Что отвергли и почему» от 15.08 держала два теста
# красными неделю, пока её не нашли случайно. Дефект записи должен кричать при
# каждом старте сессии у каждого тела, а не ждать прогона тестов.
hr
echo "ЖУРНАЛ РАЗВИЛОК (обязательные графы)"
PLOG_ERR="$("$PYTHON" - 2>&1 <<'PYEOF'
import sys
sys.path.insert(0, "orchestrator")
try:
    from kb_migrate_progress_log import parse_entries
    parse_entries()
    print("OK")
except ValueError as e:
    print(f"НЕПОЛНАЯ ЗАПИСЬ: {e}")
except Exception as e:
    print(f"валидатор не отработал: {type(e).__name__}: {e}")
PYEOF
)"
if [ "$PLOG_ERR" = "OK" ]; then
  echo "  все записи несут обязательные графы"
else
  echo "  $PLOG_ERR"
  note "Progress_Log: $PLOG_ERR — дописать может только автор записи"
fi

# ── 11. Входящие: что владелец положил и никто не разобрал ─────────────────────
# Владелец кладёт в docs/_inbox всё, для чего не знает папку и имя. Разгребает
# наблюдатель. Непрочитанный файл в репозитории равносилен его отсутствию, поэтому
# непустой inbox — это работа, а не заметка.
hr
echo "ВХОДЯЩИЕ"
INBOX="docs/_inbox"
if [ ! -d "$INBOX" ]; then
  echo "  папки нет — создать: mkdir -p $INBOX"
else
  pending="$(find "$INBOX" -type f ! -name README.md 2>/dev/null | wc -l)"
  if [ "$pending" -eq 0 ]; then
    echo "  пусто"
  else
    note "в docs/_inbox лежит неразобранного: $pending — правила в его README.md"
    find "$INBOX" -type f ! -name README.md 2>/dev/null | head -10 | while read -r f; do
      printf '  · %s  (%s)\n' "$(basename "$f")" "$(date -r "$f" '+%d.%m %H:%M' 2>/dev/null)"
    done
  fi
fi

# ── 12. Расхождения ────────────────────────────────────────────────────────────
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
