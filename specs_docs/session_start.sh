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
CURRENT_TASK="docs/Codex/CURRENT.md"

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
INVJ="docs/cartographer/inventory_RouteB.json"
LEAN_DIR="q3.lean.aristotle/Q3/Proofs/RouteB"
if [ ! -f "$INVJ" ]; then
  echo "  инвентарь не построен — python3 docs/cartographer/inventory.py"
else
  inv_at="$(git log -1 --format=%h -- "$INVJ" 2>/dev/null)"
  if [ -z "$inv_at" ]; then
    echo "  инвентарь есть, но не в git — точки отсчёта нет, протухание не вычисляется"
  elif git diff --quiet "$inv_at" HEAD -- "$LEAN_DIR" 2>/dev/null; then
    echo "  актуален: .lean в RouteB не менялись с $inv_at"
  else
    n="$(git diff --name-only "$inv_at" HEAD -- "$LEAN_DIR" 2>/dev/null | wc -l)"
    note "инвентарь картографа протух (.lean изменилось: $n с $inv_at) — python3 docs/cartographer/inventory.py"
  fi
  # Незакоммиченные .lean HEAD не видит — картограф уже врёт, хотя история чиста.
  dirty="$(git status --porcelain -- "$LEAN_DIR" 2>/dev/null | wc -l)"
  [ "$dirty" -gt 0 ] && echo "  плюс незакоммиченных .lean в дереве: $dirty"
fi

# ── 10a. Опоры и канаты: сколько шагов до жёсткости каждой опоры крыши ─────────
# Язык владельца (2026-08-19): крыша rh_of_canonical_strip_slots стоит на шести
# опорах G1-G6 (через И); канаты = незакрытые шаги дорог снабжения (assembly).
# Дороги к одной опоре — ИЛИ: платим за одну. Несосчитанные места называются
# вслух: опора без измеренных канатов хуже опоры с большим k.
hr
echo "ОПОРЫ И КАНАТЫ (крыша ждёт: G2 G3 G5 G6 · стоят: G1 G4 · бетон: G7+Гурвиц)"
.venv/bin/python - 2>/dev/null <<'PYEOF' || echo "  (assembly недоступна)"
import sqlite3
con = sqlite3.connect("file:q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro", uri=True)
# дорога -> опора (сверено по required_by финальных шагов, 2026-08-19)
GATE = {"PSD_CERTIFICATE_FOR_CCM_CELL": "G2",
        "SIMPLE_EVEN_GROUND_TO_REAL_ZEROS": "G3",
        "G3_CVS_PORT": "G3-порт CvS",
        "G5_CRITICAL_MOMENT": "G5",
        "REALZERO_GROUND_DIAGONAL_TO_XI": "гол 058 ЗАМЕНА G2+G3",
        "GOAL057_CONTINUUM_NUMERATOR_BRIDGE": "G6"}
rows = con.execute("""select chain,
    sum(case when status not in ('READY','VALIDATION') then 1 else 0 end), count(*)
    from assembly group by chain order by 2""").fetchall()
def origin(chain):
    # происхождение ЗАКРЕПЛЁННЫХ канатов: кто доказал (вопрос владельца 19.08)
    ours = ml = data = 0
    for (sf,) in con.execute(
            "select coalesce(supplier_file,'') from assembly "
            "where chain=? and status='READY'", (chain,)):
        if sf.startswith("q3.lean.aristotle"): ours += 1
        elif ".lake/packages/mathlib" in sf:   ml += 1
        else:                                   data += 1
    parts = [f"наш Lean {ours}"]
    if ml:   parts.append(f"Mathlib {ml}")
    if data: parts.append(f"данные {data}")
    return " · ".join(parts)
total = 0
for chain, k, n in rows:
    gate = GATE.get(chain, "?")
    total += k
    print(f"  {gate:14s} всего канатов {n} · закреплено {n-k} ({origin(chain)}) · ОСТАЛОСЬ НАТЯНУТЬ {k}")
    print(f"  {'':14s}   [{chain}]")
done = sum(n - k for _, k, n in rows)
alln = sum(n for _, _, n in rows)
print(f"  {'':14s} ВСЕГО в базе {alln} канатов · ЗАКРЕПЛЕНО {done} · висит {total}")
print("  бумажные движки (Connes и др.) канатами НЕ считаются, пока не формализованы")
print("  G5: 2 каната, подтверждено ядром 19.08 — равномерный моментный бюджет"
      " + PairCofinal (ОБЩИЙ канат с G6: поле CanonicalData)")
print("  G6_N1_PREANCHOR: kernel GREEN (36->5->2->0), но это УСЛОВНЫЙ композер —")
print("    SelectedProlateCofinalSourceData строится ИЗ SelectedProlatePreAnchorData")
print("    и CCMLemma73PreAnchorPort. Пересчёт судьи 20.08: дельта НОЛЬ.")
print("    Следующие несущие дыры, ПОРЯДОК ЖЁСТКИЙ (вердикт N2 20.08):")
print("      1) SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT — ЗАКРЫТ 20.08")
print("         (Linux-тело за Codex: selectedFerrersPreAnchorData, pair_spec")
print("         экспортирован, тройка аксиом, q3_check ok)")
print("      2) CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT — 9 этажей L73.0-L73.8")
print("         (вердикт FLOORS 20.08): стена L73.2 (Lemma-7.2 rate), L73.5")
print("         (Mellin=centeredXi) НЕЗАВИСИМ — бить параллельно")
print("      3) стена N2 разложена на этажи N2_0..N2_5; исполнение ДО 1-2 запрещено;")
print("         бонус: SelectedTrialNormalizerBounded для N2 НЕ НУЖЕН (zero-mode")
print("         сокращение нормировщиков — шаг 13 GOAL057 выходит из зависимостей)")
print("  G3-порт CvS: 2 узла (value-crosswalk ground/trial + сборка); типы не менять")
print("  ═══ ОСТАЛОСЬ НАТЯНУТЬ ДО RH — ВЫБОР МАРШРУТА (дедуп 19.08) ═══")
print("    G5 (1) + G6 (7) нужны в ЛЮБОМ случае, и дальше ОДНО из двух:")
print("      + G2 (0!) + G3 (5) =  13  классика; G2-ЧИСЛА СНЯТЫ С ПУТИ 20.08")
print("        (REQ-2026-08-20-B: клетка m13 = валидация/falsifier, не поставщик")
print("         SlotH2a; настоящий G2-поставщик = SIEG_of_penalty на семье — в G3/058)")
print("      + гол 058 (5)      =  13  равные дороги; 058 = ground -> Xi напрямую")
print("    платим за ОДНУ дорогу, не за обе")
print("    характер 17: 3 числа · 3 owner-data · 4-5 сборок · 2 порта · 4-5 стен")
print("    флаг: SIMPLE_EVEN:15 ~ N1 может дать 17->16 (решится при постройке N1)")
con.close()
PYEOF

# ── 10a1. Запросы судье: что висит без ответа ──────────────────────────────────
hr
echo "ЗАПРОСЫ СУДЬЕ (PROSHKA_QUEUE)"
OPEN_REQS="$(rg -o 'REQ-[0-9-]+[A-Z]' -B0 docs/routeB_bus/PROSHKA_QUEUE.md 2>/dev/null | paste -sd' ' -)"
OPEN_LIST="$(rg -B1 'STATUS: OPEN' docs/routeB_bus/PROSHKA_QUEUE.md 2>/dev/null | rg -o 'REQ-[0-9A-Za-z-]+' | paste -sd' ' -)"
if [ -n "$OPEN_LIST" ]; then
  echo "  БЕЗ ОТВЕТА: $OPEN_LIST — судья читает очередь на старте своей сессии;"
  echo "    если ответа нет два его захода подряд, напомнить ему id в чате"
else
  echo "  все запросы отвечены"
fi

# ── 10a2. Непрожатые вердикты: мигратор отстал от шины? ────────────────────────
# Дыра найдена 2026-08-20: шаг «прогнать мигратор» вшит в петлю кондуктора
# (когда шину коммитим МЫ), но Прошка пушит вердикты сам — на pull-стороне
# триггера не было, и два вердикта пролежали непрожатыми. Детектор read-only:
# кричит, боевой прогон — с per-action OK (knowledge.db бинарник в git).
hr
echo "МИГРАТОР ПРОТИВ ШИНЫ"
MIG_OUT="$(.venv/bin/python orchestrator/kb_migrate_verdicts.py --dry-run 2>/dev/null | rg 'new strategy rows|supplier-ledger rows|new verdict-kill' )"
printf '%s\n' "$MIG_OUT" | sed 's/^/  /'
if printf '%s' "$MIG_OUT" | rg -q ': *[1-9]'; then
  note "мигратор отстал от шины — есть непрожатые вердикты: .venv/bin/python orchestrator/kb_migrate_verdicts.py (боевой, с OK владельца)"
fi

# ── 10b. Записи журнала: обязательные графы заполнены? ─────────────────────────
# Валидатор существовал с самого начала (kb_migrate_progress_log.parse_entries
# требует все 8 граф), но жил только внутри pytest, который никто не гоняет на
# старте, — и запись без «Что отвергли и почему» от 15.08 держала два теста
# красными неделю, пока её не нашли случайно. Дефект записи должен кричать при
# каждом старте сессии у каждого тела, а не ждать прогона тестов.
hr
echo "ЖУРНАЛ РАЗВИЛОК (обязательные графы)"
PLOG_ERR="$(.venv/bin/python - 2>&1 <<'PYEOF'
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
