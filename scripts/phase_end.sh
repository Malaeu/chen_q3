#!/usr/bin/env bash
# phase_end.sh — one command at the end of a phase/checkpoint (plain mode, owner order 2026-09-25).
#
#   scripts/phase_end.sh "commit message"            journal → check → shelf → literature → stats → commit → push → readback
#   scripts/phase_end.sh "commit message" --no-log   same, without requiring today's journal entry (owner bypass)
#   scripts/phase_end.sh --dry-run                   check → stats only (no journal check, shelf, literature, commit/push)
#
# Steps:
#   0. Journal: docs/Progress_Log.md must have an entry "## <today> — ..." (insights, blockers,
#      Zinger needles, why we are here, next move). Template: docs/Codex/NEXT.md, «Конец фазы».
#   1. q3_check on every changed/new Lean file under q3.lean.aristotle/Q3 (build + axioms).
#   2. Shelf refresh (semantic index of the docs), non-fatal if qmd is unavailable.
#   2b. Literature scan: queries from lines "- lit: ..." in NEXT.md → docs/literature/scan_<date>.json
#       (arXiv + Crossref metadata only, read-only, non-fatal offline).
#   3. Regenerate the AUTO-STATS block in docs/Codex/NEXT.md (roof ports, Goal058 gates,
#      sorry/axiom count, open Proshka requests) and the "Updated:" line.
#   4. git add (tracked changes, new Lean files, docs/Codex, docs/routeB_bus), commit, pull --rebase, push.
#   5. Readback: origin/rh_clean must equal HEAD.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export GIT_OPTIONAL_LOCKS=0
BRANCH="rh_clean"
DRY=0
NOLOG=0
MSG=""
for a in "$@"; do
  case "$a" in
    --dry-run) DRY=1 ;;
    --no-log) NOLOG=1 ;;
    *) MSG="$a" ;;
  esac
done
if [[ $DRY -eq 0 && -z "$MSG" ]]; then
  echo "usage: scripts/phase_end.sh \"commit message\" | --dry-run" >&2
  exit 64
fi
PY="python3"
[[ -x .venv/bin/python ]] && PY=".venv/bin/python"

TODAY="$(date +%F)"
echo "== 0 Journal entry in docs/Progress_Log.md"
if [[ $DRY -eq 1 || $NOLOG -eq 1 ]]; then
  echo "   skipped"
elif grep -q "^## $TODAY" docs/Progress_Log.md; then
  echo "   OK: entry for $TODAY present"
else
  echo "   MISSING: add '## $TODAY — <what this phase found>' to docs/Progress_Log.md" >&2
  echo "   (template: docs/Codex/NEXT.md «Конец фазы»; bypass: --no-log)" >&2
  exit 65
fi

echo "== 1/5 Lean check of changed files"
mapfile -t LEAN < <(
  { git diff --name-only "origin/$BRANCH" -- 'q3.lean.aristotle/Q3/*.lean' 2>/dev/null
    git ls-files --others --exclude-standard -- 'q3.lean.aristotle/Q3/*.lean'; } | sort -u
)
if [[ ${#LEAN[@]} -eq 0 ]]; then
  echo "   no changed Lean files"
else
  for f in "${LEAN[@]}"; do
    [[ -f "$f" ]] || continue
    echo "   q3_check $f"
    scripts/q3_check.sh "$f"
  done
fi

echo "== 2/5 Shelf refresh"
if [[ $DRY -eq 1 ]]; then
  echo "   skipped (dry run)"
elif command -v qmd >/dev/null 2>&1; then
  "$PY" q3.lean.aristotle/scripts/refresh_q3_docs.py || echo "   WARN: shelf refresh failed (non-fatal)"
else
  echo "   WARN: qmd not installed on this machine — shelf not refreshed"
fi

echo "== 2b Literature scan"
if [[ $DRY -eq 1 ]]; then
  echo "   skipped (dry run)"
else
  mapfile -t LIT < <(sed -n 's/^- lit: *//p' docs/Codex/NEXT.md)
  if [[ ${#LIT[@]} -eq 0 ]]; then
    echo "   no '- lit:' queries in NEXT.md"
  else
    mkdir -p docs/literature
    OUTJ="docs/literature/scan_$TODAY.json"
    if timeout 180 "$PY" scripts/literature_discovery.py "${LIT[@]}" --max-results 5 > "$OUTJ.tmp" 2>/dev/null; then
      mv "$OUTJ.tmp" "$OUTJ"
      "$PY" -c 'import json,sys; d=json.load(open(sys.argv[1])); c=d.get("candidates",[]); print(f"   {len(c)} candidates → {sys.argv[1]}"); [print("   -", x.get("title","")[:110]) for x in c[:8]]' "$OUTJ"
    else
      rm -f "$OUTJ.tmp"; echo "   WARN: literature scan failed (offline?) — non-fatal"
    fi
  fi
fi

echo "== 3/5 Stats block in docs/Codex/NEXT.md"
"$PY" - <<'PY'
import datetime, json, re, subprocess
from pathlib import Path

root = Path(".")
next_md = root / "docs/Codex/NEXT.md"
text = next_md.read_text(encoding="utf-8")

ledger = json.loads(subprocess.run(
    ["python3", "orchestrator/roof_port_ledger.py"], capture_output=True, text=True).stdout or "{}")
ports = ledger.get("ports", [])
port_line = ", ".join(f"{p['port']}={p['status']}" for p in ports) or "UNAVAILABLE"

goal = (root / "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md").read_text(encoding="utf-8")
gates = re.findall(r"^\|\s*\d+\s*\|\s*`(G[0-9a-z]+)`\s*\|[^|]*\|\s*(.+?)\s*\|\s*$", goal, re.M)
closed = [g for g, st in gates if re.search(r"READY|PROVED", st)]
open_ = [g for g, st in gates if g not in closed]

routeb = root / "q3.lean.aristotle/Q3/Proofs/RouteB"
sorry = axiom = 0
for f in routeb.rglob("*.lean"):
    body = f.read_text(encoding="utf-8", errors="replace")
    sorry += len(re.findall(r"\bsorry\b", body))
    axiom += len(re.findall(r"^\s*axiom\s", body, re.M))

queue = (root / "docs/routeB_bus/PROSHKA_QUEUE.md").read_text(encoding="utf-8")
open_req = re.findall(r"^## (REQ-\S+).*·\s*OPEN\s*$", queue, re.M)

head = subprocess.run(["git", "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip()
today = datetime.date.today().isoformat()
block = "\n".join([
    "<!-- AUTO-STATS:BEGIN (scripts/phase_end.sh — не править руками) -->",
    f"Статистика на {today}, HEAD {head}:",
    f"- Ворота Goal058: закрыто {len(closed)}/{len(gates)} ({', '.join(closed)}); открыто: {', '.join(open_)}",
    f"- Крыша: {ledger.get('port_summary', {}).get('jointly_bound', '?')}/{len(ports)} портов связано; {port_line}",
    f"- RouteB Lean: sorry={sorry}, axiom={axiom}",
    f"- Открытые запросы Прошке: {len(open_req)}" + (f" ({', '.join(open_req)})" if open_req else ""),
    "<!-- AUTO-STATS:END -->",
])
pattern = re.compile(r"<!-- AUTO-STATS:BEGIN.*?<!-- AUTO-STATS:END -->", re.S)
if pattern.search(text):
    text = pattern.sub(block, text)
else:
    text = text.replace("## Дорожная карта", block + "\n\n## Дорожная карта", 1)
text = re.sub(r"^Updated: .*$", f"Updated: {today} · by: scripts/phase_end.sh · HEAD at update: {head}", text, count=1, flags=re.M)
next_md.write_text(text, encoding="utf-8")
print(block)
PY

if [[ $DRY -eq 1 ]]; then
  echo "== 4/5, 5/5 skipped (dry run). NEXT.md was updated locally; review with: git diff docs/Codex/NEXT.md"
  exit 0
fi

echo "== 4/5 Commit and push"
git add -u
git add -- docs/Codex docs/routeB_bus docs/Progress_Log.md
[[ -d docs/literature ]] && git add -- docs/literature
[[ ${#LEAN[@]} -gt 0 ]] && git add -- "${LEAN[@]}"
if git diff --cached --quiet; then
  echo "   nothing to commit"
else
  git commit -q -m "$MSG"
fi
git pull -q --rebase origin "$BRANCH"
git push -q origin "$BRANCH"

echo "== 5/5 Readback"
git fetch -q origin "$BRANCH"
L="$(git rev-parse HEAD)"; R="$(git rev-parse "origin/$BRANCH")"
if [[ "$L" == "$R" ]]; then
  echo "   OK: origin/$BRANCH == HEAD ($(git rev-parse --short HEAD))"
else
  echo "   FAIL: HEAD $L != origin/$BRANCH $R" >&2
  exit 1
fi
