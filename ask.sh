#!/usr/bin/env bash
# ask.sh — ОДИН вход в накопленное знание. Спрашивать ДО внешнего поиска и ДО создания чего-либо.
#
# Зачем он есть. За 6–7 августа трижды подряд повторилось одно: инструмент существовал,
# знание лежало внутри, никто не посмотрел.
#   · H2aPenaltyCoercivity.lean — теорема с явной щелью, не упомянута в MAP.md;
#   · kb_migrate_verdicts.py — мигратор написан, при закрытии цели не дёргается;
#   · Groskin 2607.02828 — PDF скачан, в bib, помечен «HAVE ✓ FLAG subagent» — а мы пошли
#     искать его в интернете.
# Причина не в забывчивости: хранилищ несколько, у каждого своя команда, и спросив одно, легко
# решить, что нигде нет. Здесь спрашиваются все сразу, и отсутствие печатается явно.
#
# Строго read-only.

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")" || exit 2

if [ $# -eq 0 ]; then
  echo "usage: ./ask.sh [--deep] [--external-receipt PATH] [--external-candidate NAME] [--external-candidate-provenance CLASS] <термин> [ещё термины]"
  echo "       ищет каскадом: knowledge.db · litreview · Lean · specs/docs · q3_docs · external Lean"
  exit 2
fi

DEEP=0
EXTERNAL_RECEIPT=""
EXTERNAL_CANDIDATE=""
EXTERNAL_CANDIDATE_PROVENANCE=""
while [ $# -gt 0 ]; do
  case "${1:-}" in
    --deep) DEEP=1; shift ;;
    --external-receipt)
      [ $# -ge 2 ] || { echo "--external-receipt requires a path"; exit 2; }
      EXTERNAL_RECEIPT="$2"
      shift 2
      ;;
    --external-candidate)
      [ $# -ge 2 ] || { echo "--external-candidate requires a name"; exit 2; }
      EXTERNAL_CANDIDATE="$2"
      shift 2
      ;;
    --external-candidate-provenance)
      [ $# -ge 2 ] || { echo "--external-candidate-provenance requires a class"; exit 2; }
      EXTERNAL_CANDIDATE_PROVENANCE="$2"
      shift 2
      ;;
    --) shift; break ;;
    -*) echo "unknown option: $1"; exit 2 ;;
    *) break ;;
  esac
done
if [ $# -eq 0 ]; then
  echo "usage: ./ask.sh [--deep] [--external-receipt PATH] [--external-candidate NAME] [--external-candidate-provenance CLASS] <термин> [ещё термины]"
  exit 2
fi
if [ -z "$EXTERNAL_RECEIPT" ] && { [ -n "$EXTERNAL_CANDIDATE" ] || [ -n "$EXTERNAL_CANDIDATE_PROVENANCE" ]; }; then
  echo "external candidate binding requires --external-receipt"
  exit 2
fi
if [ -n "$EXTERNAL_CANDIDATE_PROVENANCE" ] && [ -z "$EXTERNAL_CANDIDATE" ]; then
  echo "--external-candidate-provenance requires --external-candidate"
  exit 2
fi

Q="$*"
KB="q3.lean.aristotle/aristotle_db/knowledge.db"
PROOFS="q3.lean.aristotle/aristotle_db/aristotle_proofs.db"
HITS=0
SEARCHED=()
SEARCH_FAILURES=()

hdr() { printf '\n── %s %s\n' "$1" "$(printf '─%.0s' $(seq 1 $((60 - ${#1}))))"; }

# GNU `cut -c` truncates bytes rather than Unicode code points even under a
# UTF-8 locale.  A boundary through `ℝ` or another multibyte character makes
# this script emit invalid UTF-8, which breaks the registered Python consumer.
utf8_head_chars() {
  python3 -c '
import sys

limit = int(sys.argv[1])
for line in sys.stdin:
    sys.stdout.write(line.rstrip("\n")[:limit] + "\n")
' "$1"
}

# ── 1. База знаний: убитое, ходы, журнал, досье ───────────────────────────────
SEARCHED+=("knowledge.db (kill/move/journal/dossier)")
if [ -f "$KB" ]; then
  OUT="$(./orchestrator/kb.py ask "$Q" 2>/dev/null)"
  RC=$?
  [ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("knowledge.db: kb.py ask failed (code $RC)")
  if ! printf '%s' "$OUT" | grep -q "^no hits"; then
    hdr "ЗНАНИЕ (kb.py ask)"
    printf '%s\n' "$OUT" | head -30
    HITS=$((HITS + 1))
  fi
else
  SEARCH_FAILURES+=("knowledge.db: required database missing")
fi

# ── 2. Флаги поиска: где уже искали, что оказалось ложным другом ──────────────
SEARCHED+=("search_session/search_term (kb.py flags)")
if [ -f "$KB" ]; then
  OUT="$(./orchestrator/kb.py flags "$Q" 2>/dev/null)"
  RC=$?
  [ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("knowledge.db: kb.py flags failed (code $RC)")
  OUT="$(printf '%s\n' "$OUT" | head -20)"
  if [ -n "$OUT" ] && ! printf '%s' "$OUT" | grep -qi "no \|нет "; then
    hdr "ФЛАГИ ПОИСКА — где уже искали"
    printf '%s\n' "$OUT"
    HITS=$((HITS + 1))
  fi
fi

# ── 2b. Каталог стыковок: кто ПОСТАВЛЯЕТ и кто ТРЕБУЕТ этот вход ─────────────
# capability.provides/requires — 1157 теорем с входами и выходами. До 2026-08-19
# таблицу не опрашивал ни один инструмент, и мост строился вокруг готового
# поставщика (sourceWeilOddTailAmbientCoercive_explicit, доказан 10.08).
SEARCHED+=("capability (provides/requires — каталог стыковок)")
if [ -f "$KB" ]; then
  OUT="$(python3 - "$KB" "$Q" <<'PY'
import sqlite3, sys

db, query = sys.argv[1:]
terms = [t for t in query.split() if t]
if not terms:
    raise SystemExit(0)
conn = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
like = lambda col: " OR ".join(f"lower({col}) LIKE ?" for _ in terms)
params = [f"%{t.lower()}%" for t in terms]

sup = conn.execute(
    f"select theorem, file, line, provides from capability "
    f"where {like('provides')} OR {like('theorem')} limit 5",
    params + params).fetchall()
dem = conn.execute(
    f"select theorem, requires from capability "
    f"where {like('requires')} AND requires <> '' limit 5",
    params).fetchall()
asm = conn.execute(
    f"select chain, step, requirement, status from assembly where {like('requirement')} limit 4",
    params).fetchall()
cex = conn.execute(
    f"select name, protects, breaks_how from counterexample where {like('protects')} limit 3",
    params).fetchall()

if sup:
    print("ПОСТАВЛЯЮТ (provides):")
    for t, f, l, p in sup:
        print(f"  {t}  {f}:{l}")
        print(f"    -> {p[:110]}")
if dem:
    print("ТРЕБУЮТ (requires):")
    for t, r in dem:
        print(f"  {t}  <-  {r[:100]}")
if asm:
    print("ШАГИ СБОРКИ (assembly):")
    for c, s, r, st in asm:
        print(f"  [{st}] {c} шаг {s}: {r[:90]}")
if cex:
    print("КОНТРПРИМЕРЫ (что охраняют):")
    for n, p, b in cex:
        print(f"  {n}: охраняет {(p or '')[:70]} · ломает {(b or '')[:60]}")
conn.close()
PY
)"
  RC=$?
  [ "$RC" -eq 0 ] || SEARCH_FAILURES+=("knowledge.db: capability/assembly/counterexample SQL failed (code $RC)")
  if [ -n "$OUT" ]; then
    hdr "СТЫКОВКИ — входы и выходы"
    printf '%s\n' "$OUT"
    HITS=$((HITS + 1))
  fi
fi

# ── 3. Литобзор: ссылки, карточки, PDF ───────────────────────────────────────
SEARCHED+=("litreview (REFERENCES.md · *_CARDS.md · references.bib · pdfs/)")
LIT="docs/routeB_bus/litreview"
if [ -d "$LIT" ]; then
  for required in REFERENCES.md references.bib ZOTERO_MASTER.md; do
    [ -r "$LIT/$required" ] || SEARCH_FAILURES+=("litreview: required file unreadable: $required")
  done
  [ -d "$LIT/pdfs" ] && [ -r "$LIT/pdfs" ] || SEARCH_FAILURES+=("litreview: required pdfs directory unreadable")
  OUT="$(rg -in --max-count 3 "$Q" "$LIT"/REFERENCES.md "$LIT"/*.bib "$LIT"/ZOTERO_MASTER.md 2>/dev/null)"
  RC=$?
  [ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("litreview: text search failed (code $RC)")
  OUT="$(printf '%s\n' "$OUT" | utf8_head_chars 200)"
  shopt -s nullglob
  CARD_FILES=("$LIT"/*_CARDS.md)
  shopt -u nullglob
  CARDS=""
  if [ "${#CARD_FILES[@]}" -gt 0 ]; then
    CARDS="$(rg -l -i "$Q" "${CARD_FILES[@]}" 2>/dev/null)"
    RC=$?
    [ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("litreview: card search failed (code $RC)")
    CARDS="$(printf '%s\n' "$CARDS" | sed 's#.*/##')"
  fi
  PDFS="$(ls "$LIT"/pdfs/ 2>/dev/null | rg -i "$(printf '%s' "$Q" | tr ' ' '|')" | head -5)"
  if [ -n "$OUT$CARDS$PDFS" ]; then
    hdr "ЛИТЕРАТУРА"
    [ -n "$OUT" ] && printf '%s\n' "$OUT" | head -8
    [ -n "$CARDS" ] && echo "  разобранные карточки: $(printf '%s' "$CARDS" | tr '\n' ' ')"
    [ -n "$PDFS" ] && echo "  PDF на диске: $(printf '%s' "$PDFS" | tr '\n' ' ')"
    HITS=$((HITS + 1))
  fi
else
  SEARCH_FAILURES+=("litreview: required root missing")
fi

# ── 4. Lean: что уже объявлено (metadata index, не kernel verdict) ────────────
SEARCHED+=("aristotle_proofs.db (Lean-декларации)")
if [ -f "$PROOFS" ]; then
  OUT="$(python3 - "$PROOFS" "$Q" <<'PY'
import sqlite3, sys

db, query = sys.argv[1:]
terms = [term for term in query.split() if term]
if not terms:
    raise SystemExit(0)
where = " OR ".join("l.name LIKE ? OR COALESCE(l.statement,'') LIKE ?" for _ in terms)
params = [value for term in terms for value in (f"%{term}%", f"%{term}%")]
conn = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
rows = conn.execute(
    f"""select distinct l.name, d.path
          from lemmas l join docs d on d.doc_id = l.doc_id
         where {where}
         order by case
                    when l.name = ? then 0
                    when l.name like ? then 1
                    else 2
                  end,
                  l.name
         limit 8""",
    params + [terms[0], f"%{terms[0]}%"],
)
for name, path in rows:
    print(f"{name}   {path}")
conn.close()
PY
)"
  RC=$?
  [ "$RC" -eq 0 ] || SEARCH_FAILURES+=("aristotle_proofs.db: declaration SQL failed (code $RC)")
  if [ -n "$OUT" ]; then
    hdr "LEAN — объявления в metadata index"
    printf '%s\n' "$OUT" | utf8_head_chars 150
    HITS=$((HITS + 1))
  fi
else
  SEARCH_FAILURES+=("aristotle_proofs.db: required database missing")
fi

# Живое дерево — на случай, если база отстала от диска
SEARCHED+=("Q3/Proofs/RouteB/*.lean (живое дерево)")
FIRST_TERM="${Q%% *}"
OUT="$(rg -in -F --max-count 2 -g '*.lean' "$FIRST_TERM" \
       q3.lean.aristotle/Q3/Proofs/RouteB/ \
       --glob '!PrimeCert/**' 2>/dev/null)"
RC=$?
[ -d q3.lean.aristotle/Q3/Proofs/RouteB/ ] || SEARCH_FAILURES+=("RouteB Lean: required root missing")
[ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("RouteB Lean: fixed-string search failed (code $RC)")
OUT="$(printf '%s\n' "$OUT" | utf8_head_chars 160 | head -6)"
if [ -n "$OUT" ]; then
  hdr "LEAN — на диске сейчас"
  printf '%s\n' "$OUT"
  HITS=$((HITS + 1))
fi

# ── 5. Спеки, карты и память развилок ─────────────────────────────────────────
SEARCHED+=("specs/maps + GENEALOGY/Progress_Log/RECORDING_RULES/GLOSSARY/TOOLS")
OUT="$(rg -l -i "$Q" specs_docs/ docs/routeB_bus/maps/ docs/Codex/ docs/CHAT_DIGESTS.md \
       docs/routeB_bus/MAP.md docs/GENEALOGY.md docs/Progress_Log.md \
       docs/RECORDING_RULES.md docs/GLOSSARY.md docs/cartographer/TOOLS.yaml \
       2>/dev/null)"
RC=$?
for required in specs_docs docs/routeB_bus/maps docs/Codex; do
  [ -d "$required" ] && [ -r "$required" ] || SEARCH_FAILURES+=("specs/maps: required root unreadable: $required")
done
for required in docs/CHAT_DIGESTS.md docs/routeB_bus/MAP.md docs/GENEALOGY.md docs/Progress_Log.md docs/RECORDING_RULES.md docs/GLOSSARY.md docs/cartographer/TOOLS.yaml; do
  [ -r "$required" ] || SEARCH_FAILURES+=("specs/maps: required file unreadable: $required")
done
[ "$RC" -eq 0 ] || [ "$RC" -eq 1 ] || SEARCH_FAILURES+=("specs/maps: search failed (code $RC)")
OUT="$(printf '%s\n' "$OUT" | head -12)"
if [ -n "$OUT" ]; then
  hdr "СПЕКИ, КАРТЫ И ПАМЯТЬ РАЗВИЛОК"
  printf '%s\n' "$OUT" | sed 's/^/  /'
  HITS=$((HITS + 1))
fi

# ── 6. Семантический индекс: один search; в deep ещё один vsearch ────────────
SEARCHED+=("q3_docs (bounded qmd search через research_oracle.py)")
ORACLE_PY="scripts/research_oracle.py"
OUT="$(python3 "$ORACLE_PY" query "$Q" -c q3_docs --mode search --budget-seconds 3 2>&1)"
RC=$?
if [ "$RC" -ne 0 ]; then
  SEARCH_FAILURES+=("q3_docs: qmd search failed (code $RC)")
elif printf '%s' "$OUT" | grep -q '"file"'; then
  hdr "СЕМАНТИЧЕСКИЙ ИНДЕКС q3_docs — search-кандидаты"
  printf '%s\n' "$OUT" | head -60
  HITS=$((HITS + 1))
fi

if [ "$DEEP" -eq 1 ]; then
  SEARCHED+=("q3_docs (bounded qmd vsearch через research_oracle.py)")
  OUT="$(python3 "$ORACLE_PY" query "$Q" -c q3_docs --mode vsearch --budget-seconds 15 2>&1)"
  RC=$?
  if [ "$RC" -ne 0 ]; then
    SEARCH_FAILURES+=("q3_docs: qmd vsearch failed (code $RC)")
  elif printf '%s' "$OUT" | grep -q '"file"'; then
    hdr "СЕМАНТИЧЕСКИЙ ИНДЕКС q3_docs — vsearch-кандидаты"
    printf '%s\n' "$OUT" | head -60
    HITS=$((HITS + 1))
  fi

  # Read-only validation only. Never refresh or write the index from ask.sh.
  FRESHNESS="$(python3 -c 'from orchestrator.spine import validate_semantic_index; validate_semantic_index(); print("PASS")' 2>&1)"
  RC=$?
  if [ "$RC" -ne 0 ] || [ "$FRESHNESS" != "PASS" ]; then
    SEARCH_FAILURES+=("q3_docs: semantic-index freshness validation failed")
  else
    SEARCHED+=("q3_docs semantic-index receipt/corpus/machine/live identity (fresh)")
  fi
fi

# Enabled external bases are part of the shelf, not an optional web-search layer.
# A local hit never licenses skipping them: otherwise "not found anywhere" has a
# hidden denominator and can be false on a registered base.
if [ -n "$EXTERNAL_RECEIPT" ]; then
  EXTERNAL_VALIDATE=(python3 scripts/research_oracle.py validate-external-receipt "$Q" "$EXTERNAL_RECEIPT")
  [ -n "$EXTERNAL_CANDIDATE" ] && EXTERNAL_VALIDATE+=(--candidate "$EXTERNAL_CANDIDATE")
  [ -n "$EXTERNAL_CANDIDATE_PROVENANCE" ] && EXTERNAL_VALIDATE+=(--candidate-provenance "$EXTERNAL_CANDIDATE_PROVENANCE")
  OUT="$("${EXTERNAL_VALIDATE[@]}" 2>&1)"
else
  EXTERNAL_BUDGET=3
  [ "$DEEP" -eq 1 ] && EXTERNAL_BUDGET=15
  OUT="$(python3 scripts/search_external_lean.py "$Q" --budget-seconds "$EXTERNAL_BUDGET" 2>&1)"
fi
RC=$?
if [ "$RC" -ne 0 ]; then
  SEARCHED+=("all enabled external Lean bases (INCOMPLETE registered search)")
  EXTERNAL_ERRORS="$(printf '%s' "$OUT" | python3 -c '
import json, sys
text = sys.stdin.read()
start = text.find("{")
if start >= 0:
    print("; ".join(json.loads(text[start:]).get("errors", [])))
' 2>/dev/null)"
  SEARCH_FAILURES+=("external Lean bases: registry query failed (code $RC): ${EXTERNAL_ERRORS:-unparsed registry error}")
else
  QUERIED_BASES="$(printf '%s' "$OUT" | python3 -c '
import json, sys
text = sys.stdin.read()
start = text.find("{")
data = json.loads(text[start:])
print(",".join(data.get("bases_queried", [])))
' 2>/dev/null)"
  SEARCHED+=("all enabled external Lean bases (${QUERIED_BASES:-none}; registered read-only search)")
  EXTERNAL_MATCH_COUNT="$(printf '%s' "$OUT" | python3 -c '
import json, sys
text = sys.stdin.read()
start = text.find("{")
print(len(json.loads(text[start:]).get("matches", [])))
' 2>/dev/null)"
  if [ "${EXTERNAL_MATCH_COUNT:-0}" -gt 0 ] 2>/dev/null; then
    hdr "ВНЕШНИЕ LEAN-БАЗЫ — точные/текстовые кандидаты"
    printf '%s\n' "$OUT" | head -100
    HITS=$((HITS + 1))
  fi
fi

# ── Итог ──────────────────────────────────────────────────────────────────────
printf '\n%s\n' "$(printf '━%.0s' $(seq 1 64))"
if [ "${#SEARCH_FAILURES[@]}" -gt 0 ]; then
  echo "ПОИСК НЕПОЛОН — отсутствие не установлено"
  echo
  for failure in "${SEARCH_FAILURES[@]}"; do echo "  · $failure"; done
  echo
  echo "ASK_STATUS: INCOMPLETE"
  exit 2
elif [ "$HITS" -eq 0 ]; then
  if [ "$DEEP" -eq 0 ]; then
    echo "Быстрый поиск завершён без кандидатов; для вывода о полке требуется --deep."
    echo "ASK_STATUS: INCOMPLETE_FAST_REQUIRES_DEEP"
    exit 2
  fi
  echo "Полная зарегистрированная полка завершена без кандидатов."
  echo "SHELF_ABSENCE — только отсутствие совпадения на проверенных полках; не глобальное семантическое отсутствие."
  echo "ASK_STATUS: SHELF_ABSENCE"
  exit 1
else
  echo "Найдено в $HITS хранилищах из ${#SEARCHED[@]}."
  echo
  echo "Просмотрены хранилища:"
  for s in "${SEARCHED[@]}"; do echo "  · $s"; done
  echo
  echo "Совпадения — кандидаты. Для вопроса «подходит ли теорема точной цели» запусти:"
  echo "  python3 scripts/supplier_preflight.py --query '$Q' --candidate <имя> --target <имя>"
  echo "ASK_STATUS: HITS"
  exit 0
fi
