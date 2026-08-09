#!/usr/bin/env bash
# ask.sh — ОДИН вход в накопленное знание. Спрашивать ДО внешнего поиска и ДО создания чего-либо.
#
# Зачем он есть. За 6–7 августа трижды подряд повторилось одно: инструмент существовал,
# знание лежало внутри, никто не посмотрел.
#   · H2aPenaltyCoercivity.lean — теорема с явной щелью, не упомянута в MAP.md;
#   · kb_migrate_verdicts.py — мигратор написан, при закрытии цели не дёргается;
#   · Groskin 2607.02828 — PDF скачан, в bib, помечен «HAVE ✓ FLAG subagent» — а мы пошли
#     искать его в интернете.
# Причина не в забывчивости: хранилищ четыре, у каждого своя команда, и спросив одно, легко
# решить, что нигде нет. Здесь спрашиваются все сразу, и отсутствие печатается явно.
#
# Строго read-only.

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")" || exit 2

if [ $# -eq 0 ]; then
  echo "usage: ./ask.sh <термин> [ещё термины]"
  echo "       ищет разом: knowledge.db · litreview · Lean-декларации · specs_docs · docs"
  exit 2
fi

Q="$*"
KB="q3.lean.aristotle/aristotle_db/knowledge.db"
PROOFS="q3.lean.aristotle/aristotle_db/aristotle_proofs.db"
HITS=0
SEARCHED=()

hdr() { printf '\n── %s %s\n' "$1" "$(printf '─%.0s' $(seq 1 $((60 - ${#1}))))"; }

# ── 1. База знаний: убитое, ходы, журнал, досье ───────────────────────────────
SEARCHED+=("knowledge.db (kill/move/journal/dossier)")
if [ -f "$KB" ]; then
  OUT="$(./orchestrator/kb.py ask "$Q" 2>/dev/null)"
  if ! printf '%s' "$OUT" | grep -q "^no hits"; then
    hdr "ЗНАНИЕ (kb.py ask)"
    printf '%s\n' "$OUT" | head -30
    HITS=$((HITS + 1))
  fi
fi

# ── 2. Флаги поиска: где уже искали, что оказалось ложным другом ──────────────
SEARCHED+=("search_session/search_term (kb.py flags)")
if [ -f "$KB" ]; then
  OUT="$(./orchestrator/kb.py flags "$Q" 2>/dev/null | head -20)"
  if [ -n "$OUT" ] && ! printf '%s' "$OUT" | grep -qi "no \|нет "; then
    hdr "ФЛАГИ ПОИСКА — где уже искали"
    printf '%s\n' "$OUT"
    HITS=$((HITS + 1))
  fi
fi

# ── 3. Литобзор: ссылки, карточки, PDF ───────────────────────────────────────
SEARCHED+=("litreview (REFERENCES.md · *_CARDS.md · references.bib · pdfs/)")
LIT="docs/routeB_bus/litreview"
if [ -d "$LIT" ]; then
  OUT="$(rg -in --max-count 3 "$Q" "$LIT"/REFERENCES.md "$LIT"/*.bib "$LIT"/ZOTERO_MASTER.md 2>/dev/null | cut -c1-200)"
  CARDS="$(rg -l -i "$Q" "$LIT"/*_CARDS.md 2>/dev/null | sed 's#.*/##')"
  PDFS="$(ls "$LIT"/pdfs/ 2>/dev/null | rg -i "$(printf '%s' "$Q" | tr ' ' '|')" | head -5)"
  if [ -n "$OUT$CARDS$PDFS" ]; then
    hdr "ЛИТЕРАТУРА"
    [ -n "$OUT" ] && printf '%s\n' "$OUT" | head -8
    [ -n "$CARDS" ] && echo "  разобранные карточки: $(printf '%s' "$CARDS" | tr '\n' ' ')"
    [ -n "$PDFS" ] && echo "  PDF на диске: $(printf '%s' "$PDFS" | tr '\n' ' ')"
    HITS=$((HITS + 1))
  fi
fi

# ── 4. Lean: что уже доказано ─────────────────────────────────────────────────
SEARCHED+=("aristotle_proofs.db (Lean-декларации)")
if [ -f "$PROOFS" ]; then
  OUT="$(sqlite3 "file:$PROOFS?mode=ro" \
    "SELECT name || '   ' || COALESCE(file,'') FROM lemmas
     WHERE name LIKE '%${Q// /%}%' LIMIT 8;" 2>/dev/null)"
  if [ -n "$OUT" ]; then
    hdr "LEAN — уже доказано"
    printf '%s\n' "$OUT" | cut -c1-150
    HITS=$((HITS + 1))
  fi
fi

# Живое дерево — на случай, если база отстала от диска
SEARCHED+=("Q3/Proofs/RouteB/*.lean (живое дерево)")
OUT="$(rg -in --max-count 2 -g '*.lean' "^(theorem|def|noncomputable def) .*${Q// /.*}" \
       q3.lean.aristotle/Q3/Proofs/ 2>/dev/null | cut -c1-160 | head -6)"
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
       2>/dev/null | head -12)"
if [ -n "$OUT" ]; then
  hdr "СПЕКИ, КАРТЫ И ПАМЯТЬ РАЗВИЛОК"
  printf '%s\n' "$OUT" | sed 's/^/  /'
  HITS=$((HITS + 1))
fi

# ── Итог ──────────────────────────────────────────────────────────────────────
printf '\n%s\n' "$(printf '━%.0s' $(seq 1 64))"
if [ "$HITS" -eq 0 ]; then
  echo "НЕ НАЙДЕНО НИГДЕ — '$Q'"
  echo
  echo "Просмотрены все хранилища:"
  for s in "${SEARCHED[@]}"; do echo "  · $s"; done
  echo
  echo "Только теперь внешний поиск оправдан. Что найдёшь — занеси обратно:"
  echo "  литература → docs/routeB_bus/litreview/ (REFERENCES.md + references.bib + pdfs/)"
  echo "  знание     → ./orchestrator/kb.py add …"
  echo "  слова поиска → блок SEARCH_FLAGS в шапке answer.md"
  exit 1
else
  echo "Найдено в $HITS хранилищах из ${#SEARCHED[@]}. Внешний поиск, скорее всего, не нужен."
  exit 0
fi
