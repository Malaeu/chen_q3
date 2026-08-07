#!/usr/bin/env bash
# paper.sh — затянуть публикацию ОДНОЙ командой: PDF + метаданные + bib + Zotero + реестр.
#
#   ./paper.sh 2607.02828                  arXiv id
#   ./paper.sh 10.5281/zenodo.20427500     DOI (Zenodo, Crossref, DataCite)
#   ./paper.sh https://.../paper.pdf --id MYKEY --title "..." --author "..."   прямой URL
#
# Что делает автомат: скачивает PDF, тянет метаданные, дописывает references.bib, создаёт
# item в Zotero (коллекция Q3_frontier_2026) и заводит строку в REFERENCES.md со статусом
# **NEEDS_CARDS**.
#
# Чего автомат НЕ делает: карточку разбора. Она — чтение и суждение («этот результат не наша
# половинка, потому что его T не наш N»), автомат выдаст пересказ абстракта, и это хуже
# отсутствия: создаст видимость, что работа разобрана.  Поэтому статус NEEDS_CARDS светится
# в поясе инструментов при каждом старте, пока карточка не написана.
#
# Zotero не отвечает — не беда: PDF и bib всё равно на месте, в реестре пометка.

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")" || exit 2

LIT="docs/routeB_bus/litreview"
PDFS="$LIT/pdfs"
BIB="$LIT/references.bib"
REG="$LIT/REFERENCES.md"
ZOT_COLLECTION="8RF2S7TI"   # Q3_frontier_2026

[ $# -ge 1 ] || { echo "usage: ./paper.sh <arxiv-id | doi | url> [--id KEY] [--title T] [--author A]"; exit 2; }

SRC="$1"; shift
KEY=""; TITLE=""; AUTHOR=""; YEAR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --id) KEY="$2"; shift 2;;
    --title) TITLE="$2"; shift 2;;
    --author) AUTHOR="$2"; shift 2;;
    *) shift;;
  esac
done

# ── определить тип источника и вытянуть метаданные ────────────────────────────
ARXIV=""; DOI=""; URL=""
if [[ "$SRC" =~ ^[0-9]{4}\.[0-9]{4,5}(v[0-9]+)?$ ]]; then
  ARXIV="$SRC"
elif [[ "$SRC" =~ ^10\. ]]; then
  DOI="$SRC"
elif [[ "$SRC" =~ ^https?:// ]]; then
  URL="$SRC"
  [[ "$SRC" =~ arxiv\.org/(abs|pdf)/([0-9]{4}\.[0-9]{4,5}) ]] && ARXIV="${BASH_REMATCH[2]}"
  [[ "$SRC" =~ zenodo\.org/records?/([0-9]+) ]] && DOI="10.5281/zenodo.${BASH_REMATCH[1]}"
else
  echo "не распознан источник: $SRC"; exit 2
fi

META="$(python3 - "$ARXIV" "$DOI" <<'PY'
import json, sys, urllib.request, re
arxiv, doi = sys.argv[1], sys.argv[2]
out = {"title": "", "authors": [], "year": "", "doi": doi, "arxiv": arxiv, "abstract": ""}

def fetch(u, hdr=None):
    r = urllib.request.Request(u, headers=hdr or {"User-Agent": "q3-litreview/1.0"})
    return urllib.request.urlopen(r, timeout=25).read().decode("utf-8", "replace")

try:
    if arxiv:
        x = fetch(f"http://export.arxiv.org/api/query?id_list={arxiv}")
        t = re.search(r"<entry>.*?<title>(.*?)</title>", x, re.S)
        out["title"] = " ".join(t.group(1).split()) if t else ""
        out["authors"] = [" ".join(a.split()) for a in re.findall(r"<author>\s*<name>(.*?)</name>", x, re.S)]
        p = re.search(r"<published>(\d{4})", x)
        out["year"] = p.group(1) if p else ""
        s = re.search(r"<summary>(.*?)</summary>", x, re.S)
        out["abstract"] = " ".join(s.group(1).split())[:600] if s else ""
        d = re.search(r"<arxiv:doi[^>]*>(.*?)</arxiv:doi>", x, re.S)
        if d and not out["doi"]:
            out["doi"] = d.group(1).strip()
    elif doi:
        # DataCite покрывает Zenodo, Crossref — журналы; пробуем оба
        for u, kind in ((f"https://api.datacite.org/dois/{doi}", "dc"),
                        (f"https://api.crossref.org/works/{doi}", "cr")):
            try:
                j = json.loads(fetch(u, {"Accept": "application/json",
                                         "User-Agent": "q3-litreview/1.0"}))
            except Exception:
                continue
            if kind == "dc":
                a = j["data"]["attributes"]
                out["title"] = (a.get("titles") or [{}])[0].get("title", "")
                out["authors"] = [c.get("name", "") for c in (a.get("creators") or [])]
                out["year"] = str(a.get("publicationYear", ""))
                out["abstract"] = " ".join((a.get("descriptions") or [{}])[0]
                                           .get("description", "").split())[:600]
            else:
                m = j["message"]
                out["title"] = (m.get("title") or [""])[0]
                out["authors"] = [f"{x.get('family','')}, {x.get('given','')}".strip(", ")
                                  for x in (m.get("author") or [])]
                dp = m.get("issued", {}).get("date-parts", [[""]])[0]
                out["year"] = str(dp[0]) if dp else ""
            if out["title"]:
                break
except Exception as e:
    out["error"] = repr(e)
print(json.dumps(out, ensure_ascii=False))
PY
)"

get() { printf '%s' "$META" | python3 -c "import json,sys;d=json.load(sys.stdin);v=d.get('$1','');print(' and '.join(v) if isinstance(v,list) else v)"; }
[ -z "$TITLE" ]  && TITLE="$(get title)"
[ -z "$AUTHOR" ] && AUTHOR="$(get authors)"
YEAR="$(get year)"
[ -z "$DOI" ] && DOI="$(get doi)"

if [ -z "$TITLE" ]; then
  echo "⚠ метаданные не получены — задай --title и --author вручную"
  printf '  ответ: %s\n' "$(printf '%s' "$META" | head -c 300)"
  exit 2
fi

# ── скачать PDF ───────────────────────────────────────────────────────────────
if [ -n "$ARXIV" ]; then
  FNAME="${ARXIV}.pdf"; DL="https://arxiv.org/pdf/${ARXIV}"
elif [ -n "$DOI" ]; then
  SLUG="$(printf '%s' "$AUTHOR" | cut -d, -f1 | tr '[:upper:] ' '[:lower:]_')_$(printf '%s' "$DOI" | tr '/.' '__')"
  FNAME="${SLUG}.pdf"
  if [[ "$DOI" =~ zenodo\.([0-9]+) ]]; then
    REC="${BASH_REMATCH[1]}"
    DL="$(curl -sL "https://zenodo.org/api/records/${REC}" | python3 -c "
import json,sys
try:
    for f in json.load(sys.stdin).get('files',[]):
        if f['key'].lower().endswith('.pdf'): print(f['links']['self']); break
except Exception: pass")"
  else
    DL=""
  fi
else
  FNAME="$(basename "${URL%%\?*}")"; DL="$URL"
fi

mkdir -p "$PDFS"
if [ -f "$PDFS/$FNAME" ]; then
  echo "PDF уже есть: $PDFS/$FNAME"
elif [ -n "$DL" ]; then
  if curl -sL --max-time 120 -o "$PDFS/$FNAME" "$DL" && [ "$(file -b --mime-type "$PDFS/$FNAME")" = "application/pdf" ]; then
    echo "✓ PDF: $PDFS/$FNAME ($(stat -c%s "$PDFS/$FNAME") Б)"
  else
    rm -f "$PDFS/$FNAME"; FNAME=""
    echo "⚠ PDF не скачан (пейволл или нет прямой ссылки) — занеси вручную"
  fi
else
  FNAME=""; echo "⚠ прямая ссылка на PDF не выведена — занеси вручную"
fi

# ── ключ цитирования ──────────────────────────────────────────────────────────
if [ -z "$KEY" ]; then
  LAST="$(printf '%s' "$AUTHOR" | cut -d, -f1 | tr -cd '[:alpha:]' | tr '[:lower:]' '[:upper:]')"
  KEY="${LAST:-REF}-${YEAR:-2026}"
  n=1; while grep -q "{$KEY," "$BIB" 2>/dev/null; do KEY="${LAST}-${YEAR}-$((++n))"; done
fi

# ── references.bib ────────────────────────────────────────────────────────────
if grep -q "{$KEY," "$BIB" 2>/dev/null; then
  echo "bib: $KEY уже есть"
else
  { echo; echo "@misc{$KEY,"
    echo "  author = {$AUTHOR},"
    echo "  title  = {$TITLE},"
    [ -n "$YEAR" ]  && echo "  year   = {$YEAR},"
    [ -n "$ARXIV" ] && echo "  eprint = {$ARXIV},"
    [ -n "$DOI" ]   && echo "  doi    = {$DOI},"
    echo "  note   = {added by paper.sh $(date +%F)}"
    echo "}"; } >> "$BIB"
  echo "✓ bib: $KEY"
fi

# ── Zotero ────────────────────────────────────────────────────────────────────
# shellcheck disable=SC1090
source ~/.api_keys 2>/dev/null
if [ -n "${ZOTERO_API_KEY:-}" ]; then
  ZRES="$(python3 - "$TITLE" "$AUTHOR" "$YEAR" "$DOI" "$ARXIV" "$ZOT_COLLECTION" <<'PY'
import json, os, sys, urllib.request
title, author, year, doi, arxiv, coll = sys.argv[1:7]
key, lib, typ = (os.environ.get(k, "") for k in
                 ("ZOTERO_API_KEY", "ZOTERO_LIBRARY_ID", "ZOTERO_LIBRARY_TYPE"))
if not (key and lib):
    print("no-key"); raise SystemExit
creators = []
for a in author.split(" and "):
    a = a.strip()
    if not a: continue
    if "," in a:
        f, g = [x.strip() for x in a.split(",", 1)]
    else:
        parts = a.split(); f, g = parts[-1], " ".join(parts[:-1])
    creators.append({"creatorType": "author", "firstName": g, "lastName": f})
item = {"itemType": "preprint", "title": title, "creators": creators,
        "date": year, "DOI": doi, "repository": "arXiv" if arxiv else "",
        "archiveID": f"arXiv:{arxiv}" if arxiv else "",
        "collections": [coll] if coll else [],
        "extra": "added by paper.sh"}
req = urllib.request.Request(
    f"https://api.zotero.org/{typ}s/{lib}/items",
    data=json.dumps([item]).encode(),
    headers={"Zotero-API-Key": key, "Content-Type": "application/json",
             "Zotero-API-Version": "3"}, method="POST")
try:
    r = json.loads(urllib.request.urlopen(req, timeout=30).read().decode())
    ok = r.get("successful", {})
    print("ok:" + (list(ok.values())[0]["key"] if ok else "?") if ok else "fail:" + json.dumps(r.get("failed", {}))[:120])
except Exception as e:
    print("fail:" + repr(e)[:120])
PY
)"
  case "$ZRES" in
    ok:*)   echo "✓ Zotero: item ${ZRES#ok:} в коллекции Q3_frontier_2026";;
    no-key) echo "⚠ Zotero: ключа нет — пропущено";;
    *)      echo "⚠ Zotero: не создано — $ZRES";;
  esac
else
  echo "⚠ Zotero: ~/.api_keys не подхватился — пропущено"
fi

# ── реестр со статусом NEEDS_CARDS ────────────────────────────────────────────
if ! grep -q "$KEY" "$REG" 2>/dev/null; then
  printf '| %s | %s | %s | %s | **NEEDS_CARDS** | затянуто paper.sh %s — карточка не написана |\n' \
    "$KEY" "$(printf '%s' "$AUTHOR" | cut -d' ' -f1-4), \"$TITLE\"" \
    "${ARXIV:+arXiv:$ARXIV}${DOI:+ doi:$DOI}" \
    "${FNAME:+\`pdfs/$FNAME\`}" "$(date +%F)" >> "$REG"
  echo "✓ реестр: строка со статусом NEEDS_CARDS"
fi

cat <<EOF

────────────────────────────────────────────────────────────────
Механика сделана. Осталось суждение — его автомат не заменит:

  1. прочитать PDF   → Read $PDFS/$FNAME
  2. написать карточку → $LIT/$(printf '%s' "$KEY" | tr -d -- '-' | cut -c1-12)_USAGE_CARDS.md
     по стандарту: что ДОСЛОВНО сказано · что это даёт НАМ и чего НЕ даёт ·
     соответствие переменных с нашими объектами · что не прочитано
  3. поменять NEEDS_CARDS на HAVE в $REG

Пока стоит NEEDS_CARDS — это видно в поясе при каждом старте.
EOF
