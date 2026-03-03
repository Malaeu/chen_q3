#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
Q3_DIR="$ROOT/Q3"
MODE="all"
LIMIT=""
SHOW_LEAN="${Q3_AUDIT_SHOW_LEAN:-0}"

if [[ ! -d "$Q3_DIR" ]]; then
  echo "[audit] Q3 directory not found: $Q3_DIR" >&2
  exit 1
fi

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      cat <<'EOF'
Usage: ./scripts/audit_nosorry_active_q3.sh [--changed] [--limit N]

Runs hard no-sorry audit on active Q3 files:
- excludes Q3/Archive and Q3/Clean
- uses `lake lean <file> -- -Dwarn.sorry=true -EhasSorry`
- fails on first hasSorry occurrence

Modes:
- default: scans all active Q3 files
- `--changed`: scans only changed/untracked active Q3 Lean files

Options:
- `--limit N`: check only first N selected files (debug/quick mode)
- `Q3_AUDIT_SHOW_LEAN=1`: stream full Lean output (default is quiet; prints only on failure)

At the end, reports any `exact?` occurrences in active Q3.
EOF
      exit 0
      ;;
    --changed)
      MODE="changed"
      shift
      ;;
    --limit)
      if [[ $# -lt 2 ]]; then
        echo "[audit] --limit requires a numeric argument" >&2
        exit 1
      fi
      LIMIT="$2"
      if ! [[ "$LIMIT" =~ ^[0-9]+$ ]]; then
        echo "[audit] --limit must be a non-negative integer" >&2
        exit 1
      fi
      shift 2
      ;;
    *)
      echo "[audit] unknown option: $1" >&2
      echo "[audit] run --help for usage" >&2
      exit 1
      ;;
  esac
done

cd "$ROOT"

if [[ "$MODE" == "changed" ]]; then
  echo "[audit] collecting CHANGED active Q3 files (excluding Archive/Clean)..."
  mapfile -t CHANGED_TRACKED < <(git diff --name-only --diff-filter=ACMRTUXB HEAD -- 'Q3/**/*.lean' || true)
  mapfile -t CHANGED_UNTRACKED < <(git ls-files --others --exclude-standard -- 'Q3/**/*.lean' || true)
  mapfile -t CANDIDATES < <(printf '%s\n' "${CHANGED_TRACKED[@]}" "${CHANGED_UNTRACKED[@]}" | awk 'NF' | sort -u)
  FILES=()
  for rel in "${CANDIDATES[@]}"; do
    [[ "$rel" == Q3/Archive/* ]] && continue
    [[ "$rel" == Q3/Clean/* ]] && continue
    abs="$ROOT/$rel"
    [[ -f "$abs" ]] || continue
    FILES+=("$abs")
  done
else
  echo "[audit] collecting ALL active Q3 files (excluding Archive/Clean)..."
  mapfile -d '' FILES < <(
    find "$Q3_DIR" -type f -name '*.lean' \
      ! -path "$Q3_DIR/Archive/*" \
      ! -path "$Q3_DIR/Clean/*" \
      -print0 | sort -z
  )
fi

if [[ -n "$LIMIT" ]]; then
  echo "[audit] applying limit: $LIMIT"
  if (( LIMIT < ${#FILES[@]} )); then
    FILES=("${FILES[@]:0:LIMIT}")
  fi
fi

echo "[audit] files: ${#FILES[@]}"
echo

if [[ "${#FILES[@]}" -eq 0 ]]; then
  echo "[audit] nothing to check"
  exit 0
fi

FAIL=0
LEAN_LOG="$(mktemp)"
cleanup() {
  rm -f "$LEAN_LOG" "${EXACT_TMP:-}"
}
trap cleanup EXIT

for abs in "${FILES[@]}"; do
  rel="${abs#$ROOT/}"
  echo "[audit] checking: $rel"
  if [[ "$SHOW_LEAN" == "1" ]]; then
    if ! lake lean "$rel" -- -Dwarn.sorry=true -EhasSorry; then
      echo
      echo "[audit] FAIL at: $rel"
      FAIL=1
      break
    fi
  else
    if ! lake lean "$rel" -- -Dwarn.sorry=true -EhasSorry >"$LEAN_LOG" 2>&1; then
      echo
      echo "[audit] FAIL at: $rel"
      echo "[audit] last 120 lines:"
      tail -n 120 "$LEAN_LOG"
      FAIL=1
      break
    fi
  fi
done

echo
if [[ "$FAIL" -ne 0 ]]; then
  echo "[audit] FAIL: `hasSorry` detected in active Q3."
  exit 1
fi

echo "[audit] PASS: no 'sorry' in active Q3 (hasSorry treated as error)."

echo
echo "[audit] scanning active Q3 for exact?"
EXACT_TMP="$(mktemp)"
if rg -n --pcre2 "^(?!\\s*--).*\\bexact\\?" "$Q3_DIR" --type=lean --glob '!**/Archive/**' --glob '!**/Clean/**' > "$EXACT_TMP"; then
  echo "[audit] WARNING: found exact? in active Q3"
  sed -n '1,60p' "$EXACT_TMP"
  echo "[audit] total exact? lines: $(wc -l < "$EXACT_TMP")"
else
  echo "[audit] OK: no exact? found in active Q3"
fi
