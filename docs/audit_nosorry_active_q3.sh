#!/usr/bin/env bash
# Strict audit: fail if any active Q3 file contains `sorry` (Lean diagnostic `hasSorry`).
#
# Usage:
#   cd q3.lean.aristotle
#   ./scripts/audit_nosorry_active_q3.sh
#
# Optional:
#   ./scripts/audit_nosorry_active_q3.sh Q3   # set root explicitly

set -euo pipefail

ROOT="${1:-Q3}"

if [[ ! -d "$ROOT" ]]; then
  echo "[audit] root directory not found: $ROOT" >&2
  exit 2
fi

# Collect active Lean files (exclude Archive/Clean).
mapfile -d '' FILES < <(
  find "$ROOT" -type f -name '*.lean' \
    ! -path "$ROOT/Archive/*" \
    ! -path "$ROOT/Clean/*" \
    -print0 | sort -z
)

TOTAL=${#FILES[@]}
if [[ $TOTAL -eq 0 ]]; then
  echo "[audit] no .lean files found under $ROOT" >&2
  exit 2
fi

echo "[audit] Checking $TOTAL files under $ROOT (excluding $ROOT/Archive and $ROOT/Clean)"

i=0
for f in "${FILES[@]}"; do
  i=$((i+1))
  echo "[audit] ($i/$TOTAL) $f"
  # -EhasSorry upgrades the `hasSorry` warning to an error.
  lake env lean -EhasSorry "$f"
done

echo "[audit] PASS: no `sorry` in active Q3 (Lean `hasSorry` clean)."
