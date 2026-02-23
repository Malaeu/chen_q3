#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[audit] Root: $ROOT_DIR"
echo "[audit] Scope: Q3/**/*.lean excluding Archive/Clean/debug + non-production integrated bundles (ProofsIntegrated, node_spacing*, off_diag_exp_sum*)"

LEAN_LIST_FILE="$(mktemp)"
find Q3 -type f -name "*.lean" \
  ! -path "Q3/Archive/*" \
  ! -path "Q3/Clean/*" \
  ! -name "*_debug.lean" \
  ! -path "Q3/ProofsIntegrated.lean" \
  ! -path "Q3/Proofs/node_spacing*" \
  ! -path "Q3/Proofs/off_diag_exp_sum*" \
  ! -path "Q3/Proofs/PrimeCert/*" \
  | sort > "$LEAN_LIST_FILE"

# Re-include the PrimeCert files that are part of the active mainline contract/gate.
for f in \
  "Q3/Proofs/PrimeCert/Bmin_1826.lean" \
  "Q3/Proofs/PrimeCert/PrimeCert_Margin_Gate.lean" \
  "Q3/Proofs/PrimeCert/PrimeCert_Margin_PathB.lean"
do
  if [ -f "$f" ]; then
    echo "$f" >> "$LEAN_LIST_FILE"
  fi
done

sort -u "$LEAN_LIST_FILE" -o "$LEAN_LIST_FILE"

LEAN_FILE_COUNT="$(wc -l < "$LEAN_LIST_FILE" | tr -d '[:space:]')"
if [ "$LEAN_FILE_COUNT" = "0" ]; then
  echo "[audit] FAIL: no Lean files found in active Q3 scope"
  rm -f "$LEAN_LIST_FILE"
  exit 1
fi

echo "[audit] Files to check: $LEAN_FILE_COUNT"

while IFS= read -r file; do
  echo "[audit] checking: $file"
  module="${file%.lean}"
  module="${module//\//.}"

  lake build "$module" >/tmp/audit_nosorry_active_q3_build.log 2>&1 || {
    echo "[audit] FAIL: compile/build error in $file ($module)"
    cat /tmp/audit_nosorry_active_q3_build.log
    rm -f "$LEAN_LIST_FILE"
    exit 1
  }

  lake env lean -EhasSorry "$file" >/tmp/audit_nosorry_active_q3_nosorry.log 2>&1 || {
    echo "[audit] FAIL: hasSorry (or compile error) in $file ($module)"
    cat /tmp/audit_nosorry_active_q3_nosorry.log
    rm -f "$LEAN_LIST_FILE"
    exit 1
  }
done < "$LEAN_LIST_FILE"

rm -f "$LEAN_LIST_FILE"

echo "[audit] PASS: no sorry/admit placeholders in active Q3 scope"
