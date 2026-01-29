#!/bin/sh
set -e

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
PACK="$ROOT/full/q3.lean.aristotle/PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md"
SCRIPT="$ROOT/scripts/build_proshka_brief.py"

python3 "$SCRIPT" --mode full --max-file-lines 2000 \
  --include-glob 'full/q3.lean.aristotle/ACTIVE/spec_*.md' \
  --include-glob 'docs/Как работают модели типа Аристотель и их тренировка/*.md' \
  --include-file 'full/q3.lean.aristotle/aristotle_input/continuous_P_A_shift_tcritical.md' \
  --out "$PACK"

printf 'Updated: %s\n' "$PACK"
