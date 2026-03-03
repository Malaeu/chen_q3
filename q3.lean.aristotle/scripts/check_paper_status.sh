#!/bin/bash
# Verify that paper Lean status snapshot is in sync with the live Lean chain.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
REPO_DIR="$(dirname "$PROJECT_DIR")"
SNAPSHOT_PATH="$REPO_DIR/paper/appendix/lean_status_snapshot.tex"

cd "$PROJECT_DIR"

python3 scripts/export_paper_status.py --out "$SNAPSHOT_PATH" --check

if ! rg -n "appendix/lean_status_snapshot" "$REPO_DIR/paper/main.tex" >/dev/null; then
  echo "paper/main.tex does not include appendix/lean_status_snapshot" >&2
  exit 1
fi

if ! head -n 1 "$SNAPSHOT_PATH" | rg -F "AUTO-GENERATED FILE" >/dev/null; then
  echo "snapshot header missing auto-generated marker" >&2
  exit 1
fi

echo "paper status snapshot check: OK"
