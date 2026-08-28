#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
cd "$ROOT"
PHASE="${1:-preflight}"
if [[ "$PHASE" == "preflight" ]]; then
  uv run --locked --extra dev python orchestrator/root_archive_moves.py check-preflight
elif [[ "$PHASE" == "postmove" ]]; then
  uv run --locked --extra dev python orchestrator/root_archive_moves.py check-postmove
else
  echo "usage: $0 [preflight|postmove]" >&2
  exit 2
fi
uv run --locked --extra dev pytest -q \
  orchestrator/tests/test_root_archive_moves.py \
  orchestrator/tests/test_root_artifact_classification.py \
  orchestrator/tests/test_portability_manifest.py
uv run --locked --extra dev python orchestrator/root_artifact_classification.py check
uv run --locked --extra dev python orchestrator/root_artifact_classification.py plants
uv run --locked --extra dev python orchestrator/portability_manifest.py check
uv run --locked --extra dev python orchestrator/portability_manifest.py plants
