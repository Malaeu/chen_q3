#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
cd "$ROOT"
uv run --locked --extra dev python orchestrator/semantic_quarantine_history_successor.py check
uv run --locked --extra dev pytest -q orchestrator/tests/test_semantic_quarantine_history_successor.py
uv run --locked --extra dev python orchestrator/semantic_quarantine_history_successor.py plants
