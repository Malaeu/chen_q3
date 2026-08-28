#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git -C "${Q3_REPO:-$PWD}" rev-parse --show-toplevel)"
cd "$ROOT"
uv run --locked --extra dev python orchestrator/repository_topology_decision.py check
uv run --locked --extra dev pytest -q orchestrator/tests/test_repository_topology_decision.py
uv run --locked --extra dev python orchestrator/repository_topology_decision.py plants
