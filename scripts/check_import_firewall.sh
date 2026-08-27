#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

uv run --locked --extra dev python orchestrator/import_firewall.py check
uv run --locked --extra dev python orchestrator/import_firewall.py plants
