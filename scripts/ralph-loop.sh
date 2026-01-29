#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-build}"
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
PROMPT_DIR="$ROOT/scripts/ralph"
PLAN_PROMPT="$PROMPT_DIR/plan.md"
BUILD_PROMPT="$PROMPT_DIR/build.md"
PLAN_FILE="$ROOT/IMPLEMENTATION_PLAN.md"

case "$MODE" in
  plan)
    PROMPT="$PLAN_PROMPT"
    ;;
  build)
    PROMPT="$BUILD_PROMPT"
    ;;
  *)
    echo "usage: $0 [plan|build]" >&2
    exit 2
    ;;
esac

if [[ ! -f "$PROMPT" ]]; then
  echo "missing prompt: $PROMPT" >&2
  exit 1
fi

AGENT_CMD="${RALPH_AGENT_CMD:-codex}"
if ! command -v "$AGENT_CMD" >/dev/null 2>&1; then
  echo "agent command not found: $AGENT_CMD" >&2
  echo "set RALPH_AGENT_CMD to your agent CLI (e.g., codex)" >&2
  exit 1
fi

# Ensure plan file exists in plan mode.
if [[ "$MODE" == "plan" && ! -f "$PLAN_FILE" ]]; then
  cat <<'PLAN' > "$PLAN_FILE"
# Implementation Plan

Status: pending

## Tasks

- [ ] TODO: Generate plan via scripts/ralph-loop.sh plan

PLAN
fi

if [[ "$AGENT_CMD" == "codex" ]]; then
  # codex exec reads prompt from stdin when not provided as an argument
  exec codex exec -C "$ROOT" < "$PROMPT"
else
  exec "$AGENT_CMD" -p "$PROMPT"
fi
