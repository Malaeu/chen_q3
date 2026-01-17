#!/bin/bash
# Research Swarm Configuration

# === Paths ===
export SWARM_ROOT="/Users/emalam/Documents/GitHub/chen_q3/research_swarm"
export PROBLEM_FILE="/Users/emalam/Documents/GitHub/chen_q3/PROBLEM.md"
export PROJECT_ROOT="/Users/emalam/Documents/GitHub/chen_q3"
export LAKE_CACHE="/Users/emalam/.elan/toolchains/leanprover-lean4-v4.16.0/lib/lean4/library"

# === Worker Limits ===
export MAX_WORKERS=10
export ABANDON_THRESHOLD_HOURS=2

# === Directories ===
export INSIGHTS_NEW="${SWARM_ROOT}/insights/new"
export INSIGHTS_ACTIVE="${SWARM_ROOT}/insights/active"
export INSIGHTS_COMPLETED="${SWARM_ROOT}/insights/completed"
export WORKERS_DIR="${SWARM_ROOT}/workers"
export LOGS_DIR="${SWARM_ROOT}/logs"

# === Files ===
export REGISTRY_FILE="${SWARM_ROOT}/REGISTRY.md"
export WATCHER_LOG="${LOGS_DIR}/watcher.log"
export SPAWNER_LOG="${LOGS_DIR}/spawner.log"

# === Terminal ===
export PREFERRED_TERMINAL="Warp"  # Warp, iTerm, Terminal
export FALLBACK_TERMINAL="Terminal"

# === Sandbox ===
export SANDBOX_BASE="/tmp/research_swarm_sandboxes"
export USE_SHALLOW_CLONE=true
export LINK_LAKE_CACHE=true

# === Claude ===
# --dangerously-skip-permissions: bypass trust dialog and all permission checks
# Use this ONLY because sandboxes are isolated clones (no risk to main repo)
export BX_COMMAND="claude --dangerously-skip-permissions"

# === Timeouts ===
export SPAWN_TIMEOUT=30
export CLONE_TIMEOUT=120

# Helper function to get active worker count
get_active_workers() {
    find "${WORKERS_DIR}" -name "status.json" -exec grep -l '"status": "active"' {} \; 2>/dev/null | wc -l | tr -d ' '
}

# Helper function to check if we can spawn more workers
can_spawn_worker() {
    local count
    count=$(get_active_workers)
    [[ $count -lt $MAX_WORKERS ]]
}
