#!/bin/bash
# Research Swarm Spawner — creates sandbox and opens terminal

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/../research_swarm/config.sh"

INSIGHT_ID="$1"

if [[ -z "$INSIGHT_ID" ]]; then
    echo "Usage: $0 <insight_id>"
    exit 1
fi

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] [spawner:$INSIGHT_ID] $*" >> "${SPAWNER_LOG}"
}

log "Starting spawn for insight: $INSIGHT_ID"

# === Create sandbox directory ===
SANDBOX_DIR="${SANDBOX_BASE}/${INSIGHT_ID}"
mkdir -p "${SANDBOX_DIR}"

# === Create worker directory ===
WORKER_DIR="${WORKERS_DIR}/${INSIGHT_ID}"
mkdir -p "${WORKER_DIR}"

# === Write initial status ===
cat > "${WORKER_DIR}/status.json" << EOF
{
    "insight_id": "${INSIGHT_ID}",
    "status": "spawning",
    "started_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "sandbox_path": "${SANDBOX_DIR}",
    "terminal": "${PREFERRED_TERMINAL}"
}
EOF

# === Clone repository (without .lake to save space) ===
log "Creating sandbox clone..."
LEAN_PROJECT="${PROJECT_ROOT}/full/q3.lean.aristotle"
SANDBOX_LEAN="${SANDBOX_DIR}/repo/full/q3.lean.aristotle"

if [[ "$USE_SHALLOW_CLONE" == "true" ]]; then
    # Clone without .lake directory
    git clone --depth 1 --single-branch "${PROJECT_ROOT}" "${SANDBOX_DIR}/repo" 2>/dev/null || {
        log "Shallow clone failed, trying rsync..."
        rsync -a --exclude='.lake' --exclude='.git/objects/pack/*.pack' "${PROJECT_ROOT}/" "${SANDBOX_DIR}/repo/"
    }
    # Remove .lake if it was cloned
    rm -rf "${SANDBOX_LEAN}/.lake" 2>/dev/null || true
else
    # rsync without .lake for speed
    rsync -a --exclude='.lake' "${PROJECT_ROOT}/" "${SANDBOX_DIR}/repo/"
fi

# === Symlink Lake cache (packages + build) ===
if [[ "$LINK_LAKE_CACHE" == "true" && -d "${LEAN_PROJECT}/.lake" ]]; then
    log "Setting up Lake symlinks..."

    mkdir -p "${SANDBOX_LEAN}/.lake"

    # Symlink packages (shared, read-only effectively)
    if [[ -d "${LEAN_PROJECT}/.lake/packages" ]]; then
        ln -sf "${LEAN_PROJECT}/.lake/packages" "${SANDBOX_LEAN}/.lake/packages"
        log "Linked packages -> ${LEAN_PROJECT}/.lake/packages"
    fi

    # Symlink build artifacts (shared cache - same Lean version)
    if [[ -d "${LEAN_PROJECT}/.lake/build" ]]; then
        ln -sf "${LEAN_PROJECT}/.lake/build" "${SANDBOX_LEAN}/.lake/build"
        log "Linked build -> ${LEAN_PROJECT}/.lake/build"
    fi

    # Copy lakefile and manifest (small files, need local copies)
    cp -f "${LEAN_PROJECT}/lakefile.toml" "${SANDBOX_LEAN}/" 2>/dev/null || true
    cp -f "${LEAN_PROJECT}/lake-manifest.json" "${SANDBOX_LEAN}/" 2>/dev/null || true
    cp -f "${LEAN_PROJECT}/lean-toolchain" "${SANDBOX_LEAN}/" 2>/dev/null || true
fi

# === Copy TASK.md to sandbox ===
if [[ -f "${WORKER_DIR}/TASK.md" ]]; then
    cp "${WORKER_DIR}/TASK.md" "${SANDBOX_DIR}/repo/TASK.md"
fi

# === Update status to active ===
cat > "${WORKER_DIR}/status.json" << EOF
{
    "insight_id": "${INSIGHT_ID}",
    "status": "active",
    "started_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "sandbox_path": "${SANDBOX_DIR}",
    "terminal": "${PREFERRED_TERMINAL}"
}
EOF

log "Sandbox ready at: ${SANDBOX_DIR}/repo"

# === Open terminal with Claude ===
WORK_DIR="${SANDBOX_DIR}/repo"
LEAN_DIR="${WORK_DIR}/full/q3.lean.aristotle"
INITIAL_PROMPT="Read TASK.md and begin working on the task. Use Explore sub-agent for Mathlib lookups."

open_warp() {
    # Simple: cd + claude, no auto-prompt (user types when ready)
    local cmd="cd ${LEAN_DIR} && ${BX_COMMAND}"

    echo "${cmd}" | pbcopy
    osascript << EOF
tell application "Warp" to activate
delay 0.5
tell application "System Events"
    tell process "Warp"
        keystroke "t" using command down
        delay 0.5
        keystroke "v" using command down
        delay 0.3
        keystroke return
    end tell
end tell
EOF
    # Claude starts instantly, user types "Read TASK.md" when ready
}

open_iterm() {
    osascript << EOF
tell application "iTerm"
    activate
    tell current window
        create tab with default profile
        tell current session
            write text "cd ${LEAN_DIR} && ${BX_COMMAND}"
            delay 2
            write text "${INITIAL_PROMPT}"
        end tell
    end tell
end tell
EOF
}

open_terminal() {
    osascript << EOF
tell application "Terminal"
    activate
    do script "cd ${WORK_DIR} && ${BX_COMMAND}"
end tell
EOF
}

# Try preferred terminal, fall back if needed
case "$PREFERRED_TERMINAL" in
    Warp)
        open_warp 2>/dev/null || open_iterm 2>/dev/null || open_terminal
        ;;
    iTerm)
        open_iterm 2>/dev/null || open_terminal
        ;;
    *)
        open_terminal
        ;;
esac

log "Terminal opened for worker: $INSIGHT_ID"

# === Update registry ===
"${SCRIPT_DIR}/swarm_coordinator.py" update-registry 2>/dev/null || true

log "Spawn complete for: $INSIGHT_ID"
