#!/bin/bash
# Research Swarm Watcher — monitors insights/new/ and spawns workers

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/../research_swarm/config.sh"

# Ensure directories exist
mkdir -p "${INSIGHTS_NEW}" "${INSIGHTS_ACTIVE}" "${INSIGHTS_COMPLETED}" "${WORKERS_DIR}" "${LOGS_DIR}"

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" | tee -a "${WATCHER_LOG}"
}

log "=== Research Swarm Watcher Starting ==="
log "Monitoring: ${INSIGHTS_NEW}"
log "Max workers: ${MAX_WORKERS}"

# Create PID file for stop command
echo $$ > "${SWARM_ROOT}/watcher.pid"
trap 'rm -f "${SWARM_ROOT}/watcher.pid"; log "Watcher stopped"; exit 0' SIGTERM SIGINT

# Main watch loop
fswatch -0 --event Created "${INSIGHTS_NEW}" | while IFS= read -r -d '' file; do
    # Only process .insight.md files
    if [[ ! "$file" =~ \.insight\.md$ ]]; then
        continue
    fi

    # Wait a bit for file to be fully written
    sleep 0.5

    if [[ ! -f "$file" ]]; then
        log "WARN: File disappeared: $file"
        continue
    fi

    filename=$(basename "$file")
    insight_id="${filename%.insight.md}"

    log "New insight detected: $filename"

    # Check worker limit
    if ! can_spawn_worker; then
        log "WARN: Max workers reached ($MAX_WORKERS), queueing: $filename"
        continue
    fi

    # Move to active
    mv "$file" "${INSIGHTS_ACTIVE}/${filename}"
    log "Moved to active: $filename"

    # Generate TASK.md
    "${SCRIPT_DIR}/swarm_generate_task.sh" "${INSIGHTS_ACTIVE}/${filename}" "${insight_id}"

    # Spawn worker
    "${SCRIPT_DIR}/swarm_spawner.sh" "${insight_id}" &

    log "Worker spawned for: $insight_id"
done

log "=== Watcher exiting ==="
