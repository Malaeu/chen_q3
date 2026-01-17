#!/usr/bin/env python3
"""Research Swarm Coordinator — status aggregation and cleanup."""

import json
import os
import sys
from datetime import datetime, timedelta
from pathlib import Path

# Configuration
SWARM_ROOT = Path("/Users/emalam/Documents/GitHub/chen_q3/.claude/swarm")
WORKERS_DIR = SWARM_ROOT / "workers"
INSIGHTS_ACTIVE = SWARM_ROOT / "insights/active"
INSIGHTS_COMPLETED = SWARM_ROOT / "insights/completed"
REGISTRY_FILE = SWARM_ROOT / "REGISTRY.md"
MAX_WORKERS = 10
ABANDON_THRESHOLD_HOURS = 2


def get_workers():
    """Get all worker statuses."""
    workers = []
    if not WORKERS_DIR.exists():
        return workers

    for worker_dir in WORKERS_DIR.iterdir():
        if not worker_dir.is_dir():
            continue
        status_file = worker_dir / "status.json"
        if status_file.exists():
            try:
                with open(status_file) as f:
                    data = json.load(f)
                    data["worker_dir"] = str(worker_dir)
                    workers.append(data)
            except json.JSONDecodeError:
                workers.append({
                    "insight_id": worker_dir.name,
                    "status": "error",
                    "worker_dir": str(worker_dir)
                })
    return workers


def update_registry():
    """Update REGISTRY.md with current worker status."""
    workers = get_workers()

    active = [w for w in workers if w.get("status") == "active"]
    completed = [w for w in workers if w.get("status") == "completed"]
    failed = [w for w in workers if w.get("status") in ("failed", "error")]
    spawning = [w for w in workers if w.get("status") == "spawning"]

    content = f"""# Research Swarm Registry

**Last Updated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**Total Workers:** {len(workers)} / {MAX_WORKERS}

## Active Workers ({len(active)})

| Insight ID | Started | Sandbox |
|------------|---------|---------|
"""

    for w in active:
        started = w.get("started_at", "unknown")[:19]
        sandbox = w.get("sandbox_path", "unknown")
        content += f"| `{w['insight_id']}` | {started} | `{sandbox}` |\n"

    if not active:
        content += "| *None* | - | - |\n"

    content += f"""
## Spawning ({len(spawning)})

"""
    for w in spawning:
        content += f"- `{w['insight_id']}`\n"

    if not spawning:
        content += "*None*\n"

    content += f"""
## Completed ({len(completed)})

"""
    for w in completed:
        content += f"- `{w['insight_id']}`\n"

    if not completed:
        content += "*None*\n"

    content += f"""
## Failed ({len(failed)})

"""
    for w in failed:
        content += f"- `{w['insight_id']}`\n"

    if not failed:
        content += "*None*\n"

    content += """
---

## Commands

```bash
# Start watcher
./scripts/swarm_watcher.sh &

# Stop watcher
./scripts/swarm_coordinator.py stop

# Check status
./scripts/swarm_coordinator.py status

# Cleanup abandoned workers
./scripts/swarm_coordinator.py cleanup
```
"""

    with open(REGISTRY_FILE, "w") as f:
        f.write(content)

    print(f"Registry updated: {len(active)} active, {len(completed)} completed")


def show_status():
    """Print status to stdout."""
    workers = get_workers()

    active = [w for w in workers if w.get("status") == "active"]
    completed = [w for w in workers if w.get("status") == "completed"]
    failed = [w for w in workers if w.get("status") in ("failed", "error")]

    print(f"=== Research Swarm Status ===")
    print(f"Workers: {len(active)}/{MAX_WORKERS} active")
    print(f"Completed: {len(completed)}")
    print(f"Failed: {len(failed)}")
    print()

    if active:
        print("Active workers:")
        for w in active:
            started = w.get("started_at", "unknown")[:19]
            print(f"  - {w['insight_id']} (started: {started})")

    # Check watcher
    pid_file = SWARM_ROOT / "watcher.pid"
    if pid_file.exists():
        pid = pid_file.read_text().strip()
        try:
            os.kill(int(pid), 0)
            print(f"\nWatcher: RUNNING (PID {pid})")
        except (OSError, ValueError):
            print("\nWatcher: STOPPED (stale PID file)")
    else:
        print("\nWatcher: STOPPED")


def stop_watcher():
    """Stop the watcher daemon."""
    pid_file = SWARM_ROOT / "watcher.pid"
    if not pid_file.exists():
        print("Watcher not running (no PID file)")
        return

    pid = pid_file.read_text().strip()
    try:
        os.kill(int(pid), 15)  # SIGTERM
        print(f"Stopped watcher (PID {pid})")
        pid_file.unlink()
    except (OSError, ValueError) as e:
        print(f"Failed to stop watcher: {e}")


def cleanup_abandoned():
    """Clean up abandoned workers (exceeded threshold)."""
    workers = get_workers()
    threshold = datetime.utcnow() - timedelta(hours=ABANDON_THRESHOLD_HOURS)

    cleaned = 0
    for w in workers:
        if w.get("status") != "active":
            continue

        started_str = w.get("started_at", "")
        if not started_str:
            continue

        try:
            started = datetime.fromisoformat(started_str.replace("Z", "+00:00"))
            started = started.replace(tzinfo=None)

            if started < threshold:
                # Mark as abandoned
                status_file = Path(w["worker_dir"]) / "status.json"
                data = w.copy()
                data["status"] = "abandoned"
                data["abandoned_at"] = datetime.utcnow().isoformat() + "Z"

                with open(status_file, "w") as f:
                    json.dump(data, f, indent=2)

                print(f"Abandoned: {w['insight_id']} (running > {ABANDON_THRESHOLD_HOURS}h)")
                cleaned += 1
        except Exception as e:
            print(f"Error checking {w['insight_id']}: {e}", file=sys.stderr)

    print(f"Cleaned {cleaned} abandoned workers")
    update_registry()


def main():
    if len(sys.argv) < 2:
        print("Usage: swarm_coordinator.py <command>")
        print("Commands: status, update-registry, stop, cleanup")
        sys.exit(1)

    command = sys.argv[1]

    if command == "status":
        show_status()
    elif command == "update-registry":
        update_registry()
    elif command == "stop":
        stop_watcher()
    elif command == "cleanup":
        cleanup_abandoned()
    else:
        print(f"Unknown command: {command}")
        sys.exit(1)


if __name__ == "__main__":
    main()
