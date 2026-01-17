# Research Swarm Registry

**Last Updated:** 2026-01-17 03:52:32
**Total Workers:** 1 / 10

## Active Workers (0)

| Insight ID | Started | Sandbox |
|------------|---------|---------|
*None*

## Spawning (0)

*None*

## Completed (1)

| Insight ID | Started | Sandbox |
|------------|---------|---------|
| `test_8sec` | 2026-01-17T02:10:01 | `/tmp/research_swarm_sandboxes/test_8sec` |

## Failed (0)

*None*

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
