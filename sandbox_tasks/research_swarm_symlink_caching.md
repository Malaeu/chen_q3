# TASK: Research Swarm Symlink Caching

**Insight:** `research_swarm_symlink_caching_2026_01_17`
**Status:** Completed
**Priority:** 8/10

## Objective

Implement parallel research worker system with symlink-based Lake caching to enable 10+ concurrent workers without 80GB+ storage overhead.

## Completed Work

- [x] Created directory structure `research_swarm/`
- [x] Wrote `PROBLEM.md` with Q3 sub-problems
- [x] Implemented `swarm_watcher.sh` (fswatch daemon)
- [x] Implemented `swarm_spawner.sh` (symlink strategy)
- [x] Implemented `swarm_generate_task.sh` (insight → TASK.md)
- [x] Implemented `swarm_coordinator.py` (status, cleanup)
- [x] Created Claude skill `/x-research-swarm`
- [x] Wrote `SPEC.md` documentation

## Key Commands

```bash
# Start watcher
./scripts/swarm_watcher.sh &

# Check status
./scripts/swarm_coordinator.py status

# Stop watcher
./scripts/swarm_coordinator.py stop

# Manual spawn
./scripts/swarm_spawner.sh <insight_id>
```

## Storage Savings

| Workers | Old (copy) | New (symlink) |
|---------|------------|---------------|
| 1 | 7.7 GB | 26 MB |
| 5 | 38.5 GB | 130 MB |
| 10 | 77 GB | 260 MB |

## Next Steps

- [ ] Test with real insight generation
- [ ] Integration test: `/x-research-swarm` → insights → workers
- [ ] Load test: 10 parallel workers

---

*Created: 2026-01-17*
