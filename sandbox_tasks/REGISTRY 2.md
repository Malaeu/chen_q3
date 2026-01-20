# Sandbox Registry

Все готовые sandbox tasks. Создаются автоматически через `/x-insight`.

| Name | Created | Summary | Status |
|------|---------|---------|--------|
| explore_agent_mathlib_search | 2026-01-17 | **CRITICAL:** Use Explore sub-agent for Mathlib lemma discovery | agent-pattern |
| research_swarm_symlink_caching | 2026-01-17 | Parallel workers with symlink Lake cache (90% storage savings) | completed |
| arch_prime | 2026-01-16 | Heat localization kills prime term: Φ(ξ₂) ≈ 10⁻⁹ | ready |
| carleson | 2026-01-16 | Prime sampling is Carleson measure for heat RKHS | ready |
| measure_dom | 2026-01-16 | Discrete prime sum ≤ continuous arch integral | ready |

## Usage

```bash
# List available
bxl

# Start working
bx arch_prime

# Create new from insight
/x-insight
```

## Status Legend

- `ready` — Task file exists, can start sandbox
- `active` — Sandbox created, work in progress
- `merged` — Work completed and merged to main
- `abandoned` — Approach didn't work out
