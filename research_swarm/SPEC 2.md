# Research Swarm System — Specification

## Overview

Parallel mathematical insight generation with auto-spawning workers and symlink-based Lake caching.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        RESEARCH SWARM ARCHITECTURE                       │
└─────────────────────────────────────────────────────────────────────────┘

  Research Agent                    Watcher Daemon                Workers
       │                                  │                          │
       │  generates                       │  fswatch                 │
       ▼                                  ▼                          ▼
  ┌─────────┐    *.insight.md     ┌─────────────┐   spawn    ┌───────────┐
  │ Claude  │ ──────────────────► │  fswatch    │ ─────────► │ Sandbox 1 │
  │ Session │                     │  daemon     │            │ (symlink) │
  └─────────┘                     └─────────────┘            └───────────┘
       │                                  │                         │
       │ WebSearch                        │                   ┌───────────┐
       │ Perplexity                       │ ─────────────────►│ Sandbox 2 │
       │ research-lookup                  │                   │ (symlink) │
       ▼                                  │                   └───────────┘
  PROBLEM.md                              │                         │
                                          │                   ┌───────────┐
                                          └──────────────────►│ Sandbox N │
                                                              │ (symlink) │
                                                              └───────────┘
                                                                    │
                                                                    ▼
                                                            Shared Lake Cache
                                                            ┌─────────────┐
                                                            │ packages/   │ 7.6GB
                                                            │ build/      │ 82MB
                                                            └─────────────┘
```

## Storage Efficiency

| Approach | Per Sandbox | 10 Workers |
|----------|-------------|------------|
| Full copy | ~8 GB | ~80 GB |
| **Symlink** | ~26 MB | ~260 MB + 8GB shared = **8.3 GB** |

**Savings: 90%+**

---

## Directory Structure

```
chen_q3/
├── PROBLEM.md                           # Central problem definition
├── research_swarm/
│   ├── SPEC.md                          # This file
│   ├── config.sh                        # Configuration
│   ├── REGISTRY.md                      # Auto-generated worker status
│   ├── watcher.pid                      # PID file when running
│   ├── insights/
│   │   ├── new/                         # Watcher monitors this
│   │   ├── active/                      # Currently being worked
│   │   └── completed/                   # Done insights
│   ├── workers/<insight_id>/
│   │   ├── TASK.md                      # Generated from insight
│   │   └── status.json                  # Worker state
│   └── logs/
│       ├── watcher.log
│       └── spawner.log
└── scripts/
    ├── swarm_watcher.sh                 # fswatch daemon
    ├── swarm_spawner.sh                 # Creates sandbox + opens Warp
    ├── swarm_generate_task.sh           # Converts insight → TASK.md
    └── swarm_coordinator.py             # Status, cleanup, stop

/tmp/research_swarm_sandboxes/<insight_id>/
└── repo/                                # Cloned repo with symlinks
    └── full/q3.lean.aristotle/
        └── .lake/
            ├── packages -> /main/repo/.lake/packages  (SYMLINK)
            └── build -> /main/repo/.lake/build        (SYMLINK)
```

---

## Configuration

**File:** `research_swarm/config.sh`

| Variable | Default | Description |
|----------|---------|-------------|
| `MAX_WORKERS` | 10 | Maximum concurrent workers |
| `ABANDON_THRESHOLD_HOURS` | 2 | Mark stuck workers as abandoned |
| `USE_SHALLOW_CLONE` | true | Use git shallow clone |
| `LINK_LAKE_CACHE` | true | Symlink .lake instead of copying |
| `PREFERRED_TERMINAL` | Warp | Terminal app (Warp/iTerm/Terminal) |
| `SANDBOX_BASE` | /tmp/research_swarm_sandboxes | Sandbox location |

---

## Insight File Format

**Location:** `research_swarm/insights/new/<uuid>.insight.md`

```yaml
---
insight_id: <uuid>
subproblem: sp1_density|sp2_rayleigh|sp3_qnonneg|sp4_periodization|sp5_normalization
confidence: high|medium|low
priority: 1-10
sources:
  - url: https://...
    type: mathoverflow|arxiv|zulip|paper
---

# Insight: [Descriptive Title]

## One-Line Summary
Brief description of what this insight provides.

## Mathematical Content
Detailed mathematical explanation, formulas, theorems.

## Lean Translation
```lean
-- Hints for formalization
theorem my_theorem : ... := by
  sorry
```

## Verification Plan
1. Step to verify
2. Another step
```

---

## Worker Status

**File:** `workers/<id>/status.json`

```json
{
    "insight_id": "abc123",
    "status": "active|completed|failed|abandoned|spawning",
    "started_at": "2026-01-17T01:30:00Z",
    "sandbox_path": "/tmp/research_swarm_sandboxes/abc123",
    "terminal": "Warp"
}
```

---

## Commands

### Start Watcher (Background)
```bash
./scripts/swarm_watcher.sh &
```

### Stop Watcher
```bash
./scripts/swarm_coordinator.py stop
```

### Check Status
```bash
./scripts/swarm_coordinator.py status
```

### Update Registry
```bash
./scripts/swarm_coordinator.py update-registry
```

### Cleanup Abandoned Workers
```bash
./scripts/swarm_coordinator.py cleanup
```

### Manual Spawn (without watcher)
```bash
# 1. Create insight file
cat > research_swarm/insights/new/test.insight.md << 'EOF'
---
insight_id: test
subproblem: sp1_density
confidence: medium
priority: 5
sources: []
---
# Insight: Test
## One-Line Summary
Test insight.
## Mathematical Content
None.
## Lean Translation
None.
## Verification Plan
None.
EOF

# 2. Generate TASK.md
./scripts/swarm_generate_task.sh research_swarm/insights/new/test.insight.md test

# 3. Spawn worker
./scripts/swarm_spawner.sh test
```

### View Logs
```bash
tail -f research_swarm/logs/watcher.log
tail -f research_swarm/logs/spawner.log
```

---

## Claude Skill

**Invoke:** `/x-research-swarm`

| Command | Action |
|---------|--------|
| `/x-research-swarm` | Start research loop |
| `/x-research-swarm status` | Show workers |
| `/x-research-swarm stop` | Stop watcher |

---

## Symlink Strategy (Lake Cache)

Instead of copying 7.7GB of Lake cache per sandbox:

```bash
# Main project (source of truth)
/Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/.lake/
├── packages/   # 7.6 GB (Mathlib, etc)
└── build/      # 82 MB (compiled .olean)

# Each sandbox
/tmp/research_swarm_sandboxes/<id>/repo/full/q3.lean.aristotle/.lake/
├── packages -> /main/.lake/packages   # SYMLINK (0 bytes)
└── build -> /main/.lake/build         # SYMLINK (0 bytes)
```

**Requirements:**
- Same Lean version across all sandboxes (checked via `lean-toolchain`)
- Same Mathlib version (checked via `lake-manifest.json`)
- Workers should NOT modify packages (read-only effectively)

---

## Safety

| Limit | Value | Purpose |
|-------|-------|---------|
| Max workers | 10 | Prevent resource exhaustion |
| Abandon threshold | 2 hours | Cleanup stuck workers |
| Sandbox location | /tmp/ | Easy cleanup, no repo pollution |
| Symlinks | Read-only pattern | Workers don't corrupt shared cache |

---

## Troubleshooting

### Watcher not detecting files
```bash
# Check fswatch is installed
which fswatch

# Check watcher is running
ps aux | grep swarm_watcher

# Check PID file
cat research_swarm/watcher.pid
```

### Worker spawn fails
```bash
# Check logs
tail -50 research_swarm/logs/spawner.log

# Check sandbox was created
ls -la /tmp/research_swarm_sandboxes/
```

### Lake build fails in sandbox
```bash
# Verify symlinks are correct
ls -la /tmp/research_swarm_sandboxes/<id>/repo/full/q3.lean.aristotle/.lake/

# Check lean-toolchain matches
diff /main/lean-toolchain /sandbox/lean-toolchain
```

---

*Last updated: 2026-01-17*
