# Aristotle Projects (2025-12-16)

## Active Projects

| # | Name | Project ID | Status |
|---|------|------------|--------|
| 1 | Q_Lipschitz_v2 | `70f872fe-6eef-43e9-8ab7-a8ff6c71a862` | QUEUED |
| 2 | node_spacing | `52696cee-ad2c-4feb-a69f-dbb05bfc7433` | QUEUED |
| 3 | off_diag_exp_sum | `ada58f31-f6fb-4426-99f2-9bb5cf98a3a3` | QUEUED |
| 4 | S_K_small | `e4a93701-387d-4d80-8140-d000a959e37a` | QUEUED |
| 5 | W_sum_finite | `b7f6e83f-f549-40b4-b1e5-a46b7a7280c6` | QUEUED |

## Check Status Script

```bash
cd /Users/emalam/Documents/GitHub/chen_q3 && source .venv/bin/activate && python3 << 'EOF'
import asyncio
from aristotlelib import Project

async def check():
    ids = [
        ('Q_Lipschitz', '70f872fe-6eef-43e9-8ab7-a8ff6c71a862'),
        ('node_spacing', '52696cee-ad2c-4feb-a69f-dbb05bfc7433'),
        ('off_diag_exp_sum', 'ada58f31-f6fb-4426-99f2-9bb5cf98a3a3'),
        ('S_K_small', 'e4a93701-387d-4d80-8140-d000a959e37a'),
        ('W_sum_finite', 'b7f6e83f-f549-40b4-b1e5-a46b7a7280c6'),
    ]
    for name, pid in ids:
        p = await Project.from_id(pid)
        status = p.status.name
        pct = getattr(p, 'percent_complete', '-')
        print(f'{name:20s}: {status:15s} ({pct}%)')
        if status == 'COMPLETED':
            sol = await p.get_solution()
            print(f'  → Proof: {len(sol) if sol else 0} chars')

asyncio.run(check())
EOF
```

## Get Solution (when COMPLETED)

```bash
cd /Users/emalam/Documents/GitHub/chen_q3 && source .venv/bin/activate && python3 << 'EOF'
import asyncio
from aristotlelib import Project

async def get_proof(pid, name):
    p = await Project.from_id(pid)
    if p.status.name == 'COMPLETED':
        sol = await p.get_solution()
        with open(f'/Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/aristotle_output/{name}.lean', 'w') as f:
            f.write(sol)
        print(f'Saved {name}.lean')
    else:
        print(f'{name}: {p.status.name}')

# Replace with actual project
asyncio.run(get_proof('PROJECT_ID_HERE', 'LEMMA_NAME'))
EOF
```

## Axiom to Input File Mapping

| Axiom | Input File | Difficulty |
|-------|-----------|------------|
| `Q_Lipschitz_on_W_K` | Q_Lipschitz_v2.md | Medium |
| `node_spacing_axiom` | node_spacing.md | Easy |
| `off_diag_exp_sum_axiom` | off_diag_exp_sum.md | Easy |
| `S_K_small_axiom` | S_K_small.md | Easy |
| `W_sum_finite_axiom` | W_sum_finite.md | Easy |

## Expected Completion Times

- Simple lemmas: 5-15 min
- Medium theorems: 15-60 min
- Complex proofs: 1-8 hours
