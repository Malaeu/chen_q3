# Project Memory — Q3 Lean Formalization

## SINGLE ENTRY POINT
**START HERE:** `/full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`

This is the ONLY file you need to read at session start. All other docs are linked from there.

---

## Workflow (Axiom Closure Loop)

```
┌─────────────────────────────────────────────────────────────────┐
│                    AXIOM CLOSURE WORKFLOW                       │
└─────────────────────────────────────────────────────────────────┘

1. READ: PROJECT_ORCHESTRATOR.md → find "Active Next Step"

2. WORK: Close the axiom/bridge:
   - Find the axiom in Q3/Proofs/*.lean
   - Replace `axiom X` with `theorem X := <proof>`
   - Or wire existing theorem from bridge file

3. VERIFY:
   lake build Q3.Main
   ./scripts/check_axioms.sh
   #print axioms Q3.Main.RH_of_Weil_and_Q3

4. UPDATE:
   - PROJECT_ORCHESTRATOR.md (Closure Tracker table)
   - PROJECT_ASCII.md (if diagram changed)
   - Commit with axiom count

5. REPEAT from step 1
```

---

## Philosophy Compliance

Before EVERY commit, verify:
- [ ] Axiom count same or DECREASED
- [ ] No new `axiom` without citation
- [ ] No `sorry` in main proof chain

See: `/full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`

---

## Current Axiom Count: 12

```
Standard (3): propext, Classical.choice, Quot.sound
Level 1 (3):  Weil_criterion, a_star_pos, a_star_bdd_on_compact
Level 2 (4):  A1_density, A3_bridge, RKHS_contraction, Q_nonneg
Bridge (2):   arch_term_Lipschitz_bridge, prime_term_Lipschitz_bridge
```

Target: Reduce Level 2 + Bridge to 0 (or minimal classical results)

---

## Quick Commands

```bash
cd /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle

# Build
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'

# Automated check
./scripts/check_axioms.sh
```

---

## Key Files (reference only - use ORCHESTRATOR)

| Purpose | File |
|---------|------|
| Entry point | `full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` |
| Philosophy | `full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md` |
| ASCII diagram | `full/q3.lean.aristotle/PROJECT_ASCII.md` |
| Workflow checklist | `full/q3.lean.aristotle/WORKFLOW_CHECKLIST.md` |
| Axioms definition | `full/q3.lean.aristotle/Q3/Axioms.lean` |
| Theorem wiring | `full/q3.lean.aristotle/Q3/AxiomsTheorems.lean` |
| Main proof | `full/q3.lean.aristotle/Q3/Main.lean` |

---

## Aristotle (AI proof assistant)

```python
from aristotlelib import Project, ProjectInputType

# For .md input files:
project_input_type=ProjectInputType.INFORMAL
validate_lean_project=False

# Key attributes:
p.percent_complete  # NOT p.progress!
p.status            # ProjectStatus enum
```

See: `/ARISTOTLE_GUIDE.md`

---

## Active TODO (from Orchestrator)

1. **arch_term_Lipschitz_bridge** → wire from `Q_Lipschitz_arch_bridge.lean`
2. **prime_term_Lipschitz_bridge** → wire from `Q_Lipschitz_prime_bridge.lean`
3. **mem_nodes_finset** → remove axiom in `Bridge.lean`
4. **A3_bridge_uniform** → prove via A3_FLOOR + Szegő + RKHS
5. **Q_nonneg** → rewrite after A3+RKHS done

---

*Last updated: 2026-01-13*
