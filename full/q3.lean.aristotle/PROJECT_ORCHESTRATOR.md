# PROJECT ORCHESTRATOR — Q3
## Lean Formalization of Riemann Hypothesis

**Last Updated:** 2026-01-13
**Single entry point:** read this file at session start.

## Quick Start

Read only this file. It links to everything else you need.

## Current State (short)

- A3_FLOOR is proven and integrated: `A3_FLOOR_v22_stage4_floor.lean` →
  `Q3/Proofs/A3_bridge_v3_uniform.lean` uses `P_A_ge_c_star`.
- `Q_Lipschitz_on_W_K` is already wired as a theorem in `Q3/AxiomsTheorems.lean`,
  but it still depends on two local bridge axioms (arch/prime Lipschitz).

## Axiom Count (verified)

Command:
```bash
echo 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1 | rg -v "^info:"
```

Result: **12 axioms**
- Standard Lean: `propext`, `Classical.choice`, `Quot.sound`
- External/classical: `Weil_criterion`, `a_star_pos`, `a_star_bdd_on_compact`
- Tier-2 (closable): `A1_density_WK_axiom`, `A3_bridge_axiom`,
  `RKHS_contraction_axiom`, `Q_nonneg_on_atoms_of_A3_RKHS_axiom`
- Bridge axioms (closable): `arch_term_Lipschitz_bridge`,
  `prime_term_Lipschitz_bridge`

## Active Next Step

1) **Lipschitz Bridge Wiring (BLOCKED - signature mismatch)**:
   - `arch_term_Lipschitz_bridge` uses `arch_term_local Φ = ∫ ξ, a*·Φ` (global)
   - Bridge theorem uses `arch_term_local K Φ = ∫ ξ in [-K,K], a*·Φ` (set integral)
   - **Need:** Prove they're equal for Φ with support ⊆ [-K,K]
   - Same issue for `prime_term_Lipschitz_bridge`
   - Files: `Q3/Proofs/Q_Lipschitz_arch_bridge.lean`, `Q3/Proofs/Q_Lipschitz_prime_bridge.lean`

2) Remove `mem_nodes_finset_of_mem_Q3Nodes` axiom in `Q3/Proofs/Bridge.lean`.
3) Re-run `lake env lean Q3/Proofs/RKHS_contraction_bridge.lean`.
4) Then prove `A3_bridge_uniform` in `Q3/Proofs/A3_bridge_v3_uniform.lean`.

## Closure Tracker (remaining axioms)

| Axiom | Current proof source | Blocker | Next action | Status |
|------|-----------------------|---------|-------------|--------|
| `arch_term_Lipschitz_bridge` | `Q3/Proofs/Q_Lipschitz_arch_bridge.lean` | **signature mismatch** (global vs set integral) | prove equivalence lemma | BLOCKED |
| `prime_term_Lipschitz_bridge` | `Q3/Proofs/Q_Lipschitz_prime_bridge.lean` | **signature mismatch** (global vs local def) | prove equivalence lemma | BLOCKED |
| `RKHS_contraction_axiom` | `Q3/Proofs/RKHS_contraction.lean` + bridge | `Bridge.lean` has axiom `mem_nodes_finset_of_mem_Q3Nodes` | replace axiom with lemma | IN_PROGRESS |
| `A3_bridge_uniform` / `A3_bridge_axiom` | `Q3/Proofs/A3_bridge_v3_uniform.lean` | still uses `A3_bridge_uniform` axiom | prove via A3_FLOOR + Szego + RKHS | BLOCKED |
| `Q_nonneg_on_atoms_of_A3_RKHS_axiom` | `Q3/Proofs/Q_nonneg_on_atoms.lean` + bridge | needs A3 + RKHS proofs | rewrite `Q3/Proofs/Q_nonneg_bridge_v2.lean` | BLOCKED |
| `A1_density_WK_axiom` | `Q3/Proofs/A1_density.lean` | `A1_density_WK_thm` calls the axiom | replace axiom call with internal lemmas | TODO |

## Key Files (open only as needed)

- `PROJECT_WORKFLOW.md` — workflow loop + Aristotle rules
- `PROJECT_ASCII.md` — proof tree diagram
- `PROOF_MAP_NEW_KERNEL.md` + `A3_FLOOR_ROADMAP.md` — A3_FLOOR status
- `FORMALIZATION_STATUS.md` — detailed status (secondary, not an entry point)
- `Q3/Axioms.lean` and `Q3/AxiomsTheorems.lean` — axioms and wiring
- `Q3/Proofs/Q_Lipschitz.lean` — real proof of Q_Lipschitz
- `Q3/Proofs/Bridge.lean` + `Q3/Proofs/RKHS_contraction_bridge.lean`
- `Q3/Proofs/A3_bridge_v3_uniform.lean`
- `Q3/Proofs/Q_nonneg_bridge_v2.lean`
- `Q3/Proofs/A1_density.lean`
- `aristotle_db/parse_lean.py` — DB import

## Update Rule

After closing a step:
- run `lake env lean <file>`
- re-import to DB (`aristotle_db/parse_lean.py import ...`)
- update this file and `PROJECT_ASCII.md`

## Future: Community Presentation

After Tier-2 closure → present to Talia Ringer / Lean Zulip.
See `PHILOSOPHY_OF_PROOF.md` for the pitch.

## Build / Verify

```bash
cd /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle
lake build Q3.Main
```

```bash
./scripts/check_axioms.sh
```

```bash
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | rg -v "^info:"
```

## Change Log (recent)

- 2026-01-13: Discovered signature mismatch in Lipschitz bridges (global vs set integral)
- 2026-01-13: Added PHILOSOPHY_OF_PROOF.md, WORKFLOW_CHECKLIST.md, scripts/check_axioms.sh
- 2026-01-13: Wired Q_Lipschitz_on_W_K as theorem (axiom count: 5→4 Tier-2 + 2 bridge)
- 2026-01-13: A3_FLOOR integrated in `Q3/Proofs/A3_bridge_v3_uniform.lean`.
- 2026-01-13: DB import for `A3_bridge_v3_uniform`.
