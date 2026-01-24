# ACTIVE tree (navigation)

Goal: a compact, link-first tree so agents can follow paths without loading everything.

```
ACTIVE/
├── 00_entry/
│   ├── orchestrator.md        (status + next step)
│   ├── chain_status.md        (single-scale chain)
│   ├── insights.md            (short notes + links)
│   ├── workflow.md            (rules, tools, cadence)
│   └── KNOWLEDGE_BASE.md      (index of canonical links)
│
├── 01_axioms/
│   ├── SingleScale_Assumptions.lean
│   │   └── SingleScale.rayleigh_basis0_shift_ge_cstar_quarter  ← ONLY OPEN
│   └── PHILOSOPHY_OF_PROOF.md (axiom policy + counts)
│
├── 02_chain_blocks/
│   ├── Q_nonneg_atoms_closure.lean   (Q≥0 on atoms; depends on basis0 bound)
│   ├── Rayleigh_Q_identification.lean (RQ ↔ Q bridge)
│   ├── ShiftedWindows.lean            (P_A_shift, phi_shift, continuity)
│   └── P_A_Toeplitz_bridge_one_scale.lean (one-scale Rayleigh bound shell)
│
├── 03_floor_at_tcritical/
│   ├── A3_Floor_Critical_Goal.lean (target floor statement)
│   └── Q_nonneg_t_critical.lean    (numeric/interval sketch; has sorries)
│
├── 04_maps_specs/
│   ├── Q3_BLOCK_MAP.md
│   ├── proof_map.md
│   ├── paper_lean_mapping.md
│   └── SPECS_INDEX.md
│
└── 05_proshka/
    ├── proshka_entrypoint.md
    ├── proshka_context_single_scale.md
    └── scripts/build_proshka_brief.py
```

## Current blocker path (minimal)

1) `SingleScale_Assumptions.lean` → `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
2) reduce via `P_A_shift_tau_zero` (`Q_nonneg_base_atoms_proof.lean`)
3) use `P_A_rayleigh_lower_bound_of_floor` (`P_A_Toeplitz_bridge_one_scale.lean`)
4) need floor at `t_critical`: `A3_Floor_Critical_Goal.lean`

## If you only read one chain file

- `Q3/Proofs/Q_nonneg_atoms_closure.lean` (shows the exact dependency flow)
