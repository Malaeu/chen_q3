# ACTIVE tree (navigation)

**Purpose:** Compact navigation tree + minimal reader flow.  
**Current status:** Main blockers are in `ACTIVE/MAIN_CHAIN_DEPS.md`.  
**Next action:** Use the reader flow below; drill only as needed.  
**Links:** `ACTIVE/KNOWLEDGE_BASE.md` · `ACTIVE/MAIN_CHAIN_DEPS.md` · `ACTIVE/orchestrator.md`

---

## Reader flow (minimal)

1) `ACTIVE/KNOWLEDGE_BASE.md` (router)  
2) `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative blockers)  
3) `ACTIVE/chain_status.md` (short chain summary)  
4) `ACTIVE/requests/INDEX.md` (request tree, when needed)  

---

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

1) `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
   → `prime_b_grid_bounds_data`
2) `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
   → `prime_heat_bounds_data`
3) `Q3/Axioms.lean`
   → `Weil_criterion_tau0`
4) `Q3/CheckAxioms.lean`
   → prints live dependency list for `Q3.Main.RH_of_Weil_and_Q3`

## If you only read one chain file

- `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative blockers + file map)
