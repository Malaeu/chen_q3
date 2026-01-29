# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain

Last update: 2026-01-14
Axiom count in main chain: 9

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  |
  +-- Weil_criterion [AX external]
  |
  +-- Q_nonneg_on_Weil_cone [OK]
       |
       +-- T5_transfer [OK]
            |
            +-- A1_density_WK [OK]
            +-- Q_Lipschitz_on_W_K [OK]
            +-- Q_nonneg_on_atoms [AX]
                 |
                 +-- A3_bridge_axiom [AX]
                 +-- RKHS_contraction [OK]
```

## Notes

- `Q_Lipschitz_on_W_K` is a theorem (arch/prime bridge axioms closed).
- Remaining closable axioms: `A3_bridge_axiom`,
  `Q_nonneg_on_atoms_of_A3_RKHS_axiom`.
- `aristotle_output/A1_density_hat_chain.lean` is now exact?-free and compiles
  cleanly (ring_nf + unused variables fixed).
- External/classical axioms in the chain: `Weil_criterion`, `a_star_pos`,
  `a_star_bdd_on_compact`, `a_star_continuous`.

## A3_bridge Progress (2026-01-14)

**V3 COMPLETE:** `aristotle_output/A3_bridge_v3_proshka.lean`
- Structure proven: rayleigh + quadform_sub + main theorem
- BUT: uses placeholder P_A=const, T_P=0
- NEXT: need Aristotle/Proshka request with real definitions

**Key insight from Прошка:** SB not needed, Rayleigh direct approach works.
