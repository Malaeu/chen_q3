# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain

Last update: 2026-01-13
Axiom count in main chain: 10

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
            +-- A1_density_WK [AX]
            +-- Q_Lipschitz_on_W_K [OK]
            +-- Q_nonneg_on_atoms [AX]
                 |
                 +-- A3_bridge_axiom [AX]
                 +-- RKHS_contraction [OK]
```

## Notes

- `Q_Lipschitz_on_W_K` is a theorem (arch/prime bridge axioms closed).
- Remaining closable axioms: `A1_density_WK_axiom`, `A3_bridge_axiom`,
  `Q_nonneg_on_atoms_of_A3_RKHS_axiom`.
- External/classical axioms in the chain: `Weil_criterion`, `a_star_pos`,
  `a_star_bdd_on_compact`, `a_star_continuous`.
