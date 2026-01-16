# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain

Last update: 2026-01-16
Axiom count in main chain: 11 total (8 project + 3 standard)

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
                 +-- Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom [AX]
                 +-- RKHS_contraction [OK]
```

## Notes

- `Q_Lipschitz_on_W_K` is a theorem (arch/prime bridge axioms closed).
- Remaining closable axioms: `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`,
  `P_A_continuous`.
- `aristotle_output/A1_density_hat_chain.lean` is now exact?-free and compiles
  cleanly (ring_nf + unused variables fixed).
- External/classical axioms in the chain: `Weil_criterion`, `a_star_pos`,
  `a_star_bdd_on_compact`, `a_star_continuous`, `a_star_even`, `Schur_test`.

## A3_bridge Progress (2026-01-14)

**Fourier A3 bridge complete (theorem):** `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- Uses Fourier Toeplitz + `P_A` symbol + `T_P_comp_real`
- Main chain now depends on `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
  (still an axiom pending proof)

**Key insight from Прошка:** SB not needed, Rayleigh direct approach works.
