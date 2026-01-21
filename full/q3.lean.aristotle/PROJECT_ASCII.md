# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain
[EXT] external/classical axiom (not closable)

Last update: 2026-01-21
Axiom count in main chain: 6 total (3 project + 3 standard)

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  |
  +-- Weil_criterion [EXT classical]
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
                 +-- Schur_test [EXT classical]
```

## Axiom Summary

| Category | Axioms | Count |
|----------|--------|-------|
| Standard Lean | `propext`, `Classical.choice`, `Quot.sound` | 3 |
| Classical Literature | `Weil_criterion`, `Schur_test` | 2 |
| Q3 Paper (closable) | `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` | 1 |
| **TOTAL** | | **6** |

## Closed Axioms (2026-01-21)

- `a_star_pos` - positivity proof
- `a_star_continuous` - Mathlib Gamma continuity
- `a_star_bdd_on_compact` - continuous + compact
- `a_star_even` - Mathlib Gamma_conj
- `A1_density_WK_axiom` - bounded hat interpolation (h_even mass bound)
- `RKHS_contraction` - bridged in Q3/Proofs/Bridge.lean
- `arch/prime Lipschitz` - closed in Q3/Proofs/Q_Lipschitz.lean

## Notes

- `Q_Lipschitz_on_W_K` is a theorem (arch/prime bridge axioms closed).
- Remaining closable axiom: `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.
- Blocker: AtomCone_K_fixed gap (quantifier mismatch for fixed t).
- External axioms (`Weil_criterion`, `Schur_test`) are classical results.

## A3_bridge Progress

**Fourier A3 bridge complete (theorem):** `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- Uses Fourier Toeplitz + `P_A` symbol + `T_P_comp_real`
- Main chain depends on `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
