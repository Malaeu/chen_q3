# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain
[EXT] external/classical axiom (not closable)
[TRUST] trusted computation (native_decide / compiler)

Last update: 2026-01-26
Axiom count in main chain: 8 total (5 project + 3 kernel/standard)

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
            +-- Q_nonneg_on_atoms [OK]
                 |
                 +-- Schur_test [EXT classical]
                 |
                 +-- One-scale @ t_critical = 3/20 [OK]
                      |
                      +-- prime_term_le_at_t_critical_axiom [AX cert]
                      +-- PrimeCert: prime_b_grid_val_le_margin [AX cert]
                      +-- PrimeCert: prime_margin_Lipschitz_on_Brange [AX cert]
```

## Axiom Summary

| Category | Axioms | Count |
|----------|--------|-------|
| Standard/kernel | `propext`, `Classical.choice`, `Quot.sound` | 3 |
| Trusted computation | (none in main chain) | 0 |
| Classical Literature | `Weil_criterion`, `Schur_test` | 2 |
| One‑scale numeric certificates | `prime_term_le_at_t_critical_axiom`, `PrimeCert.*` (2) | 3 |
| **TOTAL** | | **8** |

## Closed Axioms (history)

- `a_star_even` - Mathlib Gamma_conj
- `a_star_pos` - positivity
- `a_star_continuous` - Mathlib Gamma continuity
- `a_star_bdd_on_compact` - continuous + compact
- `A1_density_WK_axiom` - bounded hat interpolation (h_even mass bound)
- `RKHS_contraction_axiom` - bridged in `Q3/Proofs/Bridge.lean`
- `arch/prime Lipschitz bridge axioms` - closed in `Q3/Proofs/Q_Lipschitz.lean`
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` - closed via `Q_nonneg_atoms_closure` (2026-01-24)

## Notes

- Mainline is now **single-scale** at `t_critical = 3/20` (see `docs/CHAIN_STATUS.md`).
- External axioms (`Weil_criterion`, `Schur_test`) are accepted classical results.
- The remaining non-classical axioms are **certificate-backed** (t_critical prime-term + B-range).
- `native_decide` is eliminated (no `Lean.trustCompiler` / `Lean.ofReduceBool` in the chain).

## A3_bridge Progress (context)

**Fourier A3 bridge complete (theorem):** `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- Uses Fourier Toeplitz + `P_A` symbol + `T_P_comp_real`
- One-scale chain depends on prime certificate axioms (see `Q3/Proofs/PrimeCert/`)
