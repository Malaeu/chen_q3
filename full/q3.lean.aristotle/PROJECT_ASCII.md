# Q3 Project Status (ASCII)

Derived from `PROJECT_ORCHESTRATOR.md`. Keep this file short and consistent.

Legend:
[OK]  formalized (no axioms in the chain)
[AX]  axiom in the chain
[EXT] external/classical axiom (not closable)
[TRUST] trusted computation (native_decide / compiler)

Last update: 2026-01-26
Axiom count in main chain: 6 total (3 project + 3 kernel/standard)

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  |
  +-- Weil_criterion_tau0 [EXT classical]
  |
  +-- Q_nonneg_on_Weil_cone_tau0 [OK]
       |
       +-- T5_transfer_tau0 [OK]
            |
            +-- Q_Lipschitz_on_W_K [OK]
            +-- Q_nonneg_on_base_atoms_brange [OK]
                 |
                 +-- One-scale @ t_critical = 3/20 [OK]
                      |
                      +-- PrimeCert: prime_b_grid_val_le_margin [AX cert]
                      +-- PrimeCert: prime_margin_Lipschitz_on_Brange [AX cert]
```

## Axiom Summary

| Category | Axioms | Count |
|----------|--------|-------|
| Standard/kernel | `propext`, `Classical.choice`, `Quot.sound` | 3 |
| Trusted computation | (none in main chain) | 0 |
| Classical Literature | `Weil_criterion_tau0` | 1 |
| One‑scale numeric certificates | `PrimeCert.*` (2) | 2 |
| **TOTAL** | | **6** |

## Sorry Summary (outside main chain)

Main chain has **no** `sorryAx` and `lake build Q3.Main` passes.

Remaining `sorry` (draft/legacy files, not in main chain):
- `Q3/Proofs/Q_nonneg_base_atoms_proof.lean` (4)
- `Q3/Proofs/A1_density.lean` (2)
- `Q3/Proofs/QSpec.lean` (4)

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
- External axiom (`Weil_criterion_tau0`) is accepted classical result.
- The remaining non-classical axioms are **certificate-backed** (B-range PrimeCert).
- `native_decide` is eliminated (no `Lean.trustCompiler` / `Lean.ofReduceBool` in the chain).

## A3_bridge Progress (context)

**Fourier A3 bridge complete (theorem):** `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- Uses Fourier Toeplitz + `P_A` symbol + `T_P_comp_real`
- One-scale chain depends on prime certificate axioms (see `Q3/Proofs/PrimeCert/`)
