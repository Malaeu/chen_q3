# Q3 Paper to Lean Mapping

This file provides a complete mapping between Q3 paper theorem labels and Lean formalization names.

**Last updated:** 2026-01-20

---

## Main Proof Chain

| Module | Q3 Label | Paper Name | Lean Name | File | Status |
|--------|----------|------------|-----------|------|--------|
| **RH** | `thm:RH` | Riemann Hypothesis | `RH_of_Weil_and_Q3` | Main.lean | theorem |
| **Main** | `thm:Main-positivity` | Main positivity on W | `Q_nonneg_on_atoms...` | Main.lean | axiom |
| **T5** | `thm:T5-compact` | Compact transfer | (implicit) | T5_Transfer.lean | - |
| **A3** | `thm:A3` | Uniform A3 bridge | `A3_bridge_uniform` | Axioms.lean | axiom |
| **RKHS** | `rkhs:thm:rkhs-contraction` | Strict contraction | `RKHS_contraction_axiom` | Axioms.lean | wired |
| **A2** | `cor:A2-Lip` | Lipschitz on compact | `Q_Lipschitz_on_W_K` | Axioms.lean | wired |
| **A1'** | `a1:thm:A1-local-density` | Local cone density | `A1_density_WK_axiom` | Axioms.lean | axiom |
| **T0** | `t0:lem:T0` | Q normalization | (implicit defs) | Basic/Defs.lean | - |

---

## Tier-2: Q3 Paper Axioms (12 total)

| # | Lean Name | Short ID | Q3 Label | TeX File | Status |
|---|-----------|----------|----------|----------|--------|
| 1 | `A1_density_WK_axiom` | A1' Density | `a1:thm:A1-local-density` | A1prime.tex | axiom |
| 2 | `A1_density_axiom` | A1' Legacy | `thm:A1-density` | A1prime.tex | deprecated |
| 3 | `W_sum_finite_axiom` | A2 Local Finite | `lem:Q-local-finite` | A2.tex | wired |
| 4 | `Q_Lipschitz_on_W_K` | A2 Lipschitz | `cor:A2-Lip` | A2.tex | wired |
| 5 | `A3_bridge_axiom` | A3 Bridge (old) | `thm:A3` | A3/main.tex | deprecated |
| 6 | `A3_bridge_uniform` | A3 Uniform | `thm:A3` | A3/main.tex | axiom |
| 7 | `RKHS_contraction_axiom` | RKHS Contract | `rkhs:thm:rkhs-contraction` | RKHS/main.tex | wired |
| 8 | `S_K_small_axiom` | RKHS S_K | `lem:rkhs-gram-off` | RKHS/prime_cap.tex | wired |
| 9 | `node_spacing_axiom` | RKHS Node Gap | `rkhs:lem:node_gap_lower_bound` | RKHS/main.tex | wired |
| 10 | `off_diag_exp_sum_axiom` | RKHS Off-Diag | `lem:rkhs-gram-off` | RKHS/prime_cap.tex | axiom |
| 11 | `T_P_row_sum_bound_axiom` | RKHS Row Sum | `prop:rkhs-gram-cap` | RKHS/prime_cap.tex | axiom |
| 12 | `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` | Main Positivity | `thm:Main-positivity` | Main_closure.tex | axiom |

### Status Legend
- **axiom**: Still an axiom in main proof chain
- **wired**: Theorem exists and is wired (axiom closed)
- **deprecated**: Superseded by newer version

---

## Tier-1: Classical Axioms (12 total)

| # | Lean Name | Short ID | Citation | Year |
|---|-----------|----------|----------|------|
| 1 | `Weil_criterion` | Weil | Weil (1952), Bombieri (2000) | 1952 |
| 2 | `explicit_formula` | Guinand-Weil | Guinand (1948) | 1948 |
| 3 | `a_star_pos` | a* positive | Titchmarsh (1986) Ch. IX | 1986 |
| 4 | `a_star_continuous` | a* continuous | NIST DLMF 5.2 | 2024 |
| 5 | `a_star_bdd_on_compact` | a* bounded | Rudin (1976) Thm 4.16 | 1976 |
| 6 | `a_star_even` | a* even | NIST DLMF 5.2 | 2024 |
| 7 | `Szego_Bottcher_eigenvalue_bound` | Szego-Bottcher | Bottcher & Silbermann (1999) | 1999 |
| 8 | `Szego_Bottcher_convergence` | Szego Conv | Grenander & Szego (1958) | 1958 |
| 9 | `Szego_Rayleigh_lower_bound` | Szego Rayleigh | Gray (2006) | 2006 |
| 10 | `Schur_test` | Schur | Schur (1911) | 1911 |
| 11 | `c_arch_pos` | c_arch | T1.3 + extreme value theorem | - |
| 12 | `eigenvalue_le_norm` | lambda <= norm | Horn & Johnson (2012) | 2012 |

---

## Module Details

### A1' Module (Density)

| Q3 Label | Lean Name | Description |
|----------|-----------|-------------|
| `a1:thm:A1-local-density` | `A1_density_WK_axiom` | Main density theorem |
| `thm:A1-density` | `A1_density_axiom` | Legacy (deprecated) |
| `lem:a1-fixed-t-density` | `A1_density_WK_thm` | Fixed-t0 version (partial) |
| `lem:convolution-compact-support` | (helper) | Convolution domain truncation |

### A2 Module (Lipschitz)

| Q3 Label | Lean Name | Description |
|----------|-----------|-------------|
| `lem:Q-local-finite` | `W_sum_finite_axiom` | Prime sum is finite on compacts |
| `cor:A2-Lip` | `Q_Lipschitz_on_W_K` | Q Lipschitz on W_K |
| `a2:lem:A2` | `Q_Lipschitz_on_W_K_thm` | Explicit Lipschitz constant |

### A3 Module (Toeplitz Bridge)

| Q3 Label | Lean Name | Description |
|----------|-----------|-------------|
| `thm:A3` | `A3_bridge_uniform` | Uniform K-independent bridge |
| `lem:uniform-arch-floor` | `P_A_ge_c_star` | P_A(theta) >= c_* = 11/10 |
| `lem:a3-sb-barrier` | (in Szego axioms) | Szego-Bottcher barrier, C_SB=4 |
| `thm:a3-rayleigh-identification` | `rayleigh_sampling` | Rayleigh quotient identification |
| `cor:uniform-discretisation` | `M0_unif` | M >= M0^unif threshold |

### RKHS Module (Prime Contraction)

| Q3 Label | Lean Name | Description |
|----------|-----------|-------------|
| `rkhs:thm:rkhs-contraction` | `RKHS_contraction_axiom` | T_P strictly contractive |
| `lem:rkhs-uniform-cap-full` | `weight_sum_le_rho_one` | rho(1) < 1/25 |
| `prop:rkhs-gram-cap` | `T_P_row_sum_bound_axiom` | RKHS cap via Gram geometry |
| `lem:rkhs-gram-off` | `S_K_small_axiom` | Off-diagonal sum S_K |
| `rkhs:lem:node_gap_lower_bound` | `node_spacing_axiom` | delta_K >= 1/(2pi*...) |

---

## Key Constants

| Constant | Value | Q3 Label | Lean Name |
|----------|-------|----------|-----------|
| c_* | 11/10 | `lem:uniform-arch-floor` | `c_star` |
| C_SB | 4 | `lem:a3-sb-barrier` | `C_SB` |
| t_sym | 3/50 | symbol_floor.tex | `t_sym` |
| t_rkhs | >= 1 | `cor:uniform-prime-cap` | `t0_A1` |
| B_min | 3 | A3/symbol_floor.tex | `B_min` |
| rho(1) | < 1/25 | `lem:rkhs-uniform-cap-full` | `rho_one_lt` |

---

## TeX Source Files

All LaTeX sources are in: `full/sections/`

| Module | Main File | Additional Files |
|--------|-----------|------------------|
| T0 | T0.tex | T0_AD_fix.tex |
| A1' | A1prime.tex | - |
| A2 | A2.tex | - |
| A3 | A3/main.tex | A3/symbol_floor.tex, A3/matrix_guard.tex, A3/rayleigh_bridge.tex |
| RKHS | RKHS/main.tex | RKHS/prime_cap.tex, RKHS/prime_norm_leq_rho.tex |
| T5 | T5/compact_transfer.tex | T5/summary.tex (archived) |
| Main | Main_closure.tex | - |
| Weil | Weil_linkage.tex | Weil_pack.tex |

---

## Axiom Count Summary

**In main proof chain (`#print axioms RH_of_Weil_and_Q3`):**

```
Total: 11 axioms
  Standard Lean (3): propext, Classical.choice, Quot.sound
  External/Classical (6): Weil_criterion, a_star_*, Schur_test
  Q3 Paper (2): A1_density_WK_axiom, Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
```

**Target:** Close the 2 Q3 paper axioms.
