# Q3 Project Status (ASCII)

Legend:
[OK]  formalized (no axioms)
[OK*] proof file exists but main chain still uses axiom or proof has TODO/sorry
[AX]  axiom in main chain
[WIP] active work

Last update: 2026-01-13

## Full Project Diagram (Top-Level)

RH
|
+-- Weil_criterion [AX]
|
+-- Q_nonneg_on_Weil_cone [OK]
    |
    +-- Q_nonneg_on_W_K (T5_transfer) [OK]
        |
        +-- A1_density_WK [AX]  # bridge_v2 CLOSED 2026-01-13 (0 sorry)
        |   |
        |   +-- A1_density_bridge_v2.lean [OK]
        |   +-- A1_density_integrated.lean [OK]
        |
        +-- Q_Lipschitz_on_W_K [OK*]  # CLOSED 2026-01-13 (0 sorry)
        |   |
        |   +-- Q_Lipschitz_prime_bridge.lean [OK]
        |   +-- Q_Lipschitz_arch_bridge.lean [OK]
        |   +-- Q_Lipschitz_bridge.lean [OK]
        |
        +-- Q_nonneg_on_atoms [AX]  # bridge_v2 CLOSED 2026-01-13 (0 sorry)
            |
            +-- Q_nonneg_bridge_v2.lean [OK]
            +-- Q_nonneg_on_atoms_integrated.lean [OK]
            +-- A3_bridge [OK*]  # CLOSED 2026-01-13 (0 sorry)
            |   |
            |   +-- A3_bridge.lean [OK]
            |   +-- A3_bridge_v3_uniform.lean [OK]  # imports P_A_ge_c_star
            |   +-- Szego_Bottcher_eigenvalue_bound [AX]
            |   +-- Szego_Bottcher_convergence [AX]
            |   +-- Szego_Rayleigh_lower_bound [AX]
            |   +-- Schur_test [AX]
            |   +-- eigenvalue_le_norm [AX]
            |   +-- c_arch_pos + a_star_* [AX]
            |   +-- A3_FLOOR (P_A >= 11/10) [OK]
            |
            +-- RKHS_contraction [OK*]  # bridge_v2 2026-01-13
                |
                +-- node_spacing [OK*]
                +-- off_diag_exp_sum [OK*]  # bridge_v3 2026-01-13
                +-- S_K_small [OK*]
                +-- T_P_row_sum_bound [OK*]

## A3_FLOOR Subdiagram

Q3 / A3_FLOOR (Lean)

[Stage 1] Trigamma foundations ............... [OK]
[Stage 2] Monotonicity ....................... [OK]
[Stage 3] Numerical bounds ................... [OK]
   +-- w_bounds .............................. [OK]
   +-- a(1/2), a(3/2), a(5/2) ................. [OK]
   +-- tail_bound (gaussian + |a| tail) ....... [OK]
[Stage 4] Final assembly ..................... [OK]
   +-- g_bounds ............................... [OK]
   +-- P_A_ge_c_star (P_A >= 11/10) ........... [OK]

## Axiom -> Closure Table

Status key:
- AX  : no closure file yet (or only axiom)
- OK* : proof file exists, but main chain still uses axiom or proof has TODO/sorry
- WIP : active work toward closure

Tier-1 (classical)
| Axiom | Closure file(s) | Status |
| --- | --- | --- |
| `Weil_criterion` | (none) | AX |
| `explicit_formula` | (none) | AX |
| `a_star_pos` | (none) | AX |
| `a_star_continuous` | (none) | AX |
| `a_star_bdd_on_compact` | (none) | AX |
| `a_star_even` | (none) | AX |
| `re_digamma_remainder_bound` | `Q3/DigammaRemainder.lean` (lemma `re_digamma_remainder_bound_stieltjes`) | OK |
| `digamma_add_one` | `A3_FLOOR_v3_trigamma_foundations.lean` | OK |
| `Szego_Bottcher_eigenvalue_bound` | (none) | AX |
| `Szego_Bottcher_convergence` | (none) | AX |
| `Szego_Rayleigh_lower_bound` | (none) | AX |
| `Schur_test` | (none) | AX |
| `c_arch_pos` | (none) | AX |
| `eigenvalue_le_norm` | (none) | AX |

Tier-2 (Q3 contributions)
| Axiom | Closure file(s) | Status |
| --- | --- | --- |
| `A1_density_WK_axiom` | `Q3/Proofs/A1_density_bridge_v2.lean`, `A1_density_integrated.lean` | **OK (0 sorry)** |
| `A1_density_axiom` | (legacy, no closure) | AX |
| `W_sum_finite_axiom` | `Q3/Proofs/W_sum_finite.lean`, `Q3/Proofs/W_sum_finite_integrated.lean` | OK* |
| `Q_Lipschitz_on_W_K` | `Q3/Proofs/Q_Lipschitz_*_bridge.lean` (3 files) | **OK (0 sorry)** |
| `RKHS_contraction_axiom` | `Q3/Proofs/RKHS_contraction_bridge_v2.lean` | OK* (0 sorry) |
| `T_P_row_sum_bound_axiom` | `Q3/Proofs/RKHS_contraction.lean` | OK* |
| `S_K_small_axiom` | `Q3/Proofs/S_K_small_integrated.lean` | OK* |
| `node_spacing_axiom` | `Q3/Proofs/node_spacing_integrated.lean` | OK* |
| `off_diag_exp_sum_axiom` | `Q3/Proofs/off_diag_exp_sum_bridge_v3.lean` | OK* |
| `A3_bridge_axiom` | `Q3/Proofs/A3_bridge.lean`, `A3_bridge_v3_uniform.lean` | **OK (0 sorry)** |
| `Q_nonneg_on_atoms_of_A3_RKHS_axiom` | `Q3/Proofs/Q_nonneg_bridge_v2.lean`, `Q_nonneg_on_atoms_integrated.lean` | **OK (0 sorry)** |

Local (A3_FLOOR)
| Axiom | Closure file(s) | Status |
| --- | --- | --- |
| (none) | (n/a) | OK |

## Bridged (axiom-free in Q3.Theorems)

These items are no longer axioms when using `Q3.AxiomsTheorems`:
- `W_sum_finite_axiom`
- `S_K_small_axiom`
- `node_spacing_axiom`
- `off_diag_exp_sum_axiom` (bridge_v3, 2026-01-13)

## Still Strictly AX (main chain)

Tier-1 (classical):
- `Weil_criterion`
- `explicit_formula`
- `a_star_pos`
- `a_star_continuous`
- `a_star_bdd_on_compact`
- `a_star_even`
- `Szego_Bottcher_eigenvalue_bound`
- `Szego_Bottcher_convergence`
- `Szego_Rayleigh_lower_bound`
- `Schur_test`
- `c_arch_pos`
- `eigenvalue_le_norm`

Tier-2 (Q3 contributions):
- `A1_density_WK_axiom`
- `A1_density_axiom`
- `Q_Lipschitz_on_W_K`
- `RKHS_contraction_axiom`
- `T_P_row_sum_bound_axiom`
- `A3_bridge_axiom`
- `Q_nonneg_on_atoms_of_A3_RKHS_axiom`

Local (A3_FLOOR):
- (none)

<!-- AUTO-STATUS:BEGIN -->
Auto status (DB snapshot): 2026-01-12 20:58

Doc status (A3_FLOOR + Q3_DigammaRemainder):
| doc_id | status | lines |
| --- | --- | --- |
| A3_FLOOR_v3 | proven | 201 |
| A3_FLOOR_v6 | proven | 313 |
| A3_FLOOR_v8 | proven | 291 |
| A3_FLOOR_v16 | proven | 329 |
| A3_FLOOR_v19 | proven | 505 |
| A3_FLOOR_v20_core | proven | 853 |
| A3_FLOOR_v20_manual | missing | 0 |
| A3_FLOOR_v21_manual | missing | 0 |
| A3_FLOOR_v22_stage4 | proven | 879 |
| A3_FLOOR_THEOREM | proven | 7 |
| Q3_DigammaRemainder | proven | 2084 |

Counts: missing=2, proven=9
Generated by scripts/update_status.py
<!-- AUTO-STATUS:END -->
