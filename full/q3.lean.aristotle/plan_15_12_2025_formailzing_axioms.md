 Q3 Lean Formalization Plan

 Current Status

 Lean Formalization (q3.lean.aristotle/)

 PROVEN (Theorems, not axioms):
 - RH_of_Weil_and_Q3 - Main theorem (RH!)
 - Q_nonneg_on_Weil_cone - Q >= 0 on full cone
 - T5_transfer - Compact transfer (KEY!)
 - Q_nonneg_on_atoms - Atoms positivity
 - ~40+ lemmas (w_max bounds, W_K subset, etc.)

 AXIOMS to formalize (16 total):

| #    | Axiom                              | Paper Source              | Difficulty | Priority |
| ---- | ---------------------------------- | ------------------------- | ---------- | -------- |
| 1    | Q_Lipschitz_on_W_K                 | A2.tex                    | 2/5        | P0       |
| 2    | A1_density_WK_axiom                | A1prime.tex               | 3/5        | P1       |
| 3    | S_K_small_axiom                    | RKHS/main.tex:32          | 3/5        | P1       |
| 4    | T_P_row_sum_bound_axiom            | RKHS/main.tex:102         | 2/5        | P1       |
| 5    | Q_nonneg_on_atoms_of_A3_RKHS_axiom | A3/rayleigh_bridge.tex:66 | 3/5        | P2       |
| 6    | RKHS_contraction_axiom             | RKHS/main.tex:45          | 4/5        | P2       |
| 7    | A3_bridge_axiom                    | A3/main.tex:152           | 4/5        | P2       |
| 8    | Weil_cone_continuous               | (trivial - move to def)   | 1/5        | P0       |

 Classical axioms (Tier-1, keep as axioms):
 - Weil_criterion - Weil 1952
 - explicit_formula - Guinand 1948
 - Szego_Bottcher_* - Szego/Bottcher 1958/1999
 - Schur_test - Schur 1911
 - a_star_pos, c_arch_pos, eigenvalue_le_norm

---
 Formalization Strategy

 Phase 1: Easy Wins (P0)

 1. Move Weil_cone_continuous into definition - make Weil_cone require Continuous
 2. Formalize Q_Lipschitz_on_W_K - standard analysis, A2.tex has full proof

 Phase 2: Approximation Theory (P1)

 3. Formalize A1_density_WK_axiom - Fejer*heat density, A1prime.tex:17-50
 4. Formalize S_K_small_axiom - geometric series bound
 5. Formalize T_P_row_sum_bound_axiom - Gershgorin-type bound

 Phase 3: Main Results (P2)

 6. Formalize Q_nonneg_on_atoms_of_A3_RKHS_axiom - Rayleigh identification
 7. Formalize RKHS_contraction_axiom - ||T_P|| < 1 (hardest!)
 8. Formalize A3_bridge_axiom - Toeplitz-Symbol bridge (hardest!)

---
 Files to Modify

 Core chain:
 Q3/Basic/Defs.lean      - Add Continuous to Weil_cone (optional)
 Q3/Axioms.lean          - Remove axioms as they become theorems
 Q3/A2_Lipschitz.lean    - NEW: Lipschitz proof
 Q3/A1_Density_Proof.lean - NEW: Density proof
 Q3/RKHS_Proofs.lean     - NEW: S_K, row sum, contraction proofs
 Q3/A3_Proofs.lean       - NEW: Bridge + Rayleigh proofs

 Paper sources (full proofs):
 full/sections/A2.tex              - Lipschitz proof
 full/sections/A1prime.tex         - Density proof (lines 17-70)
 full/sections/RKHS/main.tex       - Contraction + S_K (lines 32-60)
 full/sections/A3/main.tex         - Bridge proof (lines 94-180)
 full/sections/A3/rayleigh_bridge.tex - Rayleigh (lines 52-90)

---
 Recommended Order

 1. Weil_cone_continuous - trivial, just refactor
 2. Q_Lipschitz_on_W_K - straightforward analysis
 3. S_K_small_axiom - geometric series, easy
 4. T_P_row_sum_bound_axiom - Gershgorin bound
 5. A1_density_WK_axiom - approximation theory
 6. Q_nonneg_on_atoms_of_A3_RKHS_axiom - Rayleigh bridge
 7. RKHS_contraction_axiom - HARD but doable
 8. A3_bridge_axiom - HARDEST (Toeplitz theory)

---
 Expected Outcome

 After formalization:
 - 0 Tier-2 axioms (all become theorems!)
 - 8 Tier-1 axioms (classical results, keep as axioms)
 - RH fully formalized conditional only on classical results

---
 User Decisions

 1. Start: Q_Lipschitz_on_W_K (easiest, 2/5)
 2. Method: Aristotle API for complex proofs (A3, RKHS)
 3. Tier-1: Keep as axioms (classical results 1911-1999)

---
 Execution Plan (TODO)

 Step 1: Q_Lipschitz_on_W_K

 - Read A2.tex proof (lines 40-70)
 - Create Q3/A2_Lipschitz.lean
 - Prove theorem manually (simple analysis)
 - Replace axiom in Axioms.lean with import

 Step 2: S_K_small_axiom

 - Read RKHS/main.tex:32-40 (geometric series)
 - Add proof to Q3/RKHS_Contraction.lean
 - Replace axiom

 Step 3: T_P_row_sum_bound_axiom

 - Read RKHS/main.tex:102-120 (Gershgorin)
 - Add proof to Q3/RKHS_Contraction.lean
 - Replace axiom

 Step 4: A1_density_WK_axiom

 - Prepare input for Aristotle (A1prime.tex)
 - Submit to Aristotle API
 - Review and integrate result
 - Replace axiom

 Step 5: Q_nonneg_on_atoms_of_A3_RKHS_axiom

 - Prepare Rayleigh bridge (A3/rayleigh_bridge.tex)
 - Submit to Aristotle
 - Review and integrate
 - Replace axiom

 Step 6: RKHS_contraction_axiom (HARD)

 - Prepare full RKHS proof (main.tex:45-90)
 - Submit to Aristotle
 - Review carefully (difficulty 4/5)
 - Replace axiom

 Step 7: A3_bridge_axiom (HARDEST)

 - Prepare Toeplitz bridge (A3/main.tex:94-180)
 - Submit to Aristotle
 - Review carefully (difficulty 4/5)
 - Replace axiom

 Final: Verify

 - Run lake build - 0 errors
 - Run #print axioms RH_of_Weil_and_Q3
 - Verify only Tier-1 axioms remain
 - Update zip archive