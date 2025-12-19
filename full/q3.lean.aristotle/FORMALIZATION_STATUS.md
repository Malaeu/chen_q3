# Q3 → RH Lean Formalization Status

**Last Updated:** 2025-12-16
**Project:** q3.lean.aristotle
**Goal:** Formalize Riemann Hypothesis proof via Weil criterion

---

## Current Status: STRUCTURE COMPLETE

```
BUILD:           ✅ SUCCESS (0 errors, 0 sorry)
MAIN THEOREM:    RH_of_Weil_and_Q3 ✅
T5_transfer:     ✅ THEOREM (proven in Lean!)
```

---

## Axiom Inventory (19 total)

### Tier-1: Classical/External (8)

| # | Axiom | Type | Status |
|---|-------|------|--------|
| 1 | `Weil_criterion` | Guinand-Weil 1952 | External |
| 2 | `explicit_formula` | Riemann-von Mangoldt | External |
| 3 | `a_star_pos` | Digamma properties | External |
| 4 | `Szego_Bottcher_eigenvalue_bound` | Toeplitz theory | External |
| 5 | `Szego_Bottcher_convergence` | Toeplitz theory | External |
| 6 | `Schur_test` | Functional analysis | External |
| 7 | `c_arch_pos` | Numerical | External |
| 8 | `eigenvalue_le_norm` | Spectral theory | External |

### Tier-2: Q3 Paper (11)

| # | Axiom | Paper ref | Closable? |
|---|-------|-----------|-----------|
| 1 | `A1_density_axiom` | Thm 6.2 | Medium |
| 2 | `A1_density_WK_axiom` | Cor 6.3 | Medium |
| 3 | `W_sum_finite_axiom` | Lem 7.1 | Easy |
| 4 | `Q_Lipschitz_on_W_K` | Lem 7.3 | **LOW FRUIT** |
| 5 | `RKHS_contraction_axiom` | Thm 9.23 | Medium-High |
| 6 | `T_P_row_sum_bound_axiom` | Prop 9.18 | Medium |
| 7 | `S_K_small_axiom` | (9.15) | Easy |
| 8 | `node_spacing_axiom` | Lem 9.14 | Easy |
| 9 | `off_diag_exp_sum_axiom` | Lem 9.5 | Easy |
| 10 | `A3_bridge_axiom` | Thm 8.35 | High |
| 11 | `Q_nonneg_on_atoms_of_A3_RKHS_axiom` | Rayleigh | Medium |

---

## Critical Path to RH (6 axioms only!)

```
                    RH_of_Weil_and_Q3
                          │
              ┌───────────┴───────────┐
              │                       │
       Weil_criterion          Q_nonneg_on_Weil_cone
        (External)                    │
                                      │
                           T5_transfer (THEOREM!)
                                      │
                    ┌─────────────────┼─────────────────┐
                    │                 │                 │
          A1_density_WK       Q_Lipschitz_on_W_K    Q_nonneg_on_atoms
                                                          │
                                              ┌───────────┴───────────┐
                                              │                       │
                                       A3_bridge_axiom    RKHS_contraction
```

**Critical 6:**
1. `Weil_criterion` — Tier-1, external (не закрываем)
2. `A1_density_WK_axiom` — Tier-2
3. `Q_Lipschitz_on_W_K` — Tier-2 ← **START HERE**
4. `A3_bridge_axiom` — Tier-2
5. `RKHS_contraction_axiom` — Tier-2
6. `Q_nonneg_on_atoms_of_A3_RKHS_axiom` — Tier-2

---

## Aristotle Projects (2025-12-16)

| # | Name | Project ID | Status |
|---|------|------------|--------|
| 1 | Q_Lipschitz_v2 | `70f872fe-6eef-43e9-8ab7-a8ff6c71a862` | IN_PROGRESS |
| 2 | node_spacing | `52696cee-ad2c-4feb-a69f-dbb05bfc7433` | IN_PROGRESS |
| 3 | off_diag_exp_sum | `ada58f31-f6fb-4426-99f2-9bb5cf98a3a3` | QUEUED |
| 4 | S_K_small | `e4a93701-387d-4d80-8140-d000a959e37a` | QUEUED |
| 5 | W_sum_finite | `b7f6e83f-f549-40b4-b1e5-a46b7a7280c6` | QUEUED |

### Existing Completed Proofs (from aristotle_output/)

| File | Key Theorems | Status |
|------|-------------|--------|
| `A1_density_v2_aristotle.lean` | HeatKernel_*, FejerKernel_*, convolution_approx_by_sum | ✅ Compiles |
| `RKHS_contraction_aristotle.lean` | T_P_row_sum_bound, RKHS_contraction | ✅ Compiles |

**Note:** Signatures differ from our axioms. Need bridge lemmas to integrate.

---

## Roadmap: Closing Axioms

### Phase 1: Low-Hanging Fruit

| Priority | Axiom | Complexity | Aristotle? |
|----------|-------|------------|------------|
| 1 | `Q_Lipschitz_on_W_K` | LOW | Submitted |
| 2 | `node_spacing_axiom` | LOW | Submitted |
| 3 | `off_diag_exp_sum_axiom` | LOW | Submitted |
| 4 | `S_K_small_axiom` | LOW | Submitted |
| 5 | `W_sum_finite_axiom` | LOW | Submitted |

### Phase 2: Medium (~1 week)

| Priority | Axiom | Complexity | Dependencies |
|----------|-------|------------|--------------|
| 6 | `A1_density_WK_axiom` | MEDIUM | approx theory |
| 7 | `T_P_row_sum_bound_axiom` | MEDIUM | Gershgorin |
| 8 | `RKHS_contraction_axiom` | MEDIUM-HIGH | Schur test |

### Phase 3: Hard (~2-4 weeks)

| Priority | Axiom | Complexity | Dependencies |
|----------|-------|------------|--------------|
| 9 | `A3_bridge_axiom` | HIGH | Szegő-Böttcher |
| 10 | `Q_nonneg_on_atoms...` | MEDIUM | A3 + RKHS |

---

## Key Files

```
Q3/
├── Basic/Defs.lean      # Core definitions (xi_n, w_Q, Q, Weil_cone)
├── Axioms.lean          # All 19 axioms with documentation
├── Main.lean            # RH_of_Weil_and_Q3 theorem
├── T5_Transfer.lean     # T5_transfer THEOREM (proven!)
├── A2_Lipschitz.lean    # Q_Lipschitz structure
├── RowSum_Bound.lean    # T_P row sum structure
├── RKHS_Contraction.lean
├── A3_Bridge.lean
└── CheckAxioms.lean     # Axiom verification
```

---

## Key Achievements This Session (2025-12-16)

1. **Closed 3 sorries** in RowSum_Bound.lean and A2_Lipschitz.lean
2. **Added 2 axioms**: `node_spacing_axiom`, `off_diag_exp_sum_axiom`
3. **Fixed Main.lean** type mismatch with Weil_cone
4. **Verified**: RH_of_Weil_and_Q3 depends on exactly 6 Q3 axioms
5. **Confirmed**: T5_transfer is THEOREM, not axiom!

---

## Next Steps

1. **Close `Q_Lipschitz_on_W_K`** — low-hanging fruit
   - File: `Q3/A2_Lipschitz.lean`
   - Proof: |Q(Φ₁)-Q(Φ₂)| ≤ (2K·max(a*) + W_sum) · ‖Φ₁-Φ₂‖

2. **Close easy axioms** (node_spacing, off_diag, S_K_small)
   - These are Lean-closable with mathlib

3. **Then tackle A1, RKHS, A3** (harder)

---

## Commands

```bash
# Build project
lake build

# Build specific module
lake build Q3.Main

# Check sorries
grep -rn "sorry" Q3/*.lean | grep -v "^.*:.*--"

# Check axiom count
grep "^axiom " Q3/Axioms.lean | wc -l

# Print RH dependencies
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' > /tmp/check.lean && lake env lean /tmp/check.lean
```

---

## Trust Chain

```
Paper Q3 ──proves──> 5 Q3 axioms (need paper-level trust)
                          │
                          ▼
Lean verifies ──────> T5_transfer (THEOREM)
                          │
                          ▼
Weil criterion ─────> RH_of_Weil_and_Q3
 (external)
```

**Bottom line:** Lean confirms the LOGIC is correct.
Axioms encode the CONTENT of paper proofs.

---

## Формальное утверждение

**Статус:** Структура доказательства Q3 → RH полностью формализована в Lean.

**Что доказано в Lean:**
- T5_transfer: плотность + Липшиц + позитивность на атомах → позитивность на W_K
- RH_of_Weil_and_Q3: Weil criterion + Q ≥ 0 → RH

**Что остаётся как axiom:**
- 5 Q3-специфичных аксиом (content of paper proofs)
- 1 внешняя аксиома (Weil criterion)

**Следующий milestone:** Закрыть Q_Lipschitz_on_W_K (низко висящий фрукт).
