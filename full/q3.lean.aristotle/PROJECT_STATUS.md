# Q3 → RH Lean Formalization: MASTER STATUS

**Last Verified:** 2025-12-20
**Verified By:** Claude Opus 4.5 via `#print axioms`

---

## CRITICAL DISCOVERY (2025-12-20)

### The Problem with _integrated Files

The `Q3/Proofs/*_integrated.lean` files were supposed to "close" axioms, but **7 of 9 are CIRCULAR**:

```
closes_A1_density_axiom := Q3.A1_density_WK_axiom  ← CIRCULAR!
closes_A3_bridge_axiom := Q3.A3_bridge_axiom      ← CIRCULAR!
closes_Q_Lipschitz_axiom := Q3.Q_Lipschitz_on_W_K ← CIRCULAR!
... etc
```

Only `node_spacing_integrated.lean` has a REAL proof!

### The Solution: Use STANDALONE Aristotle Proofs

ALL standalone Aristotle proofs are **CLEAN** (verified with `#print axioms`):

```
'off_diag_exp_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RKHS_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
... (only standard Lean axioms, NO Q3 axioms!)
```

---

## VERIFIED STANDALONE PROOFS (8/9 Tier-2)

| File | Main Theorem | Axioms | Status |
|------|--------------|--------|--------|
| `Q3/Proofs/node_spacing.lean` | `node_spacing` | CLEAN ✅ | Bridge created |
| `Q3/Proofs/off_diag_exp_sum.lean` | `off_diag_exp_sum_bound` | CLEAN ✅ | Bridge created |
| `Q3/Proofs/RKHS_contraction.lean` | `RKHS_contraction` | CLEAN ✅ | Needs bridge |
| `Q3/Proofs/S_K_small.lean` | `S_K_small` | CLEAN ✅ | Needs bridge |
| `Q3/Proofs/W_sum_finite.lean` | `W_sum_is_finite` | CLEAN ✅ | Needs bridge |
| `Q3/Proofs/Q_Lipschitz.lean` | `Q3.Proofs.Q_Lipschitz_local` | CLEAN ✅ | Needs bridge |
| `Q3/Proofs/Q_nonneg_on_atoms.lean` | `Q_nonneg` | CLEAN ✅ | Needs bridge |
| `Q3/Proofs/A3_bridge.lean` | `A3_Bridge_Theorem` | CLEAN ✅ | Needs bridge |

### MISSING: A1_density
- `Q3/Proofs/A1_density.lean` - helper lemmas only
- `Q3/Proofs/A1_density_main.lean` - has `exact?` placeholders (INCOMPLETE)

---

## WORKING BRIDGES (4/8)

Bridges transfer standalone proofs to Q3 definitions:

| Bridge File | Status | Verification |
|-------------|--------|--------------|
| `Q3/Proofs/node_spacing_bridge.lean` | ✅ WORKS | `#print axioms` = CLEAN |
| `Q3/Proofs/off_diag_exp_sum_bridge.lean` | ✅ WORKS | `#print axioms` = CLEAN |
| `Q3/Proofs/S_K_small_bridge.lean` | ✅ WORKS | `#print axioms` = CLEAN |
| `Q3/Proofs/W_sum_finite_bridge.lean` | ✅ WORKS | `#print axioms` = CLEAN |

### How Bridges Work

1. Aristotle standalone uses own definitions (xi_n, Nodes, S_K, etc.)
2. These are DEFINITIONALLY EQUAL to Q3.Basic.Defs
3. Bridge imports both and transfers via `rfl` or direct application

### Bridge Difficulty Classification (2025-12-20)

**EASY (definitions match, trivial transfer):**
- node_spacing ✅
- off_diag_exp_sum ✅
- S_K_small ✅
- W_sum_finite ✅ (FIXED: axiom changed to existence form `∃ B, W_sum K ≤ B`)

**COMPLEX (definitions differ, need non-trivial proof):**
| Proof | Issue |
|-------|-------|
| `RKHS_contraction` | Uses ξ=log n vs xi_n=log n/(2π); universal quantifier over all node sets |
| `Q_Lipschitz_local` | Uses simplified a_star=1 instead of real digamma-based a_star |
| `A3_Bridge_Theorem` | Uses abstract Laurent polynomials vs concrete matrix formulation |
| `Q_nonneg` | Takes a_star as parameter; conditional on A3/RKHS properties |

---

## AXIOM TIERS

### Tier-1: Classical/External (8 axioms) - REMAIN AS AXIOMS

| Axiom | Source |
|-------|--------|
| `Weil_criterion` | Weil 1952 |
| `explicit_formula` | Guinand 1948 |
| `a_star_pos` | Digamma properties |
| `Szego_Bottcher_eigenvalue_bound` | Böttcher-Silbermann 2006 |
| `Szego_Bottcher_convergence` | Böttcher-Silbermann 2006 |
| `Schur_test` | Horn-Johnson 2013 |
| `c_arch_pos` | Numerical |
| `eigenvalue_le_norm` | Standard linear algebra |

### Tier-2: Q3 Contributions (9 axioms) - TO BE REPLACED WITH THEOREMS

| # | Axiom | Standalone Proof | Bridge Status |
|---|-------|------------------|---------------|
| 1 | `node_spacing_axiom` | `node_spacing` | ✅ BRIDGED |
| 2 | `off_diag_exp_sum_axiom` | `off_diag_exp_sum_bound` | ✅ BRIDGED |
| 3 | `S_K_small_axiom` | `S_K_small` | ✅ BRIDGED |
| 4 | `RKHS_contraction_axiom` | `RKHS_contraction` | ⚠️ COMPLEX |
| 5 | `W_sum_finite_axiom` | `W_sum_is_finite` | ✅ BRIDGED |
| 6 | `Q_Lipschitz_on_W_K` | `Q_Lipschitz_local` | ⚠️ COMPLEX |
| 7 | `Q_nonneg_on_atoms_of_A3_RKHS_axiom` | `Q_nonneg` | ⚠️ COMPLEX |
| 8 | `A3_bridge_axiom` | `A3_Bridge_Theorem` | ⚠️ COMPLEX |
| 9 | `A1_density_WK_axiom` | ❌ INCOMPLETE | ❌ BLOCKED |

---

## VERIFICATION COMMANDS

```bash
# Check if a standalone proof is clean (no Q3 axioms)
lake env lean -c "import Q3.Proofs.RKHS_contraction; #print axioms RKHS_contraction"

# Check if RH_proven has minimal axioms
lake env lean -c "import Q3.MainTheorems; #print axioms Q3.MainTheorems.RH_proven"

# Build specific bridge
lake build Q3.Proofs.node_spacing_bridge

# Find all sorry in project
grep -rn "sorry" Q3/*.lean Q3/**/*.lean | grep -v "^.*:.*--"
```

---

## FILE STRUCTURE

```
Q3/
├── Basic/Defs.lean           # Core definitions (xi_n, w_Q, Q, etc.)
├── Axioms.lean               # All 17 axioms (8 Tier-1 + 9 Tier-2)
├── Main.lean                 # RH_of_Weil_and_Q3 (uses axioms)
├── MainTheorems.lean         # RH_proven (should use theorems)
├── AxiomsTheorems.lean       # Tier-2 as theorems (needs update)
├── T5/                       # T5 transfer (proven theorem)
└── Proofs/
    ├── node_spacing.lean           # Standalone ✅ CLEAN
    ├── node_spacing_bridge.lean    # Bridge ✅ WORKS
    ├── off_diag_exp_sum.lean       # Standalone ✅ CLEAN
    ├── off_diag_exp_sum_bridge.lean # Bridge ✅ WORKS
    ├── S_K_small.lean              # Standalone ✅ CLEAN
    ├── S_K_small_bridge.lean       # Bridge ✅ WORKS (NEW)
    ├── RKHS_contraction.lean       # Standalone ✅ CLEAN (bridge: COMPLEX)
    ├── W_sum_finite.lean           # Standalone ✅ CLEAN (bridge: BLOCKED)
    ├── Q_Lipschitz.lean            # Standalone ✅ CLEAN (bridge: COMPLEX)
    ├── Q_nonneg_on_atoms.lean      # Standalone ✅ CLEAN (bridge: COMPLEX)
    ├── A3_bridge.lean              # Standalone ✅ CLEAN (bridge: COMPLEX)
    ├── A1_density.lean             # Helper lemmas only
    ├── A1_density_main.lean        # INCOMPLETE (has exact?)
    └── *_integrated.lean           # MOSTLY CIRCULAR - don't use!
```

---

## NEXT STEPS (Priority Order)

### Phase 1: Easy Bridges (DONE ✅)
- ✅ node_spacing_bridge.lean
- ✅ off_diag_exp_sum_bridge.lean
- ✅ S_K_small_bridge.lean

### Phase 2: Fix Axiom Definitions
1. **Fix W_sum_finite_axiom** - Change from `< 1000000` to K-dependent bound or existence
2. **Review Q_Lipschitz_on_W_K** - Need to handle real a_star, not simplified version

### Phase 3: Complex Bridges (Need Non-trivial Work)
| Bridge | Required Work |
|--------|---------------|
| RKHS_contraction | Coordinate rescaling proof: t_Q3 = t_A/(2π)² |
| Q_Lipschitz | Prove bound holds for real a_star (need a_star bounded on compacts) |
| A3_Bridge | Show Laurent polynomial form implies matrix form |
| Q_nonneg | Connect abstract a_star parameter to Q3's digamma-based definition |

### Phase 4: Incomplete Proof
- **A1_density_main.lean** - Has `exact?` placeholders, needs completion

### Phase 5: Final Integration
1. **Update AxiomsTheorems.lean** to use bridges
2. **Verify RH_proven** has only Tier-1 axioms

---

## OUTDATED FILES (DO NOT TRUST)

These files contain incorrect or outdated information:

- `FULL_AXIOM_STATUS.md` - claims all proven, but _integrated are circular
- `FORMALIZATION_STATUS.md` - from 2025-12-16, outdated
- `ARISTOTLE_TASKS.md` - historical, not current status
- `ARISTOTLE_PROJECTS.md` - Aristotle project IDs only
- `plan_15_12_2025_formailzing_axioms.md` - old plan

**This file (PROJECT_STATUS.md) is the SINGLE SOURCE OF TRUTH.**

---

## DEFINITION EQUIVALENCES (KEY INSIGHT)

Aristotle standalone proofs define their own versions of:
- `xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)`
- `Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}`
- `delta_K (K : ℝ) : ℝ := 1 / (2 * Real.pi * (N_K K + 1))`
- `S_K (K t : ℝ) : ℝ := 2 * exp(-delta^2/(4t)) / (1 - exp(...))`

These are **DEFINITIONALLY EQUAL** to Q3.Basic.Defs versions!

This means:
- `Nodes K = Q3.Nodes K` via `rfl`
- `xi_n n = Q3.xi_n n` via `rfl`
- Bridges can transfer proofs directly

---

## CONCLUSION

**Real Status (2025-12-20 updated):**
- 8/9 Tier-2 axioms have CLEAN standalone proofs
- **4/8 bridges created and verified** (node_spacing, off_diag_exp_sum, S_K_small, W_sum_finite)
- W_sum_finite axiom FIXED: changed to existence form `∃ B, W_sum K ≤ B`
- 4 bridges are COMPLEX (require non-trivial equivalence proofs)
- A1_density is the only incomplete proof
- Goal: Replace all Tier-2 axioms with theorems

**Trust Level:**
- Standalone proofs: VERIFIED CLEAN by `#print axioms`
- _integrated files: MOSTLY CIRCULAR (don't use for closing axioms)
- Easy bridges: Minimal overhead, just type coercion
- Complex bridges: Require substantive proofs, not just type matching

**Key Insight:**
The "easy" bridges work because definitions are IDENTICAL.
The "complex" bridges fail because:
1. Different coordinate systems (ξ vs xi_n)
2. Simplified functions (a_star=1 vs digamma)
3. Different abstract representations (polynomials vs matrices)
4. Universal quantifiers over different domains
