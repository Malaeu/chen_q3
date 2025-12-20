# COMPLETE BRIDGE AUDIT

**Date:** 2025-12-20
**Source:** Deep analysis of all Aristotle proof files vs Q3 axioms

---

## EXECUTIVE SUMMARY

The "complex bridge" narrative is **WRONG**. The rescaling issue is **RKHS_contraction-specific**, NOT global.

| File | Coordinate | Rescaling Needed? |
|------|------------|-------------------|
| `node_spacing.lean` | `xi_n = log n/(2π)` | ❌ NO |
| `off_diag_exp_sum.lean` | `xi_n = log n/(2π)` | ❌ NO |
| `W_sum_finite.lean` | `xi_n = log n/(2π)` | ❌ NO |
| `A3_bridge.lean` | `PrimeNode = log n/(2π)` | ❌ NO |
| `Q_nonneg_on_atoms.lean` | `xi = log n/(2π)` | ❌ NO |
| `Q_Lipschitz.lean` | uses `Q3.xi_n` | ❌ NO |
| **`RKHS_contraction.lean`** | `ξ = log n` | ✅ YES! |

**Conclusion:** Only RKHS_contraction needs coordinate rescaling. Others have DIFFERENT problems.

---

## CANONICAL Q3 COORDINATE (Authoritative)

```lean
-- File: Q3/Basic/Defs.lean
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)
def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}
```

All Tier-2 axioms in `Q3/Axioms.lean` use this coordinate system.

---

## PROBLEM 1: RKHS_contraction - COORDINATE + K RESCALING

### The Outlier File

```lean
-- File: Q3/Proofs/RKHS_contraction.lean
noncomputable def ξ (n : ℕ) : ℝ := Real.log n  -- NO (2π)!
def nodes (K : ℝ) : Finset ℕ := ... filter (fun n => ... Real.log n ≤ K)
```

### Rescaling Requirements

**Coordinate relationship:**
```
ξ = 2π · xi_n
```

**For Gaussian kernel:**
```
exp(-(xi_n_i - xi_n_j)² / (4·t_Q3)) = exp(-(ξ_i - ξ_j)² / (4·t_A))
```

Requires:
```
t_A = (4π²) · t_Q3
t_Q3 = t_A / (4π²)
```

**For K parameter (MISSING FROM PREVIOUS ANALYSIS!):**
```
xi_n n ≤ K_Q3  ⟺  log n ≤ (2π)·K_Q3
```

So:
```
K_A = (2π) · K_Q3
K_Q3 = K_A / (2π)
```

### Required Bridge Lemmas

```lean
namespace Q3.Bridge

noncomputable def xiA (n : ℕ) : ℝ := Real.log n

lemma xi_q3_eq_xiA_div_2pi (n : ℕ) :
  Q3.xi_n n = xiA n / (2 * Real.pi) := rfl

def K_rescale (K_Q3 : ℝ) : ℝ := (2 * Real.pi) * K_Q3

lemma exp_kernel_rescale (n m : ℕ) (t_A : ℝ) (ht : 0 < t_A) :
  let t_Q3 := t_A / (4 * Real.pi^2)
  Real.exp (-(Q3.xi_n n - Q3.xi_n m)^2 / (4 * t_Q3))
    = Real.exp (-(xiA n - xiA m)^2 / (4 * t_A)) := by ...

end Q3.Bridge
```

### CRITICAL: Statement-Strength Mismatch

**Q3 Axiom (STRONGER):**
```lean
axiom RKHS_contraction_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
  ∀ (Nodes_K : Set ℕ) [Fintype Nodes_K],  -- ANY finite node set!
    ∀ (T_P : Matrix Nodes_K Nodes_K ℝ), T_P.IsSymm →
    (∀ i j : Nodes_K, T_P i j = ...) →
    ‖T_P‖ ≤ ρ
```

**Aristotle Proves (WEAKER):**
- Contraction for a SPECIFIC node type `Node K` built from `Finset nodes K`
- Not for arbitrary `Nodes_K : Set ℕ`

**Resolution Options:**
1. **Weaken the axiom** to match what's proven (recommended)
2. **Add monotonicity lemmas** showing contraction on maximal set implies contraction on subsets

---

## PROBLEM 2: Q_Lipschitz - NO RESCALING, BUT WRONG OBJECTS

### Coordinate Situation
- Uses Q3's `xi_n` ✓
- **NO rescaling needed**

### Actual Problem

```lean
-- File: Q3/Proofs/Q_Lipschitz.lean
noncomputable def a_star_const (ξ : ℝ) : ℝ := 1  -- TOY VERSION!
noncomputable def Q_local (Φ : ℝ → ℝ) : ℝ := arch_term_const Φ - prime_term_local Φ
```

This proves Lipschitz for `Q_local` with `a_star = 1`, NOT for `Q3.Q` with real `a_star`.

### Required Changes

Option A: **Generalize the proof**
- Replace `a_star_const` with `Q3.a_star`
- Replace `Q_local` with `Q3.Q`
- Replace `W_K_local` with `Q3.W_K`
- Add boundedness lemma: `BddAbove (Set.image Q3.a_star (Set.Icc (-K) K))`

Option B: **Accept it as partial**
- Rename to make clear it's a toy version
- Add axiom for `a_star` continuity/boundedness

---

## PROBLEM 3: A3_bridge - NO RESCALING, BUT REPRESENTATION MISMATCH

### Coordinate Situation
- Uses `PrimeNode := log n/(2π)` ✓
- **NO rescaling needed**

### Actual Problem: Different Mathematical Objects

**Aristotle uses:**
```lean
-- LaurentPolynomial representation
noncomputable def ToeplitzForm (P_A : ℝ → ℝ) (p : LaurentPolynomial ℂ) : ℝ :=
  (∫ θ in (0)..(2*π), P_A θ * Complex.normSq (evalTrig p θ)) / (2 * π)

noncomputable def PrimeForm (B t : ℝ) (p : LaurentPolynomial ℂ) : ℝ :=
  ∑' n, PrimeWeight n * FejerHeatWindow B t (PrimeNode n) * Complex.normSq (evalTrig p (PrimeNode n))
```

**Q3 axiom uses:**
```lean
-- Matrix representation
def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ := ...
-- Rayleigh quotient: (∑ i, ∑ j, v i * v j * ...) / (∑ i, v i ^ 2)
```

### Additional Kernel Mismatch

Aristotle's `FejerHeatWindow`:
```lean
exp(-4 * π^2 * t * ξ^2)  -- Fourier domain
```

Q3's RKHS kernel:
```lean
exp(-(Δξ)^2 / (4*t))  -- Position domain
```

These are related by Fourier duality but NOT syntactically equal.

### Resolution Options

1. **Change Q3's axiom** to form-based version (adapt downstream code)
2. **Build full equivalence layer:**
   - Laurent polynomial ↔ coefficient vector
   - ToeplitzForm = v^T · T · v
   - PrimeForm = v^T · P · v
   - Kernel equivalence via Fourier

Option 2 is SUBSTANTIAL work.

---

## PROBLEM 4: Q_nonneg - NO RESCALING, BUT ATOMCONE MISMATCH

### Coordinate Situation
- Uses `xi := log n/(2π)` ✓
- **NO rescaling needed**

### Actual Problem: AtomCone Definition Mismatch

**Aristotle's AtomCone:**
```lean
def AtomCone (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (s : Finset _) (c : _ → ℝ),
    (∀ f ∈ s, f ∈ Atoms K) ∧
    (∀ f ∈ s, 0 ≤ c f) ∧
    s.sum (fun f => c f • f) = g }
-- NO constraint on B ≤ K
-- NO explicit g ∈ W_K
```

**Q3's AtomCone_K:**
```lean
def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ ... ,
    (∀ i, B i ≤ K) ∧     -- EXTRA constraint!
    g ∈ W_K K }           -- EXTRA constraint!
```

### Resolution Options

1. **Strengthen Aristotle's AtomCone** to match Q3's constraints
2. **Prove embedding lemma** (nontrivial):
   ```lean
   lemma AtomCone_local_subset_AtomCone_K (K : ℝ) :
     AtomCone_local K ⊆ Q3.AtomCone_K K
   ```

### Data Plumbing Mismatch

Also need conversion lemmas:
```lean
lemma A3_bridge_data_to_local :
  Q3.A3_bridge_data K → A3BridgeProperty_local K Q3.a_star ... := ...

lemma RKHS_data_to_local :
  Q3.RKHS_contraction_data K → RKHSContractionProperty_local K := ...
```

---

## REVISED BRIDGE DIFFICULTY CLASSIFICATION

| Bridge | Rescaling? | Real Problem | Difficulty |
|--------|------------|--------------|------------|
| **Q_nonneg** | NO | AtomCone mismatch + data plumbing | MEDIUM |
| **RKHS** | YES (t AND K) | Statement strength mismatch | MEDIUM-HARD |
| **Q_Lipschitz** | NO | a_star = 1 toy version | MEDIUM |
| **A3** | NO | Form vs Matrix representation | HARD |

---

## ACTION PLAN

### 1. Update/Rename Bridge.lean
- **Current:** `Q3/Proofs/Bridge.lean` implies global rescaling
- **Rename to:** `Q3/Proofs/RKHS_coordinate_rescaling.lean`
- **Add:** K-rescaling lemmas, not just t

### 2. RKHS_contraction Bridge
- **Decision needed:** Weaken axiom OR add monotonicity lemmas
- **Create:** `Q3/Proofs/RKHS_contraction_bridge.lean`

### 3. Q_Lipschitz
- **Option A:** Generalize to real a_star (needs continuity lemma)
- **Option B:** Accept as toy, document limitation

### 4. A3_bridge
- **Decision needed:** Form-based axiom OR full equivalence layer
- **Document:** Kernel mismatch (Fourier duality)

### 5. Q_nonneg Bridge
- **Fix:** AtomCone definition alignment
- **Add:** Data plumbing conversions

---

## FILES TO MODIFY

| File | Change |
|------|--------|
| `Q3/Proofs/Bridge.lean` | Rename, add K-rescaling, clarify scope |
| `Q3/Axioms.lean` | Possibly weaken RKHS axiom |
| `Q3/Proofs/Q_Lipschitz.lean` | Either generalize or rename |
| (new) `Q3/Proofs/RKHS_contraction_bridge.lean` | Create with rescaling |
| `Q3/Proofs/Q_nonneg_bridge.lean` | Fix AtomCone, add conversions |

---

## KEY INSIGHT

The "complex bridge" problem is NOT about coordinates.

**Real problems by category:**

1. **Statement Strength:** RKHS axiom is stronger than proof
2. **Object Representation:** A3 uses forms, Q3 uses matrices
3. **Definition Constraints:** AtomCone has extra requirements in Q3
4. **Function Simplification:** Q_Lipschitz uses a_star = 1

Rescaling is a MINOR issue affecting only ONE file.
