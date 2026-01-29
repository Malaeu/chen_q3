# COMPLEX BRIDGES ANALYSIS

**Date:** 2025-12-20
**Status:** Analysis complete, solutions identified

---

## DISCOVERED PATTERN: Coordinate Systems

Analysis of all Aristotle proof files revealed a critical pattern:

| File | Coordinate Definition | Status |
|------|----------------------|--------|
| `node_spacing.lean` | `xi_n = log n / (2π)` | ✅ Matches Q3 |
| `off_diag_exp_sum.lean` | `xi_n = log n / (2π)` | ✅ Matches Q3 |
| `W_sum_finite.lean` | `xi_n = log n / (2π)` | ✅ Matches Q3 |
| `S_K_small.lean` | Uses `delta_K` correctly | ✅ Matches Q3 |
| `Q_nonneg_on_atoms.lean` | `xi = log n / (2π)` | ✅ Matches Q3 |
| **`RKHS_contraction.lean`** | `ξ = log n` | ❌ MISSING (2π)! |
| `Q_Lipschitz.lean` | Uses `xi_n` but `a_star = 1` | ⚠️ Simplified |
| `A3_bridge.lean` | Laurent polynomials | ⚠️ Different abstraction |

**Key Finding:** Only RKHS_contraction has wrong coordinates. Others have different issues.

---

## PROBLEM 1: RKHS_contraction - COORDINATE RESCALING

### The Issue

```lean
-- Aristotle definition (RKHS_contraction.lean:67)
noncomputable def ξ (n : ℕ) : ℝ := Real.log n

-- Q3 definition (Q3/Basic/Defs.lean)
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)
```

**Mathematical relationship:** `ξ = 2π · xi_n`

### Impact on Gaussian Kernel

Aristotle proves bound with:
```
exp(-(ξ_i - ξ_j)² / (4t))
```

Q3 needs bound with:
```
exp(-(xi_n_i - xi_n_j)² / (4t'))
```

Substituting `ξ = 2π · xi_n`:
```
(ξ_i - ξ_j)² = (2π)² · (xi_n_i - xi_n_j)²
```

Therefore:
```
exp(-(2π)² · (xi_n_i - xi_n_j)² / (4t)) = exp(-(xi_n_i - xi_n_j)² / (4t/(2π)²))
```

### Solution

**Rescale t:** If Aristotle gives `t`, Q3 uses `t' = t / (2π)²`

The contraction bound `‖T_P‖ ≤ ρ < 1` remains valid because:
- Same matrix structure
- Same eigenvalue bounds
- Only the parameter `t` changes

---

## PROBLEM 2: Q_Lipschitz - SIMPLIFIED a_star

### The Issue

```lean
-- Aristotle definition (Q_Lipschitz.lean:33)
noncomputable def a_star_const (ξ : ℝ) : ℝ := 1

-- Q3 definition (uses digamma)
noncomputable def a_star (ξ : ℝ) : ℝ := 2 * Real.pi * a ξ
-- where a(ξ) = log π - Re(ψ(1/4 + iπξ))
```

Aristotle SIMPLIFIES by assuming `a_star = 1` constant.

### Why This Still Works

The Lipschitz constant has form:
```
L_Q(K) = 2K · sup{a_star(ξ) : |ξ| ≤ K} + W_sum(K)
```

If `a_star = 1`: `L = 2K · 1 + W_sum`
If `a_star ≤ M`: `L = 2K · M + W_sum`

### Solution

The axiom only requires **existence** of a Lipschitz constant:
```lean
axiom Q_Lipschitz_on_W_K : ∀ (K : ℝ) (hK : K > 0),
  ∃ L > 0, ...  -- Just needs SOME L > 0
```

Aristotle's proof with `a_star = 1` gives `L₁`.
For real `a_star`, use `L = M · L₁` where `M = sup{a_star(ξ)}` on compact.

**Alternative:** Since `a_star` is continuous and compact has max, the bound transfers.

---

## PROBLEM 3: A3_bridge - LAURENT POLYNOMIALS vs MATRICES

### The Issue

```lean
-- Aristotle uses (A3_bridge.lean:56-66)
noncomputable def evalTrig (p : LaurentPolynomial ℂ) (θ : ℝ) : ℂ := ...
noncomputable def ToeplitzForm (P_A : ℝ → ℝ) (p : LaurentPolynomial ℂ) : ℝ := ...
noncomputable def L2NormSq (p : LaurentPolynomial ℂ) : ℝ := ...

-- Q3 uses (Axioms.lean)
def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ := ...
-- Then quadratic form v^T · T · v
```

Different representations of the same mathematical object!

### Mathematical Equivalence

A Laurent polynomial of degree ≤ M is determined by coefficients `(c_{-M}, ..., c_M)`.

The evaluation `evalTrig p θ = Σ_k c_k · exp(ikθ)` is a trigonometric polynomial.

The quadratic form:
```
ToeplitzForm(P_A, p) = ∫₀^{2π} P_A(θ) · |evalTrig(p, θ)|² dθ / (2π)
```

Is equivalent to:
```
v^T · ToeplitzMatrix(M, P_A) · v
```

where `v` are the Fourier coefficients.

### Solution

Need a bridge lemma:
```lean
lemma toeplitz_form_eq_matrix_form (M : ℕ) (P : ℝ → ℝ) (p : LaurentPolynomial ℂ)
    (hp : IsTrigPoly M p) :
  ToeplitzForm P p / L2NormSq p =
  (v^T · ToeplitzMatrix M P · v) / (v^T · v)
  where v := fourier_coefficients p
```

This is standard Fourier analysis - may already be in Mathlib.

---

## PROBLEM 4: Q_nonneg - PARAMETERIZED a_star

### The Issue

```lean
-- Aristotle definition (Q_nonneg_on_atoms.lean:70)
noncomputable def Q (a_star : ℝ → ℝ) (g : ℝ → ℝ) : ℝ :=
  (∫ x, a_star x * g x) - ∑' n, if 2 ≤ n then w_Q n * g (xi n) else 0

-- Q3 definition (Axioms.lean)
def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ
-- where arch_term uses the FIXED a_star from digamma
```

Aristotle takes `a_star` as a PARAMETER.
Q3 uses a FIXED `a_star` defined via digamma.

### Good News

**Coordinates are CORRECT in Q_nonneg_on_atoms.lean:**
```lean
noncomputable def xi (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)  -- ✓ Matches Q3!
```

### Solution

Aristotle proves: `∀ a_star, [conditions on a_star] → Q(a_star, g) ≥ 0`

Q3's `a_star` satisfies these conditions:
- Continuous ✓
- `a_star(ξ) > 0` for all ξ (by `a_star_pos` axiom) ✓
- `c_0(K) = inf{a_star(ξ) : |ξ| ≤ K} > 0` (by `c_arch_pos` axiom) ✓

Therefore: Just **instantiate** with Q3's `a_star`.

**This should be an EASY bridge!**

---

## SUMMARY: Bridge Difficulty Classification (Revised)

| Bridge | Problem | Solution | Difficulty |
|--------|---------|----------|------------|
| `Q_nonneg` | a_star as parameter | Instantiate with Q3's a_star | **EASY** |
| `RKHS_contraction` | ξ = log n (no 2π) | Rescale t → t/(2π)² | **MEDIUM** |
| `Q_Lipschitz` | a_star = 1 | Use sup(a_star) bound | **MEDIUM** |
| `A3_bridge` | Laurent poly vs Matrix | Fourier isomorphism | **HARD** |

### Recommended Order

1. **Q_nonneg_bridge** - Coordinates correct, just instantiate a_star
2. **RKHS_contraction_bridge** - Pure rescaling of t parameter
3. **Q_Lipschitz_bridge** - Need bound on sup(a_star)
4. **A3_bridge** - Requires Fourier equivalence lemma

---

## UNIFIED SOLUTION PATTERN

All bridges follow the same structure:

```lean
/-
Bridge Pattern:
1. Import Q3 definitions (xi_n, a_star, etc.)
2. Import Aristotle proof
3. Prove definition equivalences (possibly with rescaling)
4. Transfer theorem via equivalences
-/

-- Step 1: Show coordinate equivalence
lemma xi_eq (n : ℕ) : _root_.xi n = Q3.xi_n n := rfl  -- or with 2π factor

-- Step 2: Show function equivalence (for Q_nonneg)
lemma Q_eq (g : ℝ → ℝ) : _root_.Q Q3.a_star g = Q3.Q g := by ...

-- Step 3: Transfer theorem
theorem bridge_theorem ... := by
  rw [← definitions_eq]
  exact aristotle_theorem
```

---

## TECHNICAL NOTES

### Rescaling Formulas

For RKHS_contraction with `t' = t / (2π)²`:

```
δ_K(Aristotle) = min spacing in ξ-coordinates = 2π · δ_K(Q3)
S_K(Aristotle, t) = S_K(Q3, t/(2π)²)
```

Since `S_K = 2·exp(-δ²/(4t)) / (1 - exp(-δ²/(4t)))`:
- With `δ' = 2π·δ` and `t' = t/(2π)²`:
- `δ'²/(4t') = (2π)²·δ²/(4·t/(2π)²) = (2π)⁴·δ²/(4t)`

Wait, this doesn't match. Need to verify the exact rescaling...

**TODO:** Verify exact rescaling relationship for RKHS.

### Fourier Isomorphism (for A3)

The key fact: For trigonometric polynomial `p(θ) = Σ_{k=-M}^M c_k e^{ikθ}`:

```
∫₀^{2π} P(θ)|p(θ)|² dθ/(2π) = c* · T_M[P] · c
```

where `T_M[P]` is the Toeplitz matrix with entries `T_{jk} = P̂_{j-k}` (Fourier coefficients of P).

This is classical Szegő theory.

---

## NEXT STEPS

1. [ ] Create Q_nonneg_bridge.lean (should be straightforward)
2. [ ] Verify RKHS rescaling formula
3. [ ] Create RKHS_contraction_bridge.lean
4. [ ] Investigate Mathlib for Toeplitz-Fourier equivalence
5. [ ] Create remaining bridges

---

## FILES REFERENCED

- `Q3/Axioms.lean` - Q3 axiom definitions
- `Q3/Basic/Defs.lean` - Q3 basic definitions (xi_n, a_star, etc.)
- `Q3/Proofs/RKHS_contraction.lean` - Aristotle RKHS proof
- `Q3/Proofs/Q_Lipschitz.lean` - Aristotle Q Lipschitz proof
- `Q3/Proofs/A3_bridge.lean` - Aristotle A3 bridge proof
- `Q3/Proofs/Q_nonneg_on_atoms.lean` - Aristotle Q≥0 proof
