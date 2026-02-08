---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# C3 Prime Cap: RKHS vs Window-Specific Approach

**Date:** 2026-01-19
**Status:** ANALYSIS COMPLETE, DECISION NEEDED

---

## Problem Statement

For C3 (prime term cap), we need:
```
|prime_term Φ| ≤ rho_one ≤ c_star/4
```

The **wrong** approach was:
```
|prime_term Φ| ≤ ∑ |w_Q(n)| ≤ rho_one  // FALSE! ∑|w_Q| ~ O(e^{πK})
```

---

## Two Valid Approaches

### Option A: Window-Specific (Current Path)

**Idea:** Use structure of `phi_shift = fejer_heat_window(· - τ)`.

**Existing infrastructure:**
```lean
-- PROVEN in RKHS_cap_rayleigh.lean:
lemma weight_sum_le_rho_one (K B : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K, ‖(w_Q n * fejer_heat_window B t_rkhs_cap (xi_n n) : ℂ)‖ ≤ rho_one

lemma weight_term_le_pow_inv (K B : ℝ) (hB : 0 < B) (n : Q3.Nodes K) :
    ‖(w_Q n * fejer_heat_window B t_rkhs_cap (xi_n n) : ℂ)‖ ≤ (4/e) * pow_inv_shift (n - 2)
```

**Needed:** Adapt for shifted window `(xi_n - τ)`:
```lean
-- TODO:
lemma weight_sum_shifted_le_rho_one (K B τ : ℝ) (hB : 0 < B) (hτ : |τ| + B ≤ K) :
    ∑ n : Q3.Nodes K, ‖(w_Q n * fejer_heat_window B t_rkhs_cap (xi_n n - τ) : ℂ)‖ ≤ rho_one
```

**Why it works:** Window decay is translation-invariant — shifting by τ doesn't change the exponential decay rate.

**Pros:**
- Uses existing proven lemmas
- Minimal new infrastructure

**Cons:**
- Window-specific (not general)
- Need to prove shift-invariance of bounds

---

### Option B: RKHS Abstract (Review Recommendation)

**Idea:** Use operator norm bound directly.

**Required infrastructure:**
```lean
-- NEED TO ADD:
def rkhs_norm (Φ : ℝ → ℝ) : ℝ := ...

lemma prime_term_le_rkhs_norm (Φ : ℝ → ℝ) :
    |prime_term Φ| ≤ T_P_norm * rkhs_norm Φ

lemma rkhs_norm_phi_shift_le_one (B τ : ℝ) (hB : 0 < B) :
    rkhs_norm (phi_shift B t_sym τ) ≤ 1
```

**Existing partial support:**
```lean
-- Already proven:
def T_P_norm (K t : ℝ) : ℝ := Matrix.opNorm (T_P_matrix K t)

theorem RKHS_contraction (K : ℝ) (hK : K ≥ 1) :
    ∃ t > 0, ∃ ρ < 1, T_P_norm K t ≤ ρ
```

**Pros:**
- Mathematically cleaner
- Works for any Φ in RKHS unit ball (not just windows)

**Cons:**
- Requires new `rkhs_norm` definition
- Need to connect `T_P_norm` with `prime_term`
- More infrastructure to build

---

## Comparison Table

| Aspect | Option A (Window) | Option B (RKHS) |
|--------|-------------------|-----------------|
| Proven base | `weight_sum_le_rho_one` | `T_P_norm ≤ ρ < 1` |
| Missing piece | Shift adaptation | `rkhs_norm` definition + connection |
| Effort estimate | Medium | High |
| Generality | phi_shift only | All RKHS unit ball |
| Math cleanliness | OK | Better |

---

## C2 (arch term) Approach Note

**Wrong approach:** Lipschitz on window function.

**Correct approach (from review):**
```
F(τ) := arch_term(phi_shift τ)
     = ∫ a_star(ξ) * window(ξ - τ) dξ

Substitution η = ξ - τ:
F(τ) = ∫ a_star(η + τ) * window(η) dη

Difference:
F(τ) - F(0) = ∫ (a_star(η + τ) - a_star(η)) * window(η) dη
```

**Key insight:** Lipschitz needed for `a_star`, not for window.
`a_star` is smooth on compacts → Lipschitz constant is reasonable.

---

## Current Code Status

**Fixed:**
- Removed false `prime_term_le_rho_one_of_bounded`
- Added window-specific approach comment
- Sign of Q is correct: `Q = arch_term - prime_term`

**Remaining sorry:**
- `prime_term_phi_shift_le` — needs Option A or B implementation

---

## Recommendation

**Short-term:** Option A (window-specific)
- Adapt existing `weight_sum_le_rho_one` for shifted windows
- Faster to implement

**Long-term:** Option B (RKHS abstract)
- Build proper RKHS infrastructure
- More general and mathematically elegant

---

## Related Files

- `Q3/Proofs/Q_nonneg_atoms_proof.lean` — current sorry location
- `Q3/Proofs/RKHS_cap_rayleigh.lean` — weight_sum bounds
- `Q3/Proofs/RKHS_contraction.lean` — T_P_norm bounds
- `docs/insights/C3_prime_cap_correctness_2026_01_19.md` — why ∑|w_Q| is wrong
