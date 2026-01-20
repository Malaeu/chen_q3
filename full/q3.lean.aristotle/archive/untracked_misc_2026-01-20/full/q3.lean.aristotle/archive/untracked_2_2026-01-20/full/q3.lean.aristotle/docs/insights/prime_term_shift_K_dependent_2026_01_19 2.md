# Prime Term Shift: K-Dependent Bound Required

**Date:** 2026-01-19
**Status:** CRITICAL BUG FOUND, FIX PROPOSED

---

## The Bug

`prime_term_phi_shift_le` claimed uniform bound:
```lean
Q3.prime_term (phi_shift B t τ) ≤ Q3.c_star / 4  -- uniform in K, τ
```

**This is mathematically FALSE.**

---

## Root Cause

### Option A (sum-based) doesn't work:
- ∑|w_Q(n) * window(ξ_n - τ)| grows with number of "active" nodes
- For τ ~ 1, K = 1: ~50 primes contribute ~0.5 each → sum ≈ 25
- But c*/4 = 0.275 << 25

### Correct approach from TeX (Lemma shift-trace-cap):
```
‖T_P[Φ_{B,t,τ}]‖ ≤ e^{πK}(ρ(t) + 2πK σ(t))
```

where:
- ρ(t) = 2∫ y e^{y/2} e^{-4π²ty²} dy
- σ(t) = 2∫ e^{y/2} e^{-4π²ty²} dy

**Key:** Bound is K-dependent with factor e^{πK}!

---

## How Q ≥ 0 Works in TeX

For each K, choose **t = t(K)** large enough so:
```
e^{πK}(ρ(t_K) + 2πK σ(t_K)) < arch_term_lower_bound
```

Since ρ(t) → 0 and σ(t) → 0 as t → ∞, such t_K always exists.

**Contrast with arch_term:**
- arch_term bound **IS uniform** (shift-robust core mass lemma)
- arch_term ≥ c*/2 for all τ, K

---

## Weight Confusion: w_Q vs w_RKHS

**CRITICAL:** Two different weights in the project!

| Weight | Formula | Used In |
|--------|---------|---------|
| w_RKHS | Λ(n)/√n | RKHS operator estimates |
| w_Q | 2·Λ(n)/√n | Weil functional Q |

The factor of 2 comes from **evenization** (±ξ_n collapse).

Mixing these gives wrong constants by factor 2!

---

## Proposed Fix

### Option 1: K-dependent t (RECOMMENDED)

Change signature:
```lean
/-- Prime term bound with K-dependent heat parameter.
    For each K, t_K must be chosen large enough. -/
lemma prime_term_phi_shift_le_K (B τ K : ℝ) (hB : 0 < B) (hK : |τ| + B ≤ K) (hK1 : K ≥ 1)
    (t : ℝ) (ht : t ≥ t_min_K K)  -- t depends on K!
    : Q3.prime_term (phi_shift B t τ) ≤ Q3.c_star / 4 := by
  ...
```

Where `t_min_K K` is defined so that `e^{πK}(ρ(t) + 2πK σ(t)) < c*/4`.

### Option 2: T_P_comp operator approach

Use compression operator T_P_comp with proven ‖T_P_comp‖ ≤ rho_one.
But need to connect T_P_comp to prime_term for shifted windows.

---

## Files Affected

- `Q3/Proofs/Q_nonneg_atoms_proof.lean` — main fix location
- `Q3/Proofs/RKHS_cap_rayleigh.lean` — add t_min_K and K-dependent bounds
- `Q3/Basic/Defs.lean` — possibly add w_RKHS vs w_Q distinction

---

## Related TeX

- `/full/sections/RKHS/prime_trace_closed_form.tex` — Lemma shift-trace-cap
- `/full/sections/A3/symbol_floor.tex` — Lemma shift-robust core mass

---

## Key Lesson

**Uniform bounds don't exist for shifted prime term!**

The shift τ can align with many nodes ξ_n, making window values large.
Only way to control: increase t to compensate e^{πK} growth.
