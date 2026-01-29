# Periodization Bottleneck Fix

**Date:** 2026-01-17
**Author:** Proshka analysis + Claude implementation
**Status:** Archived (draft removed from main)

## Problem

`Rayleigh_Q_identification.lean` took 645+ minutes CPU time, repeatedly getting killed (exit code 143 = SIGTERM after ~1200-1900 seconds).

### Root Cause

The bottleneck was `MeasureTheory.integral_tsum_of_summable_integral_norm` which requires:
1. Restricted measures on compact intervals
2. Dominators and Summable proofs
3. Heavy machinery that explodes elaboration time

## Solution: Finite Sum Bypass

**Key insight:** g B t has compact support in `[-B, B]`, so the periodization sum `∑' n : ℤ, g(θ + n)` is actually FINITE for `θ ∈ [-1/2, 1/2]`.

### Why This Works

For `θ ∈ [-1/2, 1/2]` and `|n| > ⌈B + 1/2⌉ + 1`:
- `|θ + n| ≥ |n| - |θ| > B + 1/2 - 1/2 = B`
- So `g(θ + n) = 0` (outside support)

Therefore only finitely many terms in the sum are nonzero!

### New Strategy (Lean-friendly)

```
tsum → Finset.sum → linear integral swap
```

**Lemma 1:** `tsum_periodize_eq_finset_sum`
- For θ ∈ [-1/2, 1/2]: `∑' n : ℤ, g(θ+n) = ∑ n ∈ Finset.Icc (-N) N, g(θ+n)`
- Uses `tsum_eq_sum` (functions zero outside finite set)

**Lemma 2:** `intervalIntegral_periodize_eq_integral`
- `∫_{-1/2}^{1/2} (∑' n, g(θ+n)) dθ = ∫_ℝ g(x) dx`
- Uses:
  - Step 1: Replace tsum with Finset.sum (Lemma 1)
  - Step 2: `intervalIntegral.integral_finset_sum` (CHEAP swap!)
  - Step 3: `integral_comp_add_right` for substitution
  - Step 4: `Integrable.hasSum_intervalIntegral` for partition

## Key Mathlib Lemmas

| Lemma | Purpose |
|-------|---------|
| `tsum_eq_sum` | tsum = finite sum when vanishes outside |
| `intervalIntegral.integral_finset_sum` | Swap ∫ with finite ∑ (free!) |
| `integral_comp_add_right` | Change of variables θ → θ+n |
| `Integrable.hasSum_intervalIntegral` | Unit interval partition of ℝ |

## Implementation (archived)

The draft file `Q3/Proofs/Periodization.lean` was removed from main to avoid new
`sorry` in the Q3 tree. The periodization lemma is now proven directly inside
`Q3/Proofs/Rayleigh_Q_identification.lean`.

## Why This Is Better

| Approach | Compile Time | Why |
|----------|--------------|-----|
| Old (dominated convergence) | 645+ min | Heavy elaboration, restricted measures |
| New (finite sum) | ~3 sec | Simple reduction, no dominators |

The key is avoiding `integral_tsum_of_summable_integral_norm` entirely by recognizing the sum is finite.
