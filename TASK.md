# Task: measure_dom

## Goal

**Prove:** Measure domination — discrete prime sum bounded by continuous arch integral.

## Mathematical Statement

$$\sum_{n \geq 2} w_Q(n) \cdot \Phi(\xi_n) \leq \int_{\mathbb{R}} a^*(\xi) \cdot \Phi(\xi) \, d\xi$$

via disjoint neighborhoods around prime nodes.

## Key Insight

**Approach:**
1. Around each prime node $\xi_n$, take neighborhood $I_n = [\xi_n - \delta_n, \xi_n + \delta_n]$
2. Make neighborhoods **disjoint** (use prime gap)
3. Show $w_Q(n) \leq \int_{I_n} a^*(\xi) d\xi$ (density comparison)
4. Sum up

## Problem

**Prime gap shrinks:**
$$\xi_{n+1} - \xi_n = \frac{\log((n+1)/n)}{2\pi} \approx \frac{1}{2\pi n}$$

At large $n$, neighborhoods may overlap.

## Aristotle Reference

- **Input:** `full/q3.lean.aristotle/aristotle_input/measure_domination_v1.md`
- **UUID:** `d7bf9689-4431-4ea0-90df-170f7bb82d6c`

## Proof Strategy

### Option A: Truncated Sum
Work with $n \leq N_0$ where gaps are big enough, handle tail separately.

### Option B: Weighted Neighborhoods
Use $\delta_n \propto 1/n$ to match shrinking gaps.

### Option C: Different Approach
Use Stieltjes integral representation instead of explicit neighborhoods.

## Key Files

- `full/q3.lean.aristotle/docs/insights/localization_argument_full_analysis_2026_01_16.md`
- `full/q3.lean.aristotle/aristotle_input/measure_domination_v1.md`

## Success Criteria

- [x] Disjoint neighborhood construction (or alternative)
- [x] Density comparison proven (partial - identified obstruction)
- [ ] Full bound established (blocked by fundamental obstruction)
- [x] `lake build Q3.Main` passes
- [x] LaTeX formulas corrected (rayleigh_bridge.tex, calibration.tex)
- [ ] Changes committed

## 2026-01-17 Progress: Rayleigh-Q Identification Fix

### Problem Identified
The original formula was **WRONG**:
```
(2M+1) * RQ(ToeplitzFourier(P_A) - T_P_comp, basis0) = Q(Φ)
```
Problem: The `1/√(2M+1)` normalization in `prime_vec` causes:
- `T_P_comp[i0,i0] = (1/(2M+1)) * prime_term`
- When multiplied by `(2M+1)`, the **arch part also gets multiplied!**
- Result: `(2M+1) * arch_term - prime_term ≠ Q(Φ)`

### Solution Implemented
Created `Q3/Basic/Defs.lean` additions:
- `prime_vec_unnorm`: WITHOUT `1/√(2M+1)` normalization
- `T_P_comp_unnorm`: Uses unnormalized vectors
- `T_P_comp_unnorm_real`: Real part

Created `Q3/Proofs/Rayleigh_Q_correct.lean`:
- **Correct formula**: `RQ(ToeplitzFourier(P_A) - T_P_comp_unnorm, basis0) = Q(Φ)`
- NO `(2M+1)` multiplier needed!
- `T_P_comp_unnorm[i0,i0] = prime_term` (not scaled)

### Remaining Sorries (3) — Updated 2026-01-17
**CLOSED (4):**
1. ✅ `T_P_comp_unnorm_diag_i0` — diagonal evaluation (prime_vec_unnorm at i0 = 1)
2. ✅ `g_zero_large_m` — reverse triangle inequality (abs_sub_abs_le_abs_sub)
3. ✅ `g_zero_beyond_cutoff` — follows from g_zero_large_m + Int.natAbs casts
4. ✅ `tsum_eq_finite_sum_g` — tsum_eq_sum + Int.natAbs_of_nonneg/nonpos

**REMAINING (3):**
5. `periodization_lemma` — `∫ P_A = arch_term` (finite sum + interval decomposition)
6. `ToeplitzFourier_P_A_diag` — Toeplitz diagonal = integral (needs integral_re for intervalIntegral)
7. `Q_finite_eq_Q_large_K` — finite ↔ full Q connection (tail vanishes when K ≥ B)

### Periodization via Finite Sum (New Approach)
The key insight: **g has compact support in [-B, B]**.

For θ ∈ [-1/2, 1/2]:
- |θ + m| ≥ |m| - |θ| ≥ |m| - 1/2
- So if |m| > B + 1/2, then g(θ+m) = 0

**Cutoff**: N = ⌈B⌉ + 1 suffices (for B_min = 3: only m ∈ {-4,...,4})

**Lemmas added**:
- `w_support`: w(B,t,ξ) = 0 when |ξ| > B ✓
- `g_support`: g(B,t,ξ) = 0 when |ξ| > B ✓
- `g_zero_large_m`: g(θ+m) = 0 for |m| > B+1/2 ✓ (reverse triangle)
- `periodization_cutoff`: N = ⌈B⌉ + 1 ✓
- `g_zero_beyond_cutoff`: g vanishes beyond cutoff ✓ (Int casts)
- `tsum_eq_finite_sum_g`: infinite sum = finite sum ✓ (tsum_eq_sum)

### Key Theorem Proven (modulo sorries)
```lean
theorem rayleigh_Q_identification_correct :
    RQ(ToeplitzFourier(P_A) - T_P_comp_unnorm_real, basis0) = Q_finite(K, Φ)
```

### Files Created/Modified
- `Q3/Basic/Defs.lean` — added unnormalized definitions
- `Q3/Proofs/Rayleigh_Q_correct.lean` — new correct identification
- `Q3/Proofs/MeasureDomination.lean` — neighborhood approach (research)

## Difficulty Rating

**5/10** — May work with cutoff, but not trivial for all $n$.

## Notes — Analysis Complete

### Key Finding: Fundamental Obstruction

The neighborhood approach **fails for large n** due to growth rate mismatch:

**Prime gap**: $\delta_n = \text{gap}_n/2 \approx 1/(4\pi n)$

**Required condition**: $w_Q(n) \leq a^*(\xi_n) \cdot 2\delta_n \approx a^*(\xi_n)/(2\pi n)$

**For prime p**: Need $a^*(\xi_p) \gtrsim 4\pi \sqrt{p} \log(p)$

**But**: $a^*(\xi) \sim \log(\pi\xi)$ — grows logarithmically, not like $\sqrt{n}\log(n)$

### What Works

1. **Disjoint neighborhoods**: Proven in `MeasureDomination.lean:89-105`
   - `spectral_gap_strictly_decreasing` proves gaps decrease
   - `neighborhoods_disjoint` proves consecutive neighborhoods don't overlap

2. **Truncation + tail bound**: Theorems stated with `sorry` for integration machinery
   - `truncated_prime_term`: sum over $n \in [2, N_0]$
   - `tail_error_tendsto`: tail → 0 as $N_0 \to \infty$

### Alternative: Rayleigh Identification (Already in Q3)

The main Q3 proof uses **Rayleigh identification** instead:
$$\langle (T_M[P_A] - T_P^{(M)}) 1, 1 \rangle = Q(\Phi_{B,t})$$

This spectral approach is more powerful because it doesn't require point-by-point comparison.

### Lean File Created

`Q3/Proofs/MeasureDomination.lean` contains:
- `spectral_gap_pos`: gap > 0 ✓
- `spectral_gap_strictly_decreasing`: gaps decrease ✓
- `neighborhood_radius_pos`: δ_n > 0 ✓
- `neighborhoods_disjoint`: key disjointness theorem ✓
- `tail_error_tendsto`: sorry (requires measure theory)
- `measure_domination_truncated`: sorry (main theorem skeleton)

**Build status**: Compiles with 2 sorry (expected)
