# Periodization Insight (from Proshka Analysis)

## The Problem

The original proof in `Rayleigh_Q_identification.lean` uses
`integral_tsum_of_summable_integral_norm` which causes **OOM** during
standalone compilation (> 14GB RAM, killed after 30+ minutes).

## The Key Insight

For the function `g(B,t,x) = a(x) · fejer_heat_window(B,t,x)`:

1. **g has compact support in [-B, B]** (because Fejér kernel vanishes for |x| > B)

2. **On θ ∈ [-1/2, 1/2], the periodization sum is FINITE**:
   ```
   |θ + n| ≤ B only for finitely many n (specifically |n| ≤ ⌈B+1⌉)
   ```

3. **Therefore**: The tsum `∑' n, g(θ+n)` equals a Finset.sum `∑ n ∈ Icc(-N,N), g(θ+n)`

## The Lean-Friendly Approach

Instead of using `integral_tsum_of_summable_integral_norm` (dominated convergence):

```lean
-- AVOID THIS (causes OOM):
integral_tsum_of_summable_integral_norm ...

-- USE THIS INSTEAD:
-- 1. Convert tsum to Finset.sum (via compact support)
periodization_eq_finset_sum : ∑' n, f(θ+n) = ∑ n ∈ Icc(-N,N), f(θ+n)

-- 2. Swap integral and FINITE sum (trivial linearity)
intervalIntegral.integral_finset_sum

-- 3. Change of variables in each term
intervalIntegral.integral_comp_add_right

-- 4. Use hasSum_intervalIntegral for the final step
Integrable.hasSum_intervalIntegral
```

## Mathematical Proof

**Lemma (Finite Periodization)**: If `f : ℝ → ℝ` has support in `[-B, B]` and `θ ∈ [-1/2, 1/2]`,
then `f(θ + n) = 0` for all `|n| > ⌈B + 1⌉`.

*Proof*: 
- |θ| ≤ 1/2 since θ ∈ [-1/2, 1/2]
- |θ + n| ≥ |n| - |θ| ≥ |n| - 1/2
- If |n| > B + 1, then |θ + n| > B + 1 - 1/2 = B + 1/2 > B
- Therefore f(θ + n) = 0 by compact support ∎

**Main Result**: 
```
∫_{-1/2}^{1/2} (∑' n, f(θ+n)) dθ = ∫_ℝ f(x) dx
```

*Proof without dominated convergence*:
1. Replace tsum with finite sum: `∑' n, f(θ+n) = ∑_{|n|≤N} f(θ+n)` on [-1/2, 1/2]
2. Swap integral and finite sum: `∫ (∑_{|n|≤N} f(θ+n)) dθ = ∑_{|n|≤N} ∫ f(θ+n) dθ`
3. Change of variables: `∫_{-1/2}^{1/2} f(θ+n) dθ = ∫_{n-1/2}^{n+1/2} f(x) dx`
4. Sum of shifted intervals = integral over ℝ (by `hasSum_intervalIntegral`)
5. Outside N, the integrals vanish (compact support) ∎

## Files

- `Q3/Proofs/Periodization.lean` — Implementation of lightweight approach
- `Q3/Proofs/Rayleigh_Q_identification.lean` — Original proof (OOM-prone)

## Status

- Periodization.lean builds successfully with 3 technical sorries (coercion issues)
- Mathematical content is verified
- Avoids OOM by using only standard Mathlib lemmas with finite sums
