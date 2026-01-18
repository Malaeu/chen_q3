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

- **Periodization.lean FULLY CLOSED** ✓
- All lemmas proven without sorries:
  - `support_implies_finite_periodization`
  - `tsum_eq_finset_sum_of_outside_zero`
  - `periodization_eq_finset_sum`
  - `intervalIntegral_periodization_eq_integral`
- Avoids OOM by using only standard Mathlib lemmas with finite sums

---

## Proshka's Additional Analysis (2026-01-18)

### Why `maxHeartbeats 0` is Dangerous

`maxHeartbeats 0` doesn't *cause* the hang, but **hides the real error**. Any bad tactic
branch (especially `simp`, `convert`, `aesop`, typeclass search) will loop forever
instead of failing with a heartbeat error.

**Rule**: Use finite heartbeat limits (2-5M) on specific theorems, not globally.

### Anti-Patterns That Cause Explosion

| Anti-Pattern | Why Bad | Fix |
|--------------|---------|-----|
| `convert ... using 1 <;> ring` | Creates huge congruence goals | `simpa [add_assoc]` or `have` first |
| `EqOn` + `Set.uIcc` | Triggers simp explosion | Use `integral_congr_ae` (AE version) |
| `Finset.Icc (-⌈B⌉-1) (⌈B⌉+1)` inline | Bloats goals | Freeze: `let N := ⌈B⌉ + 1` |
| Typeclass synthesis inside tactic | Can explode | Provide explicit instances |

### Preferred Mathlib Lemmas

| Lemma | Use For |
|-------|---------|
| `Integrable.hasSum_intervalIntegral_comp_add_int` | Periodization core |
| `intervalIntegral.integral_comp_add_right/left` | Interval shifting (no convert!) |
| `intervalIntegral.integral_congr_ae` | Function replacement (AE, not EqOn) |
| `IsAddFundamentalDomain.integral_eq_tsum_of_ac` | Alternative approach |

### Diagnostics Commands

```lean
-- Enable to find slow spots
set_option diagnostics true
set_option diagnostics.threshold 5

-- Profile specific theorem
set_option trace.profiler true in
theorem slow_lemma ... := by
  ...
```

### References

- [IntervalIntegral.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html)
- [FundamentalDomain](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/FundamentalDomain.html)
- [Lean 4.8 Diagnostics](https://lean-lang.org/blog/2024-6-1-lean-480)
