# Missing Bridge Lemma for A1 Density

## The Gap

We have `real_convolution` defined as integral over ℝ:
```lean
noncomputable def real_convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (x - y)
```

We have `uniform_riemann_sum` that works on bounded intervals `[a, b]`.

We need a bridge lemma that connects them when `f` has compact support.

## Lemma to Prove

```lean
/-- If f has compact support, the convolution integral equals integral over the support. -/
lemma convolution_eq_Icc_of_compact_support (f g : ℝ → ℝ) (hf : HasCompactSupport f) :
  ∃ L > 0, ∀ x, real_convolution f g x = ∫ y in Set.Icc (-L) L, f y * g (x - y) := by
  -- Since f has compact support, there exists L such that supp(f) ⊂ [-L, L]
  -- For y outside [-L, L], we have f(y) = 0, so f(y) * g(x - y) = 0
  -- Therefore the integral over ℝ equals the integral over [-L, L]
  sorry
```

## Proof Sketch

1. By `HasCompactSupport f`, there exists a compact set K such that f = 0 outside K
2. Since K is compact in ℝ, it's bounded: K ⊂ [-L, L] for some L > 0
3. For y ∉ [-L, L], we have y ∉ K, so f(y) = 0, hence f(y) * g(x - y) = 0
4. Therefore:
   ```
   ∫ y, f y * g (x - y) = ∫ y in [-L, L], f y * g (x - y) + ∫ y in ℝ \ [-L, L], f y * g (x - y)
                        = ∫ y in [-L, L], f y * g (x - y) + 0
                        = ∫ y in [-L, L], f y * g (x - y)
   ```

## Mathlib Tools

- `HasCompactSupport.exists_compact_superset` or similar
- `MeasureTheory.setIntegral_eq_of_eq_zero` for showing integral over complement is 0
- `Metric.isBounded_of_isCompact` for getting bounds from compact

## Expected Output

Complete proof of `convolution_eq_Icc_of_compact_support` (about 20-40 lines).
