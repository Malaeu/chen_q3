# A3 Core Lower Bound Lemma

## Goal
Prove a lower bound on the Archimedean coefficient A_0 in terms of core region parameters.

## Definitions

```lean
-- Archimedean density (digamma-related)
noncomputable def a_density (ξ : ℝ) : ℝ := Real.log Real.pi - (Complex.re (Complex.digamma (1/4 + Complex.I * Real.pi * ξ)))

-- Fejér×heat window
noncomputable def FejerHeatWindow (B t : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

-- Zeroth Fourier coefficient
noncomputable def A_zero (B t : ℝ) : ℝ :=
  ∫ ξ in Set.Icc (-B) B, a_density ξ * FejerHeatWindow B t ξ

-- Core region infimum
noncomputable def m_r (r : ℝ) : ℝ := ⨅ ξ ∈ Set.Icc (-r) r, a_density ξ

-- Supremum on [-B, B]
noncomputable def M_B (B : ℝ) : ℝ := ⨆ ξ ∈ Set.Icc (-B) B, |a_density ξ|
```

## Main Lemma to Prove

```lean
/-- Core contribution lemma: A_0 has explicit lower bound from core region -/
lemma core_lower_bound (B r t : ℝ) (hB : B > 0) (hr : 0 < r) (hrB : r < B) (ht : t > 0) :
    A_zero B t ≥ 2 * m_r r * r * (1 - r / B) * Real.exp (-4 * Real.pi^2 * t * r^2)
                 - M_B B / (4 * Real.pi^2 * t * r) * Real.exp (-4 * Real.pi^2 * t * r^2) := by
  sorry
```

## Proof Sketch

1. **Split the integral defining A_0** into core region [-r, r] and tails [−B, −r] ∪ [r, B].

2. **On the core [-r, r]**:
   - Lower bound a_density(ξ) by m_r (its infimum on this region)
   - The Fejér factor (1 - |ξ|/B) ≥ (1 - r/B) on [-r, r]
   - The Gaussian factor exp(-4π²tξ²) ≥ exp(-4π²tr²) on [-r, r]
   - Core integral contributes at least: 2·m_r·r·(1 - r/B)·exp(-4π²tr²)

3. **On the tails |ξ| ∈ [r, B]**:
   - Upper bound |a_density(ξ)| by M_B
   - The tail integral of the Gaussian×Fejér window:
     ∫_{r}^{B} (1 - ξ/B)·exp(-4π²tξ²) dξ ≤ 1/(4π²t·r)·exp(-4π²tr²)
   - Tail contributes at most: -M_B/(4π²t·r)·exp(-4π²tr²)

4. **Combine** to get the stated lower bound.

## Notes

- The digamma function is available in Mathlib as `Complex.digamma`
- Use `MeasureTheory.integral_Icc_sub_Icc` for splitting integrals
- The Gaussian integral bounds follow from standard tail estimates
- All integrals are over compact sets, so finite by default
