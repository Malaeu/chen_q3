# A3 Core Shift Lemma (Shift-Robust Core Mass)

## Goal
Prove that the Fejér hat function has a minimum mass when integrated over any shifted interval of fixed length inside its support.

## Definitions

```lean
-- Fejér hat (tent function)
noncomputable def FejerHat (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

-- Shifted core integral
noncomputable def shifted_core_integral (B r τ : ℝ) : ℝ :=
  ∫ x in Set.Icc (τ - r) (τ + r), FejerHat B x

-- Gaussian-weighted shifted integral
noncomputable def gaussian_shifted_integral (B t τ : ℝ) : ℝ :=
  ∫ x, FejerHat B (x - τ) * Real.exp (-4 * Real.pi^2 * t * (x - τ)^2)
```

## Main Lemma to Prove

```lean
/-- Shift-robust core mass: Fejér hat has minimum mass 2r²/B over any interval of length 2r -/
lemma core_shift_mass (B r τ : ℝ) (hB : B > 0) (hr : 0 < r) (hrB : r < B)
    (hτ : |τ| ≤ B - r) :
    shifted_core_integral B r τ ≥ 2 * r^2 / B := by
  sorry

/-- Consequently, with Gaussian weight -/
lemma gaussian_core_shift (B t τ r : ℝ) (hB : B > 0) (ht : t > 0) (hr : 0 < r) (hrB : r < B)
    (hτ : |τ| ≤ B - r) :
    gaussian_shifted_integral B t τ ≥ (2 * r^2 / B) * Real.exp (-4 * Real.pi^2 * t * r^2) := by
  sorry
```

## Proof Sketch

### For core_shift_mass:

1. **Fejér hat is piecewise linear**: Λ_B(x) = max(0, 1 - |x|/B)
   - Linear on [-B, 0] with slope 1/B
   - Linear on [0, B] with slope -1/B

2. **Worst-case position**: The interval [τ-r, τ+r] attains minimum integral when it abuts an endpoint of [-B, B]
   - At τ = B - r: the interval is [B - 2r, B]
   - Direct computation: ∫_{B-2r}^{B} Λ_B(x) dx = 2r²/B

3. **Symmetric argument** for τ = -(B - r) gives same result.

4. **Any other translate** gives strictly larger mass.

### For gaussian_core_shift:

1. Use that exp(-4π²t(x-τ)²) ≥ exp(-4π²tr²) when |x - τ| ≤ r

2. Factor out the Gaussian bound and apply core_shift_mass.

## Notes

- The Fejér hat is continuous and piecewise linear
- Use `intervalIntegral.integral_comp_sub_right` for translation
- The minimum is attained at boundary positions
- Explicit calculation: ∫_{B-2r}^{B} (1 - x/B) dx = [x - x²/(2B)]_{B-2r}^{B} = 2r - 2r²/B - 0 = 2r²/B
