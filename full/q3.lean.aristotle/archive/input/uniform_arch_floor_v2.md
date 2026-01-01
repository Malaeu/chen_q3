# Uniform Archimedean Floor - V2

## Previously Proven (from V1)

The following definitions were established in V1 and should be reused:

```lean
noncomputable def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)

noncomputable def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * (ξ : ℂ))).re

noncomputable def A_0 (B t_sym : ℝ) : ℝ :=
  ∫ ξ in -B..B, a ξ * (max 0 (1 - |ξ| / B)) * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

noncomputable def L_int (B t_sym : ℝ) : ℝ :=
  ∫ ξ in -B..B, |a ξ| * |ξ| * (max 0 (1 - |ξ| / B)) * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

noncomputable def A_star (B_min t_sym : ℝ) : ℝ :=
  sInf { y | ∃ B ≥ B_min, y = A_0 B t_sym }

noncomputable def L_star (B_min t_sym : ℝ) : ℝ :=
  sSup { y | ∃ B ≥ B_min, y = L_int B t_sym }

noncomputable def c_star (B_min t_sym : ℝ) : ℝ :=
  A_star B_min t_sym - Real.pi * L_star B_min t_sym

noncomputable def t_sym_val : ℝ := 3 / 50
```

## Current Goal

Prove the following key bounds for t_sym = 3/50:

```lean
/-- The mean integral A_* is bounded below by 1867/1000 -/
theorem A_star_lower_bound (B_min : ℝ) (hB : B_min > 0) :
    A_star B_min t_sym_val ≥ 1867 / 1000 := by
  sorry

/-- The Lipschitz integral L_* is bounded above by 42/125 -/
theorem L_star_upper_bound (B_min : ℝ) (hB : B_min > 0) :
    L_star B_min t_sym_val ≤ 42 / 125 := by
  sorry

/-- The uniform floor c_* is positive: c_* >= 811/1000 -/
theorem uniform_arch_floor (B_min : ℝ) (hB : B_min > 0) :
    c_star B_min t_sym_val ≥ 811 / 1000 := by
  have hA : A_star B_min t_sym_val ≥ 1867 / 1000 := A_star_lower_bound B_min hB
  have hL : L_star B_min t_sym_val ≤ 42 / 125 := L_star_upper_bound B_min hB
  -- c_* = A_* - π * L_* ≥ 1867/1000 - π * (42/125)
  -- ≥ 1867/1000 - 3.1416 * 0.336 ≈ 1.867 - 1.056 ≈ 0.811
  sorry
```

## Proof Strategy Hints

### For A_star_lower_bound:

1. The digamma function satisfies: ψ(1/4) = -γ - π/2 - 3 log 2 where γ is Euler's constant
2. For real ξ: Re(ψ(1/4 + iπξ)) ≤ ψ(1/4) + C|ξ|² for small ξ
3. Therefore a(ξ) = log π - Re(ψ(1/4 + iπξ)) ≥ log π - ψ(1/4) - C|ξ|²
4. The Gaussian weight e^{-4π²t_sym ξ²} with t_sym = 3/50 decays fast enough
5. Use: γ ≥ 577/1000, log 2 ≥ 693/1000, log π ≥ 1145/1000

### For L_star_upper_bound:

1. |a(ξ)| is bounded: |a(ξ)| ≤ log π + |ψ(1/4)| + C|ξ| for bounded ξ
2. The factor |ξ| * (1 - |ξ|/B) is bounded by B/4 (maximum at ξ = B/2)
3. The Gaussian decay makes the integral converge
4. Taking sup over B gives a finite bound

### For uniform_arch_floor:

Simply combine the two bounds:
- c_* = A_* - π * L_*
- ≥ 1867/1000 - π * (42/125)
- = 1867/1000 - π * 336/1000
- ≥ 1867/1000 - 1056/1000  (using π < 3.1416)
- = 811/1000

## Numerical Evidence

With t_sym = 3/50 = 0.06:
- A_*(0.06) ≈ 1.867 (computed numerically)
- L_*(0.06) ≈ 0.336 (computed numerically)
- c_* = A_* - π*L_* ≈ 1.867 - 3.14159*0.336 ≈ 0.811

## Key Mathlib Lemmas to Use

- `Complex.Gamma_ne_zero` for non-vanishing of Gamma
- `Real.log_le_log` for logarithm bounds
- `MeasureTheory.integral_mono` for integral bounds
- `Real.exp_le_exp` for exponential comparisons
- `norm_num` for rational arithmetic
