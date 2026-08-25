import Q3.Proofs.RouteB.G6N1SelectedFerrersW5JumpSeamRate

/-!
# W5 — the additive-log `L¹` packet mass component

`C_k` has four components.  The seam sum is closed in
`G6N1SelectedFerrersW5JumpSeamRate`.  This file works on the next one:

```
L1_k = ∫ x, ‖selectedFerrersAbelLogZeroExtension k x‖
```

The route is the uniform F72.6 window estimate summed over the active indices.
There are exactly `k + 2` of them and the estimate carries `1 / lambda_k ^ 2`,
so the accumulated approximation error is `(k + 2) * C / lambda_k ^ 2 = C`:
the index count grows exactly as fast as each term decays, because
`lambda_k ^ 2 = k + 2` is an identity here, not an asymptotic.

What is left is the explicit polynomial-Gaussian target, and this file starts
by trimming its polynomial factor against half of its own Gaussian.

SEARCH_FLAGS:
  - `./ask.sh "explicitCCMLimitH decay gaussian polynomial"`
  - `./ask.sh "L1 mass packet integral bound rate"`

LEDGER:
  CLOSES: []
  OPENS: []
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Half of the Gaussian absorbs the whole polynomial factor: the literal CCM
limit packet is below `12 * exp (-pi * y ^ 2 / 2)` everywhere.  Both maxima are
taken with the exponential's own Taylor terms, so no numerical evaluation
enters. -/
private theorem explicitCCMLimitH_le_half_gaussian (y : ℝ) :
    ‖explicitCCMLimitH y‖ ≤ 12 * Real.exp (-(Real.pi * y ^ 2) / 2) := by
  have hpi := Real.pi_pos
  set t : ℝ := y ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  -- Norm of the packet, factored exactly as in the edge lemma.
  have hnorm : ‖explicitCCMLimitH y‖ =
      |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| *
        Real.exp (-Real.pi * t) := by
    rw [explicitCCMLimitH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (-Real.pi * (y : ℂ) ^ 2) = ((-Real.pi * t : ℝ) : ℂ) by
      rw [ht]; push_cast; ring]
    exact Complex.norm_exp_ofReal _
  have hpoly : |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| ≤
      Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t := by
    have h1 : |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| =
        (Real.pi / 2) * t * |2 * Real.pi * t - 3| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2),
        abs_of_nonneg ht0]
    have h2 : |2 * Real.pi * t - 3| ≤ 2 * Real.pi * t + 3 := by
      rw [abs_le]
      constructor <;> nlinarith [ht0, hpi]
    rw [h1]
    have h3 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0:ℝ) ≤ Real.pi / 2 * t)
    nlinarith [ht0, hpi, h3]
  -- Split the Gaussian and spend the second half on the polynomial.
  have hsplit : Real.exp (-Real.pi * t) =
      Real.exp (-(Real.pi * t) / 2) * Real.exp (-(Real.pi * t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : (Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t) *
      Real.exp (-(Real.pi * t) / 2) ≤ 12 := by
    have hquad : (Real.pi * t / 2) ^ 2 / 2 ≤ Real.exp (Real.pi * t / 2) := by
      have h := Real.pow_div_factorial_le_exp (x := Real.pi * t / 2)
        (by positivity) 2
      simpa [Nat.factorial] using h
    have hlin : Real.pi * t / 2 ≤ Real.exp (Real.pi * t / 2) := by
      have h := Real.pow_div_factorial_le_exp (x := Real.pi * t / 2)
        (by positivity) 1
      simpa [Nat.factorial] using h
    have hexppos : (0 : ℝ) < Real.exp (Real.pi * t / 2) := Real.exp_pos _
    have hinv : Real.exp (-(Real.pi * t) / 2) =
        (Real.exp (Real.pi * t / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hinv, mul_inv_le_iff₀ hexppos]
    nlinarith [hquad, hlin, hexppos, ht0, hpi]
  rw [hnorm, hsplit, ← mul_assoc]
  have hexpNonneg : (0 : ℝ) ≤ Real.exp (-(Real.pi * t) / 2) := (Real.exp_pos _).le
  have hstep := mul_le_mul_of_nonneg_right hpoly hexpNonneg
  calc
    |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| *
          Real.exp (-(Real.pi * t) / 2) *
        Real.exp (-(Real.pi * t) / 2) ≤
        ((Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t) *
            Real.exp (-(Real.pi * t) / 2)) *
          Real.exp (-(Real.pi * t) / 2) :=
      mul_le_mul_of_nonneg_right hstep hexpNonneg
    _ ≤ 12 * Real.exp (-(Real.pi * t) / 2) :=
      mul_le_mul_of_nonneg_right hhalf hexpNonneg
    _ = 12 * Real.exp (-(Real.pi * y ^ 2) / 2) := by rw [ht]

#print axioms explicitCCMLimitH_le_half_gaussian

/-! ## The right half of the signed envelope: `1 ≤ u`

For `1 ≤ u` every active index satisfies `n * u ≥ n`, so the signed comb is
dominated termwise by the Gaussian series `Σ_n 12 * exp (-pi * (n*u)^2 / 2)`,
and that series telescopes below a single geometric tail.  No cancellation is
spent here; the left half `u ≤ 1` is where zero mass will have to work. -/

/-- Geometric domination of the Gaussian series on the right half.  For
`1 ≤ u` the `n`-th Gaussian is at most the first one times `2^(1-n)`, because
`exp (-pi u^2 (n^2 - 1) / 2) ≤ exp (-(n-1)) ≤ 2^(1-n)`. -/
private theorem gaussian_series_le_geometric
    {u : ℝ} (hu : 1 ≤ u) (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-(Real.pi * ((n : ℝ) * u) ^ 2) / 2) ≤
      Real.exp (-(Real.pi * u ^ 2) / 2) * (2 : ℝ)⁻¹ ^ (n - 1) := by
  have hpi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- (n*u)^2 = u^2 + u^2*(n^2-1) and u^2*(n^2-1) >= n-1 pointwise.
  have hgap : (Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2 ≥ ((n : ℝ) - 1) := by
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith [hn1]
    have htwo : (2 : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hthree : (3 : ℝ) ≤ Real.pi * u ^ 2 := by nlinarith [hpi3, hu2, hpi]
    have hchain : (3 : ℝ) * ((n : ℝ) ^ 2 - 1) ≤
        Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hthree hsq
    linarith [hchain, htwo]
  have hsplit : -(Real.pi * ((n : ℝ) * u) ^ 2) / 2 =
      -(Real.pi * u ^ 2) / 2 - (Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2 := by
    ring
  rw [hsplit, Real.exp_sub]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  -- exp (-(gap)) <= exp (-(n-1)) <= 2^(1-n)
  have hstep1 : Real.exp (-((Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2)) ≤
      Real.exp (-((n : ℝ) - 1)) := by
    apply Real.exp_le_exp.mpr
    linarith [hgap]
  refine le_trans (by simpa [Real.exp_neg] using hstep1) ?_
  -- exp (n-1) >= 2^(n-1) since exp 1 >= 2
  have hgoal : Real.exp (1 - (n : ℝ)) = (Real.exp ((n : ℝ) - 1))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hgoal, show ((2 : ℝ)⁻¹ ^ (n - 1)) = ((2 : ℝ) ^ (n - 1))⁻¹ by
    rw [inv_pow]]
  rw [inv_le_inv₀ (Real.exp_pos _) (by positivity)]
  have hcast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast, ← Real.exp_one_rpow ((n - 1 : ℕ) : ℝ), Real.rpow_natCast]
  apply pow_le_pow_left₀ (by norm_num)
  linarith [Real.add_one_le_exp (1 : ℝ)]

end Q3.RouteB.D0Pstar
