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

/-! ## Global bound for the starred target comb on the right half -/

/-- On `1 ≤ u` the starred target comb is a single Gaussian with an explicit
constant: the half-Gaussian bound dominates each term and the geometric lemma
telescopes the series to twice its first term. -/
private theorem E_star_explicitCCMLimitH_norm_le_of_one_le
    {u : ℝ} (hu : 1 ≤ u) :
    ‖E_star explicitCCMLimitH u‖ ≤
      24 * Real.sqrt u * Real.exp (-(Real.pi * u ^ 2) / 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hnorm_summable : Summable
      (fun n : ℕ+ => ‖explicitCCMLimitH ((n : ℕ) * u)‖) := by
    -- dominated by the geometric Gaussian series
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_)
      (f := fun n : ℕ+ =>
        12 * Real.exp (-(Real.pi * u ^ 2) / 2) * (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1))
    · apply Summable.mul_left
      have hgeo : Summable (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hinj : Function.Injective (fun n : ℕ+ => ((n : ℕ) - 1)) := by
        intro a b hab
        have ha := a.pos
        have hb := b.pos
        have hab' : (a : ℕ) - 1 = (b : ℕ) - 1 := hab
        exact PNat.coe_injective (by omega)
      simpa using hgeo.comp_injective hinj
    · calc
        ‖explicitCCMLimitH ((n : ℕ) * u)‖ ≤
            12 * Real.exp (-(Real.pi * ((n : ℕ) * u) ^ 2) / 2) :=
          explicitCCMLimitH_le_half_gaussian _
        _ ≤ 12 * (Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1)) := by
          have := gaussian_series_le_geometric hu (n : ℕ) n.pos
          nlinarith [this, Real.exp_pos (-(Real.pi * ((n:ℕ) * u) ^ 2) / 2)]
        _ = 12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by ring
  rw [E_star, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have htsum : ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
      24 * Real.exp (-(Real.pi * u ^ 2) / 2) := by
    calc
      ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
          ∑' n : ℕ+, ‖explicitCCMLimitH ((n : ℕ) * u)‖ :=
        norm_tsum_le_tsum_norm hnorm_summable
      _ ≤ ∑' n : ℕ+,
            12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by
        apply hnorm_summable.tsum_le_tsum _ ?_
        · intro n
          calc
            ‖explicitCCMLimitH ((n : ℕ) * u)‖ ≤
                12 * Real.exp (-(Real.pi * ((n : ℕ) * u) ^ 2) / 2) :=
              explicitCCMLimitH_le_half_gaussian _
            _ ≤ 12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
                  (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by
              have := gaussian_series_le_geometric hu (n : ℕ) n.pos
              nlinarith [this,
                Real.exp_pos (-(Real.pi * ((n:ℕ) * u) ^ 2) / 2)]
        · apply Summable.mul_left
          have hgeo : Summable (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have hinj : Function.Injective (fun n : ℕ+ => ((n : ℕ) - 1)) := by
            intro a b hab
            have ha := a.pos
            have hb := b.pos
            have hab' : (a : ℕ) - 1 = (b : ℕ) - 1 := hab
            exact PNat.coe_injective (by omega)
          simpa using hgeo.comp_injective hinj
      _ ≤ 24 * Real.exp (-(Real.pi * u ^ 2) / 2) := by
        rw [tsum_mul_left]
        have hval : ∑' n : ℕ+, ((2 : ℝ)⁻¹) ^ ((n : ℕ) - 1) = 2 := by
          have hfun : (fun n : ℕ+ => ((2 : ℝ)⁻¹) ^ ((n : ℕ) - 1)) =
              (fun n : ℕ+ =>
                (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) (Equiv.pnatEquivNat n)) := by
            funext n
            simp [Equiv.pnatEquivNat, PNat.natPred]
          rw [hfun, Equiv.pnatEquivNat.tsum_eq
            (f := fun m : ℕ => ((2 : ℝ)⁻¹) ^ m), tsum_geometric_inv_two]
        rw [hval]
        nlinarith [Real.exp_pos (-(Real.pi * u ^ 2) / 2)]
  calc
    Real.sqrt u * ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
        Real.sqrt u * (24 * Real.exp (-(Real.pi * u ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left htsum (Real.sqrt_nonneg _)
    _ = 24 * Real.sqrt u * Real.exp (-(Real.pi * u ^ 2) / 2) := by ring

#print axioms E_star_explicitCCMLimitH_norm_le_of_one_le

/-! ## The left half by exact inversion -/

/-- On `0 < u ≤ 1` the same Gaussian bound holds with `u` replaced by its
inverse: the starred comb is inversion-symmetric, so the left half of the
envelope is the right half read backwards.  This is the exact cancellation
mechanism; no Poisson summation is needed. -/
private theorem E_star_explicitCCMLimitH_norm_le_of_le_one
    {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1) :
    ‖E_star explicitCCMLimitH u‖ ≤
      24 * Real.sqrt u⁻¹ * Real.exp (-(Real.pi * (u⁻¹) ^ 2) / 2) := by
  have hinv : E_star explicitCCMLimitH u = E_star explicitCCMLimitH u⁻¹ := by
    have h := E_star_explicitCCMLimitH_inv u⁻¹ (by positivity)
    simpa [inv_inv] using h
  rw [hinv]
  exact E_star_explicitCCMLimitH_norm_le_of_one_le
    (one_le_inv_iff₀.mpr ⟨hu0, hu⟩)

#print axioms E_star_explicitCCMLimitH_norm_le_of_le_one

end Q3.RouteB.D0Pstar
