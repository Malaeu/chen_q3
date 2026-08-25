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

/-! ## The Gaussian tail integral with an explicit constant -/

/-- On `[1, b]` the half-Gaussian integrates below `(2 / pi) * exp (-pi / 2)`:
compare with `exp (-(pi * u) / 2)` (valid since `u ≤ u ^ 2` there) and
integrate the exponential exactly through its antiderivative. -/
private theorem gaussian_tail_intervalIntegral_le {b : ℝ} (hb : 1 ≤ b) :
    ∫ u in (1 : ℝ)..b, Real.exp (-(Real.pi * u ^ 2) / 2) ≤
      2 / Real.pi * Real.exp (-Real.pi / 2) := by
  have hpi := Real.pi_pos
  -- termwise comparison on [1, b]
  have hcompare : ∀ u ∈ Set.Icc (1 : ℝ) b,
      Real.exp (-(Real.pi * u ^ 2) / 2) ≤ Real.exp (-(Real.pi * u) / 2) := by
    intro u hu
    apply Real.exp_le_exp.mpr
    have hu1 : (1 : ℝ) ≤ u := hu.1
    have hsq : u ≤ u ^ 2 := by nlinarith [hu1]
    have := mul_le_mul_of_nonneg_left hsq hpi.le
    linarith
  -- the exponential has an exact antiderivative
  have hanti : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => -(2 / Real.pi) * Real.exp (-(Real.pi * v) / 2))
      (Real.exp (-(Real.pi * u) / 2)) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => -(Real.pi * v) / 2)
        (-(Real.pi) / 2) u := by
      have heq : (fun v : ℝ => -(Real.pi * v) / 2) =
          (fun v : ℝ => (-(Real.pi) / 2) * v) := by
        funext v; ring
      rw [heq]
      simpa using (hasDerivAt_id u).const_mul (-(Real.pi) / 2)
    have hexp := hlin.exp
    have := hexp.const_mul (-(2 / Real.pi))
    convert this using 1
    field_simp
  have hint : ∫ u in (1 : ℝ)..b, Real.exp (-(Real.pi * u) / 2) =
      -(2 / Real.pi) * Real.exp (-(Real.pi * b) / 2) -
        (-(2 / Real.pi) * Real.exp (-(Real.pi * 1) / 2)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hanti u)
    apply Continuous.intervalIntegrable
    continuity
  have hmono : ∫ u in (1 : ℝ)..b, Real.exp (-(Real.pi * u ^ 2) / 2) ≤
      ∫ u in (1 : ℝ)..b, Real.exp (-(Real.pi * u) / 2) := by
    apply intervalIntegral.integral_mono_on hb
    · apply Continuous.intervalIntegrable
      continuity
    · apply Continuous.intervalIntegrable
      continuity
    · exact hcompare
  refine le_trans hmono ?_
  rw [hint]
  simp only [mul_one]
  have hpos : (0 : ℝ) < Real.exp (-(Real.pi * b) / 2) := Real.exp_pos _
  have hconst : (0 : ℝ) < 2 / Real.pi := by positivity
  nlinarith [hpos, hconst, Real.exp_pos (-(Real.pi) / 2)]

#print axioms gaussian_tail_intervalIntegral_le

/-! ## The envelope in the additive coordinate

Writing `u = exp y` with `y ≥ 0` turns the Gaussian envelope into a plain
decaying exponential: `exp (2*y) ≥ 1 + 2*y` is the only inequality spent, and
no change of variables is ever needed. -/

private theorem envelope_additive_bound {y : ℝ} (hy : 0 ≤ y) :
    24 * Real.sqrt (Real.exp y) *
        Real.exp (-(Real.pi * (Real.exp y) ^ 2) / 2) ≤
      24 * Real.exp (-Real.pi / 2) *
        Real.exp (-(Real.pi - 1 / 2) * y) := by
  have hpi := Real.pi_pos
  have hsqrt : Real.sqrt (Real.exp y) = Real.exp (y / 2) :=
    (Real.exp_half y).symm
  have hsq : (Real.exp y) ^ 2 = Real.exp (2 * y) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hlin : (1 : ℝ) + 2 * y ≤ (Real.exp y) ^ 2 := by
    rw [hsq]
    have := Real.add_one_le_exp (2 * y)
    linarith
  -- compare the exponents directly
  have hexp_le : Real.exp (-(Real.pi * (Real.exp y) ^ 2) / 2) ≤
      Real.exp (-(Real.pi * (1 + 2 * y)) / 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hlin hpi.le
    linarith
  calc
    24 * Real.sqrt (Real.exp y) *
        Real.exp (-(Real.pi * (Real.exp y) ^ 2) / 2) ≤
        24 * Real.exp (y / 2) * Real.exp (-(Real.pi * (1 + 2 * y)) / 2) := by
      rw [hsqrt]
      exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = 24 * Real.exp (-Real.pi / 2) * Real.exp (-(Real.pi - 1 / 2) * y) := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

#print axioms envelope_additive_bound

/-- The decaying exponential integrates below its constant over `[0, b]`. -/
private theorem exp_decay_intervalIntegral_le {b : ℝ} (hb : 0 ≤ b) :
    ∫ y in (0 : ℝ)..b, Real.exp (-(Real.pi - 1 / 2) * y) ≤
      (Real.pi - 1 / 2)⁻¹ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hc : (0 : ℝ) < Real.pi - 1 / 2 := by linarith
  have hanti : ∀ y : ℝ, HasDerivAt
      (fun v : ℝ => -(Real.pi - 1 / 2)⁻¹ * Real.exp (-(Real.pi - 1 / 2) * v))
      (Real.exp (-(Real.pi - 1 / 2) * y)) y := by
    intro y
    have hlin : HasDerivAt (fun v : ℝ => -(Real.pi - 1 / 2) * v)
        (-(Real.pi - 1 / 2)) y := by
      simpa using (hasDerivAt_id y).const_mul (-(Real.pi - 1 / 2))
    have hexp := hlin.exp
    have hmul := hexp.const_mul (-(Real.pi - 1 / 2)⁻¹)
    have hne : Real.pi - 1 / 2 ≠ 0 := ne_of_gt hc
    have hrew : -(Real.pi - 1 / 2)⁻¹ *
        (Real.exp (-(Real.pi - 1 / 2) * y) * -(Real.pi - 1 / 2)) =
        Real.exp (-(Real.pi - 1 / 2) * y) := by
      have hstep : -(Real.pi - 1 / 2)⁻¹ *
          (Real.exp (-(Real.pi - 1 / 2) * y) * -(Real.pi - 1 / 2)) =
          ((Real.pi - 1 / 2)⁻¹ * (Real.pi - 1 / 2)) *
            Real.exp (-(Real.pi - 1 / 2) * y) := by ring
      rw [hstep, inv_mul_cancel₀ hne, one_mul]
    rw [hrew] at hmul
    exact hmul
  have hint : ∫ y in (0 : ℝ)..b, Real.exp (-(Real.pi - 1 / 2) * y) =
      -(Real.pi - 1 / 2)⁻¹ * Real.exp (-(Real.pi - 1 / 2) * b) -
        (-(Real.pi - 1 / 2)⁻¹ * Real.exp (-(Real.pi - 1 / 2) * 0)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hanti y)
    apply Continuous.intervalIntegrable
    continuity
  rw [hint]
  have h0 : Real.exp (-(Real.pi - 1 / 2) * 0) = 1 := by
    norm_num
  rw [h0]
  have hpos : (0 : ℝ) < Real.exp (-(Real.pi - 1 / 2) * b) := Real.exp_pos _
  have hinvpos : (0 : ℝ) < (Real.pi - 1 / 2)⁻¹ := by positivity
  nlinarith [hpos, hinvpos]

#print axioms exp_decay_intervalIntegral_le

/-- The two envelope halves combine into one continuous majorant on the whole
line: with `t = x - log lam` the starred target obeys
`24 * exp (-pi/2) * exp (-(pi - 1/2) * |t|)`.  This is the only bound the L1
assembly ever integrates, so the (unproved) continuity of `E_star H` itself is
never needed. -/
private theorem E_star_explicitCCMLimitH_additive_envelope
    {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    ‖E_star explicitCCMLimitH (Real.exp x / lam)‖ ≤
      24 * Real.exp (-Real.pi / 2) *
        Real.exp (-(Real.pi - 1 / 2) * |x - Real.log lam|) := by
  have hu : Real.exp x / lam = Real.exp (x - Real.log lam) := by
    rw [Real.exp_sub, Real.exp_log hlam]
  set t : ℝ := x - Real.log lam with ht
  rw [hu]
  rcases le_or_lt 0 t with hpos | hneg
  · -- right half: u = exp t >= 1
    have habs : |t| = t := abs_of_nonneg hpos
    rw [habs]
    refine le_trans (E_star_explicitCCMLimitH_norm_le_of_one_le
      (Real.one_le_exp_iff.mpr hpos)) ?_
    simpa using envelope_additive_bound hpos
  · -- left half: u = exp t <= 1, invert
    have habs : |t| = -t := abs_of_neg hneg
    rw [habs]
    have hle : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr hneg.le
    have hinv : (Real.exp t)⁻¹ = Real.exp (-t) := (Real.exp_neg t).symm
    refine le_trans (E_star_explicitCCMLimitH_norm_le_of_le_one
      (Real.exp_pos t) hle) ?_
    rw [hinv]
    simpa using envelope_additive_bound (neg_nonneg.mpr hneg.le)

#print axioms E_star_explicitCCMLimitH_additive_envelope

end Q3.RouteB.D0Pstar
