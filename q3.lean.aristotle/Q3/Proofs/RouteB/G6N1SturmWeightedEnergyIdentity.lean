import Q3.Proofs.RouteB.G6N1CylinderTransportL1Budget

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# STURM_ENERGY_NODE, part A (verdict 4c0e13ba, node 1)

The abstract weighted Sturm energy identity on a symmetric window with
degenerate weight `w(x) = lam² − x²`, and the exact cylinder eigenrelations
for the two fixed physical profiles.  The boundary enters only through the
zero limits of the weighted flux at the two singular endpoints: no
derivative trace and no endpoint value is consumed anywhere.
-/

/--
**The abstract weighted energy identity.**  If `g` is differentiable on the
open window with derivative `gd`, the weighted flux `w·gd` is differentiable
with derivative `r` (the caller supplies `r` from an ODE), the flux
`w·gd·g` tends to zero at both singular endpoints, and both the source and
the energy are integrable, then

`∫_{(-lam,lam)} w·gd² = − ∫_{(-lam,lam)} r·g`.
-/
theorem sturm_weighted_energy_identity
    (lam : ℝ) (hlam : 0 < lam)
    (g gd r : ℝ → ℝ)
    (hg : ∀ x ∈ Ioo (-lam) lam, HasDerivAt g (gd x) x)
    (hr : ∀ x ∈ Ioo (-lam) lam,
      HasDerivAt (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y) (r x) x)
    (hflux_top : Tendsto (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x * g x)
      (nhdsWithin lam (Iio lam)) (𝓝 0))
    (hflux_bot : Tendsto (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x * g x)
      (nhdsWithin (-lam) (Ioi (-lam))) (𝓝 0))
    (hint1 : IntegrableOn (fun x : ℝ => r x * g x) (Ioo (-lam) lam) volume)
    (hint2 : IntegrableOn (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x ^ 2)
      (Ioo (-lam) lam) volume) :
    (∫ x in Ioo (-lam) lam, (lam ^ 2 - x ^ 2) * gd x ^ 2) =
      -∫ x in Ioo (-lam) lam, r x * g x := by
  set F : ℝ → ℝ := fun x => (lam ^ 2 - x ^ 2) * gd x * g x with hF
  set h : ℝ → ℝ := fun x => r x * g x + (lam ^ 2 - x ^ 2) * gd x ^ 2 with hh
  have hint : IntegrableOn h (Ioo (-lam) lam) volume := hint1.add hint2
  set a : ℕ → ℝ := fun n => -lam + lam / ((n : ℝ) + 2) with ha
  set b : ℕ → ℝ := fun n => lam - lam / ((n : ℝ) + 2) with hb
  have hquot_pos : ∀ n : ℕ, 0 < lam / ((n : ℝ) + 2) := by
    intro n
    positivity
  have hquot_le : ∀ n : ℕ, lam / ((n : ℝ) + 2) ≤ lam / 2 := by
    intro n
    apply div_le_div_of_nonneg_left hlam.le (by norm_num)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hquot_anti : ∀ n m : ℕ, n ≤ m →
      lam / ((m : ℝ) + 2) ≤ lam / ((n : ℝ) + 2) := by
    intro n m hnm
    apply div_le_div_of_nonneg_left hlam.le
    · push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · have hc : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
  have hab_mem : ∀ n : ℕ, a n ∈ Ioo (-lam) lam ∧ b n ∈ Ioo (-lam) lam := by
    intro n
    have h1 := hquot_pos n
    have h2 := hquot_le n
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> [rw [ha]; rw [ha]; rw [hb]; rw [hb]] <;>
      simp only [] <;> linarith
  have hle : ∀ n : ℕ, a n ≤ b n := by
    intro n
    have h2 := hquot_le n
    rw [ha, hb]
    simp only []
    linarith
  have hFderiv : ∀ x ∈ Ioo (-lam) lam, HasDerivAt F (h x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((lam ^ 2 - y ^ 2) * gd y) * g y)
        (r x * g x + (lam ^ 2 - x ^ 2) * gd x * gd x) x :=
      (hr x hx).mul (hg x hx)
    have hFfun : (fun y : ℝ => ((lam ^ 2 - y ^ 2) * gd y) * g y) = F := by
      funext y
      rw [hF]
    rw [hFfun] at h1
    exact h1.congr_deriv (by rw [hh]; ring)
  have hsub_uIcc : ∀ n : ℕ, Set.uIcc (a n) (b n) ⊆ Ioo (-lam) lam := by
    intro n
    rw [Set.uIcc_of_le (hle n)]
    intro x hx
    exact ⟨lt_of_lt_of_le (hab_mem n).1.1 hx.1,
      lt_of_le_of_lt hx.2 (hab_mem n).2.2⟩
  have hFTC : ∀ n : ℕ, (∫ x in (a n)..(b n), h x) = F (b n) - F (a n) := by
    intro n
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hFderiv x (hsub_uIcc n hx)
    · exact (hint.mono_set (hsub_uIcc n)).intervalIntegrable
  have hquot_tendsto : Tendsto (fun n : ℕ => lam / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hIoc_mono : Monotone (fun n : ℕ => Ioc (a n) (b n)) := by
    intro n m hnm
    apply Set.Ioc_subset_Ioc
    · rw [ha]
      simp only []
      linarith [hquot_anti n m hnm]
    · rw [hb]
      simp only []
      linarith [hquot_anti n m hnm]
  have hIoc_union : (⋃ n : ℕ, Ioc (a n) (b n)) = Ioo (-lam) lam := by
    apply Set.Subset.antisymm
    · apply Set.iUnion_subset
      intro n x hx
      exact ⟨lt_of_lt_of_le (hab_mem n).1.1 hx.1.le,
        lt_of_le_of_lt hx.2 (hab_mem n).2.2⟩
    · intro x hx
      have hgap1 : 0 < x + lam := by linarith [hx.1]
      have hgap2 : 0 < lam - x := by linarith [hx.2]
      have hev : ∀ᶠ n : ℕ in atTop,
          lam / ((n : ℝ) + 2) < min (x + lam) (lam - x) :=
        hquot_tendsto.eventually_lt_const (lt_min hgap1 hgap2)
      obtain ⟨n, hn⟩ := hev.exists
      have hn1 := (lt_min_iff.mp hn).1
      have hn2 := (lt_min_iff.mp hn).2
      refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · rw [ha]
        simp only []
        linarith
      · rw [hb]
        simp only []
        linarith
  have htendsto_int : Tendsto (fun n : ℕ => ∫ x in Ioc (a n) (b n), h x)
      atTop (𝓝 (∫ x in Ioo (-lam) lam, h x)) := by
    have h1 := MeasureTheory.tendsto_setIntegral_of_monotone
      (fun n : ℕ => measurableSet_Ioc) hIoc_mono
      (by rw [hIoc_union]; exact hint)
    rwa [hIoc_union] at h1
  have hbn : Tendsto b atTop (nhdsWithin lam (Iio lam)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h1 : Tendsto b atTop (𝓝 (lam - 0)) :=
        tendsto_const_nhds.sub hquot_tendsto
      simpa using h1
    · filter_upwards [] with n
      exact (hab_mem n).2.2
  have han : Tendsto a atTop (nhdsWithin (-lam) (Ioi (-lam))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h1 : Tendsto a atTop (𝓝 (-lam + 0)) :=
        tendsto_const_nhds.add hquot_tendsto
      simpa using h1
    · filter_upwards [] with n
      exact (hab_mem n).1.1
  have hFb : Tendsto (fun n : ℕ => F (b n)) atTop (𝓝 0) := hflux_top.comp hbn
  have hFa : Tendsto (fun n : ℕ => F (a n)) atTop (𝓝 0) := hflux_bot.comp han
  have hdiff : Tendsto (fun n : ℕ => F (b n) - F (a n)) atTop (𝓝 0) := by
    simpa using hFb.sub hFa
  have hseq_eq : (fun n : ℕ => ∫ x in Ioc (a n) (b n), h x) =
      fun n : ℕ => F (b n) - F (a n) := by
    funext n
    rw [← hFTC n, intervalIntegral.integral_of_le (hle n)]
  rw [hseq_eq] at htendsto_int
  have hzero : (∫ x in Ioo (-lam) lam, h x) = 0 :=
    tendsto_nhds_unique htendsto_int hdiff
  have hadd := MeasureTheory.integral_add hint1 hint2
  rw [hh] at hzero
  rw [hzero] at hadd
  linarith [hadd]

/--
**Energy finiteness and bound from the flux limits.**  Same hypotheses as the
identity, but WITHOUT assuming integrability of the energy: on every
truncated interval the FTC gives
`∫_{a_n}^{b_n} w·gd² = F(b_n) − F(a_n) − ∫_{a_n}^{b_n} r·g`, the right side
converges, and the left side is monotone in `n`; hence every truncated
energy integral obeys the uniform bound
`∫_{Ioc(a,b)} w·gd² ≤ |F(b)| + |F(a)| + ∫_{Ioo} |r·g|` — which is what the
rate ledger consumes.  (Stated at the truncated level to avoid assuming
integrability; the consumer works with truncations and monotone limits.)
-/
theorem sturm_weighted_energy_truncated_bound
    (lam : ℝ) (hlam : 0 < lam)
    (g gd r : ℝ → ℝ)
    (hg : ∀ x ∈ Ioo (-lam) lam, HasDerivAt g (gd x) x)
    (hr : ∀ x ∈ Ioo (-lam) lam,
      HasDerivAt (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y) (r x) x)
    (hcont_gd : ContinuousOn gd (Ioo (-lam) lam))
    (hcont_rg : ContinuousOn (fun x : ℝ => r x * g x) (Ioo (-lam) lam))
    (hint1 : IntegrableOn (fun x : ℝ => r x * g x) (Ioo (-lam) lam) volume)
    (a b : ℝ)
    (hab : a ≤ b)
    (haI : a ∈ Ioo (-lam) lam) (hbI : b ∈ Ioo (-lam) lam) :
    (∫ x in a..b, (lam ^ 2 - x ^ 2) * gd x ^ 2) ≤
      |(lam ^ 2 - b ^ 2) * gd b * g b| + |(lam ^ 2 - a ^ 2) * gd a * g a| +
        ∫ x in Ioo (-lam) lam, |r x * g x| := by
  set F : ℝ → ℝ := fun x => (lam ^ 2 - x ^ 2) * gd x * g x with hF
  have hsub_uIcc : Set.uIcc a b ⊆ Ioo (-lam) lam := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact ⟨lt_of_lt_of_le haI.1 hx.1, lt_of_le_of_lt hx.2 hbI.2⟩
  have hFderiv : ∀ x ∈ Ioo (-lam) lam,
      HasDerivAt F (r x * g x + (lam ^ 2 - x ^ 2) * gd x ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((lam ^ 2 - y ^ 2) * gd y) * g y)
        (r x * g x + (lam ^ 2 - x ^ 2) * gd x * gd x) x :=
      (hr x hx).mul (hg x hx)
    have hFfun : (fun y : ℝ => ((lam ^ 2 - y ^ 2) * gd y) * g y) = F := by
      funext y
      rw [hF]
    rw [hFfun] at h1
    exact h1.congr_deriv (by ring)
  have hcont_sum : ContinuousOn
      (fun x : ℝ => r x * g x + (lam ^ 2 - x ^ 2) * gd x ^ 2)
      (Ioo (-lam) lam) := by
    apply hcont_rg.add
    apply ContinuousOn.mul
    · fun_prop
    · exact (hcont_gd.mul hcont_gd).congr (fun x _ => by ring)
  have hFTC : (∫ x in a..b, (r x * g x + (lam ^ 2 - x ^ 2) * gd x ^ 2)) =
      F b - F a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hFderiv x (hsub_uIcc hx)
    · exact (hcont_sum.mono hsub_uIcc).intervalIntegrable
  have hint_rg_ab : IntervalIntegrable (fun x : ℝ => r x * g x) volume a b :=
    ((hint1.mono_set hsub_uIcc)).intervalIntegrable
  have hint_en_ab : IntervalIntegrable
      (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply (ContinuousOn.mono _ hsub_uIcc)
    apply ContinuousOn.mul
    · fun_prop
    · exact (hcont_gd.mul hcont_gd).congr (fun x _ => by ring)
  have hsplit : (∫ x in a..b, (lam ^ 2 - x ^ 2) * gd x ^ 2) =
      (F b - F a) - ∫ x in a..b, r x * g x := by
    rw [← hFTC, ← intervalIntegral.integral_sub
      (hint_rg_ab.add hint_en_ab) hint_rg_ab]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hsplit]
  have h1 : |∫ x in a..b, r x * g x| ≤
      ∫ x in Ioo (-lam) lam, |r x * g x| := by
    calc
      |∫ x in a..b, r x * g x| ≤ abs (∫ x in a..b, |r x * g x|) := by
        have h := intervalIntegral.norm_integral_le_abs_integral_norm
          (f := fun x : ℝ => r x * g x) (a := a) (b := b) (μ := volume)
        simpa [Real.norm_eq_abs] using h
      _ = ∫ x in a..b, |r x * g x| :=
          abs_of_nonneg (intervalIntegral.integral_nonneg hab
            (fun x _ => abs_nonneg _))
      _ = ∫ x in Ioc a b, |r x * g x| :=
          intervalIntegral.integral_of_le hab
      _ ≤ ∫ x in Ioo (-lam) lam, |r x * g x| := by
          apply setIntegral_mono_set hint1.abs
            (Eventually.of_forall fun x => abs_nonneg _)
          apply HasSubset.Subset.eventuallyLE
          intro x hx
          exact ⟨lt_of_lt_of_le haI.1 hx.1.le, lt_of_le_of_lt hx.2 hbI.2⟩
  have h2 : F b - F a ≤ |F b| + |F a| := by
    have := abs_sub_abs_le_abs_sub (F b) (F a)
    have h3 := le_abs_self (F b - F a)
    have h4 : |F b - F a| ≤ |F b| + |F a| := by
      calc |F b - F a| = |F b + -F a| := by rw [sub_eq_add_neg]
        _ ≤ |F b| + |-F a| := abs_add_le _ _
        _ = |F b| + |F a| := by rw [abs_neg]
    linarith
  have h5 : -(∫ x in a..b, r x * g x) ≤ |∫ x in a..b, r x * g x| :=
    neg_le_abs _
  rw [hF] at h2
  simp only [] at h2
  linarith [h1, h2, h5]

/-! ## Exact cylinder eigenrelations for the two fixed profiles -/

/-- First derivative of the mode-0 profile. -/
def ctW0d (x : ℝ) : ℝ := -2 * Real.pi * x * Real.exp (-Real.pi * x ^ 2)

/-- Second derivative of the mode-0 profile. -/
def ctW0dd (x : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * Real.exp (-Real.pi * x ^ 2)

/-- First derivative of the mode-4 profile. -/
def ctW4d (x : ℝ) : ℝ :=
  (-32 * Real.pi ^ 3 * x ^ 5 + 112 * Real.pi ^ 2 * x ^ 3 - 54 * Real.pi * x) *
    Real.exp (-Real.pi * x ^ 2)

/-- Second derivative of the mode-4 profile. -/
def ctW4dd (x : ℝ) : ℝ :=
  (64 * Real.pi ^ 4 * x ^ 6 - 384 * Real.pi ^ 3 * x ^ 4 +
      444 * Real.pi ^ 2 * x ^ 2 - 54 * Real.pi) *
    Real.exp (-Real.pi * x ^ 2)

private theorem ct2_exp_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      (-2 * Real.pi * y * Real.exp (-Real.pi * y ^ 2)) y := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2) (-2 * Real.pi * y) y := by
    have := (hasDerivAt_pow 2 y).const_mul (-Real.pi)
    exact this.congr_deriv (by push_cast; ring)
  have := h1.exp
  simpa [mul_comm] using this

private theorem ct2_polyexp_hasDerivAt {P : ℝ → ℝ} {p : ℝ} (y : ℝ)
    (hP : HasDerivAt P p y) :
    HasDerivAt (fun t : ℝ => P t * Real.exp (-Real.pi * t ^ 2))
      ((p - 2 * Real.pi * y * P y) * Real.exp (-Real.pi * y ^ 2)) y := by
  have h := hP.mul (ct2_exp_hasDerivAt y)
  exact h.congr_deriv (by ring)

theorem ctW0_hasDerivAt' (y : ℝ) : HasDerivAt ctW0 (ctW0d y) y := by
  have := ct2_exp_hasDerivAt y
  unfold ctW0 ctW0d
  exact this.congr_deriv (by ring)

theorem ctW0d_hasDerivAt (y : ℝ) : HasDerivAt ctW0d (ctW0dd y) y := by
  have hP : HasDerivAt (fun t : ℝ => -2 * Real.pi * t) (-2 * Real.pi) y := by
    have := (hasDerivAt_id y).const_mul (-2 * Real.pi)
    exact this.congr_deriv (by ring)
  have h := ct2_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    -2 * Real.pi * t * Real.exp (-Real.pi * t ^ 2)) (ctW0dd y) y
  refine (h.congr_deriv (by unfold ctW0dd; ring)).congr_of_eventuallyEq ?_
  filter_upwards [] with t
  ring

theorem ctW4_hasDerivAt' (y : ℝ) : HasDerivAt ctW4 (ctW4d y) y := by
  have hP : HasDerivAt
      (fun t : ℝ => 16 * Real.pi ^ 2 * t ^ 4 - 24 * Real.pi * t ^ 2 + 3)
      (16 * Real.pi ^ 2 * (4 * y ^ 3) - 24 * Real.pi * (2 * y) + 0) y := by
    have h4 := (hasDerivAt_pow 4 y).const_mul (16 * Real.pi ^ 2)
    have h2 := (hasDerivAt_pow 2 y).const_mul (24 * Real.pi)
    have hc := hasDerivAt_const y (3 : ℝ)
    exact ((HasDerivAt.sub h4 h2).add hc).congr_deriv (by push_cast; ring)
  have h := ct2_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (16 * Real.pi ^ 2 * t ^ 4 - 24 * Real.pi * t ^ 2 + 3) *
      Real.exp (-Real.pi * t ^ 2)) (ctW4d y) y
  exact h.congr_deriv (by unfold ctW4d; ring)

theorem ctW4d_hasDerivAt (y : ℝ) : HasDerivAt ctW4d (ctW4dd y) y := by
  have hP : HasDerivAt
      (fun t : ℝ => -32 * Real.pi ^ 3 * t ^ 5 + 112 * Real.pi ^ 2 * t ^ 3 -
        54 * Real.pi * t)
      (-32 * Real.pi ^ 3 * (5 * y ^ 4) + 112 * Real.pi ^ 2 * (3 * y ^ 2) -
        54 * Real.pi * 1) y := by
    have h5 := (hasDerivAt_pow 5 y).const_mul (-32 * Real.pi ^ 3)
    have h3 := (hasDerivAt_pow 3 y).const_mul (112 * Real.pi ^ 2)
    have h1 := (hasDerivAt_id y).const_mul (54 * Real.pi)
    exact ((HasDerivAt.add h5 h3).sub h1).congr_deriv (by push_cast; ring)
  have h := ct2_polyexp_hasDerivAt y hP
  show HasDerivAt (fun t : ℝ =>
    (-32 * Real.pi ^ 3 * t ^ 5 + 112 * Real.pi ^ 2 * t ^ 3 -
      54 * Real.pi * t) * Real.exp (-Real.pi * t ^ 2)) (ctW4dd y) y
  exact h.congr_deriv (by unfold ctW4dd; ring)

/-- Exact cylinder eigenrelation for the mode-0 profile: eigenvalue `2π`. -/
theorem ctW0_cylinder_eigenrelation (x : ℝ) :
    -ctW0dd x + 4 * Real.pi ^ 2 * x ^ 2 * ctW0 x = 2 * Real.pi * ctW0 x := by
  unfold ctW0dd ctW0
  ring

/-- Exact cylinder eigenrelation for the mode-4 profile: eigenvalue `18π`. -/
theorem ctW4_cylinder_eigenrelation (x : ℝ) :
    -ctW4dd x + 4 * Real.pi ^ 2 * x ^ 2 * ctW4 x = 18 * Real.pi * ctW4 x := by
  unfold ctW4dd ctW4
  ring

#print axioms sturm_weighted_energy_identity
#print axioms sturm_weighted_energy_truncated_bound
#print axioms ctW0_cylinder_eigenrelation
#print axioms ctW4_cylinder_eigenrelation

end Q3.RouteB.D0Pstar
