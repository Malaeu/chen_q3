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
#print axioms ctW0_cylinder_eigenrelation
#print axioms ctW4_cylinder_eigenrelation

end Q3.RouteB.D0Pstar
