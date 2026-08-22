/-! ## Upper and lower bounds for the mass of a normalised eigenfunction -/

/-- Reflection formula for the integral of an even function. -/
theorem integral_even_reflect (h : ℝ → ℝ) (hev : ∀ x : ℝ, h (-x) = h x) (a b : ℝ) :
    (∫ x in a..b, h x) = ∫ x in (-b)..(-a), h x := by
  rw [← intervalIntegral.integral_comp_neg h]
  simp [hev]

/-- If an even eigenfunction is bounded by `P` on `[0,c]` and carries at most a quarter of its
mass on the layer `[c,1]`, its total mass is at most `4P²`. -/
theorem spheroidal_mass_upper (f : ℝ → ℝ) (c P : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hev : ∀ x : ℝ, f (-x) = f x) (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) c, |f x| ≤ P)
    (htail : (∫ x in c..1, f x ^ 2) ≤ (1 / 4) * ∫ x in (-1 : ℝ)..1, f x ^ 2) :
    (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 := by
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hsplit : (∫ x in (0 : ℝ)..c, f x ^ 2) + (∫ x in c..1, f x ^ 2)
      = ∫ x in (0 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hisq 0 c (by norm_num) ⟨by linarith, hc1⟩) (hisq c 1 ⟨by linarith, hc1⟩ (by norm_num))
  have hmid : (∫ x in (0 : ℝ)..c, f x ^ 2) ≤ c * P ^ 2 := by
    have h := intervalIntegral.integral_mono_on hc0.le
      (hisq 0 c (by norm_num) ⟨by linarith, hc1⟩) (intervalIntegrable_const (c := P ^ 2))
      (fun x hx => by
        have h1 := hP x hx
        nlinarith [abs_nonneg (f x), sq_abs (f x)])
    simpa [smul_eq_mul, mul_comm] using h
  have hhalf := integral_sq_even_half f hev hcf
  nlinarith [sq_nonneg P, hc1, hc0]

/-- A normalised even eigenfunction whose derivative is bounded by `P` on `[0,c]` has mass at
least `(min c (1/(2P)))/2`. -/
theorem spheroidal_mass_lower (f f1 : ℝ → ℝ) (c P : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hP0 : 0 < P)
    (hev : ∀ x : ℝ, f (-x) = f x) (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hf0 : f 0 = 1)
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) c, |f1 x| ≤ P) :
    (min c (1 / (2 * P))) / 2 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
  set r := min c (1 / (2 * P)) with hrdef
  have hr0 : 0 < r := lt_min hc0 (by positivity)
  have hrc : r ≤ c := min_le_left _ _
  have hrP : r * P ≤ 1 / 2 := by
    have h1 : r ≤ 1 / (2 * P) := min_le_right _ _
    calc r * P ≤ (1 / (2 * P)) * P := by nlinarith
      _ = 1 / 2 := by field_simp
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hlow : ∀ x ∈ Icc (0 : ℝ) r, (1 : ℝ) / 4 ≤ f x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxr : x ≤ r := hx.2
    have hxc : x ≤ c := le_trans hxr hrc
    have hxIoo : Icc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hxc]⟩
    have hsubu : uIcc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 := by
      rw [uIcc_of_le hx0]; exact hxIoo
    have hint : IntervalIntegrable f1 volume 0 x := (hf1c.mono hsubu).intervalIntegrable
    have hFTC : f x - f 0 = ∫ t in (0 : ℝ)..x, f1 t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsubu ht)) hint).symm
    have habs : |f x - f 0| ≤ x * P := by
      rw [hFTC]
      have h1 : |∫ t in (0 : ℝ)..x, f1 t| ≤ ∫ t in (0 : ℝ)..x, |f1 t| :=
        intervalIntegral.abs_integral_le_integral_abs hx0
      have h2 : (∫ t in (0 : ℝ)..x, |f1 t|) ≤ ∫ _t in (0 : ℝ)..x, P := by
        refine intervalIntegral.integral_mono_on hx0 hint.abs intervalIntegrable_const
          (fun t ht => hP t ⟨ht.1, le_trans ht.2 hxc⟩)
      rw [intervalIntegral.integral_const] at h2
      simp only [smul_eq_mul, sub_zero] at h2
      linarith
    have hxP : x * P ≤ 1 / 2 := by nlinarith [hP0.le, hx0]
    rw [hf0] at habs
    have : (1 : ℝ) / 2 ≤ f x := by
      have := abs_le.mp (le_trans habs hxP)
      linarith [this.1]
    nlinarith
  have hmass : r / 4 ≤ ∫ x in (0 : ℝ)..r, f x ^ 2 := by
    have h := intervalIntegral.integral_mono_on hr0.le
      (intervalIntegrable_const (c := (1 : ℝ) / 4))
      (hisq 0 r (by norm_num) ⟨by linarith, by linarith [hrc, hc1]⟩) hlow
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul, sub_zero] at h
    linarith
  have hmono : (∫ x in (0 : ℝ)..r, f x ^ 2) ≤ ∫ x in (0 : ℝ)..1, f x ^ 2 := by
    refine intervalIntegral.integral_mono_interval (le_refl 0) hr0.le
      (by linarith [hrc, hc1]) (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
      (hisq 0 1 (by norm_num) (by norm_num))
  have hhalf := integral_sq_even_half f hev hcf
  linarith

