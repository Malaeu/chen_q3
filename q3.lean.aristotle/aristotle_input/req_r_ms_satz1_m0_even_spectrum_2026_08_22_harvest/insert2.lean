/-- An arithmetic–geometric mean characterisation of the Cauchy–Schwarz bound: if a
nonnegative number `u` satisfies `u ≤ (l * A + B / l) / 2` for every `l > 0`, then `u² ≤ A * B`. -/
theorem real_sq_le_mul_of_forall_amgm {u A B : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → u ≤ (l * A + B / l) / 2) : u ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · have hu0 : u = 0 := by
      by_contra hne
      have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
      have hl : (0 : ℝ) < B / u + 1 := by positivity
      have hkey := h _ hl
      rw [← hA0] at hkey
      have hBl : B / (B / u + 1) < u := by
        rw [div_lt_iff₀ hl]
        have : B / u * u = B := div_mul_cancel₀ B (ne_of_gt hupos)
        nlinarith [this]
      simp only [mul_zero, zero_add] at hkey
      linarith
    simp [hu0, ← hA0]
  · rcases eq_or_lt_of_le hB with hB0 | hB0
    · have hu0 : u = 0 := by
        by_contra hne
        have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
        have hl : (0 : ℝ) < u / A := by positivity
        have hkey := h _ hl
        rw [← hB0] at hkey
        have hkey2 : u ≤ (u / A * A) / 2 := by simpa using hkey
        rw [div_mul_cancel₀ u (ne_of_gt hA0)] at hkey2
        linarith
      simp [hu0, ← hB0]
    · set s := Real.sqrt (A * B) with hs
      have hs2 : s ^ 2 = A * B := Real.sq_sqrt (by positivity)
      have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hl : (0 : ℝ) < s / A := by positivity
      have hkey := h _ hl
      have h1 : s / A * A = s := div_mul_cancel₀ s (ne_of_gt hA0)
      have h2 : B / (s / A) = s := by
        field_simp
        nlinarith [hs2]
      rw [h1, h2] at hkey
      have hus : u ≤ s := by linarith
      nlinarith [hs2, hu]

/-- **Cauchy–Schwarz for the degenerate weight.** The squared increment of `f` is bounded by the
weighted Dirichlet energy times the integral of the reciprocal weight. -/
theorem spheroidal_sq_sub_le (f f1 : ℝ → ℝ)
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    {y x : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) (hyx : y ≤ x) :
    (f x - f y) ^ 2 ≤ (∫ t in y..x, (1 - t ^ 2) * f1 t ^ 2) * (∫ t in y..x, 1 / (1 - t ^ 2)) := by
  have hsub : uIcc y x ⊆ Ioo (-1 : ℝ) 1 := (Set.ordConnected_Ioo).uIcc_subset hy hx
  have hpos : ∀ t ∈ uIcc y x, (0 : ℝ) < 1 - t ^ 2 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hc1 : ContinuousOn f1 (uIcc y x) := hf1c.mono hsub
  have hi1 : IntervalIntegrable f1 volume y x := hc1.intervalIntegrable
  have hiabs : IntervalIntegrable (fun t => |f1 t|) volume y x := hi1.abs
  have hiA : IntervalIntegrable (fun t => (1 - t ^ 2) * f1 t ^ 2) volume y x :=
    ContinuousOn.intervalIntegrable
      ((continuousOn_const.sub (continuousOn_pow 2)).mul (hc1.pow 2))
  have hcw : ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2)) (uIcc y x) := by
    intro t ht
    have hne : (1 - t ^ 2) ≠ 0 := ne_of_gt (hpos t ht)
    have h1 : ContinuousAt (fun t : ℝ => 1 - t ^ 2) t := by fun_prop
    exact (continuousAt_const.div h1 hne).continuousWithinAt
  have hiB : IntervalIntegrable (fun t : ℝ => 1 / (1 - t ^ 2)) volume y x :=
    hcw.intervalIntegrable
  set A := ∫ t in y..x, (1 - t ^ 2) * f1 t ^ 2 with hAdef
  set B := ∫ t in y..x, 1 / (1 - t ^ 2) with hBdef
  set u := ∫ t in y..x, |f1 t| with hudef
  have hA0 : 0 ≤ A := by
    refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
    have := hpos t (by rw [uIcc_of_le hyx]; exact ht)
    positivity
  have hB0 : 0 ≤ B := by
    refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
    have := hpos t (by rw [uIcc_of_le hyx]; exact ht)
    positivity
  have hu0 : 0 ≤ u := intervalIntegral.integral_nonneg hyx (fun t _ => abs_nonneg _)
  have hkey : ∀ l : ℝ, 0 < l → u ≤ (l * A + B / l) / 2 := by
    intro l hl
    have hmono : u ≤ ∫ t in y..x,
        (l * ((1 - t ^ 2) * f1 t ^ 2) + (1 / l) * (1 / (1 - t ^ 2))) / 2 := by
      refine intervalIntegral.integral_mono_on hyx hiabs ?_ (fun t ht => ?_)
      · exact (((hiA.const_mul l).add (hiB.const_mul (1 / l))).div_const 2)
      · have htm : t ∈ uIcc y x := by rw [uIcc_of_le hyx]; exact ht
        have hp := hpos t htm
        have hsq : f1 t ^ 2 = |f1 t| ^ 2 := (sq_abs _).symm
        rw [hsq, ← sub_nonneg]
        have key : (l * ((1 - t ^ 2) * |f1 t| ^ 2) + 1 / l * (1 / (1 - t ^ 2))) / 2 - |f1 t|
            = (l * (1 - t ^ 2) * |f1 t| - 1) ^ 2 / (2 * l * (1 - t ^ 2)) := by
          field_simp
          ring
        rw [key]
        positivity
    have hval : (∫ t in y..x, (l * ((1 - t ^ 2) * f1 t ^ 2) + (1 / l) * (1 / (1 - t ^ 2))) / 2)
        = (l * A + B / l) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hiA.const_mul l)
        (hiB.const_mul (1 / l)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      rw [← hAdef, ← hBdef]
      field_simp
    linarith [hval ▸ hmono]
  have hfin := real_sq_le_mul_of_forall_amgm hu0 hA0 hB0 hkey
  have hFTC : f x - f y = ∫ t in y..x, f1 t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht)) hi1).symm
  have habs : |f x - f y| ≤ u := by
    rw [hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hyx
  nlinarith [abs_nonneg (f x - f y), sq_abs (f x - f y), hfin, habs, hu0]

/-- The reciprocal weight has a logarithmic integral on `[y,x] ⊆ [0,1)`. -/
theorem spheroidal_integral_inv_one_sub_sq_le {y x : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    (∫ t in y..x, 1 / (1 - t ^ 2)) ≤ Real.log (1 - y) - Real.log (1 - x) := by
  have hsub : ∀ t ∈ Icc y x, 0 ≤ t ∧ t < 1 := fun t ht =>
    ⟨le_trans hy ht.1, lt_of_le_of_lt ht.2 hx⟩
  have hcw : ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2)) (uIcc y x) := by
    rw [uIcc_of_le hyx]
    intro t ht
    obtain ⟨h0, h1⟩ := hsub t ht
    have hne : (1 - t ^ 2) ≠ 0 := by nlinarith
    have hc : ContinuousAt (fun t : ℝ => 1 - t ^ 2) t := by fun_prop
    exact (continuousAt_const.div hc hne).continuousWithinAt
  have hcw2 : ContinuousOn (fun t : ℝ => 1 / (1 - t)) (uIcc y x) := by
    rw [uIcc_of_le hyx]
    intro t ht
    obtain ⟨h0, h1⟩ := hsub t ht
    have hne : (1 - t) ≠ 0 := by linarith
    have hc : ContinuousAt (fun t : ℝ => 1 - t) t := by fun_prop
    exact (continuousAt_const.div hc hne).continuousWithinAt
  have hval : (∫ t in y..x, 1 / (1 - t)) = Real.log (1 - y) - Real.log (1 - x) := by
    have hderiv : ∀ t ∈ uIcc y x, HasDerivAt (fun s : ℝ => -Real.log (1 - s)) (1 / (1 - t)) t := by
      intro t ht
      rw [uIcc_of_le hyx] at ht
      obtain ⟨h0, h1⟩ := hsub t ht
      have hne : (1 - t) ≠ 0 := by linarith
      have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have h3 := (Real.hasDerivAt_log hne).comp t h2
      have h4 := h3.neg
      convert h4 using 1
      field_simp
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcw2.intervalIntegrable
    rw [hI]
    ring
  rw [← hval]
  refine intervalIntegral.integral_mono_on hyx hcw.intervalIntegrable hcw2.intervalIntegrable
    (fun t ht => ?_)
  obtain ⟨h0, h1⟩ := hsub t ht
  exact one_div_le_one_div_of_le (by linarith) (by nlinarith)

/-- The integral of the reciprocal weight is nonnegative. -/
theorem spheroidal_integral_inv_one_sub_sq_nonneg {y x : ℝ} (hy : -1 < y) (hyx : y ≤ x)
    (hx : x < 1) : 0 ≤ ∫ t in y..x, 1 / (1 - t ^ 2) := by
  refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
  have h1 : -1 < t := lt_of_lt_of_le hy ht.1
  have h2 : t < 1 := lt_of_le_of_lt ht.2 hx
  have : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  positivity

/-- **Uniform tail bound.** If the weighted Dirichlet energy of `f` over every interior interval
is at most `D`, then the mass of `f²` on the endpoint layer `[1-τ, 1]` is at most
`2τ f(1-τ)² + 2Dτ`; in particular it tends to `0` with `τ`, uniformly in the family. -/
theorem spheroidal_tail_bound (f f1 : ℝ → ℝ) (D τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    (hD0 : 0 ≤ D)
    (hD : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ v →
        (∫ t in u..v, (1 - t ^ 2) * f1 t ^ 2) ≤ D) :
    (∫ x in (1 - τ)..1, f x ^ 2) ≤ 2 * τ * f (1 - τ) ^ 2 + 2 * D * τ := by
  set c := 1 - τ with hcdef
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hcτ : (1 : ℝ) - c = τ := by rw [hcdef]; ring
  have hcIoo : c ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hc1⟩
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-1 : ℝ) 1, f x ^ 2 ≤ M := by
    obtain ⟨M, hMb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hcf.pow 2)
    refine ⟨max M 0, le_max_right _ _, fun x hx => le_trans ?_ (le_max_left _ _)⟩
    have hb := hMb x hx
    calc f x ^ 2 ≤ |f x ^ 2| := le_abs_self _
      _ ≤ M := by simpa [Real.norm_eq_abs] using hb
  set H : ℝ → ℝ := fun x => (1 - x) * (Real.log (1 - x) - Real.log τ - 1) with hHdef
  have hHderiv : ∀ x : ℝ, x < 1 → HasDerivAt H (Real.log τ - Real.log (1 - x)) x := by
    intro x hx
    have hne : (1 - x) ≠ 0 := ne_of_gt (by linarith)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h3 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - x)) x := by
      have h := (Real.hasDerivAt_log hne).comp x h2
      simpa [div_eq_inv_mul] using h
    have h4 := h2.mul ((h3.sub_const (Real.log τ)).sub_const 1)
    convert h4 using 1
    field_simp
    ring
  have hlogcont : ∀ x : ℝ, x < 1 →
      ContinuousAt (fun s : ℝ => Real.log τ - Real.log (1 - s)) x := by
    intro x hx
    have hne : (1 - x) ≠ 0 := ne_of_gt (by linarith)
    have h1 : ContinuousAt (fun s : ℝ => 1 - s) x := by fun_prop
    exact continuousAt_const.sub ((Real.continuousAt_log hne).comp h1)
  have key : ∀ d : ℝ, c ≤ d → d < 1 → (∫ x in c..d, f x ^ 2) ≤ 2 * τ * f c ^ 2 + 2 * D * τ := by
    intro d hcd hd1
    set g : ℝ → ℝ := fun x => 2 * f c ^ 2 + 2 * D * (Real.log τ - Real.log (1 - x)) with hgdef
    have hlc : ContinuousOn (fun x : ℝ => Real.log τ - Real.log (1 - x)) (uIcc c d) := by
      rw [uIcc_of_le hcd]
      intro x hx
      exact (hlogcont x (lt_of_le_of_lt hx.2 hd1)).continuousWithinAt
    have hgc : ContinuousOn g (uIcc c d) := by
      rw [uIcc_of_le hcd]
      intro x hx
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 hd1
      exact (continuousAt_const.add (continuousAt_const.mul (hlogcont x hx1))).continuousWithinAt
    have hmono : (∫ x in c..d, f x ^ 2) ≤ ∫ x in c..d, g x := by
      refine intervalIntegral.integral_mono_on hcd
        (hisq c d ⟨by linarith, hc1.le⟩ ⟨by linarith, hd1.le⟩) hgc.intervalIntegrable
        (fun x hx => ?_)
      have hcx : c ≤ x := hx.1
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 hd1
      have hxIoo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
      have hA := hD c x hcIoo hxIoo hcx
      have hA0 : 0 ≤ ∫ t in c..x, (1 - t ^ 2) * f1 t ^ 2 := by
        refine intervalIntegral.integral_nonneg hcx (fun t ht => ?_)
        have h1 : -1 < t := by linarith [ht.1]
        have h2 : t < 1 := lt_of_le_of_lt ht.2 hx1
        have h3 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
        positivity
      have hB := spheroidal_integral_inv_one_sub_sq_le hc0 hcx hx1
      rw [hcτ] at hB
      have hB0 := spheroidal_integral_inv_one_sub_sq_nonneg hcIoo.1 hcx hx1
      have hsq := spheroidal_sq_sub_le f f1 hd hf1c hcIoo hxIoo hcx
      have hprod : (f x - f c) ^ 2 ≤ D * (Real.log τ - Real.log (1 - x)) :=
        le_trans hsq (mul_le_mul hA hB hB0 hD0)
      have hexp : f x ^ 2 ≤ 2 * f c ^ 2 + 2 * (f x - f c) ^ 2 := by
        nlinarith [sq_nonneg (f x - 2 * f c)]
      simp only [hgdef]
      linarith
    have hL : (∫ x in c..d, (Real.log τ - Real.log (1 - x))) = H d - H c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hHderiv x (by rw [uIcc_of_le hcd] at hx; exact lt_of_le_of_lt hx.2 hd1))
        hlc.intervalIntegrable
    have hval : (∫ x in c..d, g x) = (d - c) * (2 * f c ^ 2) + 2 * D * (H d - H c) := by
      rw [hgdef]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hlc.intervalIntegrable.const_mul (2 * D)), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, hL]
      simp [smul_eq_mul]
    have hHc : H c = -τ := by
      simp only [hHdef, hcτ]
      ring
    have hHd : H d ≤ 0 := by
      have h1 : (0 : ℝ) < 1 - d := by linarith
      have h2 : (1 : ℝ) - d ≤ τ := by linarith [hcd, hcτ]
      have h3 : Real.log (1 - d) ≤ Real.log τ := Real.log_le_log h1 h2
      have h4 : Real.log (1 - d) - Real.log τ - 1 ≤ 0 := by linarith
      simp only [hHdef]
      exact mul_nonpos_of_nonneg_of_nonpos h1.le h4
    have hdc : d - c ≤ τ := by linarith [hcτ]
    have hfin : (∫ x in c..d, g x) ≤ 2 * τ * f c ^ 2 + 2 * D * τ := by
      rw [hval, hHc]
      nlinarith [sq_nonneg (f c), hD0, hHd]
    linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set d := max c (1 - ε / (M + 1)) with hddef
  have hcd : c ≤ d := le_max_left _ _
  have hd1 : d < 1 := by
    refine max_lt hc1 ?_
    have : 0 < ε / (M + 1) := by positivity
    linarith
  have hsplit : (∫ x in c..(1 : ℝ), f x ^ 2)
      = (∫ x in c..d, f x ^ 2) + (∫ x in d..(1 : ℝ), f x ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hisq c d ⟨by linarith, hc1.le⟩ ⟨by linarith, hd1.le⟩)
      (hisq d 1 ⟨by linarith, hd1.le⟩ ⟨by norm_num, le_refl 1⟩)).symm
  have htail : (∫ x in d..(1 : ℝ), f x ^ 2) ≤ (1 - d) * M := by
    have h := intervalIntegral.integral_mono_on hd1.le
      (hisq d 1 ⟨by linarith, hd1.le⟩ ⟨by norm_num, le_refl 1⟩)
      (intervalIntegrable_const (c := M)) (fun x hx => hM x ⟨by linarith [hx.1], hx.2⟩)
    simpa [smul_eq_mul] using h
  have hlast : (1 - d) * M ≤ ε := by
    have h1 : 1 - d ≤ ε / (M + 1) := by
      have h := le_max_right c (1 - ε / (M + 1))
      linarith
    have h2 : (0 : ℝ) < M + 1 := by linarith
    calc (1 - d) * M ≤ (ε / (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ h2]
          nlinarith
  linarith [key d hcd hd1]

