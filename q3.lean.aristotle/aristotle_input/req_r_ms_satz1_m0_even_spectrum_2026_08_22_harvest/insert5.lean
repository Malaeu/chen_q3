/-! ## Normalised eigenfunctions and elementary separation facts -/

/-- Every regular even eigenvalue has an eigenfunction normalised by `f 0 = 1`, whose derivative
vanishes at the origin. -/
theorem spheroidal_normalized_witness {G Λ : ℝ} (h : RegularEvenSpheroidalEigenvalue G Λ) :
    ∃ f f1 f2 : ℝ → ℝ, f 0 = 1 ∧ f1 0 = 0 ∧ (∀ x : ℝ, f (-x) = f x) ∧
      ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1,
        -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  obtain ⟨f, f1, f2, hne, hev, hc, hd, hode, hlim1, hlim2⟩ := h
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero G Λ f f1 f2 hne hc hev hd hode
  set k := (f 0)⁻¹ with hk
  have hk0 : k ≠ 0 := inv_ne_zero hf0
  refine ⟨fun x => k * f x, fun x => k * f1 x, fun x => k * f2 x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_mul_cancel₀ hf0
  · have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    have := deriv_zero_of_even hev (hd 0 h0).1
    simp [this]
  · intro x; rw [hev x]
  · exact continuousOn_const.mul hc
  · intro x hx
    exact ⟨((hd x hx).1.const_mul k), ((hd x hx).2.const_mul k)⟩
  · intro x hx
    have h := hode x hx
    have : -(1 - x ^ 2) * (k * f2 x) + 2 * x * (k * f1 x) + G * x ^ 2 * (k * f x)
        = k * (-(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x) := by ring
    rw [this, h]
    ring
  · have h := hlim1.const_mul k
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  · have h := hlim2.const_mul k
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring

/-- A set of reals contained in a bounded interval whose points are pairwise `δ`-separated is
finite. -/
theorem finite_of_separated {T : Set ℝ} {a b δ : ℝ} (hδ : 0 < δ) (hT : T ⊆ Icc a b)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y|) : T.Finite := by
  have hinj : Set.InjOn (fun x : ℝ => ⌊x / δ⌋) T := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hsep x hx y hy hne
    have h2 : |x / δ - y / δ| < 1 := by
      have := Int.abs_sub_lt_one_of_floor_eq_floor (α := ℝ) (a := x / δ) (b := y / δ) hxy
      simpa using this
    rw [div_sub_div_same, abs_div, abs_of_pos hδ, div_lt_one hδ] at h2
    linarith
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (Set.finite_Icc ⌊a / δ⌋ ⌊b / δ⌋) ?_
  rintro n ⟨x, hx, rfl⟩
  have hxab := hT hx
  exact ⟨Int.floor_le_floor (by gcongr; exact hxab.1), Int.floor_le_floor (by gcongr; exact hxab.2)⟩

/-- The uniform tail factor `τ (4 + 4K log (1/τ) + 2K)` can be made arbitrarily small. -/
theorem exists_small_tail_factor (K ε : ℝ) (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) ≤ ε := by
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have hlog' : Tendsto (fun x : ℝ => Real.log x * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hlog.congr (fun x => ?_)
    rw [Real.rpow_one]
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun x : ℝ => x * (4 + 4 * K * (-Real.log x) + 2 * K))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (4 + 2 * K) * x + (-(4 * K)) * (Real.log x * x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (hid.const_mul (4 + 2 * K)).add (hlog'.const_mul (-(4 * K)))
      simpa using this
    refine h1.congr (fun x => ?_)
    ring
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x * (4 + 4 * K * (-Real.log x) + 2 * K) < ε := by
    have := hmain (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [this] with x hx
    have : |x * (4 + 4 * K * (-Real.log x) + 2 * K)| < ε := by
      simpa [Real.dist_eq] using hx
    exact lt_of_le_of_lt (le_abs_self _) this
  obtain ⟨τ, hτ⟩ := Filter.nonempty_of_mem (inter_mem (Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2))
    hev)
  exact ⟨τ, hτ.1.1, hτ.1.2, le_of_lt hτ.2⟩

