/-! ## A uniform endpoint tail bound for eigenfunctions -/

/-- Reflection formula for the integral of the square of an even function. -/
theorem integral_sq_even_reflect (f : ℝ → ℝ) (hev : ∀ x : ℝ, f (-x) = f x) (a b : ℝ) :
    (∫ x in a..b, f x ^ 2) = ∫ x in (-b)..(-a), f x ^ 2 := by
  rw [← intervalIntegral.integral_comp_neg (fun x => f x ^ 2)]
  simp [hev]

/-- For an even function, the mass on `[-1,1]` is twice the mass on `[0,1]`. -/
theorem integral_sq_even_half (f : ℝ → ℝ) (hev : ∀ x : ℝ, f (-x) = f x)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    (∫ x in (-1 : ℝ)..1, f x ^ 2) = 2 * ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hsplit : (∫ x in (-1 : ℝ)..0, f x ^ 2) + (∫ x in (0 : ℝ)..1, f x ^ 2)
      = ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hisq (-1) 0 (by norm_num) (by norm_num)) (hisq 0 1 (by norm_num) (by norm_num))
  have hrefl : (∫ x in (0 : ℝ)..1, f x ^ 2) = ∫ x in (-1 : ℝ)..(0 : ℝ), f x ^ 2 := by
    have h := integral_sq_even_reflect f hev 0 1
    simpa using h
  linarith

/-- A pointwise value of `f` is controlled by the mass of `f²` near the origin together with the
Dirichlet energy. -/
theorem spheroidal_val_sq_le (f : ℝ → ℝ) (D W : ℝ) (hD0 : 0 ≤ D) (hW0 : 0 ≤ W)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1)) (x : ℝ)
    (hbd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), (f x - f y) ^ 2 ≤ D * W) :
    f x ^ 2 ≤ 4 * (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) + 2 * D * W := by
  have hisq : IntervalIntegrable (fun y => f y ^ 2) volume 0 (1 / 2) := by
    refine ContinuousOn.intervalIntegrable ((hcf.mono ?_).pow 2)
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono : (∫ _y in (0 : ℝ)..(1 / 2), f x ^ 2)
      ≤ ∫ y in (0 : ℝ)..(1 / 2), (2 * f y ^ 2 + 2 * (D * W)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      ((hisq.const_mul 2).add intervalIntegrable_const) (fun y hy => ?_)
    have h1 := hbd y hy
    nlinarith [sq_nonneg (f x - 2 * f y)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hisq.const_mul 2)
    intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  linarith

/-- **Uniform tail bound for eigenfunctions.** With `K` an upper bound for `Λ + |G|`, the mass of
`f²` on the endpoint layer `[1-τ,1]` is at most `τ (4 + 4K log(1/τ) + 2K)` times the total mass.
The right-hand side tends to `0` with `τ`, uniformly over all eigenfunctions with `Λ + |G| ≤ K`. -/
theorem spheroidal_tail_uniform (G Λ K τ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hK0 : 0 ≤ Λ + |G|) (hKle : Λ + |G| ≤ K)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hev : ∀ x : ℝ, f (-x) = f x)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hlim1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hlim2 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    (∫ x in (1 - τ)..1, f x ^ 2)
      ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2) := by
  have hK0' : 0 ≤ K := le_trans hK0 hKle
  have hWτ : 0 ≤ -Real.log τ := by
    have h1 : Real.log τ ≤ Real.log (1 / 2) := Real.log_le_log hτ0 hτ1
    have h2 : Real.log (1 / 2) < 0 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
      simp [Real.log_pos]
    linarith
  set S := ∫ x in (-1 : ℝ)..1, f x ^ 2 with hSdef
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  set D := K * S with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1) :=
    fun x hx => ((hfd x hx).2.continuousAt).continuousWithinAt
  have hfd1 : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x := fun x hx => (hfd x hx).1
  have hDb : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ v →
      (∫ t in u..v, (1 - t ^ 2) * f1 t ^ 2) ≤ D := by
    intro u v hu hv huv
    have h := spheroidal_dirichlet_energy_bound G Λ f f1 f2 hK0 hcf hfd hode hlim1 hlim2 hu hv huv
    have h2 : (Λ + |G|) * S ≤ K * S := mul_le_mul_of_nonneg_right hKle hS0
    rw [hDdef]
    linarith
  -- the value of `f` at the inner edge of the layer
  have hc1 : (1 : ℝ) - τ < 1 := by linarith
  have hcIoo : (1 : ℝ) - τ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hc1⟩
  have hval : f (1 - τ) ^ 2 ≤ 4 * (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) + 2 * D * (-Real.log τ) := by
    refine spheroidal_val_sq_le f D (-Real.log τ) hD0 hWτ hcf (1 - τ) (fun y hy => ?_)
    have hy0 : 0 ≤ y := hy.1
    have hyc : y ≤ 1 - τ := by linarith [hy.2]
    have hyIoo : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hA := hDb y (1 - τ) hyIoo hcIoo hyc
    have hA0 : 0 ≤ ∫ t in y..(1 - τ), (1 - t ^ 2) * f1 t ^ 2 := by
      refine intervalIntegral.integral_nonneg hyc (fun t ht => ?_)
      have h1 : -1 < t := by linarith [ht.1]
      have h2 : t < 1 := by linarith [ht.2]
      have h3 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
      positivity
    have hB := spheroidal_integral_inv_one_sub_sq_le hy0 hyc hc1
    have hB0 := spheroidal_integral_inv_one_sub_sq_nonneg hyIoo.1 hyc hc1
    have hBle : Real.log (1 - y) - Real.log (1 - (1 - τ)) ≤ -Real.log τ := by
      have h1 : Real.log (1 - y) ≤ 0 := by
        refine Real.log_nonpos (by linarith) (by linarith)
      have h2 : (1 : ℝ) - (1 - τ) = τ := by ring
      rw [h2]
      linarith
    have hsq := spheroidal_sq_sub_le f f1 hfd1 hf1c hyIoo hcIoo hyc
    calc (f (1 - τ) - f y) ^ 2 ≤ (f (1 - τ) - f y) ^ 2 := le_refl _
      _ = (f (1 - τ) - f y) ^ 2 := rfl
      _ ≤ D * (-Real.log τ) := by
          have hstep : (f (1 - τ) - f y) ^ 2 ≤ D * (-Real.log τ) := by
            have hle := le_trans hsq (mul_le_mul hA (le_trans hB hBle) hB0 hD0)
            have hswap : (f (1 - τ) - f y) ^ 2 = (f y - f (1 - τ)) ^ 2 := by ring
            linarith [hle]
          exact hstep
  -- the mass on `[0,1/2]` is at most half the total mass
  have hhalf : (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) ≤ S / 2 := by
    have h1 : (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) ≤ ∫ y in (0 : ℝ)..1, f y ^ 2 := by
      refine intervalIntegral.integral_mono_interval (le_refl 0) (by norm_num) (by norm_num)
        (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
        (hisq 0 1 (by norm_num) (by norm_num))
    have h2 := integral_sq_even_half f hev hcf
    rw [← hSdef] at h2
    linarith
  have htail := spheroidal_tail_bound f f1 D τ hτ0 hτ1 hcf hfd1 hf1c hD0 hDb
  have hfin : 2 * τ * f (1 - τ) ^ 2 + 2 * D * τ
      ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * S := by
    have h1 : f (1 - τ) ^ 2 ≤ 2 * S + 2 * D * (-Real.log τ) := by linarith
    have h2 : 2 * τ * f (1 - τ) ^ 2 ≤ 2 * τ * (2 * S + 2 * D * (-Real.log τ)) := by
      apply mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : D = K * S := hDdef
    nlinarith [hτ0.le, hS0, hK0', hWτ]
  linarith

