/-! ## The uniform package attached to an eigenvalue below a fixed bound -/

/-- All the uniform information attached to a regular even eigenvalue `Λ ≤ b`: a normalised
eigenfunction together with two-sided bounds for its mass, the uniform tail bound and the
uniform a priori bound on compact subintervals. -/
theorem spheroidal_package (G b K Θ τ1 c1 L1 P Λ : ℝ)
    (hΛ : RegularEvenSpheroidalEigenvalue G Λ) (hΛb : Λ ≤ b)
    (hKb : b + |G| ≤ K) (hK0 : 0 ≤ K)
    (hΘb : ∀ x : ℝ, -max G 0 ≤ x → x ≤ b → |x + G| ≤ Θ)
    (hτ10 : 0 < τ1) (hτ1h : τ1 ≤ 1 / 2) (hc1def : c1 = 1 - τ1)
    (hτ1s : τ1 * (4 + 4 * K * (-Real.log τ1) + 2 * K) ≤ 1 / 4)
    (hL1 : (2 + |G| + Θ) / (1 - c1 ^ 2) + 1 ≤ L1) (hPdef : P = Real.exp (L1 * c1)) :
    ∃ f f1 f2 : ℝ → ℝ,
      (∀ x : ℝ, f (-x) = f x) ∧ ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1,
        -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0) ∧
      f 0 = 1 ∧ f1 0 = 0 ∧
      (min c1 (1 / (2 * P))) / 2 ≤ (∫ x in (-1 : ℝ)..1, f x ^ 2) ∧
      (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
        (∫ x in (1 - τ)..1, f x ^ 2)
          ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2)) ∧
      (∀ c L : ℝ, 0 < c → c < 1 → (2 + |G| + Θ) / (1 - c ^ 2) + 1 ≤ L →
        ∀ x ∈ Icc (0 : ℝ) c, max |f x| |f1 x| ≤ Real.exp (L * c)) := by
  obtain ⟨f, f1, f2, hf0, hf10, hev, hcf, hfd, hode, hlim1, hlim2⟩ :=
    spheroidal_normalized_witness hΛ
  have hlow := spheroidal_eigenvalue_lower_bound hΛ
  have hGabs : max G 0 ≤ |G| := max_le (le_abs_self G) (abs_nonneg G)
  have hK0' : 0 ≤ Λ + |G| := by linarith
  have hKle : Λ + |G| ≤ K := by linarith
  have hΘΛ : |Λ + G| ≤ Θ := hΘb Λ hlow hΛb
  have hc10 : 0 < c1 := by rw [hc1def]; linarith
  have hc11 : c1 < 1 := by rw [hc1def]; linarith
  have hc1sq : 0 < 1 - c1 ^ 2 := by nlinarith
  have hL1nonneg : 0 ≤ L1 := by
    have h1 : (0 : ℝ) ≤ (2 + |G| + Θ) / (1 - c1 ^ 2) := by
      have hΘ0 : 0 ≤ Θ := le_trans (abs_nonneg _) hΘΛ
      positivity
    linarith
  have hP0 : 0 < P := by rw [hPdef]; exact Real.exp_pos _
  -- the a priori bound, for any admissible `c` and `L`
  have hapriori : ∀ c L : ℝ, 0 < c → c < 1 → (2 + |G| + Θ) / (1 - c ^ 2) + 1 ≤ L →
      ∀ x ∈ Icc (0 : ℝ) c, max |f x| |f1 x| ≤ Real.exp (L * c) := by
    intro c L hc0 hc1 hLc x hx
    have hcsq : 0 < 1 - c ^ 2 := by nlinarith
    have hLmono : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L := by
      have h1 : (2 + |G| + |Λ + G|) / (1 - c ^ 2) ≤ (2 + |G| + Θ) / (1 - c ^ 2) := by
        gcongr
      linarith
    have h := spheroidal_apriori_bound G Λ c L hc0 hc1 hLmono f f1 f2 hfd hode hx
    have hLnn : 0 ≤ L := by
      have h1 : (0 : ℝ) ≤ (2 + |G| + |Λ + G|) / (1 - c ^ 2) := by positivity
      linarith
    have hinit : max |f 0| |f1 0| = 1 := by
      rw [hf0, hf10]
      simp
    rw [hinit, one_mul] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    nlinarith [hx.1, hx.2]
  -- the uniform tail bound
  have htailall : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      (∫ x in (1 - τ)..1, f x ^ 2)
        ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2) := by
    intro τ hτ0 hτh
    exact spheroidal_tail_uniform G Λ K τ f f1 f2 hK0' hKle hτ0 hτh hev hcf hfd hode hlim1 hlim2
  have hS0 : 0 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hPbound : ∀ x ∈ Icc (0 : ℝ) c1, |f x| ≤ P ∧ |f1 x| ≤ P := by
    intro x hx
    have h := hapriori c1 L1 hc10 hc11 hL1 x hx
    rw [← hPdef] at h
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  have hupper : (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 := by
    refine spheroidal_mass_upper f c1 P hc10 hc11.le hev hcf (fun x hx => (hPbound x hx).1) ?_
    have h := htailall τ1 hτ10 hτ1h
    rw [← hc1def] at h
    have h2 : τ1 * (4 + 4 * K * (-Real.log τ1) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2)
        ≤ (1 / 4) * ∫ x in (-1 : ℝ)..1, f x ^ 2 := mul_le_mul_of_nonneg_right hτ1s hS0
    linarith
  have hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1) :=
    fun x hx => ((hfd x hx).2.continuousAt).continuousWithinAt
  have hlower : (min c1 (1 / (2 * P))) / 2 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    spheroidal_mass_lower f f1 c1 P hc10 hc11 hP0 hev hcf hf0 (fun x hx => (hfd x hx).1) hf1c
      (fun x hx => (hPbound x hx).2)
  exact ⟨f, f1, f2, hev, hcf, hfd, hode, hlim1, hlim2, hf0, hf10, hlower, hupper, htailall,
    hapriori⟩

