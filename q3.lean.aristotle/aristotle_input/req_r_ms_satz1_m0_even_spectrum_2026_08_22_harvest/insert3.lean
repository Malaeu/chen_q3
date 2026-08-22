/-! ## Grönwall estimates: a priori bounds and dependence on the eigenvalue parameter -/

/-- **A priori bound.** On `[0,c]` with `c < 1`, a solution of the spheroidal system grows at
most exponentially, with rate the Lipschitz constant of the field. -/
theorem spheroidal_apriori_bound (G Λ c L : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hL : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L)
    (f f1 f2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    {x : ℝ} (hx : x ∈ Icc 0 c) :
    max |f x| |f1 x| ≤ max |f 0| |f1 0| * Real.exp (L * x) := by
  have hcsq : 0 < 1 - c ^ 2 := by nlinarith
  set L0 := (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 with hL0def
  have hL00 : 0 ≤ L0 := by positivity
  have hLnn : 0 ≤ L := le_trans hL00 hL
  set v : ℝ → ℝ × ℝ → ℝ × ℝ :=
    fun t p => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)) with hv
  set F : ℝ → ℝ × ℝ := fun t => (f t, f1 t) with hF
  have hsub : Icc (0 : ℝ) c ⊆ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hc1⟩
  have hlip : ∀ t ∈ Ico (0 : ℝ) c, LipschitzOnWith ⟨L, hLnn⟩ (v t) univ := by
    intro t ht
    have h := spheroidal_field_lipschitzOnWith G Λ c hc1 hcsq L0 hL0def hL00 t
      ⟨by linarith [ht.1], ht.2⟩
    exact h.weaken (by exact_mod_cast hL)
  have hne : ∀ t ∈ Icc (0 : ℝ) c, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hFderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt F (v t (F t)) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hfd t (hsub htc)
    have hde : HasDerivAt F (f1 t, f2 t) t := hd.1.prodMk hd.2
    have heq : v t (F t) = (f1 t, f2 t) := by
      have hodd := hfe t (hsub htc)
      have hnz := hne t htc
      simp only [hv, hF, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      field_simp
      linarith
    rw [heq]
    exact hde.hasDerivWithinAt
  have hFcont : ContinuousOn F (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hfd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hzeroderiv : ∀ t ∈ Ico (0 : ℝ) c,
      HasDerivWithinAt (fun _ : ℝ => ((0 : ℝ), (0 : ℝ))) (v t ((0 : ℝ), (0 : ℝ))) (Ici t) t := by
    intro t ht
    have : v t ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [hv]
    rw [this]
    exact (hasDerivAt_const t ((0 : ℝ), (0 : ℝ))).hasDerivWithinAt
  have hinit : dist (F 0) ((0 : ℝ), (0 : ℝ)) ≤ max |f 0| |f1 0| := by
    simp [hF, Prod.dist_eq, Real.dist_eq]
  have key := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := ⟨L, hLnn⟩) hlip hFcont hFderiv (fun _ _ => mem_univ _) continuousOn_const
    hzeroderiv (fun _ _ => mem_univ _) hinit x hx
  have hd : dist (F x) ((0 : ℝ), (0 : ℝ)) = max |f x| |f1 x| := by
    simp [hF, Prod.dist_eq, Real.dist_eq]
  rw [hd] at key
  simpa using key

/-- **Dependence on the parameter.** Two solutions with the same initial data at `0` but
eigenvalue parameters `Λ` and `Λ'` stay close on `[0,c]`, with an error proportional to
`|Λ - Λ'|`. -/
theorem spheroidal_param_dependence (G Λ Λ' c L P : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hL : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L) (hL1 : 1 ≤ L) (hP0 : 0 ≤ P)
    (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Λ' + G) * g x)
    (hgP : ∀ t ∈ Icc (0 : ℝ) c, |g t| ≤ P)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0)
    {x : ℝ} (hx : x ∈ Icc 0 c) :
    |f x - g x| ≤ |Λ - Λ'| * P / (1 - c ^ 2) * Real.exp (L * c) := by
  have hcsq : 0 < 1 - c ^ 2 := by nlinarith
  set L0 := (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 with hL0def
  have hL00 : 0 ≤ L0 := by positivity
  have hLnn : 0 ≤ L := by linarith
  set ε := |Λ - Λ'| * P / (1 - c ^ 2) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  set v : ℝ → ℝ × ℝ → ℝ × ℝ :=
    fun t p => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)) with hv
  set F : ℝ → ℝ × ℝ := fun t => (f t, f1 t) with hF
  set Gg : ℝ → ℝ × ℝ := fun t => (g t, g1 t) with hGg
  have hsub : Icc (0 : ℝ) c ⊆ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hc1⟩
  have hlip : ∀ t ∈ Ico (0 : ℝ) c, LipschitzOnWith ⟨L, hLnn⟩ (v t) univ := by
    intro t ht
    have h := spheroidal_field_lipschitzOnWith G Λ c hc1 hcsq L0 hL0def hL00 t
      ⟨by linarith [ht.1], ht.2⟩
    exact h.weaken (by exact_mod_cast hL)
  have hne : ∀ t ∈ Icc (0 : ℝ) c, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hFderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt F (f1 t, f2 t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hfd t (hsub htc)
    exact (hd.1.prodMk hd.2).hasDerivWithinAt
  have hGderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt Gg (g1 t, g2 t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hgd t (hsub htc)
    exact (hd.1.prodMk hd.2).hasDerivWithinAt
  have hFcont : ContinuousOn F (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hfd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hGcont : ContinuousOn Gg (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hgd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hFbound : ∀ t ∈ Ico (0 : ℝ) c, dist ((f1 t, f2 t) : ℝ × ℝ) (v t (F t)) ≤ 0 := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have heq : v t (F t) = (f1 t, f2 t) := by
      have hodd := hfe t (hsub htc)
      have hnz := hne t htc
      simp only [hv, hF, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      field_simp
      linarith
    rw [heq]
    simp
  have hGbound : ∀ t ∈ Ico (0 : ℝ) c, dist ((g1 t, g2 t) : ℝ × ℝ) (v t (Gg t)) ≤ ε := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hnz := hne t htc
    have htsq : 1 - c ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have htpos : (0 : ℝ) < 1 - t ^ 2 := by linarith
    have hodd := hge t (hsub htc)
    have hsecond : (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2) - g2 t
        = (Λ' - Λ) * g t / (1 - t ^ 2) := by
      field_simp
      linarith
    rw [Prod.dist_eq]
    simp only [hv, hGg]
    refine max_le (by simp) ?_
    rw [Real.dist_eq]
    have : |g2 t - (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2)|
        = |Λ' - Λ| * |g t| / (1 - t ^ 2) := by
      rw [show g2 t - (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2)
          = -((Λ' - Λ) * g t / (1 - t ^ 2)) by linarith [hsecond]]
      rw [abs_neg, abs_div, abs_mul, abs_of_pos htpos]
    rw [this, hεdef]
    have habs : |Λ' - Λ| = |Λ - Λ'| := abs_sub_comm _ _
    rw [habs]
    have h1 : |Λ - Λ'| * |g t| ≤ |Λ - Λ'| * P :=
      mul_le_mul_of_nonneg_left (hgP t htc) (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ |Λ - Λ'| * P := by positivity
    calc |Λ - Λ'| * |g t| / (1 - t ^ 2) ≤ |Λ - Λ'| * P / (1 - t ^ 2) := by
          gcongr
          exact hgP t htc
      _ ≤ |Λ - Λ'| * P / (1 - c ^ 2) := by
          gcongr
  have hinit : dist (F 0) (Gg 0) ≤ 0 := by
    simp [hF, hGg, Prod.dist_eq, Real.dist_eq, h0, h1]
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := ⟨L, hLnn⟩) hlip hFcont hFderiv hFbound (fun _ _ => mem_univ _) hGcont hGderiv
    hGbound (fun _ _ => mem_univ _) hinit x hx
  have hKne : (L : ℝ) ≠ 0 := by linarith
  have hgb : gronwallBound 0 L (0 + ε) (x - 0) ≤ ε * Real.exp (L * c) := by
    rw [gronwallBound_of_K_ne_0 hKne]
    simp only [zero_mul, zero_add, sub_zero]
    have h1 : Real.exp (L * x) ≤ Real.exp (L * c) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.1, hx.2]
    have h2 : (0 : ℝ) < Real.exp (L * x) := Real.exp_pos _
    have h3 : ε / L ≤ ε := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith [Real.exp_pos (L * c)]
  have hfin : |f x - g x| ≤ ε * Real.exp (L * c) := by
    have hle : |f x - g x| ≤ dist (F x) (Gg x) := by
      rw [Prod.dist_eq]
      exact le_trans (le_of_eq (Real.dist_eq (f x) (g x)).symm) (le_max_left _ _)
    have hcoe : ((⟨L, hLnn⟩ : NNReal) : ℝ) = L := rfl
    rw [hcoe] at key
    linarith [le_trans hle key, hgb]
  exact hfin

