/-! ## Uniform energy and tail estimates for eigenfunctions

The estimates in this section are uniform over the family of all regular even eigenfunctions
with eigenvalue below a fixed bound; they are the quantitative input for discreteness. -/

/-- **Dirichlet energy bound.** For a regular even eigenfunction, the weighted Dirichlet energy
`∫ (1 - x²) f'(x)²` over any interior interval is at most `(Λ + |G|) ∫_{-1}^{1} f²`. -/
theorem spheroidal_dirichlet_energy_bound (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hK : 0 ≤ Λ + |G|)
    (hc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hlim1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hlim2 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) (hab : a ≤ b) :
    (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2) ≤ (Λ + |G|) * ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
  have hsubu : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → uIcc u v ⊆ Ioo (-1 : ℝ) 1 :=
    fun u v hu hv => (Set.ordConnected_Ioo).uIcc_subset hu hv
  have hsubi : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → Icc u v ⊆ Ioo (-1 : ℝ) 1 :=
    fun u v hu hv => (Set.ordConnected_Ioo).out hu hv
  have hint1 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)
        volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint2 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint3 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (1 - x ^ 2) * f1 x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint4 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + |G|) * f x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hintsq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      (((hc.mul hc).mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).congr
        (fun x _ => by ring))
  set E : ℝ → ℝ := fun t => -((1 - t ^ 2) * (f1 t * f t)) with hE
  have hFTC : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      (∫ x in u..v, ((Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)) = E v - E u := by
    intro u v hu hv
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) (hint1 u v hu hv)
    exact spheroidal_energy_identity G Λ f f1 f2 hd hode (hsubu u v hu hv hx)
  have hEright : Tendsto E (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
    have h := (hlim1.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  have hEleft : Tendsto E (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (f (-1))) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
    have h := (hlim2.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  -- the key estimate on a slightly larger interval
  have hkey : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ a → b ≤ v →
      (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2)
        ≤ (Λ + |G|) * (∫ x in (-1 : ℝ)..1, f x ^ 2) + (|E v| + |E u|) := by
    intro u v hu hv hua hbv
    have huv : u ≤ v := le_trans hua (le_trans hab hbv)
    have henlarge : (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2)
        ≤ ∫ x in u..v, (1 - x ^ 2) * f1 x ^ 2 := by
      refine intervalIntegral.integral_mono_interval hua hab hbv ?_ (hint3 u v hu hv)
      have hpos : ∀ x ∈ Ioc u v, 0 ≤ (1 - x ^ 2) * f1 x ^ 2 := by
        intro x hx
        have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi u v hu hv ⟨hx.1.le, hx.2⟩
        have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        positivity
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hpos x hx
    have hsplit : (∫ x in u..v, (1 - x ^ 2) * f1 x ^ 2)
        = (∫ x in u..v, (Λ + G * (1 - x ^ 2)) * f x ^ 2) - (E v - E u) := by
      rw [← hFTC u v hu hv, intervalIntegral.integral_sub (hint2 u v hu hv) (hint3 u v hu hv)]
      ring
    have hmono1 : (∫ x in u..v, (Λ + G * (1 - x ^ 2)) * f x ^ 2)
        ≤ ∫ x in u..v, (Λ + |G|) * f x ^ 2 := by
      refine intervalIntegral.integral_mono_on huv (hint2 u v hu hv) (hint4 u v hu hv)
        (fun x hx => ?_)
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi u v hu hv hx
      have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      have h2 : G * (1 - x ^ 2) ≤ |G| := by
        nlinarith [le_abs_self G, neg_abs_le G, abs_nonneg G, hx'.1, hx'.2]
      nlinarith [sq_nonneg (f x)]
    have hconst : (∫ x in u..v, (Λ + |G|) * f x ^ 2) = (Λ + |G|) * ∫ x in u..v, f x ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have hmono2 : (∫ x in u..v, f x ^ 2) ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
      refine intervalIntegral.integral_mono_interval (by linarith [hu.1]) huv
        (by linarith [hv.2]) (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
        (hintsq (-1) 1 (by norm_num) (by norm_num))
    have hfin : (Λ + |G|) * (∫ x in u..v, f x ^ 2) ≤ (Λ + |G|) * ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
      mul_le_mul_of_nonneg_left hmono2 hK
    have h1 : E v - E u ≥ -(|E v| + |E u|) := by
      have := abs_le.mp (le_refl |E v|)
      have h2 := neg_abs_le (E v)
      have h3 := le_abs_self (E u)
      linarith
    linarith [hconst ▸ hfin]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨v, hvmem, hvE⟩ : ∃ v ∈ Ioo b 1, |E v| < ε / 2 := by
    have h1 : Ioo b 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hb.2
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[<] (1 : ℝ) := by
      have hball := hEright (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨v, hv⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨v, hv.1, hv.2⟩
  obtain ⟨u, humem, huE⟩ : ∃ u ∈ Ioo (-1 : ℝ) a, |E u| < ε / 2 := by
    have h1 : Ioo (-1 : ℝ) a ∈ 𝓝[>] (-1 : ℝ) := Ioo_mem_nhdsGT ha.1
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[>] (-1 : ℝ) := by
      have hball := hEleft (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨u, hu⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨u, hu.1, hu.2⟩
  have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨humem.1, by linarith [humem.2, ha.2]⟩
  have hv' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hvmem.1, hb.1], hvmem.2⟩
  have := hkey u v hu' hv' humem.2.le hvmem.1.le
  linarith

