import Q3.Proofs.RouteB.SpheroidalSourceMain
import Q3.Proofs.RouteB.D0ModeZeroFourSelectedFerrersPhysicalProlate
import Q3.Proofs.RouteB.D0Mode4FerrersCenterValueNonzero

open Set Filter Topology MeasureTheory

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Q3.RouteB

private theorem selectedFerrers_regularEvenSpheroidalEigenvalue
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    RegularEvenSpheroidalEigenvalue (mode4JacobiG mProject) Λ := by
  refine ⟨mode4FerrersSeries S.coefficients,
    mode4FerrersFirstDerivativeSeries S.coefficients,
    mode4FerrersSecondDerivativeSeries S.coefficients,
    ⟨0, by norm_num, S.center_value_ne_zero⟩,
    S.even,
    S.continuousOn_closed,
    ?_,
    S.prolateDifferentialEquation,
    S.zeroFlux_at_endpoints.1,
    S.zeroFlux_at_endpoints.2⟩
  intro x hx
  exact ⟨S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hx,
    S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx⟩

/-- A regular even source eigenvalue has strict shifted energy above zero
when the prolate parameter is positive. -/
theorem spheroidal_eigenvalue_strict_lower_bound
    {G Λ : ℝ} (hG : 0 < G)
    (h : RegularEvenSpheroidalEigenvalue G Λ) :
    -G < Λ := by
  have hlow := spheroidal_eigenvalue_lower_bound h
  have hlow' : -G ≤ Λ := by
    simpa [max_eq_left hG.le] using hlow
  by_contra hnot
  have hupper : Λ ≤ -G := le_of_not_gt hnot
  have hΛeq : Λ = -G := le_antisymm hupper hlow'
  obtain ⟨f, f1, f2, hne, hev, hc, hd, hode, hlim1, hlim2⟩ := h
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero G Λ f f1 f2 hne hc hev hd hode
  let E : ℝ → ℝ := fun t => -((1 - t ^ 2) * (f1 t * f t))
  have hEcont : ContinuousOn E (Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hfc : ContinuousAt f x := (hd x hx).1.continuousAt
    have hf1c : ContinuousAt f1 x := (hd x hx).2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hEanti : AntitoneOn E (Ioo (-1 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _) hEcont ?_ ?_
    · rw [interior_Ioo]
      intro x hx
      exact (spheroidal_energy_identity G Λ f f1 f2 hd hode hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      have hder := (spheroidal_energy_identity G Λ f f1 f2 hd hode hx).deriv
      have hcoef : Λ + G * (1 - x ^ 2) = -(G * x ^ 2) := by rw [hΛeq]; ring
      rw [hcoef] at hder
      have hp : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have hGx : 0 ≤ G * x ^ 2 := mul_nonneg hG.le (sq_nonneg x)
      rw [hder]
      nlinarith [mul_nonneg hGx (sq_nonneg (f x)),
        mul_nonneg hp (sq_nonneg (f1 x))]
  have hEright : Tendsto E (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
    have h := (hlim1.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [E]
    ring
  have hEleft : Tendsto E (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (f (-1))) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
    have h := (hlim2.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [E]
    ring
  have hEz : ∀ x ∈ Ioo (-1 : ℝ) 1, E x = 0 := by
    intro x hx
    have hleftNear : Ioo (-1 : ℝ) x ∈ 𝓝[>] (-1 : ℝ) := by
      rw [show Ioo (-1 : ℝ) x = Ioi (-1) ∩ Iio x by
        ext y
        simp [and_comm]]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.1)
    have hleftOrder : ∀ᶠ t in 𝓝[>] (-1 : ℝ), E x ≤ E t := by
      filter_upwards [hleftNear] with t ht
      have htMem : t ∈ Ioo (-1 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hx.2⟩
      exact hEanti htMem hx ht.2.le
    have hxle : E x ≤ 0 := by
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hEleft hleftOrder
    have hrightNear : Ioo x 1 ∈ 𝓝[<] (1 : ℝ) := by
      rw [show Ioo x (1 : ℝ) = Iio 1 ∩ Ioi x by
        ext y
        simp [and_comm]]
      exact inter_mem_nhdsWithin _ (Ioi_mem_nhds hx.2)
    have hrightOrder : ∀ᶠ t in 𝓝[<] (1 : ℝ), E t ≤ E x := by
      filter_upwards [hrightNear] with t ht
      have htMem : t ∈ Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 ht.1, ht.2⟩
      exact hEanti hx htMem ht.1.le
    have hxge : 0 ≤ E x := by
      exact le_of_tendsto_of_tendsto hEright tendsto_const_nhds hrightOrder
    exact le_antisymm hxle hxge
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hfc0 : ContinuousAt f 0 := (hd 0 hzero).1.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hfc0.eventually_ne hf0)
  let x : ℝ := min (δ / 2) (1 / 2)
  have hxpos : 0 < x := by
    dsimp [x]
    exact lt_min (by linarith) (by norm_num)
  have hxlt : x < 1 := by
    dsimp [x]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hxmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hxlt⟩
  have hfx : f x ≠ 0 := by
    apply hδ
    rw [Real.dist_eq, sub_zero]
    dsimp [x]
    have hxa : |min (δ / 2) (1 / 2)| < min (δ / 2) (1 / 2) + (δ / 2) := by
      have hmin0 : 0 ≤ min (δ / 2) (1 / 2) := by positivity
      rw [abs_of_nonneg hmin0]
      linarith
    have hxm : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
    linarith
  have hEzeroNear : E =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxmem] with y hy
    exact hEz y hy
  have hEderiv0 : HasDerivAt E 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hEzeroNear
  have hEnergy := (spheroidal_energy_identity G Λ f f1 f2 hd hode hxmem).deriv
  have hEnergy' :
      deriv E x =
        (Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2 := by
    change deriv (fun t => -((1 - t ^ 2) * (f1 t * f t))) x = _
    exact hEnergy
  have hEq :
      0 = (Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2 := by
    rw [← hEderiv0.deriv]
    exact hEnergy'
  have hcoef : Λ + G * (1 - x ^ 2) = -(G * x ^ 2) := by rw [hΛeq]; ring
  rw [hcoef] at hEq
  have hGx : 0 < G * x ^ 2 := mul_pos hG (sq_pos_of_ne_zero (ne_of_gt hxpos))
  have hfx2 : 0 < f x ^ 2 := sq_pos_of_ne_zero hfx
  have hp : 0 ≤ 1 - x ^ 2 := by nlinarith [hxmem.1, hxmem.2]
  nlinarith [mul_pos hGx hfx2, mul_nonneg hp (sq_nonneg (f1 x))]

/-- Both actually selected Ferrers modes (degrees zero and four) have positive
shifted Green energy `theta = Lambda + G` at every admissible project size. -/
theorem selectedFerrers_modeZero_modeFour_theta_positive
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    0 < mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 +
        mode4JacobiG mProject ∧
      0 < mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 +
        mode4JacobiG mProject := by
  obtain ⟨hS0, hS4, _hOrder, _hCut⟩ :=
    exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions
      mProject K hm hK hsep
  obtain ⟨S0⟩ := hS0
  obtain ⟨S4⟩ := hS4
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hΛ0 := spheroidal_eigenvalue_strict_lower_bound hG
    (selectedFerrers_regularEvenSpheroidalEigenvalue S0)
  have hΛ4 := spheroidal_eigenvalue_strict_lower_bound hG
    (selectedFerrers_regularEvenSpheroidalEigenvalue S4)
  constructor <;> linarith

#print axioms spheroidal_eigenvalue_strict_lower_bound
#print axioms selectedFerrers_regularEvenSpheroidalEigenvalue
#print axioms selectedFerrers_modeZero_modeFour_theta_positive

end Q3.RouteB
