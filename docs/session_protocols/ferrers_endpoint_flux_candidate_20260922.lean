import Mathlib
import Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution
open Set Filter
open scoped Topology
noncomputable section
namespace Q3EndpointFlux

theorem endpoint_flux_bound (F F' : ℝ → ℝ) (a b M x : ℝ)
    (hx : x ∈ Ioo a b)
    (hd : ∀ y ∈ Ioo a b, HasDerivAt F (F' y) y)
    (hM : ∀ y ∈ Ioo a b, ‖F' y‖ ≤ M)
    (hz : Tendsto F (𝓝[<] b) (𝓝 0)) :
    ‖F x‖ ≤ M*(b-x) := by
  have hid : Tendsto (fun y : ℝ => y) (𝓝[<] b) (𝓝 b) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hy : ∀ᶠ y in 𝓝[<] b, y ∈ Ioo a b := by
    have hlo : ∀ᶠ y in 𝓝 b, a < y := Ioi_mem_nhds (lt_trans hx.1 hx.2)
    filter_upwards [hlo.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy1 hy2
    exact ⟨hy1,hy2⟩
  have hb : ∀ᶠ y in 𝓝[<] b, ‖F y-F x‖ ≤ M*‖y-x‖ := by
    filter_upwards [hy] with y hy
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hd z hz).hasDerivWithinAt) hM (convex_Ioo a b) hx hy
  have h := le_of_tendsto_of_tendsto ((hz.sub tendsto_const_nhds).norm)
    (tendsto_const_nhds.mul ((hid.sub tendsto_const_nhds).norm)) hb
  simpa [Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hx.2)] using h
#print axioms endpoint_flux_bound

theorem left_endpoint_flux_bound (F F' : ℝ → ℝ) (a b M x : ℝ)
    (hx : x ∈ Ioo a b)
    (hd : ∀ y ∈ Ioo a b, HasDerivAt F (F' y) y)
    (hM : ∀ y ∈ Ioo a b, ‖F' y‖ ≤ M)
    (hz : Tendsto F (𝓝[>] a) (𝓝 0)) :
    ‖F x‖ ≤ M*(x-a) := by
  have hid : Tendsto (fun y : ℝ => y) (𝓝[>] a) (𝓝 a) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hy : ∀ᶠ y in 𝓝[>] a, y ∈ Ioo a b := by
    have hhi : ∀ᶠ y in 𝓝 a, y < b := Iio_mem_nhds (lt_trans hx.1 hx.2)
    filter_upwards [hhi.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy1 hy2
    exact ⟨hy2,hy1⟩
  have hb : ∀ᶠ y in 𝓝[>] a, ‖F x-F y‖ ≤ M*‖x-y‖ := by
    filter_upwards [hy] with y hy
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hd z hz).hasDerivWithinAt) hM (convex_Ioo a b) hy hx
  have h := le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub hz).norm)
    (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hid).norm)) hb
  simpa [Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hx.1)] using h

open Q3.RouteB

theorem actual_ferrers_derivative_bounded {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Ioo (-1:ℝ) 1,
      ‖mode4FerrersFirstDerivativeSeries S.coefficients x‖ ≤ M := by
  let g := mode4FerrersFirstDerivativeSeries S.coefficients
  let F := fun x : ℝ => (1-x^2)*g x
  let D := fun x : ℝ => (mode4JacobiG m*x^2-(Λ+mode4JacobiG m))*
    mode4FerrersSeries S.coefficients x
  have hD : ContinuousOn D (Icc (-1) 1) := by
    exact (by fun_prop : Continuous (fun x : ℝ => mode4JacobiG m*x^2-(Λ+mode4JacobiG m))).continuousOn.mul S.continuousOn_closed
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  let M := max C 0
  have hM : ∀ x ∈ Ioo (-1:ℝ) 1, ‖D x‖ ≤ M := fun x hx =>
    (hC x ⟨hx.1.le,hx.2.le⟩).trans (le_max_left _ _)
  have hd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F (D x) x := by
    intro x hx
    have hp : HasDerivAt (fun y : ℝ => 1-y^2) (-2*x) x := by
      convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
    have h := hp.mul (S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx)
    have he := S.prolateDifferentialEquation x hx
    apply h.congr_deriv
    dsimp [D,g]
    nlinarith
  refine ⟨M,le_max_right _ _,fun x hx => ?_⟩
  have hp : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
  by_cases hx0 : 0 ≤ x
  · have hb := endpoint_flux_bound F D (-1) 1 M x hx hd hM S.zeroFlux_at_endpoints.1
    simp only [F,norm_mul,Real.norm_eq_abs,abs_of_pos hp] at hb
    apply (mul_le_mul_iff_of_pos_left (show 0 < 1-x by linarith [hx.2])).mp
    calc
      (1-x)*‖g x‖ ≤ (1-x^2)*‖g x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith [hx.2]
      _ ≤ M*(1-x) := hb
      _ = (1-x)*M := by ring
  · have hb := left_endpoint_flux_bound F D (-1) 1 M x hx hd hM S.zeroFlux_at_endpoints.2
    simp only [F,norm_mul,Real.norm_eq_abs,abs_of_pos hp] at hb
    apply (mul_le_mul_iff_of_pos_left (show 0 < 1+x by linarith [hx.1])).mp
    calc
      (1+x)*‖g x‖ ≤ (1-x^2)*‖g x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith [hx.1]
      _ ≤ M*(x- -1) := hb
      _ = (1+x)*M := by ring
#print axioms actual_ferrers_derivative_bounded


open MeasureTheory
 theorem actual_ferrers_derivative_square_integrable {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    IntegrableOn (fun x => (mode4FerrersFirstDerivativeSeries S.coefficients x)^2)
      (Ioo (-1:ℝ) 1) := by
  obtain ⟨M,hM,hb⟩ := actual_ferrers_derivative_bounded S
  have hc : ContinuousOn (mode4FerrersFirstDerivativeSeries S.coefficients) (Ioo (-1:ℝ) 1) :=
    fun x hx => (S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx).continuousAt.continuousWithinAt
  apply IntegrableOn.of_bound (by simp) ((hc.pow 2).aestronglyMeasurable measurableSet_Ioo) (M^2)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2
#print axioms actual_ferrers_derivative_square_integrable


theorem actual_ferrers_squares_integrable_closed {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    IntegrableOn (fun x => (mode4FerrersSeries S.coefficients x)^2) (Icc (-1:ℝ) 1) ∧
    IntegrableOn (fun x => (mode4FerrersFirstDerivativeSeries S.coefficients x)^2)
      (Icc (-1:ℝ) 1) := by
  constructor
  · exact (S.continuousOn_closed.pow 2).integrableOn_compact isCompact_Icc
  · rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact actual_ferrers_derivative_square_integrable S
#print axioms actual_ferrers_squares_integrable_closed


def actualFlux {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ) (x : ℝ) :=
  (1-x^2)*mode4FerrersFirstDerivativeSeries S.coefficients x

def actualFluxDerivative {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ) (x : ℝ) :=
  (mode4JacobiG m*x^2-(Λ+mode4JacobiG m))*mode4FerrersSeries S.coefficients x

theorem actual_flux_hasDerivAt {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (actualFlux S) (actualFluxDerivative S x) x := by
  have hp : HasDerivAt (fun y : ℝ => 1-y^2) (-2*x) x := by
    convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  have h := hp.mul (S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx)
  apply h.congr_deriv
  have he := S.prolateDifferentialEquation x hx
  dsimp [actualFluxDerivative]
  nlinarith

theorem actual_flux_continuousOn {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    ContinuousOn (actualFlux S) (Icc (-1:ℝ) 1) := by
  intro x hx
  by_cases ha : x = -1
  · subst x
    have h : ContinuousWithinAt (actualFlux S) (Ioi (-1)) (-1) := by
      simpa [ContinuousWithinAt,actualFlux] using S.zeroFlux_at_endpoints.2
    apply h.insert.mono
    intro y hy
    by_cases he : y = -1
    · exact Or.inl he
    · exact Or.inr (lt_of_le_of_ne hy.1 (Ne.symm he))
  · by_cases hb : x = 1
    · subst x
      have h : ContinuousWithinAt (actualFlux S) (Iio 1) 1 := by
        simpa [ContinuousWithinAt,actualFlux] using S.zeroFlux_at_endpoints.1
      apply h.insert.mono
      intro y hy
      by_cases he : y = 1
      · exact Or.inl he
      · exact Or.inr (lt_of_le_of_ne hy.2 he)
    · exact (actual_flux_hasDerivAt S ⟨lt_of_le_of_ne hx.1 (Ne.symm ha),lt_of_le_of_ne hx.2 hb⟩).continuousAt.continuousWithinAt

theorem actual_ferrers_natural_weak_identity {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ)
    (φ φ' : ℝ → ℝ) (hc : Continuous φ) (hc' : Continuous φ')
    (hd : ∀ x, HasDerivAt φ (φ' x) x) :
    (∫ x in (-1:ℝ)..1, actualFluxDerivative S x * φ x + actualFlux S x * φ' x) = 0 := by
  have hD : ContinuousOn (actualFluxDerivative S) (Icc (-1:ℝ) 1) :=
    (by fun_prop : Continuous (fun x : ℝ => mode4JacobiG m*x^2-(Λ+mode4JacobiG m))).continuousOn.mul S.continuousOn_closed
  have hu : ContinuousOn (actualFlux S) (uIcc (-1:ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using actual_flux_continuousOn S
  have hi : IntervalIntegrable (actualFluxDerivative S) volume (-1:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hD
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hu hc.continuousOn
    (fun x hx => actual_flux_hasDerivAt S (by simpa using hx))
    (fun x _ => hd x) hi (hc'.intervalIntegrable _ _)
  simpa [actualFlux] using h
#print axioms actual_ferrers_natural_weak_identity


theorem actual_ferrers_derivative_intervalIntegrable {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    IntervalIntegrable (mode4FerrersFirstDerivativeSeries S.coefficients) volume (-1:ℝ) 1 := by
  obtain ⟨M,hM,hb⟩ := actual_ferrers_derivative_bounded S
  have hc : ContinuousOn (mode4FerrersFirstDerivativeSeries S.coefficients) (Ioo (-1:ℝ) 1) :=
    fun x hx => (S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries x hx).continuousAt.continuousWithinAt
  have hi : IntegrableOn (mode4FerrersFirstDerivativeSeries S.coefficients) (Ioo (-1:ℝ) 1) := by
    apply IntegrableOn.of_bound (by simp) (hc.aestronglyMeasurable measurableSet_Ioo) M
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact hb x hx
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact hi

theorem actual_ferrers_energy_identity {m K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution m K Λ) :
    (∫ x in (-1:ℝ)..1,
      (1-x^2)*(mode4FerrersFirstDerivativeSeries S.coefficients x)^2 +
      mode4JacobiG m*x^2*(mode4FerrersSeries S.coefficients x)^2 -
      (Λ+mode4JacobiG m)*(mode4FerrersSeries S.coefficients x)^2) = 0 := by
  have hD : ContinuousOn (actualFluxDerivative S) (Icc (-1:ℝ) 1) :=
    (by fun_prop : Continuous (fun x : ℝ => mode4JacobiG m*x^2-(Λ+mode4JacobiG m))).continuousOn.mul S.continuousOn_closed
  have hu : ContinuousOn (actualFlux S) (uIcc (-1:ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using actual_flux_continuousOn S
  have hv : ContinuousOn (mode4FerrersSeries S.coefficients) (uIcc (-1:ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using S.continuousOn_closed
  have hi : IntervalIntegrable (actualFluxDerivative S) volume (-1:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hD
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hu hv
    (fun x hx => actual_flux_hasDerivAt S (by simpa using hx))
    (fun x hx => S.ferrersSeries_hasDerivAt_firstDerivativeSeries x (by simpa using hx))
    hi (actual_ferrers_derivative_intervalIntegrable S)
  have hz : (∫ x in (-1:ℝ)..1, actualFluxDerivative S x * mode4FerrersSeries S.coefficients x +
      actualFlux S x * mode4FerrersFirstDerivativeSeries S.coefficients x) = 0 := by
    simpa [actualFlux] using h
  rw [← hz]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp [actualFlux,actualFluxDerivative]
  ring
#print axioms actual_ferrers_energy_identity
end Q3EndpointFlux
