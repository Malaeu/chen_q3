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
end Q3EndpointFlux
