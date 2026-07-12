import Q3.Proofs.RouteB.CompletedTrackerScope
import Q3.Proofs.RouteB.ClassicalXiInterface

set_option linter.mathlibStandardSet false

open Complex Filter Set Metric
open scoped Topology

noncomputable section
namespace Q3.RouteB

def normalizedDoubleCompletedXi (z : ℂ) : ℂ :=
  (gammaC ((1 / 2 : ℂ) + Complex.I * z) / gammaC (1 / 2)) * centeredXi z

theorem gammaC_half_ne_zero : gammaC (1 / 2) ≠ 0 := by
  unfold gammaC
  norm_num
  apply Complex.Gamma_ne_zero
  intro m h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

theorem gamma_differentiableAt_half : DifferentiableAt ℂ Complex.Gamma (1 / 2) := by
  apply Complex.differentiableAt_Gamma
  intro m h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

theorem continuousAt_gammaC_one : ContinuousAt gammaC 1 := by
  have hGamma : ContinuousAt (fun s : ℂ => Complex.Gamma (s / 2)) 1 := by
    exact gamma_differentiableAt_half.continuousAt.comp_of_eq
      (continuousAt_id.div_const 2) (by norm_num)
  have hpow : ContinuousAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) 1 := by
    exact (continuousAt_id.neg.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  unfold gammaC
  fun_prop

theorem continuousAt_normalizedDoubleCompletedXi_boundary :
    ContinuousAt normalizedDoubleCompletedXi (-Complex.I / 2) := by
  unfold normalizedDoubleCompletedXi
  have harg : ContinuousAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) (-Complex.I / 2) := by
    fun_prop
  have hgc : ContinuousAt (fun z : ℂ => gammaC ((1 / 2 : ℂ) + Complex.I * z)) (-Complex.I / 2) := by
    exact continuousAt_gammaC_one.comp_of_eq harg centered_argument_neg_I_div_two
  have hxi : ContinuousAt centeredXi (-Complex.I / 2) :=
    differentiable_centeredXi.continuous.continuousAt
  fun_prop

theorem neg_I_div_two_mem_closure_centeredCriticalStrip :
    (-Complex.I / 2 : ℂ) ∈ closure centeredCriticalStrip := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 4)
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδle : δ ≤ 1 / 4 := min_le_right _ _
  have hδltε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  let z : ℂ := -Complex.I / 2 + (δ : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · change |z.im| < 1 / 2
    have hzim : z.im = -1 / 2 + δ := by simp [z]
    rw [hzim, abs_lt]
    constructor <;> linarith
  · rw [dist_comm]
    calc
      dist z (-Complex.I / 2) = ‖(δ : ℂ) * Complex.I‖ := by simp [z]
      _ = δ := by simp [abs_of_pos hδpos]
      _ < ε := hδltε

@[simp] theorem normalizedDoubleCompletedXi_boundary_zero :
    normalizedDoubleCompletedXi (-Complex.I / 2) = 0 := by
  unfold normalizedDoubleCompletedXi
  rw [centered_argument_neg_I_div_two, gammaC_one]
  simp

@[simp] theorem centeredXi_boundary_eq_half :
    centeredXi (-Complex.I / 2) = 1 / 2 := by
  unfold centeredXi
  rw [centered_argument_neg_I_div_two, riemannXi_one]

theorem normalizedDoubleCompletedXi_not_eqOn_centeredCriticalStrip :
    ¬ Set.EqOn normalizedDoubleCompletedXi centeredXi centeredCriticalStrip := by
  intro hEqOn
  let z0 : ℂ := -Complex.I / 2
  have hz0 : z0 ∈ closure centeredCriticalStrip := by
    simpa [z0] using neg_I_div_two_mem_closure_centeredCriticalStrip
  letI : (𝓝[centeredCriticalStrip] z0).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hz0
  have hEventually :
      normalizedDoubleCompletedXi =ᶠ[𝓝[centeredCriticalStrip] z0] centeredXi := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hEqOn hz
  have hBoundaryEq : normalizedDoubleCompletedXi z0 = centeredXi z0 :=
    tendsto_nhds_unique_of_eventuallyEq
      continuousAt_normalizedDoubleCompletedXi_boundary.continuousWithinAt
      (differentiable_centeredXi.continuous.continuousAt.continuousWithinAt)
      hEventually
  simp [z0] at hBoundaryEq

theorem exists_normalizedDoubleCompletedXi_mismatch_in_strip :
    ∃ z ∈ centeredCriticalStrip,
      normalizedDoubleCompletedXi z ≠ centeredXi z := by
  have h := normalizedDoubleCompletedXi_not_eqOn_centeredCriticalStrip
  change ¬ ∀ z, z ∈ centeredCriticalStrip →
    normalizedDoubleCompletedXi z = centeredXi z at h
  push_neg at h
  exact h

#print axioms gammaC_half_ne_zero
#print axioms normalizedDoubleCompletedXi_not_eqOn_centeredCriticalStrip
#print axioms exists_normalizedDoubleCompletedXi_mismatch_in_strip

end Q3.RouteB
