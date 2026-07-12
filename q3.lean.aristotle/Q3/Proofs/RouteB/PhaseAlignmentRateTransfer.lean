import Mathlib

open Complex Filter Topology
open scoped Topology

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

def alignmentPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem alignmentPhase_zero : alignmentPhase 0 = 1 := by
  simp [alignmentPhase]

theorem norm_alignmentPhase (z : ℂ) : ‖alignmentPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [alignmentPhase, hz]
  · simp [alignmentPhase, hz]

theorem starRingEnd_alignmentPhase_mul (z : ℂ) :
    (starRingEnd ℂ) (alignmentPhase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [alignmentPhase, hz]
  · rw [alignmentPhase, if_neg hz, map_div₀, Complex.conj_ofReal]
    rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) z) z,
      Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    norm_cast
    field_simp

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem phase_alignment_norm_sq
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖alignmentPhase (inner ℂ u v) • u - v‖ ^ 2 =
      2 - 2 * ‖inner ℂ u v‖ := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, norm_alignmentPhase, hu, hv]
  rw [inner_smul_left, starRingEnd_alignmentPhase_mul]
  norm_num
  ring

theorem linear_overlap_defect_le_projective_defect
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    1 - ‖inner ℂ u v‖ ≤ 1 - ‖inner ℂ u v‖ ^ 2 := by
  have hr0 : 0 ≤ ‖inner ℂ u v‖ := norm_nonneg _
  have hr1 : ‖inner ℂ u v‖ ≤ 1 := by
    calc
      ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ :=
        norm_inner_le_norm (𝕜 := ℂ) u v
      _ = 1 := by rw [hu, hv]; norm_num
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]

theorem phase_alignment_norm_le_sqrt_two_projective_defect
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖alignmentPhase (inner ℂ u v) • u - v‖ ≤
      √(2 * (1 - ‖inner ℂ u v‖ ^ 2)) := by
  calc
    ‖alignmentPhase (inner ℂ u v) • u - v‖ =
        √(‖alignmentPhase (inner ℂ u v) • u - v‖ ^ 2) := by
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(2 * (1 - ‖inner ℂ u v‖)) := by
      congr 1
      rw [phase_alignment_norm_sq u v hu hv]
      ring
    _ ≤ √(2 * (1 - ‖inner ℂ u v‖ ^ 2)) := by
      apply Real.sqrt_le_sqrt
      have h := linear_overlap_defect_le_projective_defect u v hu hv
      linarith

theorem phase_alignment_tendsto_zero_of_projective_defect
    {ι : Type*} {l : Filter ι} [NeBot l] (u v : ι → E)
    (hu : ∀ᶠ i in l, ‖u i‖ = 1)
    (hv : ∀ᶠ i in l, ‖v i‖ = 1)
    (hdefect :
      Tendsto (fun i => 1 - ‖inner ℂ (u i) (v i)‖ ^ 2) l (𝓝 0)) :
    Tendsto
      (fun i => ‖alignmentPhase (inner ℂ (u i) (v i)) • u i - v i‖)
      l (𝓝 0) := by
  have hnonneg :
      ∀ᶠ i in l, 0 ≤ 1 - ‖inner ℂ (u i) (v i)‖ := by
    filter_upwards [hu, hv] with i hui hvi
    have hr := norm_inner_le_norm (𝕜 := ℂ) (u i) (v i)
    rw [hui, hvi] at hr
    norm_num at hr ⊢
    exact hr
  have hle : ∀ᶠ i in l,
      1 - ‖inner ℂ (u i) (v i)‖ ≤
        1 - ‖inner ℂ (u i) (v i)‖ ^ 2 := by
    filter_upwards [hu, hv] with i hui hvi
    exact linear_overlap_defect_le_projective_defect
      (u i) (v i) hui hvi
  have hlinear :
      Tendsto (fun i => 1 - ‖inner ℂ (u i) (v i)‖) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hdefect hnonneg hle
  have hsqrt :
      Tendsto (fun i => √(2 * (1 - ‖inner ℂ (u i) (v i)‖)))
        l (𝓝 0) := by
    simpa using (hlinear.const_mul 2).sqrt
  apply hsqrt.congr'
  filter_upwards [hu, hv] with i hui hvi
  rw [← Real.sqrt_sq (norm_nonneg
    (alignmentPhase (inner ℂ (u i) (v i)) • u i - v i))]
  congr 1
  rw [phase_alignment_norm_sq (u i) (v i) hui hvi]
  ring

#print axioms alignmentPhase_zero
#print axioms norm_alignmentPhase
#print axioms starRingEnd_alignmentPhase_mul
#print axioms phase_alignment_norm_sq
#print axioms linear_overlap_defect_le_projective_defect
#print axioms phase_alignment_norm_le_sqrt_two_projective_defect
#print axioms phase_alignment_tendsto_zero_of_projective_defect

end Q3.RouteB
