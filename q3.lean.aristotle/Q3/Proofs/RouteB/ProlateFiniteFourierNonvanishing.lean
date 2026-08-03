import Mathlib.Analysis.Fourier.Inversion
import Q3.Proofs.RouteB.ProlateSourceRegularity

open Complex Filter MeasureTheory Metric Set
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The project finite-Fourier action uses the positive phase, so it is the
Mathlib Fourier transform of the interval indicator evaluated at the negative
frequency. -/
private theorem finiteFourierAction_eq_fourier_indicator_neg
    (lambda : ℝ) (φ : ℝ → ℂ) (x : ℝ) :
    finiteFourierAction lambda φ x =
      𝓕 ((Icc (-lambda) lambda).indicator φ) (-x) := by
  rw [Real.fourier_eq']
  unfold finiteFourierAction
  calc
    (∫ y in Icc (-lambda) lambda,
        finiteFourierKernel x y * φ y) =
        ∫ y, (Icc (-lambda) lambda).indicator
          (fun y => finiteFourierKernel x y * φ y) y := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ y,
        Complex.exp
            ((↑(-2 * Real.pi * ⟪y, -x⟫) * Complex.I)) •
          (Icc (-lambda) lambda).indicator φ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Icc (-lambda) lambda
      · simp only [indicator_of_mem hy, smul_eq_mul]
        unfold finiteFourierKernel
        congr 2
        have hyx : ⟪y, -x⟫ = -(x * y) := by
          simp [RCLike.inner_apply, mul_comm]
        rw [hyx]
        push_cast
        ring
      · simp [indicator_of_notMem hy]

/-- A continuous, nonzero interior value of an interval-integrable function
forces its finite-Fourier action to be nonzero at some frequency.  The proof
uses only Fourier inversion for the zero extension; it does not construct or
select a prolate mode. -/
theorem finiteFourierAction_ne_zero_of_integrableOn_continuousAt
    (lambda : ℝ) (φ : ℝ → ℂ) (x₀ : ℝ)
    (hint : IntegrableOn φ (Icc (-lambda) lambda))
    (hx₀ : x₀ ∈ Ioo (-lambda) lambda)
    (hcont : ContinuousAt φ x₀) (hne : φ x₀ ≠ 0) :
    ∃ x : ℝ, finiteFourierAction lambda φ x ≠ 0 := by
  let f : ℝ → ℂ := (Icc (-lambda) lambda).indicator φ
  have hf : Integrable f := by
    exact hint.integrable_indicator measurableSet_Icc
  have hcontf : ContinuousAt f x₀ := by
    apply hcont.congr
    filter_upwards [isOpen_Ioo.mem_nhds hx₀] with y hy
    have hyIcc : y ∈ Icc (-lambda) lambda := ⟨hy.1.le, hy.2.le⟩
    simp only [f, indicator_of_mem hyIcc]
  by_contra hzero
  push_neg at hzero
  have hFourier : 𝓕 f = 0 := by
    funext w
    have hbridge :=
      finiteFourierAction_eq_fourier_indicator_neg lambda φ (-w)
    simp only [neg_neg] at hbridge
    rw [← hbridge, hzero]
    rfl
  have hFourierInt : Integrable (𝓕 f) := by
    rw [hFourier]
    exact integrable_zero ℝ ℂ volume
  have hinv := hf.fourierInv_fourier_eq hFourierInt hcontf
  have hfx₀ : f x₀ = 0 := by
    rw [hFourier] at hinv
    simpa [Real.fourierInv_eq] using hinv.symm
  have hx₀Icc : x₀ ∈ Icc (-lambda) lambda := ⟨hx₀.1.le, hx₀.2.le⟩
  apply hne
  simpa only [f, indicator_of_mem hx₀Icc] using hfx₀

#print axioms finiteFourierAction_ne_zero_of_integrableOn_continuousAt

end Q3.RouteB.D0Pstar
