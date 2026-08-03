import Q3.Proofs.RouteB.ProlateSourceRegularity

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The canonical pointwise representative attached to a nonzero real
finite-Fourier eigenvalue.  This is only a representative constructor; it does
not assert that an eigenpair exists or select a PSWF index. -/
def finiteFourierEigenRepresentative
    (lambda chi : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((chi : ℂ)⁻¹) * finiteFourierAction lambda f y

/-- An a.e. finite-Fourier eigenfunction has a canonical Lipschitz
representative on the source interval.  This isolates representative
regularity from the still-open existence and PSWF index-selection problem. -/
theorem finiteFourier_aeEigenfunction_lipschitzRepresentative
    (lambda chi : ℝ)
    (hlambda : 0 ≤ lambda)
    (hchi : chi ≠ 0)
    (f : ℝ → ℂ)
    (hf : IntegrableOn f (Icc (-lambda) lambda))
    (heig : ∀ᵐ y ∂(volume.restrict (Icc (-lambda) lambda)),
      finiteFourierAction lambda f y = (chi : ℂ) * f y) :
    ∃ K : NNReal,
      LipschitzOnWith K
          (finiteFourierEigenRepresentative lambda chi f)
          (Icc (-lambda) lambda) ∧
      finiteFourierEigenRepresentative lambda chi f
        =ᵐ[volume.restrict (Icc (-lambda) lambda)] f := by
  obtain ⟨K, hK⟩ := finiteFourierAction_lipschitzWith lambda hlambda f hf
  let Kg : NNReal := ‖((chi : ℂ)⁻¹)‖₊ * K
  refine ⟨Kg, ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun x _ z _ => ?_
    calc
      dist (finiteFourierEigenRepresentative lambda chi f x)
          (finiteFourierEigenRepresentative lambda chi f z) =
          ‖((chi : ℂ)⁻¹)‖ *
            dist (finiteFourierAction lambda f x)
              (finiteFourierAction lambda f z) := by
        rw [finiteFourierEigenRepresentative,
          finiteFourierEigenRepresentative, dist_eq_norm, dist_eq_norm,
          ← mul_sub, norm_mul]
      _ ≤ ‖((chi : ℂ)⁻¹)‖ * ((K : ℝ) * dist x z) := by
        gcongr
        exact hK.dist_le_mul x z
      _ = (Kg : ℝ) * dist x z := by
        simp only [Kg, NNReal.coe_mul, coe_nnnorm]
        ring
  · filter_upwards [heig] with y hy
    rw [finiteFourierEigenRepresentative, hy]
    simp [hchi]

#print axioms finiteFourierEigenRepresentative
#print axioms finiteFourier_aeEigenfunction_lipschitzRepresentative

end Q3.RouteB.D0Pstar
