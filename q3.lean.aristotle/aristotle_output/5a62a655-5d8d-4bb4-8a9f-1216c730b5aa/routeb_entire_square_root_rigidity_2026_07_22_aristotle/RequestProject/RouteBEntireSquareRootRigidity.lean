import Mathlib

noncomputable section

namespace Q3.RouteB

/-- Two entire functions with identical pointwise squares differ by one
global sign.  The sign may not vary across zeros. -/
theorem entireSquareRootRigidity
    (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G)
    (hsquare : ∀ z : ℂ, F z * F z = G z * G z) :
    F = G ∨ F = -G := by
  have hsub : AnalyticOnNhd ℂ (F - G) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (hF.sub hG)
  have hadd : AnalyticOnNhd ℂ (F + G) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (hF.add hG)
  have hmul : ∀ z ∈ Set.univ, (F - G) z * (F + G) z = 0 := by
    intro z _
    change (F z - G z) * (F z + G z) = 0
    calc
      (F z - G z) * (F z + G z) = F z * F z - G z * G z := by ring
      _ = 0 := sub_eq_zero.mpr (hsquare z)
  rcases hsub.eq_zero_or_eq_zero_of_mul_eq_zero hadd hmul
      PreconnectedSpace.isPreconnected_univ with h | h
  · left
    funext z
    exact sub_eq_zero.mp (h z (Set.mem_univ z))
  · right
    funext z
    exact eq_neg_of_add_eq_zero_left (h z (Set.mem_univ z))

#print axioms entireSquareRootRigidity

end Q3.RouteB
