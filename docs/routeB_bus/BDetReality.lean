import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- The finite detector scalar on a fixed two-parameter carrier. -/
def bDetFinite (L zetaHalf : ℝ) (c : ℤ → ℂ) : ℂ :=
  (Real.sqrt L : ℂ) * c 0 / (zetaHalf : ℂ)

/--
The finite `bDet` formula is definitionally fixed, and the usual reality
symmetry of Fourier coefficients makes this scalar real.  No asymptotic
selector or detector parameter is introduced here.
-/
theorem bDet_finite_definition_and_reality
    (L zetaHalf : ℝ) (c : ℤ → ℂ)
    (hreal : ∀ n : ℤ, c (-n) = star (c n)) :
    star (c 0) = c 0 ∧
      bDetFinite L zetaHalf c =
        (Real.sqrt L : ℂ) * c 0 / (zetaHalf : ℂ) ∧
      star (bDetFinite L zetaHalf c) = bDetFinite L zetaHalf c := by
  have hc0 : star (c 0) = c 0 := by
    simpa using (hreal 0).symm
  exact ⟨hc0, rfl, by simp [bDetFinite, hc0]⟩

#print axioms bDet_finite_definition_and_reality

end Q3.RouteB
