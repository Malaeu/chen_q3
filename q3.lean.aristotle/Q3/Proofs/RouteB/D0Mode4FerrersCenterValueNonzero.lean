import Q3.Proofs.RouteB.D0Mode4FerrersInteriorZeroSimplicity

/-!
# Goal 058 G3: nonzero center value of the mode-four Ferrers solution

Evenness forces the derivative at the center to vanish.  The accepted
interior-zero simplicity theorem therefore rules out a simultaneous zero of
the function at the center.

This theorem still does not count the noncentral roots or identify the
constructed solution with the ordered degree-four PSWF.
-/

namespace Q3.RouteB

/-- The regular even mode-four Ferrers source solution is nonzero at the
center of its source interval. -/
theorem Mode4FerrersRegularEvenProlateSolution.center_value_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients 0 ≠ 0 := by
  intro hCenter
  have hzero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hFirst :=
    S.ferrersSeries_hasDerivAt_firstDerivativeSeries 0 hzero
  have hNeg :
      HasDerivAt
        (fun t : ℝ => mode4FerrersSeries S.coefficients (-t))
        (-mode4FerrersFirstDerivativeSeries S.coefficients 0)
        0 := by
    have hFirstAtNegZero :
        HasDerivAt
          (mode4FerrersSeries S.coefficients)
          (mode4FerrersFirstDerivativeSeries S.coefficients 0)
          (-0) := by
      simpa using hFirst
    convert hFirstAtNegZero.comp 0 (hasDerivAt_neg 0) using 1;
      norm_num
  have hNegEq :
      (fun t : ℝ => mode4FerrersSeries S.coefficients (-t)) =
        mode4FerrersSeries S.coefficients := by
    funext t
    exact S.even t
  rw [hNegEq] at hNeg
  have hFirstZero :
      mode4FerrersFirstDerivativeSeries S.coefficients 0 = 0 := by
    have hUnique := hNeg.unique hFirst
    linarith
  have hDerivZero : deriv (mode4FerrersSeries S.coefficients) 0 = 0 := by
    rw [hFirst.deriv]
    exact hFirstZero
  exact (S.interior_zero_simple hzero hCenter) hDerivZero

#print axioms Mode4FerrersRegularEvenProlateSolution.center_value_ne_zero

end Q3.RouteB
