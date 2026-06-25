import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivSharpOrder16Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Exact rational half-cell order-16 budget audit for the active Step33A.1-A sub0
combined-cancellation route.

This file is fail-closed: it checks only the arithmetic gate suggested by the
Browser/Computer Use route review after the sharp ShapeSqDeriv order-16
one-cell budget kill, and records that halving the radius is still not enough.
It does not build segmented center jets, segmented source-interval rows, Horner
rows, target-budget rows, or a `Step33Sub0CombinedCancellationSourceIntervalCert.Valid`
payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- Halving the centered-Taylor radius from `1/20` to `1/40` still leaves the
exact sharp ShapeSqDeriv order-16 remainder contribution wider than the current
combined-cancellation half-width. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sharpOrder16_halfCell_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth <
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
        ((1 : Rat) / 40) ^ 16 / (Nat.factorial 16 : Rat) := by
  native_decide

/-- Reducing the centered-Taylor radius to `1/80` still leaves the exact sharp
ShapeSqDeriv order-16 remainder contribution wider than the current
combined-cancellation half-width. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sharpOrder16_quarterCell_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth <
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
        ((1 : Rat) / 80) ^ 16 / (Nat.factorial 16 : Rat) := by
  native_decide

/-- Radius `1/1280` is still insufficient for the exact sharp ShapeSqDeriv
order-16 remainder contribution. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sharpOrder16_radius1280_width_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth <
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
        ((1 : Rat) / 1280) ^ 16 / (Nat.factorial 16 : Rat) := by
  native_decide

/-- Radius `1/2560` is enough for the exact sharp ShapeSqDeriv order-16
remainder contribution.  On the full interval `[0, 1/10]`, this corresponds to
128 equal subsegments if used as a naive centered-Taylor split preflight. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sharpOrder16_radius2560_width_pass_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationSharpShapeSqDerivOrder16BudgetRat *
        ((1 : Rat) / 2560) ^ 16 / (Nat.factorial 16 : Rat) <=
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth := by
  native_decide

end Step33
end PSDpd
end Q3
