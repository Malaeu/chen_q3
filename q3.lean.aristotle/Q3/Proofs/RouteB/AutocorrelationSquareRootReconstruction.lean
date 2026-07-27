import Mathlib

set_option linter.mathlibStandardSet false

open Filter MeasureTheory Set

noncomputable section

namespace Q3.RouteB

/-!
# Status: STUB / INACTIVE

This file is a typed Round-12 contract only.  It does not prove that a square
root candidate exists and is not an active input to the canonical Route-B
roof.  Promotion requires a separate existence theorem satisfying every field
of `AutocorrelationSquareRootReconstructionInput`.
-/

/-- Standard epsilon-form definition of exponential type at most `sigma`. -/
def ExponentialTypeAtMost (sigma : ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp ((sigma + ε) * ‖z‖)

/-- A local-factorization certificate for the finite order of every zero of
an entire function.  This is stronger than a boolean claim that the orders
are even: `order` is tied to a nonvanishing local factor. -/
structure EntireZeroMultiplicityCertificate (H : ℂ → ℂ) where
  order : ℂ → ℕ
  zero_iff_order_pos : ∀ z, H z = 0 ↔ 0 < order z
  localFactor : ∀ z, ∃ g : ℂ → ℂ,
    Differentiable ℂ g ∧ g z ≠ 0 ∧
      ∀ᶠ w in nhds z, H w = (w - z) ^ (order z) * g w
  even_at_zeros : ∀ z, H z = 0 → Even (order z)

/-- Strict Round-12 input contract.

`even_entire` is a type invariant of an *autocorrelation transform* rather
than an optional analytic estimate.  Without it, the displayed scalar
conditions do not imply a real-even source (a translated sinc square is a
counterexample). -/
structure AutocorrelationSquareRootReconstructionInput where
  R : ℝ
  H : ℂ → ℂ
  hR : 0 ≤ R
  entire : Differentiable ℂ H
  nonzero : H ≠ 0
  even_entire : Function.Even H
  nonnegative_on_real : ∀ x : ℝ,
    (H (x : ℂ)).im = 0 ∧ 0 ≤ (H (x : ℂ)).re
  integrable_on_real : Integrable (fun x : ℝ => ‖H (x : ℂ)‖)
  type_at_most_two_R : ExponentialTypeAtMost (2 * R) H
  zeros : EntireZeroMultiplicityCertificate H
  order_zero_multiple_four : ∃ k : ℕ, zeros.order 0 = 4 * k

/-- One real-even compactly supported source whose entire transform squares
to the supplied autocorrelation transform. -/
structure AutocorrelationSquareRootCandidate
    (Fourier : (ℝ → ℝ) →+ (ℂ → ℂ))
    (C : AutocorrelationSquareRootReconstructionInput) (q : ℝ → ℝ) : Prop where
  even_source : Function.Even q
  square_integrable : Integrable (fun x : ℝ => |q x| ^ 2)
  compact_support : Function.support q ⊆ Icc (-C.R) C.R
  transform_entire : Differentiable ℂ (Fourier q)
  transform_type_at_most_R : ExponentialTypeAtMost C.R (Fourier q)
  transform_square : ∀ z : ℂ, Fourier q z * Fourier q z = C.H z

/-- Typed statement of `SOFT_L2_AutocorrelationSquareRootReconstruction`.

The proposition asserts existence of a nonzero real-even source and that the
complete candidate set is exactly its two global signs.  This file freezes the
type; it does not smuggle an existence proof into the assumptions. -/
def AutocorrelationSquareRootReconstruction
    (Fourier : (ℝ → ℝ) →+ (ℂ → ℂ))
    (C : AutocorrelationSquareRootReconstructionInput) : Prop :=
  ∃ q : ℝ → ℝ,
    q ≠ 0 ∧
    AutocorrelationSquareRootCandidate Fourier C q ∧
    AutocorrelationSquareRootCandidate Fourier C (-q) ∧
    ∀ p : ℝ → ℝ, AutocorrelationSquareRootCandidate Fourier C p →
      p = q ∨ p = -q

#check AutocorrelationSquareRootReconstructionInput
#check AutocorrelationSquareRootCandidate
#check AutocorrelationSquareRootReconstruction

end Q3.RouteB
