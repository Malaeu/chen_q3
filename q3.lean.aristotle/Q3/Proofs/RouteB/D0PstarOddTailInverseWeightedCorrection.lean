import Q3.Proofs.RouteB.D0PstarOddTailDividedDifference13
import Mathlib.Analysis.InnerProductSpace.Positive

set_option linter.mathlibStandardSet false

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Lawful inverse-weighted odd-tail correction

This file isolates the operator interface required by the surviving
resolvent-weighted Schur route.  An outer tail operator must be continuously
invertible, its actual continuous inverse must be positive, and the residual
must be a continuous map into the same tail Hilbert space.  Only then do we
form

`R† ∘ C⁻¹ ∘ R`.

The interface deliberately does not manufacture these hypotheses from the
finite `N = 960` audit.  It also does not replace `C⁻¹` by a scalar multiple
of the identity.
-/

variable {Head Tail : Type*}
  [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
  [NormedAddCommGroup Tail] [InnerProductSpace ℂ Tail] [CompleteSpace Tail]

omit [CompleteSpace Tail] in
/-- A positive continuously invertible operator has a positive actual
continuous inverse.  This is proved directly from surjectivity and symmetry;
no spectral theorem or finite-dimensional diagonalization is used. -/
theorem isPositive_inverse_of_isPositive_isInvertible
    (C : Tail →L[ℂ] Tail)
    (hC : C.IsPositive)
    (hInv : C.IsInvertible) :
    C.inverse.IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    have hx : C (C.inverse x) = x := by
      have h := hInv.inverse_apply_eq
        (x := C.inverse x) (y := x)
      exact (h.mp rfl).symm
    have hy : C (C.inverse y) = y := by
      have h := hInv.inverse_apply_eq
        (x := C.inverse y) (y := y)
      exact (h.mp rfl).symm
    calc
      inner ℂ (C.inverse x) y =
          inner ℂ (C.inverse x) (C (C.inverse y)) := by rw [hy]
      _ = inner ℂ (C (C.inverse x)) (C.inverse y) := by
        exact (hC.isSymmetric (C.inverse x) (C.inverse y)).symm
      _ = inner ℂ x (C.inverse y) := by rw [hx]
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have hx : C (C.inverse x) = x := by
      have h := hInv.inverse_apply_eq
        (x := C.inverse x) (y := x)
      exact (h.mp rfl).symm
    calc
      0 ≤ re (inner ℂ (C.inverse x) (C (C.inverse x))) :=
        hC.re_inner_nonneg_right (C.inverse x)
      _ = re (inner ℂ (C.inverse x) x) := by rw [hx]

/-- The exact data needed to make an inverse-weighted outer correction a
bounded operator.  Positivity and continuous invertibility of the actual
outer block are explicit mathematical supplier obligations, not consequences
of finite numerics. -/
structure OddTailInverseWeightedData (Head Tail : Type*)
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
  [NormedAddCommGroup Tail] [InnerProductSpace ℂ Tail] [CompleteSpace Tail] where
  outerBlock : Tail →L[ℂ] Tail
  residual : Head →L[ℂ] Tail
  outerBlock_positive : outerBlock.IsPositive
  outerBlock_invertible : outerBlock.IsInvertible

/-- The exact inverse-weighted Gram correction `R† C⁻¹ R`. -/
noncomputable def oddTailInverseWeightedCorrection
    (D : OddTailInverseWeightedData Head Tail) : Head →L[ℂ] Head :=
  (D.residual.adjoint.comp D.outerBlock.inverse).comp D.residual

/-- The inverse appearing in the correction really solves the outer-block
equation; it is not an arbitrary right inverse or a scalar floor surrogate. -/
theorem outerBlock_apply_inverse_residual
    (D : OddTailInverseWeightedData Head Tail) (x : Head) :
    D.outerBlock (D.outerBlock.inverse (D.residual x)) = D.residual x := by
  have h := D.outerBlock_invertible.inverse_apply_eq
    (x := D.outerBlock.inverse (D.residual x))
    (y := D.residual x)
  exact (h.mp rfl).symm

/-- The exact correction is positive because it is the adjoint conjugation of
the positive actual outer inverse. -/
theorem oddTailInverseWeightedCorrection_isPositive
    (D : OddTailInverseWeightedData Head Tail) :
    (oddTailInverseWeightedCorrection D).IsPositive := by
  exact
    (isPositive_inverse_of_isPositive_isInvertible D.outerBlock
      D.outerBlock_positive D.outerBlock_invertible).adjoint_conj D.residual

/-- Pointwise action of the inverse-weighted correction. -/
theorem oddTailInverseWeightedCorrection_apply
    (D : OddTailInverseWeightedData Head Tail) (x : Head) :
    oddTailInverseWeightedCorrection D x =
      D.residual.adjoint (D.outerBlock.inverse (D.residual x)) := by
  rfl

/-- Exact quadratic pairing: the correction measures the residual through the
actual outer inverse. -/
theorem inner_oddTailInverseWeightedCorrection
    (D : OddTailInverseWeightedData Head Tail) (x y : Head) :
    inner ℂ (oddTailInverseWeightedCorrection D x) y =
      inner ℂ (D.outerBlock.inverse (D.residual x)) (D.residual y) := by
  rw [oddTailInverseWeightedCorrection_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The inverse-weighted residual quadratic value is nonnegative. -/
theorem re_inner_oddTailInverseWeightedCorrection_nonneg
    (D : OddTailInverseWeightedData Head Tail) (x : Head) :
    0 ≤ re (inner ℂ (oddTailInverseWeightedCorrection D x) x) :=
  (oddTailInverseWeightedCorrection_isPositive D).re_inner_nonneg_left x

/-- The corresponding exact Schur complement of a bounded head operator. -/
noncomputable def oddTailSchurComplement
    (A : Head →L[ℂ] Head)
    (D : OddTailInverseWeightedData Head Tail) : Head →L[ℂ] Head :=
  A - oddTailInverseWeightedCorrection D

/-- Exact head decomposition into Schur complement plus the inverse-weighted
outer correction. -/
theorem operator_eq_oddTailSchurComplement_add_correction
    (A : Head →L[ℂ] Head)
    (D : OddTailInverseWeightedData Head Tail) :
    A = oddTailSchurComplement A D + oddTailInverseWeightedCorrection D := by
  simp [oddTailSchurComplement]

/-- Quadratic-form version of the exact head decomposition. -/
theorem inner_operator_eq_schur_add_inverseWeighted
    (A : Head →L[ℂ] Head)
    (D : OddTailInverseWeightedData Head Tail)
    (x : Head) :
    inner ℂ (A x) x =
      inner ℂ (oddTailSchurComplement A D x) x +
        inner ℂ (oddTailInverseWeightedCorrection D x) x := by
  simp [oddTailSchurComplement]

#print axioms OddTailInverseWeightedData
#print axioms isPositive_inverse_of_isPositive_isInvertible
#print axioms oddTailInverseWeightedCorrection_isPositive
#print axioms outerBlock_apply_inverse_residual
#print axioms inner_oddTailInverseWeightedCorrection
#print axioms re_inner_oddTailInverseWeightedCorrection_nonneg
#print axioms operator_eq_oddTailSchurComplement_add_correction
#print axioms inner_operator_eq_schur_add_inverseWeighted

end Q3.RouteB.D0Pstar
