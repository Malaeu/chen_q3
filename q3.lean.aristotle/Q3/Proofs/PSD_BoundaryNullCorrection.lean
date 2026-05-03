import Q3.Proofs.PSD_CertificateFamily
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
Algebraic boundary-null correction for the PSD-pd exhaustion lane.

The analytic boundary functionals are eventually

* `h ↦ H(1/2)`;
* `h ↦ H(-1/2)`.

This file proves only the linear algebra core: if two corrector vectors have an
invertible two-by-two boundary evaluation matrix, then every vector can be
corrected by their span so that both boundary functionals vanish.
-/

/-- Two boundary linear functionals. -/
structure BoundaryPair (V : Type*) [AddCommGroup V] [Module ℝ V] where
  evalPlus : V →ₗ[ℝ] ℝ
  evalMinus : V →ₗ[ℝ] ℝ

/-- Determinant of the two-by-two boundary evaluation matrix on two
correctors. -/
def boundaryDet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus : V) : ℝ :=
  E.evalPlus bPlus * E.evalMinus bMinus
    - E.evalPlus bMinus * E.evalMinus bPlus

/-- Algebraic boundary correction.

If two corrector vectors have invertible boundary evaluation matrix, then every
vector can be corrected by a linear combination of them so that both boundary
functionals vanish. -/
theorem boundary_correction_exists
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V)
    (hdet : boundaryDet E bPlus bMinus ≠ 0) :
    ∃ aPlus aMinus : ℝ,
      E.evalPlus (g - aPlus • bPlus - aMinus • bMinus) = 0 ∧
      E.evalMinus (g - aPlus • bPlus - aMinus • bMinus) = 0 := by
  let A : ℝ := E.evalPlus bPlus
  let B : ℝ := E.evalPlus bMinus
  let C : ℝ := E.evalMinus bPlus
  let D : ℝ := E.evalMinus bMinus
  let p : ℝ := E.evalPlus g
  let q : ℝ := E.evalMinus g
  let Δ : ℝ := A * D - B * C
  have hΔ : Δ ≠ 0 := by
    simpa [boundaryDet, A, B, C, D, Δ] using hdet
  have hΔcomm : D * A - B * C ≠ 0 := by
    simpa [Δ, mul_comm] using hΔ
  let aPlus : ℝ := (p * D - B * q) / Δ
  let aMinus : ℝ := (A * q - p * C) / Δ
  refine ⟨aPlus, aMinus, ?_, ?_⟩
  · calc
      E.evalPlus (g - aPlus • bPlus - aMinus • bMinus)
          = p - aPlus * A - aMinus * B := by
              simp [p, A, B, aPlus, aMinus]
      _ = 0 := by
              simp [aPlus, aMinus, Δ]
              field_simp [hΔcomm]
              ring_nf
  · calc
      E.evalMinus (g - aPlus • bPlus - aMinus • bMinus)
          = q - aPlus * C - aMinus * D := by
              simp [q, C, D, aPlus, aMinus]
      _ = 0 := by
              simp [aPlus, aMinus, Δ]
              field_simp [hΔcomm]
              ring_nf

/-- Future analytic corrector data.

The construction of compactly supported smooth corrector bumps belongs to the
exhaustion layer.  This structure records the data needed by the algebraic
correction lemma. -/
structure BoundaryCorrectorData
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  boundary : BoundaryPair V
  bPlus : V
  bMinus : V
  det_ne_zero : boundaryDet boundary bPlus bMinus ≠ 0

/-- Every `BoundaryCorrectorData` gives algebraic correction coefficients. -/
theorem boundary_correction_from_data
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : BoundaryCorrectorData V) (g : V) :
    ∃ aPlus aMinus : ℝ,
      D.boundary.evalPlus (g - aPlus • D.bPlus - aMinus • D.bMinus) = 0 ∧
      D.boundary.evalMinus (g - aPlus • D.bPlus - aMinus • D.bMinus) = 0 :=
  boundary_correction_exists D.boundary D.bPlus D.bMinus g D.det_ne_zero

end PSDpd
end Q3
