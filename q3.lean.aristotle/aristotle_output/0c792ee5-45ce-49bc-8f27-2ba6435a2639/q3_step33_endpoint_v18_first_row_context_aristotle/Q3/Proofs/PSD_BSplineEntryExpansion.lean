import Q3.Proofs.PSD_BSplineFormulaContract
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
B-spline packet entry expansion.

Step 32B introduced a formula contract that expects:

* concrete two-row boundary formulas;
* Arch and prime matrix identities on synthesized packets.

This file lowers those requirements to basis-level facts.  If a packet
synthesis map is a finite linear combination of basis packets, and the
boundary / bilinear form values are known on the basis, Lean expands the sums
and produces the Step 32B contract.

The remaining analytic work after this file is therefore sharply localized:
prove the actual B-spline basis transform, correlation, Arch-entry, and
prime-entry formulas.
-/

/-- A finite packet synthesis map expanded in a concrete basis. -/
structure PacketBasisExpansion
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  basis : ι → V
  synth : (ι → ℝ) → V
  synth_eq_sum :
    ∀ v : ι → ℝ,
      synth v = ∑ i, v i • basis i

namespace PacketBasisExpansion

/-- Boundary plus row formula from basis values. -/
theorem boundaryPlus_formula_of_basis_values
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (E : PacketBasisExpansion ι V)
    (boundary : BoundaryPair V)
    (qPlus : ι → ℝ) (scalePlus : ℝ)
    (hPlusBasis :
      ∀ i : ι, boundary.evalPlus (E.basis i) = scalePlus * qPlus i)
    (v : ι → ℝ) :
    boundary.evalPlus (E.synth v) =
      scalePlus * ∑ i, qPlus i * v i := by
  rw [E.synth_eq_sum v]
  simp [hPlusBasis, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Boundary minus row formula from basis values. -/
theorem boundaryMinus_formula_of_basis_values
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (E : PacketBasisExpansion ι V)
    (boundary : BoundaryPair V)
    (qMinus : ι → ℝ) (scaleMinus : ℝ)
    (hMinusBasis :
      ∀ i : ι, boundary.evalMinus (E.basis i) = scaleMinus * qMinus i)
    (v : ι → ℝ) :
    boundary.evalMinus (E.synth v) =
      scaleMinus * ∑ i, qMinus i * v i := by
  rw [E.synth_eq_sum v]
  simp [hMinusBasis, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Convert basis-level boundary transform formulas to the Step 32B boundary
row contract. -/
def toBoundaryRows
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (E : PacketBasisExpansion ι V)
    (boundary : BoundaryPair V)
    (qPlus qMinus : ι → ℝ)
    (scalePlus scaleMinus : ℝ)
    (scalePlus_ne_zero : scalePlus ≠ 0)
    (scaleMinus_ne_zero : scaleMinus ≠ 0)
    (hPlusBasis :
      ∀ i : ι, boundary.evalPlus (E.basis i) = scalePlus * qPlus i)
    (hMinusBasis :
      ∀ i : ι, boundary.evalMinus (E.basis i) = scaleMinus * qMinus i) :
    BSplineBoundaryRows ι V where
  synth := E.synth
  boundary := boundary
  qPlus := qPlus
  qMinus := qMinus
  scalePlus := scalePlus
  scaleMinus := scaleMinus
  scalePlus_ne_zero := scalePlus_ne_zero
  scaleMinus_ne_zero := scaleMinus_ne_zero
  boundaryPlus_formula :=
    E.boundaryPlus_formula_of_basis_values boundary qPlus scalePlus hPlusBasis
  boundaryMinus_formula :=
    E.boundaryMinus_formula_of_basis_values boundary qMinus scaleMinus hMinusBasis

end PacketBasisExpansion

/--
Basis-entry expansion for a bilinear form.

`form` is curried as a linear map into linear functionals.  This keeps the
finite expansion fully algebraic and avoids any analytic assumptions.
-/
structure PacketBilinearMatrixExpansion
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  basisExpansion : PacketBasisExpansion ι V
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  M : Matrix ι ι ℝ
  /--
  Matrix-entry convention.

  The row index is placed in the second bilinear slot.  This matches the
  `quadForm` convention used by the finite certificate files and is harmless
  for the symmetric real Arch/Prime matrices used in the PSD-pd block.
  -/
  entry_ident :
    ∀ i j : ι,
      M i j = form (basisExpansion.basis j) (basisExpansion.basis i)

namespace PacketBilinearMatrixExpansion

/-- A bilinear form with known basis entries expands to its finite matrix
quadratic form on synthesized packets. -/
theorem form_synth_eq_quadForm
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (E : PacketBilinearMatrixExpansion ι V)
    (v : ι → ℝ) :
    E.form (E.basisExpansion.synth v) (E.basisExpansion.synth v) =
      Q3.Proofs.quadForm E.M v := by
  rw [E.basisExpansion.synth_eq_sum v]
  unfold Q3.Proofs.quadForm
  simp [E.entry_ident, Finset.mul_sum, mul_comm, mul_left_comm]

end PacketBilinearMatrixExpansion

/--
Basis-entry formula package for a B-spline packet block.

This is the practical landing surface for the next analytic lemmas:

* basis transform values give boundary rows;
* Arch basis pairings give `A`;
* prime basis pairings give `P`;
* the Weil form splits as Arch minus Prime.
-/
structure BSplineBasisFormulaContract
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  basisExpansion : PacketBasisExpansion ι V
  boundary : BoundaryPair V
  qPlus : ι → ℝ
  qMinus : ι → ℝ
  scalePlus : ℝ
  scaleMinus : ℝ
  scalePlus_ne_zero : scalePlus ≠ 0
  scaleMinus_ne_zero : scaleMinus ≠ 0
  boundaryPlus_basis :
    ∀ i : ι, boundary.evalPlus (basisExpansion.basis i) = scalePlus * qPlus i
  boundaryMinus_basis :
    ∀ i : ι, boundary.evalMinus (basisExpansion.basis i) = scaleMinus * qMinus i
  archExpansion : PacketBilinearMatrixExpansion ι V
  primeExpansion : PacketBilinearMatrixExpansion ι V
  arch_basisExpansion_eq :
    archExpansion.basisExpansion = basisExpansion
  prime_basisExpansion_eq :
    primeExpansion.basisExpansion = basisExpansion
  archForm : V → ℝ
  primeForm : V → ℝ
  weilForm : V → ℝ
  archForm_eq :
    ∀ v : ι → ℝ,
      archForm (basisExpansion.synth v) =
        archExpansion.form (basisExpansion.synth v) (basisExpansion.synth v)
  primeForm_eq :
    ∀ v : ι → ℝ,
      primeForm (basisExpansion.synth v) =
        primeExpansion.form (basisExpansion.synth v) (basisExpansion.synth v)
  weil_split :
    ∀ v : ι → ℝ,
      weilForm (basisExpansion.synth v) =
        archForm (basisExpansion.synth v) - primeForm (basisExpansion.synth v)

namespace BSplineBasisFormulaContract

/-- Boundary rows supplied by the basis formula package. -/
def boundaryRows
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBasisFormulaContract ι V) :
    BSplineBoundaryRows ι V :=
  B.basisExpansion.toBoundaryRows
    B.boundary
    B.qPlus
    B.qMinus
    B.scalePlus
    B.scaleMinus
    B.scalePlus_ne_zero
    B.scaleMinus_ne_zero
    B.boundaryPlus_basis
    B.boundaryMinus_basis

/-- Arch matrix identity on synthesized packets. -/
theorem arch_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBasisFormulaContract ι V)
    (v : ι → ℝ) :
    B.archForm (B.boundaryRows.synth v) =
      Q3.Proofs.quadForm B.archExpansion.M v := by
  change B.archForm (B.basisExpansion.synth v) =
    Q3.Proofs.quadForm B.archExpansion.M v
  rw [B.archForm_eq v]
  rw [← B.arch_basisExpansion_eq]
  exact B.archExpansion.form_synth_eq_quadForm v

/-- Prime matrix identity on synthesized packets. -/
theorem prime_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBasisFormulaContract ι V)
    (v : ι → ℝ) :
    B.primeForm (B.boundaryRows.synth v) =
      Q3.Proofs.quadForm B.primeExpansion.M v := by
  change B.primeForm (B.basisExpansion.synth v) =
    Q3.Proofs.quadForm B.primeExpansion.M v
  rw [B.primeForm_eq v]
  rw [← B.prime_basisExpansion_eq]
  exact B.primeExpansion.form_synth_eq_quadForm v

/-- Convert basis-level formulas into the Step 32B formula contract. -/
def toFormulaContract
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBasisFormulaContract ι V) :
    BSplineFormulaContract ι V where
  boundaryRows := B.boundaryRows
  A := B.archExpansion.M
  P := B.primeExpansion.M
  archForm := B.archForm
  primeForm := B.primeForm
  weilForm := B.weilForm
  arch_ident := B.arch_ident
  prime_ident := B.prime_ident
  weil_split := B.weil_split

/-- Basis-level formulas produce the Step 31 finite matrix-to-Weil model. -/
def toFiniteWeilMatrixModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBasisFormulaContract ι V) :
    FiniteWeilMatrixModel
      (V := V)
      B.toFormulaContract.C
      B.toFormulaContract.boundaryRows.Q :=
  B.toFormulaContract.toFiniteWeilMatrixModel

end BSplineBasisFormulaContract

end PSDpd
end Q3
