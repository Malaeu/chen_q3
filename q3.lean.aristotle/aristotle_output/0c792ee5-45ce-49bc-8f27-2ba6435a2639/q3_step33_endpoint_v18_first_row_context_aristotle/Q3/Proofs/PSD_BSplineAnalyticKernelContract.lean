import Q3.Proofs.PSD_BSplineEntryExpansion
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd

/-!
B-spline analytic kernel contract.

Steps 32A--32C reduce the matrix-identification problem to basis-level data.
This file gives the last theorem-facing contract before the genuine analytic
work:

* boundary rows are the concrete exponential rows `exp(±u_i/2)`, up to nonzero
  global row scales;
* Arch and prime matrices are built from kernels whose entries are identified
  with basis pairings.

The next file should prove the actual B-spline transform and correlation
formulas that instantiate this contract.
-/

/-- The plus boundary row attached to packet centers. -/
def bsplineBoundaryPlusRow {ι : Type*} (center : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (center i / 2)

/-- The minus boundary row attached to packet centers. -/
def bsplineBoundaryMinusRow {ι : Type*} (center : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (-(center i) / 2)

/-- Turn a two-variable kernel into a finite matrix. -/
def matrixOfKernel {ι : Type*} (K : ι → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K i j

/--
Basis-pairing data for a packet kernel.

The convention matches `PacketBilinearMatrixExpansion`: the first matrix index
is the row/evaluation slot and the second index is the coefficient slot, so

\[
K_{ij}=B(\psi_j,\psi_i).
\]
-/
structure PacketKernelPairingData
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  basisExpansion : PacketBasisExpansion ι V
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  kernel : ι → ι → ℝ
  pairing_ident :
    ∀ i j : ι,
      kernel i j = form (basisExpansion.basis j) (basisExpansion.basis i)

namespace PacketKernelPairingData

/-- Matrix associated to a packet kernel. -/
def matrix
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketKernelPairingData ι V) : Matrix ι ι ℝ :=
  matrixOfKernel K.kernel

/-- Convert kernel-pairing data into the Step 32C bilinear matrix expansion. -/
def toBilinearMatrixExpansion
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketKernelPairingData ι V) :
    PacketBilinearMatrixExpansion ι V where
  basisExpansion := K.basisExpansion
  form := K.form
  M := K.matrix
  entry_ident := by
    intro i j
    exact K.pairing_ident i j

/-- Kernel-pairing data expands to a quadratic matrix form on synthesized
packets. -/
theorem form_synth_eq_quadForm
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketKernelPairingData ι V) (v : ι → ℝ) :
    K.form (K.basisExpansion.synth v) (K.basisExpansion.synth v) =
      Q3.Proofs.quadForm K.matrix v :=
  K.toBilinearMatrixExpansion.form_synth_eq_quadForm v

end PacketKernelPairingData

/--
Analytic kernel contract for a B-spline packet block.

This is the intended landing surface for the concrete Step 32D/32E analytic
formulas:

* `center i = u_i`;
* `boundaryPlus_basis` and `boundaryMinus_basis` come from the B-spline packet
  transform at \(z=\pm 1/2\);
* `archKernel` comes from the Arch integral pairings;
* `primeKernel` comes from the prime-shift correlation identity.
-/
structure BSplineAnalyticKernelContract
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  center : ι → ℝ
  basisExpansion : PacketBasisExpansion ι V
  boundary : BoundaryPair V
  scalePlus : ℝ
  scaleMinus : ℝ
  scalePlus_ne_zero : scalePlus ≠ 0
  scaleMinus_ne_zero : scaleMinus ≠ 0
  boundaryPlus_basis :
    ∀ i : ι,
      boundary.evalPlus (basisExpansion.basis i) =
        scalePlus * bsplineBoundaryPlusRow center i
  boundaryMinus_basis :
    ∀ i : ι,
      boundary.evalMinus (basisExpansion.basis i) =
        scaleMinus * bsplineBoundaryMinusRow center i
  archKernel : PacketKernelPairingData ι V
  primeKernel : PacketKernelPairingData ι V
  arch_basisExpansion_eq :
    archKernel.basisExpansion = basisExpansion
  prime_basisExpansion_eq :
    primeKernel.basisExpansion = basisExpansion
  archForm : V → ℝ
  primeForm : V → ℝ
  weilForm : V → ℝ
  archForm_eq :
    ∀ v : ι → ℝ,
      archForm (basisExpansion.synth v) =
        archKernel.form (basisExpansion.synth v) (basisExpansion.synth v)
  primeForm_eq :
    ∀ v : ι → ℝ,
      primeForm (basisExpansion.synth v) =
        primeKernel.form (basisExpansion.synth v) (basisExpansion.synth v)
  weil_split :
    ∀ v : ι → ℝ,
      weilForm (basisExpansion.synth v) =
        archForm (basisExpansion.synth v) - primeForm (basisExpansion.synth v)

namespace BSplineAnalyticKernelContract

/-- Convert the analytic kernel contract into the Step 32C basis formula
contract. -/
def toBasisFormulaContract
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineAnalyticKernelContract ι V) :
    BSplineBasisFormulaContract ι V where
  basisExpansion := B.basisExpansion
  boundary := B.boundary
  qPlus := bsplineBoundaryPlusRow B.center
  qMinus := bsplineBoundaryMinusRow B.center
  scalePlus := B.scalePlus
  scaleMinus := B.scaleMinus
  scalePlus_ne_zero := B.scalePlus_ne_zero
  scaleMinus_ne_zero := B.scaleMinus_ne_zero
  boundaryPlus_basis := B.boundaryPlus_basis
  boundaryMinus_basis := B.boundaryMinus_basis
  archExpansion := B.archKernel.toBilinearMatrixExpansion
  primeExpansion := B.primeKernel.toBilinearMatrixExpansion
  arch_basisExpansion_eq := B.arch_basisExpansion_eq
  prime_basisExpansion_eq := B.prime_basisExpansion_eq
  archForm := B.archForm
  primeForm := B.primeForm
  weilForm := B.weilForm
  archForm_eq := B.archForm_eq
  primeForm_eq := B.primeForm_eq
  weil_split := B.weil_split

/-- Convert the analytic kernel contract all the way to the Step 32B formula
contract. -/
def toFormulaContract
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineAnalyticKernelContract ι V) :
    BSplineFormulaContract ι V :=
  B.toBasisFormulaContract.toFormulaContract

/-- Convert the analytic kernel contract all the way to the Step 31 finite
matrix-to-Weil model. -/
def toFiniteWeilMatrixModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineAnalyticKernelContract ι V) :
    FiniteWeilMatrixModel
      (V := V)
      B.toFormulaContract.C
      B.toFormulaContract.boundaryRows.Q :=
  B.toFormulaContract.toFiniteWeilMatrixModel

/-- The analytic kernel contract identifies the synthesized Weil form with the
finite matrix assembled from the Arch and prime kernels. -/
theorem weil_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineAnalyticKernelContract ι V) :
    ∀ v : ι → ℝ,
      B.weilForm (B.basisExpansion.synth v) =
        Q3.Proofs.quadForm B.toFormulaContract.C v :=
  B.toFormulaContract.weil_ident

end BSplineAnalyticKernelContract

end PSDpd
end Q3
