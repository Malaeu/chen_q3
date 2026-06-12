import Q3.Proofs.PSD_BSplineMatrixIdentification
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
B-spline packet formula contract.

Step 32A added a receiver for B-spline packet entry identities.  This file
pushes one layer closer to the concrete B-spline formulas while staying honest:
it does not prove the special-function identities yet, but it discharges the
finite algebra that those identities should feed.

The two useful reductions here are:

* the boundary matrix really has two rows, up to nonzero row scalings;
* the full Weil matrix can be supplied as the entrywise difference `A - P`,
  and the quadratic-form identity `C = A - P` is then automatic.
-/

/-- Entrywise matrix difference. -/
def matrixSub {ι : Type*} (A P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j - P i j

/-- Quadratic forms respect entrywise matrix subtraction. -/
theorem quadForm_matrixSub
    {ι : Type*} [Fintype ι]
    (A P : Matrix ι ι ℝ) (v : ι → ℝ) :
    Q3.Proofs.quadForm (matrixSub A P) v =
      Q3.Proofs.quadForm A v - Q3.Proofs.quadForm P v := by
  unfold Q3.Proofs.quadForm matrixSub
  simp_rw [sub_eq_add_neg]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp [Finset.sum_neg_distrib]

/-- The concrete two-row boundary matrix used by the PSD-pd finite blocks. -/
def twoRowBoundaryMatrix {ι : Type*}
    (qPlus qMinus : ι → ℝ) : Matrix (Fin 2) ι ℝ :=
  fun r i => if r = 0 then qPlus i else qMinus i

@[simp] theorem twoRowBoundaryMatrix_zero
    {ι : Type*} (qPlus qMinus : ι → ℝ) (i : ι) :
    twoRowBoundaryMatrix qPlus qMinus 0 i = qPlus i := by
  simp [twoRowBoundaryMatrix]

@[simp] theorem twoRowBoundaryMatrix_one
    {ι : Type*} (qPlus qMinus : ι → ℝ) (i : ι) :
    twoRowBoundaryMatrix qPlus qMinus 1 i = qMinus i := by
  simp [twoRowBoundaryMatrix]

/--
Boundary-row formula data for a B-spline packet.

The intended concrete input is:

* `qPlus j = exp(u_j / 2)`;
* `qMinus j = exp(-u_j / 2)`;
* `boundary.evalPlus (synth v) = scalePlus * sum_j qPlus j * v j`;
* `boundary.evalMinus (synth v) = scaleMinus * sum_j qMinus j * v j`.

The row scales absorb harmless nonzero constants such as
`\sqrt{\ell} E_{\ell,k}(±1/2)`.
-/
structure BSplineBoundaryRows
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  synth : (ι → ℝ) → V
  boundary : BoundaryPair V
  qPlus : ι → ℝ
  qMinus : ι → ℝ
  scalePlus : ℝ
  scaleMinus : ℝ
  scalePlus_ne_zero : scalePlus ≠ 0
  scaleMinus_ne_zero : scaleMinus ≠ 0
  boundaryPlus_formula :
    ∀ v : ι → ℝ,
      boundary.evalPlus (synth v) =
        scalePlus * ∑ i, qPlus i * v i
  boundaryMinus_formula :
    ∀ v : ι → ℝ,
      boundary.evalMinus (synth v) =
        scaleMinus * ∑ i, qMinus i * v i

namespace BSplineBoundaryRows

/-- The two-row matrix attached to a boundary-row formula package. -/
def Q
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBoundaryRows ι V) : Matrix (Fin 2) ι ℝ :=
  twoRowBoundaryMatrix B.qPlus B.qMinus

/-- Plus boundary vanishing kills the plus matrix row. -/
theorem plus_row_zero_of_boundary_zero
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBoundaryRows ι V) (v : ι → ℝ)
    (hPlus : B.boundary.evalPlus (B.synth v) = 0) :
    ∑ i, B.qPlus i * v i = 0 := by
  have hmul : B.scalePlus * ∑ i, B.qPlus i * v i = 0 := by
    simpa [B.boundaryPlus_formula v] using hPlus
  exact (mul_eq_zero.mp hmul).resolve_left B.scalePlus_ne_zero

/-- Minus boundary vanishing kills the minus matrix row. -/
theorem minus_row_zero_of_boundary_zero
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBoundaryRows ι V) (v : ι → ℝ)
    (hMinus : B.boundary.evalMinus (B.synth v) = 0) :
    ∑ i, B.qMinus i * v i = 0 := by
  have hmul : B.scaleMinus * ∑ i, B.qMinus i * v i = 0 := by
    simpa [B.boundaryMinus_formula v] using hMinus
  exact (mul_eq_zero.mp hmul).resolve_left B.scaleMinus_ne_zero

/--
Analytic boundary-null packets land in the concrete two-row matrix kernel.
-/
theorem analyticBoundary_to_matrixBoundary
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineBoundaryRows ι V) (v : ι → ℝ)
    (hPlus : B.boundary.evalPlus (B.synth v) = 0)
    (hMinus : B.boundary.evalMinus (B.synth v) = 0) :
    Q3.Proofs.BoundaryNull B.Q v := by
  intro r
  fin_cases r
  · simpa [Q] using B.plus_row_zero_of_boundary_zero v hPlus
  · simpa [Q] using B.minus_row_zero_of_boundary_zero v hMinus

end BSplineBoundaryRows

/--
Concrete formula-level receiver for one B-spline packet block.

Compared with `BSplinePacketEntryData`, this record no longer asks for the
boundary-kernel implication or for the quadratic-form identity `C = A - P`.
Those are discharged by `BSplineBoundaryRows` and `quadForm_matrixSub`.
-/
structure BSplineFormulaContract
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  boundaryRows : BSplineBoundaryRows ι V
  A : Matrix ι ι ℝ
  P : Matrix ι ι ℝ
  archForm : V → ℝ
  primeForm : V → ℝ
  weilForm : V → ℝ
  arch_ident :
    ∀ v : ι → ℝ,
      archForm (boundaryRows.synth v) = Q3.Proofs.quadForm A v
  prime_ident :
    ∀ v : ι → ℝ,
      primeForm (boundaryRows.synth v) = Q3.Proofs.quadForm P v
  weil_split :
    ∀ v : ι → ℝ,
      weilForm (boundaryRows.synth v) =
        archForm (boundaryRows.synth v) - primeForm (boundaryRows.synth v)

namespace BSplineFormulaContract

/-- The full Weil matrix supplied by the concrete formula contract. -/
def C
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineFormulaContract ι V) : Matrix ι ι ℝ :=
  matrixSub B.A B.P

/-- Convert the concrete formula contract into the Step 32A entry receiver. -/
def toEntryData
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineFormulaContract ι V) :
    BSplinePacketEntryData (Fin 2) ι V where
  A := B.A
  P := B.P
  C := B.C
  Q := B.boundaryRows.Q
  synth := B.boundaryRows.synth
  archForm := B.archForm
  primeForm := B.primeForm
  weilForm := B.weilForm
  boundary := B.boundaryRows.boundary
  arch_ident := B.arch_ident
  prime_ident := B.prime_ident
  weil_split := B.weil_split
  C_ident := by
    intro v
    exact quadForm_matrixSub B.A B.P v
  analyticBoundary_to_matrixBoundary := by
    intro v hPlus hMinus
    exact B.boundaryRows.analyticBoundary_to_matrixBoundary v hPlus hMinus

/-- Formula contracts produce the Step 31 finite matrix-to-Weil model. -/
def toFiniteWeilMatrixModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineFormulaContract ι V) :
    FiniteWeilMatrixModel (V := V) B.C B.boundaryRows.Q :=
  B.toEntryData.toFiniteWeilMatrixModel

/-- Formula contracts identify the analytic Weil form with `vᵀ(A-P)v`. -/
theorem weil_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineFormulaContract ι V) :
    ∀ v : ι → ℝ,
      B.weilForm (B.boundaryRows.synth v) =
        Q3.Proofs.quadForm B.C v :=
  B.toEntryData.weil_ident

end BSplineFormulaContract

end PSDpd
end Q3
