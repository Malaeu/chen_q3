import Q3.Proofs.PSD_BSplineAnalyticKernelContract
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd

/-!
B-spline translated-packet identities.

Step 32D records the analytic kernel contract needed by the finite PSD-pd
certificate.  This file proves the next real reduction: for a packet basis made
from translates of one bump, the concrete exponential boundary rows and
difference-kernel matrix entries follow from translation covariance.

The remaining analytic work is now localized to proving those covariance laws
for the actual B-spline bump and the Arch/prime pairings.
-/

/--
Boundary transform data for translated packets.

The intended analytic model is:

* `basis i = translate (center i) base`;
* `E_+(translate u f) = exp(u/2) E_+(f)`;
* `E_-(translate u f) = exp(-u/2) E_-(f)`.

The nonzero base boundary values become the harmless row scales in
`BSplineAnalyticKernelContract`.
-/
structure PacketTranslationBoundaryData
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  center : ι → ℝ
  basisExpansion : PacketBasisExpansion ι V
  boundary : BoundaryPair V
  base : V
  translate : ℝ → V → V
  basis_eq_translate :
    ∀ i : ι, basisExpansion.basis i = translate (center i) base
  boundaryPlus_translate :
    ∀ (u : ℝ) (f : V),
      boundary.evalPlus (translate u f) =
        Real.exp (u / 2) * boundary.evalPlus f
  boundaryMinus_translate :
    ∀ (u : ℝ) (f : V),
      boundary.evalMinus (translate u f) =
        Real.exp (-(u) / 2) * boundary.evalMinus f
  basePlus_ne_zero : boundary.evalPlus base ≠ 0
  baseMinus_ne_zero : boundary.evalMinus base ≠ 0

namespace PacketTranslationBoundaryData

/-- Plus-row scale: the boundary value of the untranslated bump. -/
def scalePlus
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) : ℝ :=
  B.boundary.evalPlus B.base

/-- Minus-row scale: the boundary value of the untranslated bump. -/
def scaleMinus
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) : ℝ :=
  B.boundary.evalMinus B.base

theorem scalePlus_ne_zero'
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) :
    B.scalePlus ≠ 0 :=
  B.basePlus_ne_zero

theorem scaleMinus_ne_zero'
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) :
    B.scaleMinus ≠ 0 :=
  B.baseMinus_ne_zero

/-- Translation covariance gives the concrete plus boundary row. -/
theorem boundaryPlus_basis
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) (i : ι) :
    B.boundary.evalPlus (B.basisExpansion.basis i) =
      B.scalePlus * bsplineBoundaryPlusRow B.center i := by
  rw [B.basis_eq_translate i, B.boundaryPlus_translate]
  simp [scalePlus, bsplineBoundaryPlusRow, mul_comm]

/-- Translation covariance gives the concrete minus boundary row. -/
theorem boundaryMinus_basis
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : PacketTranslationBoundaryData ι V) (i : ι) :
    B.boundary.evalMinus (B.basisExpansion.basis i) =
      B.scaleMinus * bsplineBoundaryMinusRow B.center i := by
  rw [B.basis_eq_translate i, B.boundaryMinus_translate]
  simp [scaleMinus, bsplineBoundaryMinusRow, mul_comm]

end PacketTranslationBoundaryData

/--
Kernel pairing data for translated packets.

The intended model is a translation-invariant/difference kernel:

`form (translate u base) (translate v base) = profile (u - v)`.

With the Step 32C convention `K i j = form (basis j) (basis i)`, the finite
matrix entry is therefore `profile (center j - center i)`.
-/
structure PacketTranslationKernelData
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  center : ι → ℝ
  basisExpansion : PacketBasisExpansion ι V
  base : V
  translate : ℝ → V → V
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  profile : ℝ → ℝ
  basis_eq_translate :
    ∀ i : ι, basisExpansion.basis i = translate (center i) base
  pairing_translate_ident :
    ∀ u v : ℝ,
      form (translate u base) (translate v base) = profile (u - v)

/-- Bundle an unbundled real bilinear pairing into the curried `LinearMap`
shape expected by the finite packet receivers. -/
def realBilinearFormOfPairing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (map_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (map_smul_left : ∀ (c : ℝ) (x z : V), B (c • x) z = c * B x z)
    (map_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (map_smul_right : ∀ (c : ℝ) (x y : V), B x (c • y) = c * B x y) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => B x y
      map_add' := by
        intro y z
        exact map_add_right x y z
      map_smul' := by
        intro c y
        exact map_smul_right c x y }
  map_add' := by
    intro x y
    ext z
    exact map_add_left x y z
  map_smul' := by
    intro c x
    ext z
    exact map_smul_left c x z

namespace PacketTranslationKernelData

/-- Build translated-kernel data from an unbundled bilinear pairing plus its
linearity laws.  This keeps analytic pairings easy to state while still
feeding the bundled linear-map API used by the finite matrix layer. -/
def ofPairing
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (center : ι → ℝ)
    (basisExpansion : PacketBasisExpansion ι V)
    (base : V)
    (translate : ℝ → V → V)
    (B : V → V → ℝ)
    (profile : ℝ → ℝ)
    (map_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (map_smul_left : ∀ (c : ℝ) (x z : V), B (c • x) z = c * B x z)
    (map_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (map_smul_right : ∀ (c : ℝ) (x y : V), B x (c • y) = c * B x y)
    (basis_eq_translate :
      ∀ i : ι, basisExpansion.basis i = translate (center i) base)
    (pairing_translate_ident :
      ∀ u v : ℝ, B (translate u base) (translate v base) = profile (u - v)) :
    PacketTranslationKernelData ι V where
  center := center
  basisExpansion := basisExpansion
  base := base
  translate := translate
  form :=
    realBilinearFormOfPairing B
      map_add_left map_smul_left map_add_right map_smul_right
  profile := profile
  basis_eq_translate := basis_eq_translate
  pairing_translate_ident := pairing_translate_ident

/-- Difference-kernel matrix associated to translated packet pairings. -/
def kernel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketTranslationKernelData ι V) : ι → ι → ℝ :=
  fun i j => K.profile (K.center j - K.center i)

/-- Translation covariance identifies the kernel entries with basis pairings. -/
theorem pairing_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketTranslationKernelData ι V) :
    ∀ i j : ι,
      K.kernel i j =
        K.form (K.basisExpansion.basis j) (K.basisExpansion.basis i) := by
  intro i j
  rw [K.basis_eq_translate j, K.basis_eq_translate i]
  simp [kernel, K.pairing_translate_ident]

/-- Difference-kernel data feeds the Step 32D packet-kernel pairing receiver. -/
def toPacketKernelPairingData
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketTranslationKernelData ι V) :
    PacketKernelPairingData ι V where
  basisExpansion := K.basisExpansion
  form := K.form
  kernel := K.kernel
  pairing_ident := K.pairing_ident

end PacketTranslationKernelData

/--
Translated-packet analytic contract.

This packages boundary translation covariance together with Arch and prime
difference-kernel pairings.  It constructs the Step 32D
`BSplineAnalyticKernelContract` without any additional finite algebra.
-/
structure BSplineTranslatedAnalyticContract
    (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℝ V] where
  boundaryData : PacketTranslationBoundaryData ι V
  archData : PacketTranslationKernelData ι V
  primeData : PacketTranslationKernelData ι V
  arch_basisExpansion_eq :
    archData.basisExpansion = boundaryData.basisExpansion
  prime_basisExpansion_eq :
    primeData.basisExpansion = boundaryData.basisExpansion
  archForm : V → ℝ
  primeForm : V → ℝ
  weilForm : V → ℝ
  archForm_eq :
    ∀ v : ι → ℝ,
      archForm (boundaryData.basisExpansion.synth v) =
        archData.form
          (boundaryData.basisExpansion.synth v)
          (boundaryData.basisExpansion.synth v)
  primeForm_eq :
    ∀ v : ι → ℝ,
      primeForm (boundaryData.basisExpansion.synth v) =
        primeData.form
          (boundaryData.basisExpansion.synth v)
          (boundaryData.basisExpansion.synth v)
  weil_split :
    ∀ v : ι → ℝ,
      weilForm (boundaryData.basisExpansion.synth v) =
        archForm (boundaryData.basisExpansion.synth v)
          - primeForm (boundaryData.basisExpansion.synth v)

namespace BSplineTranslatedAnalyticContract

/--
Translated-packet covariance data instantiates the Step 32D analytic kernel
contract.
-/
def toAnalyticKernelContract
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineTranslatedAnalyticContract ι V) :
    BSplineAnalyticKernelContract ι V where
  center := B.boundaryData.center
  basisExpansion := B.boundaryData.basisExpansion
  boundary := B.boundaryData.boundary
  scalePlus := B.boundaryData.scalePlus
  scaleMinus := B.boundaryData.scaleMinus
  scalePlus_ne_zero := B.boundaryData.scalePlus_ne_zero'
  scaleMinus_ne_zero := B.boundaryData.scaleMinus_ne_zero'
  boundaryPlus_basis := B.boundaryData.boundaryPlus_basis
  boundaryMinus_basis := B.boundaryData.boundaryMinus_basis
  archKernel := B.archData.toPacketKernelPairingData
  primeKernel := B.primeData.toPacketKernelPairingData
  arch_basisExpansion_eq := B.arch_basisExpansion_eq
  prime_basisExpansion_eq := B.prime_basisExpansion_eq
  archForm := B.archForm
  primeForm := B.primeForm
  weilForm := B.weilForm
  archForm_eq := B.archForm_eq
  primeForm_eq := B.primeForm_eq
  weil_split := B.weil_split

/-- Translated-packet analytic data gives the final finite Weil matrix model. -/
def toFiniteWeilMatrixModel
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineTranslatedAnalyticContract ι V) :
    FiniteWeilMatrixModel
      (V := V)
      B.toAnalyticKernelContract.toFormulaContract.C
      B.toAnalyticKernelContract.toFormulaContract.boundaryRows.Q :=
  B.toAnalyticKernelContract.toFiniteWeilMatrixModel

/-- The translated-packet contract identifies the synthesized Weil form with
the finite Arch-minus-prime matrix. -/
theorem weil_ident
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : BSplineTranslatedAnalyticContract ι V) :
    ∀ v : ι → ℝ,
      B.weilForm (B.boundaryData.basisExpansion.synth v) =
        Q3.Proofs.quadForm B.toAnalyticKernelContract.toFormulaContract.C v :=
  B.toAnalyticKernelContract.weil_ident

end BSplineTranslatedAnalyticContract

end PSDpd
end Q3
