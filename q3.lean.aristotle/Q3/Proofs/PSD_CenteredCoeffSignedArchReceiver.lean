import Q3.Proofs.PSD_CenteredCardinalBSpline
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import
import Q3.Proofs.PSD_CenteredCoeffBaseAHboxImport
import Q3.Proofs.PSD_CenteredCoeffDictionaryImport
import Q3.Proofs.PSD_CenteredCoeffSignedQ3AStarPayloadImport
import Q3.Proofs.PSD_MatrixIdentification

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd

open CenteredCoeffPayloadImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffBaseHboxImport
open CenteredCoeffDictionaryImport
open CenteredCoeffPenaltyImport
open CenteredCoeffPenaltyRadiusDominanceImport

/-!
Signed Arch receiver prototype for the Step33A.1-A sign-location fork.

This file does not change the existing Step32/Step33 contract.  It isolates the
minimal algebraic surface needed by route B: a finite-Weil `A` matrix whose
entries are the negative of the current `centeredBSplineArchKernelProfile`,
while the formula contract still uses `C = A - P`.
-/

/-- Negate a packet-kernel pairing package without changing the basis. -/
def negPacketKernelPairingData
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketKernelPairingData ι V) :
    PacketKernelPairingData ι V where
  basisExpansion := K.basisExpansion
  form := -K.form
  kernel := fun i j => -K.kernel i j
  pairing_ident := by
    intro i j
    simp [K.pairing_ident i j]

@[simp] theorem negPacketKernelPairingData_matrix
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (K : PacketKernelPairingData ι V) (i j : ι) :
    (negPacketKernelPairingData K).matrix i j = -K.matrix i j := by
  rfl

/-- Signed Arch packet coefficient kernel: same basis, negated Arch form. -/
def centeredBSplineSignedArchPacketCoeffKernelData
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hk : 0 < k) (hell : 0 < ell) :
    PacketKernelPairingData ι (ι → ℂ) :=
  negPacketKernelPairingData
    (centeredBSplineArchPacketCoeffKernelData k ell center hk hell)

theorem centeredBSplineSignedArchPacketCoeffKernelData_matrix_entry
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hk : 0 < k) (hell : 0 < ell)
    (i j : ι) :
    (centeredBSplineSignedArchPacketCoeffKernelData k ell center hk hell).matrix i j =
      -centeredBSplineArchKernelProfile k ell (center j - center i) := by
  rfl

/--
Signed coefficient-space analytic kernel contract.

This is the route-B prototype: the finite-Weil Arch `A` is the negative of the
current Arch profile, and `C = A - P` is kept by `BSplineFormulaContract`.
-/
def centeredBSplineSignedCoeffAnalyticKernelContract
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    BSplineAnalyticKernelContract ι (ι → ℂ) where
  center := center
  basisExpansion := centeredBSplineCoeffBasisExpansion
  boundary := centeredBSplineCoeffBoundaryPair center
  scalePlus := 1
  scaleMinus := 1
  scalePlus_ne_zero := by norm_num
  scaleMinus_ne_zero := by norm_num
  boundaryPlus_basis := by
    intro i
    simpa using centeredBSplineCoeffBoundaryPair_evalPlus_basis center i
  boundaryMinus_basis := by
    intro i
    simpa using centeredBSplineCoeffBoundaryPair_evalMinus_basis center i
  archKernel := centeredBSplineSignedArchPacketCoeffKernelData k ell center hk hell
  primeKernel := centeredBSplineFinitePrimePacketCoeffKernelData k ell center weight shift
  arch_basisExpansion_eq := rfl
  prime_basisExpansion_eq := rfl
  archForm := fun x =>
    -((centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell) x x)
  primeForm := fun x =>
    (centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift) x x
  weilForm := fun x =>
    -((centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell) x x) -
      (centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift) x x
  archForm_eq := by
    intro v
    rfl
  primeForm_eq := by
    intro v
    rfl
  weil_split := by
    intro v
    rfl

/-- The signed coefficient contract identifies the signed Weil form with
`(-Arch) - Prime` as `matrixSub signedA P`. -/
theorem centeredBSplineSignedCoeffWeilForm_eq_matrixSub_quadForm
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) (v : ι → ℝ) :
    (centeredBSplineSignedCoeffAnalyticKernelContract
      k ell center weight shift hk hell).weilForm
        ((centeredBSplineCoeffBasisExpansion (ι := ι)).synth v) =
      Q3.Proofs.quadForm
        (matrixSub
          (centeredBSplineSignedArchPacketCoeffKernelData
            k ell center hk hell).matrix
          (centeredBSplineFinitePrimePacketCoeffKernelData
            k ell center weight shift).matrix) v := by
  simpa [centeredBSplineSignedCoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    BSplineFormulaContract.C] using
      (centeredBSplineSignedCoeffAnalyticKernelContract
        k ell center weight shift hk hell).weil_ident v

/-!
Concrete primary/control signed surfaces.

These definitions do not replace the current positive Arch dictionaries.  They
name the route-B finite-Weil convention explicitly so downstream hbox receivers
can target a signed `A` matrix without pretending that the existing
`primaryK11AnalyticA` / `controlK9AnalyticA` changed sign.
-/

/-- Concrete signed analytic contract for the active primary block. -/
noncomputable def primaryK11SignedCoeffAnalyticKernelContract :
    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 → Complex) :=
  centeredBSplineSignedCoeffAnalyticKernelContract
    11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
    primaryK11_hk primaryK11_hell

/-- Concrete signed analytic contract for the active control block. -/
noncomputable def controlK9SignedCoeffAnalyticKernelContract :
    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 → Complex) :=
  centeredBSplineSignedCoeffAnalyticKernelContract
    9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
    controlK9_hk controlK9_hell

/-- Signed primary finite-Weil Arch matrix. -/
def primaryK11SignedAnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.A

/-- Signed primary finite-Weil prime matrix, unchanged from the prime source. -/
def primaryK11SignedAnalyticP : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.P

/-- Signed primary finite-Weil `C = A - P`. -/
def primaryK11SignedAnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.C

/-- Signed control finite-Weil Arch matrix. -/
def controlK9SignedAnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.A

/-- Signed control finite-Weil prime matrix, unchanged from the prime source. -/
def controlK9SignedAnalyticP : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.P

/-- Signed control finite-Weil `C = A - P`. -/
def controlK9SignedAnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.C

/-- Parallel signed primary `A` payload: sign-transport of the legacy positive table. -/
def primaryK11SignedA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => -primaryK11A i j

/-- Signed primary `A` payload radius; sign transport does not change radii. -/
def primaryK11SignedARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11ARadius

/-- Parallel signed control `A` payload: sign-transport of the legacy positive table. -/
def controlK9SignedA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => -controlK9A i j

/-- Signed control `A` payload radius; sign transport does not change radii. -/
def controlK9SignedARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9ARadius

/-!
Canonical signed-Q3.a_star payload surface.

Louise route B rejects the finite recert attempt for `-current Step22 A`.
The signed finite-Weil receiver is canonical, but the payload source must be
the transformed `Q3.a_star` candidate.  These names keep that data path separate
from the legacy Step22 midpoint table above.
-/

def centeredBSplineSignedFiniteWeilAProfile (k : Nat) (ell x : Real) : Real :=
  -centeredBSplineArchKernelProfile k ell x

theorem centeredBSplineSignedFiniteWeilAProfile_eq_neg_q3AStarProfile
    (k : Nat) (ell x : Real) :
    centeredBSplineSignedFiniteWeilAProfile k ell x =
      -centeredBSplineArchKernelProfile k ell x := by
  rfl

theorem centeredBSplineSignedAnalyticAProfile_eq_neg_Q3_a_star
    (k : Nat) (ell x : Real) :
    centeredBSplineSignedFiniteWeilAProfile k ell x =
      -(∫ t : Real,
          Q3.a_star t *
            (ell * Real.cos (t * x) *
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)) := by
  rfl

def primaryK11SignedQ3AStarA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarA

def primaryK11SignedQ3AStarARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarARadius

def controlK9SignedQ3AStarA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarA

def controlK9SignedQ3AStarARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarARadius

def primaryK11SignedQ3AStarR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarR

def primaryK11SignedQ3AStarD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarD

def controlK9SignedQ3AStarR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarR

def controlK9SignedQ3AStarD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarD

def primaryK11SignedQ3AStarRBaseRadius :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarRBaseRadius

def primaryK11SignedQ3AStarDBaseRadius :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarDBaseRadius

def controlK9SignedQ3AStarRBaseRadius :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarRBaseRadius

def controlK9SignedQ3AStarDBaseRadius :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarDBaseRadius

theorem primaryK11SignedAnalyticA_entry (i j : CoeffIndex23) :
    primaryK11SignedAnalyticA i j =
      -centeredBSplineArchKernelProfile
        11 primaryK11Ell (primaryK11Center j - primaryK11Center i) := by
  simpa [primaryK11SignedAnalyticA, primaryK11SignedCoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion] using
      (centeredBSplineSignedArchPacketCoeffKernelData_matrix_entry
        11 primaryK11Ell primaryK11Center primaryK11_hk primaryK11_hell i j)

theorem controlK9SignedAnalyticA_entry (i j : CoeffIndex23) :
    controlK9SignedAnalyticA i j =
      -centeredBSplineArchKernelProfile
        9 controlK9Ell (controlK9Center j - controlK9Center i) := by
  simpa [controlK9SignedAnalyticA, controlK9SignedCoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion] using
      (centeredBSplineSignedArchPacketCoeffKernelData_matrix_entry
        9 controlK9Ell controlK9Center controlK9_hk controlK9_hell i j)

theorem primaryK11SignedAnalyticA_entry_index_delta (i j : CoeffIndex23) :
    primaryK11SignedAnalyticA i j =
      -centeredBSplineArchKernelProfile
        11 primaryK11Ell (((j.1 : Real) - (i.1 : Real)) / 4) := by
  rw [primaryK11SignedAnalyticA_entry,
    primaryK11Center_sub_eq_index_delta]

theorem controlK9SignedAnalyticA_entry_index_delta (i j : CoeffIndex23) :
    controlK9SignedAnalyticA i j =
      -centeredBSplineArchKernelProfile
        9 controlK9Ell (((j.1 : Real) - (i.1 : Real)) / 4) := by
  rw [controlK9SignedAnalyticA_entry,
    controlK9Center_sub_eq_index_delta]

theorem primaryK11SignedAnalyticA_entry_signedFiniteWeilProfile
    (i j : CoeffIndex23) :
    primaryK11SignedAnalyticA i j =
      centeredBSplineSignedFiniteWeilAProfile
        11 primaryK11Ell (primaryK11Center j - primaryK11Center i) := by
  rw [primaryK11SignedAnalyticA_entry]
  rfl

theorem controlK9SignedAnalyticA_entry_signedFiniteWeilProfile
    (i j : CoeffIndex23) :
    controlK9SignedAnalyticA i j =
      centeredBSplineSignedFiniteWeilAProfile
        9 controlK9Ell (controlK9Center j - controlK9Center i) := by
  rw [controlK9SignedAnalyticA_entry]
  rfl

/-- Negating both center and point preserves an entry hbox radius. -/
lemma hbox_neg_of_hbox
    {x c r : Real}
    (h : |x - c| ≤ r) :
    |(-x) - (-c)| ≤ r := by
  have hx : (-x) - (-c) = -(x - c) := by
    ring
  rw [hx, abs_neg]
  exact h

theorem primaryK11SignedAnalyticA_eq_neg_positiveAnalyticA
    (i j : CoeffIndex23) :
    primaryK11SignedAnalyticA i j =
      -CenteredCoeffBaseHboxImport.primaryK11AnalyticA i j := by
  rw [primaryK11SignedAnalyticA_entry,
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry]

theorem controlK9SignedAnalyticA_eq_neg_positiveAnalyticA
    (i j : CoeffIndex23) :
    controlK9SignedAnalyticA i j =
      -CenteredCoeffBaseHboxImport.controlK9AnalyticA i j := by
  rw [controlK9SignedAnalyticA_entry,
    CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry]

/-- Generator-facing signed primary `A` hbox certificate over index deltas. -/
structure primaryK11SignedAnalyticADeltaHboxCert : Prop where
  h : ∀ i j : CoeffIndex23,
    |-centeredBSplineArchKernelProfile
        11 primaryK11Ell (((j.1 : Real) - (i.1 : Real)) / 4) -
      primaryK11SignedA i j| ≤ primaryK11SignedARadius i j

/-- Generator-facing signed control `A` hbox certificate over index deltas. -/
structure controlK9SignedAnalyticADeltaHboxCert : Prop where
  h : ∀ i j : CoeffIndex23,
    |-centeredBSplineArchKernelProfile
        9 controlK9Ell (((j.1 : Real) - (i.1 : Real)) / 4) -
      controlK9SignedA i j| ≤ controlK9SignedARadius i j

theorem primaryK11SignedAnalyticA_entry_hbox_of_delta_cert
    (cert : primaryK11SignedAnalyticADeltaHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA primaryK11SignedA primaryK11SignedARadius := by
  intro i j
  rw [primaryK11SignedAnalyticA_entry_index_delta]
  exact cert.h i j

theorem controlK9SignedAnalyticA_entry_hbox_of_delta_cert
    (cert : controlK9SignedAnalyticADeltaHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA controlK9SignedA controlK9SignedARadius := by
  intro i j
  rw [controlK9SignedAnalyticA_entry_index_delta]
  exact cert.h i j

/-- Generator-facing signed-Q3.a_star primary `A` hbox certificate. -/
structure primaryK11SignedQ3AStarAnalyticADeltaHboxCert : Prop where
  h : ∀ i j : CoeffIndex23,
    |-centeredBSplineArchKernelProfile
        11 primaryK11Ell (((j.1 : Real) - (i.1 : Real)) / 4) -
      primaryK11SignedQ3AStarA i j| ≤ primaryK11SignedQ3AStarARadius i j

/-- Generator-facing signed-Q3.a_star control `A` hbox certificate. -/
structure controlK9SignedQ3AStarAnalyticADeltaHboxCert : Prop where
  h : ∀ i j : CoeffIndex23,
    |-centeredBSplineArchKernelProfile
        9 controlK9Ell (((j.1 : Real) - (i.1 : Real)) / 4) -
      controlK9SignedQ3AStarA i j| ≤ controlK9SignedQ3AStarARadius i j

theorem primaryK11SignedQ3AStarAnalyticA_entry_hbox_of_delta_cert
    (cert : primaryK11SignedQ3AStarAnalyticADeltaHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA
      primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius := by
  intro i j
  rw [primaryK11SignedAnalyticA_entry_index_delta]
  exact cert.h i j

theorem controlK9SignedQ3AStarAnalyticA_entry_hbox_of_delta_cert
    (cert : controlK9SignedQ3AStarAnalyticADeltaHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA
      controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius := by
  intro i j
  rw [controlK9SignedAnalyticA_entry_index_delta]
  exact cert.h i j

theorem primaryK11SignedAnalyticA_entry_hbox_of_negatedPositivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA primaryK11SignedA primaryK11SignedARadius := by
  intro i j
  have hneg := hbox_neg_of_hbox (hpos i j)
  simpa [primaryK11SignedA, primaryK11SignedARadius,
    primaryK11SignedAnalyticA_eq_neg_positiveAnalyticA i j] using hneg

theorem controlK9SignedAnalyticA_entry_hbox_of_negatedPositivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA controlK9SignedA controlK9SignedARadius := by
  intro i j
  have hneg := hbox_neg_of_hbox (hpos i j)
  simpa [controlK9SignedA, controlK9SignedARadius,
    controlK9SignedAnalyticA_eq_neg_positiveAnalyticA i j] using hneg

theorem primaryK11SignedAnalyticADeltaHboxCert_of_negatedPositivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius) :
    primaryK11SignedAnalyticADeltaHboxCert := by
  constructor
  intro i j
  have hsigned :=
    primaryK11SignedAnalyticA_entry_hbox_of_negatedPositivePayload hpos i j
  rw [primaryK11SignedAnalyticA_entry_index_delta] at hsigned
  exact hsigned

theorem controlK9SignedAnalyticADeltaHboxCert_of_negatedPositivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius) :
    controlK9SignedAnalyticADeltaHboxCert := by
  constructor
  intro i j
  have hsigned :=
    controlK9SignedAnalyticA_entry_hbox_of_negatedPositivePayload hpos i j
  rw [controlK9SignedAnalyticA_entry_index_delta] at hsigned
  exact hsigned

theorem primaryK11SignedAnalyticC_eq_matrixSub :
    primaryK11SignedAnalyticC =
      matrixSub primaryK11SignedAnalyticA primaryK11SignedAnalyticP := by
  rfl

theorem controlK9SignedAnalyticC_eq_matrixSub :
    controlK9SignedAnalyticC =
      matrixSub controlK9SignedAnalyticA controlK9SignedAnalyticP := by
  rfl

theorem primaryK11SignedAnalyticP_eq_positiveAnalyticP
    (i j : CoeffIndex23) :
    primaryK11SignedAnalyticP i j =
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP i j := by
  rfl

theorem controlK9SignedAnalyticP_eq_positiveAnalyticP
    (i j : CoeffIndex23) :
    controlK9SignedAnalyticP i j =
      CenteredCoeffBaseHboxImport.controlK9AnalyticP i j := by
  rfl

theorem primaryK11SignedAnalyticP_entry_hbox_of_positivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP
      primaryK11P primaryK11PRadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticP primaryK11P primaryK11PRadius := by
  intro i j
  simpa [primaryK11SignedAnalyticP_eq_positiveAnalyticP i j] using hpos i j

theorem controlK9SignedAnalyticP_entry_hbox_of_positivePayload
    (hpos : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticP
      controlK9P controlK9PRadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticP controlK9P controlK9PRadius := by
  intro i j
  simpa [controlK9SignedAnalyticP_eq_positiveAnalyticP i j] using hpos i j

/-!
Signed entry-hbox bundle.

The existing `ActiveCenteredCoeffEntryHboxCert` is hardwired to the positive
Arch `A`.  Route B therefore uses a separate signed surface; downstream finite
PSD recert must consume the signed `D/R` matrices below.
-/

structure PrimaryK11SignedBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11SignedAnalyticA primaryK11SignedA primaryK11SignedARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11SignedAnalyticP primaryK11P primaryK11PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius

structure ControlK9SignedBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9SignedAnalyticA controlK9SignedA controlK9SignedARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9SignedAnalyticP controlK9P controlK9PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP0 controlK9P0 controlK9P0Radius

structure ActiveSignedAEntryHboxCert : Prop where
  primary : PrimaryK11SignedBaseEntryHboxCert
  control : ControlK9SignedBaseEntryHboxCert

structure PrimaryK11SignedQ3AStarBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11SignedAnalyticA
    primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11SignedAnalyticP primaryK11P primaryK11PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius

structure ControlK9SignedQ3AStarBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9SignedAnalyticA
    controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9SignedAnalyticP controlK9P controlK9PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP0 controlK9P0 controlK9P0Radius

structure ActiveSignedQ3AStarEntryHboxCert : Prop where
  primary : PrimaryK11SignedQ3AStarBaseEntryHboxCert
  control : ControlK9SignedQ3AStarBaseEntryHboxCert

theorem primaryK11SignedBaseEntryHboxCert_of_positive_payloads
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP
      primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    PrimaryK11SignedBaseEntryHboxCert := by
  exact PrimaryK11SignedBaseEntryHboxCert.mk
    (primaryK11SignedAnalyticA_entry_hbox_of_negatedPositivePayload hA)
    (primaryK11SignedAnalyticP_entry_hbox_of_positivePayload hP)
    hP0

theorem controlK9SignedBaseEntryHboxCert_of_positive_payloads
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticP
      controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ControlK9SignedBaseEntryHboxCert := by
  exact ControlK9SignedBaseEntryHboxCert.mk
    (controlK9SignedAnalyticA_entry_hbox_of_negatedPositivePayload hA)
    (controlK9SignedAnalyticP_entry_hbox_of_positivePayload hP)
    hP0

theorem activeSignedAEntryHboxCert_of_positive_payloads
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP
      primaryK11P primaryK11PRadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticP
      controlK9P controlK9PRadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveSignedAEntryHboxCert := by
  exact ActiveSignedAEntryHboxCert.mk
    (primaryK11SignedBaseEntryHboxCert_of_positive_payloads
      primary_hA primary_hP primary_hP0)
    (controlK9SignedBaseEntryHboxCert_of_positive_payloads
      control_hA control_hP control_hP0)

theorem primaryK11SignedQ3AStarBaseEntryHboxCert_of_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA
      primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP
      primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    PrimaryK11SignedQ3AStarBaseEntryHboxCert := by
  exact PrimaryK11SignedQ3AStarBaseEntryHboxCert.mk
    hA
    (primaryK11SignedAnalyticP_entry_hbox_of_positivePayload hP)
    hP0

theorem controlK9SignedQ3AStarBaseEntryHboxCert_of_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA
      controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticP
      controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ControlK9SignedQ3AStarBaseEntryHboxCert := by
  exact ControlK9SignedQ3AStarBaseEntryHboxCert.mk
    hA
    (controlK9SignedAnalyticP_entry_hbox_of_positivePayload hP)
    hP0

theorem signedQ3AStarActiveCenteredCoeffEntryHboxCert_of_hboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA
      primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius)
    (primary_hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticP
      primaryK11P primaryK11PRadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA
      controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius)
    (control_hP : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticP
      controlK9P controlK9PRadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveSignedQ3AStarEntryHboxCert := by
  exact ActiveSignedQ3AStarEntryHboxCert.mk
    (primaryK11SignedQ3AStarBaseEntryHboxCert_of_hboxes
      primary_hA primary_hP primary_hP0)
    (controlK9SignedQ3AStarBaseEntryHboxCert_of_hboxes
      control_hA control_hP control_hP0)

/-! Signed `D/R` surfaces for the next finite penalty recert. -/

def primaryK11SignedAnalyticRkappa
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa primaryK11SignedAnalyticA P0a primaryK11Kappa

def primaryK11SignedAnalyticDtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta primaryK11SignedAnalyticA primaryK11SignedAnalyticP P0a
    primaryK11Kappa primaryK11Theta

def primaryK11SignedAnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub primaryK11SignedAnalyticC R primaryK11Theta

def primaryK11SignedR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa primaryK11SignedA primaryK11P0 primaryK11Kappa

def primaryK11SignedD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta primaryK11SignedA primaryK11P primaryK11P0
    primaryK11Kappa primaryK11Theta

theorem primaryK11SignedAnalyticDFromR_eq_Dtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    primaryK11SignedAnalyticDFromR (primaryK11SignedAnalyticRkappa P0a) =
      primaryK11SignedAnalyticDtheta P0a := by
  ext i j
  simp [primaryK11SignedAnalyticDFromR, primaryK11SignedAnalyticC_eq_matrixSub,
    primaryK11SignedAnalyticRkappa, primaryK11SignedAnalyticDtheta,
    matrixRkappa, matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem primaryK11SignedAnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm primaryK11SignedAnalyticC v =
        Q3.Proofs.quadForm (primaryK11SignedAnalyticDFromR R) v +
          primaryK11Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold primaryK11SignedAnalyticDFromR
  exact quadForm_scaled_sub_split primaryK11SignedAnalyticC R primaryK11Theta v

theorem primaryK11SignedAnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA primaryK11SignedA primaryK11SignedARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11SignedAnalyticRkappa P0a)
      primaryK11SignedR primaryK11RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      primaryK11SignedAnalyticA primaryK11SignedA P0a primaryK11P0
      primaryK11SignedARadius primaryK11P0Radius primaryK11Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [primaryK11SignedAnalyticRkappa, primaryK11SignedR,
    primaryK11SignedARadius, primaryK11RBaseRadius, primaryK11RBaseRadiusRat,
    primaryK11ARadius, primaryK11ARadiusRat, primaryK11P0Radius,
    primaryK11P0RadiusRat, primaryK11Kappa, primaryK11KappaRat,
    matrixRkappa, matrixScaledSub, matrixScaledSubRat, Rat.cast_abs] using hij

theorem primaryK11SignedAnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA primaryK11SignedA primaryK11SignedARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11SignedAnalyticDtheta P0a)
      primaryK11SignedD primaryK11DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      primaryK11SignedAnalyticA primaryK11SignedA
      primaryK11SignedAnalyticP primaryK11P
      P0a primaryK11P0 primaryK11SignedARadius primaryK11PRadius
      primaryK11P0Radius primaryK11Kappa primaryK11Theta
      primaryK11Theta_nonneg primaryK11Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  simpa [primaryK11SignedAnalyticDtheta, primaryK11SignedD,
    primaryK11SignedARadius, primaryK11DBaseRadius, primaryK11DBaseRadiusRat,
    primaryK11ARadius, primaryK11ARadiusRat, primaryK11PRadius,
    primaryK11PRadiusRat, primaryK11P0Radius, primaryK11P0RadiusRat,
    primaryK11Kappa, primaryK11KappaRat, primaryK11Theta,
    primaryK11ThetaRat, matrixDtheta, Rat.cast_abs] using hij

def controlK9SignedAnalyticRkappa
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa controlK9SignedAnalyticA P0a controlK9Kappa

def controlK9SignedAnalyticDtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta controlK9SignedAnalyticA controlK9SignedAnalyticP P0a
    controlK9Kappa controlK9Theta

def controlK9SignedAnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub controlK9SignedAnalyticC R controlK9Theta

def controlK9SignedR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa controlK9SignedA controlK9P0 controlK9Kappa

def controlK9SignedD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta controlK9SignedA controlK9P controlK9P0
    controlK9Kappa controlK9Theta

theorem controlK9SignedAnalyticDFromR_eq_Dtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    controlK9SignedAnalyticDFromR (controlK9SignedAnalyticRkappa P0a) =
      controlK9SignedAnalyticDtheta P0a := by
  ext i j
  simp [controlK9SignedAnalyticDFromR, controlK9SignedAnalyticC_eq_matrixSub,
    controlK9SignedAnalyticRkappa, controlK9SignedAnalyticDtheta,
    matrixRkappa, matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem controlK9SignedAnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm controlK9SignedAnalyticC v =
        Q3.Proofs.quadForm (controlK9SignedAnalyticDFromR R) v +
          controlK9Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold controlK9SignedAnalyticDFromR
  exact quadForm_scaled_sub_split controlK9SignedAnalyticC R controlK9Theta v

theorem controlK9SignedAnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA controlK9SignedA controlK9SignedARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9SignedAnalyticRkappa P0a)
      controlK9SignedR controlK9RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      controlK9SignedAnalyticA controlK9SignedA P0a controlK9P0
      controlK9SignedARadius controlK9P0Radius controlK9Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [controlK9SignedAnalyticRkappa, controlK9SignedR,
    controlK9SignedARadius, controlK9RBaseRadius, controlK9RBaseRadiusRat,
    controlK9ARadius, controlK9ARadiusRat, controlK9P0Radius,
    controlK9P0RadiusRat, controlK9Kappa, controlK9KappaRat,
    matrixRkappa, matrixScaledSub, matrixScaledSubRat, Rat.cast_abs] using hij

theorem controlK9SignedAnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA controlK9SignedA controlK9SignedARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9SignedAnalyticDtheta P0a)
      controlK9SignedD controlK9DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      controlK9SignedAnalyticA controlK9SignedA
      controlK9SignedAnalyticP controlK9P
      P0a controlK9P0 controlK9SignedARadius controlK9PRadius
      controlK9P0Radius controlK9Kappa controlK9Theta
      controlK9Theta_nonneg controlK9Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  simpa [controlK9SignedAnalyticDtheta, controlK9SignedD,
    controlK9SignedARadius, controlK9DBaseRadius, controlK9DBaseRadiusRat,
    controlK9ARadius, controlK9ARadiusRat, controlK9PRadius,
    controlK9PRadiusRat, controlK9P0Radius, controlK9P0RadiusRat,
    controlK9Kappa, controlK9KappaRat, controlK9Theta,
    controlK9ThetaRat, matrixDtheta, Rat.cast_abs] using hij

theorem primaryK11SignedQ3AStarAnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA
      primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11SignedAnalyticRkappa P0a)
      primaryK11SignedQ3AStarR primaryK11SignedQ3AStarRBaseRadius := by
  have h :=
    matrixRkappa_hbox
      primaryK11SignedAnalyticA primaryK11SignedQ3AStarA P0a primaryK11P0
      primaryK11SignedQ3AStarARadius primaryK11P0Radius
      primaryK11Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [primaryK11SignedAnalyticRkappa, primaryK11SignedQ3AStarR,
    primaryK11SignedQ3AStarA, primaryK11SignedQ3AStarARadius,
    primaryK11SignedQ3AStarRBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarR,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarA,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarARadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarRBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarRBaseRadiusRat,
    primaryK11P0Radius, primaryK11P0RadiusRat,
    primaryK11Kappa, primaryK11KappaRat, matrixRkappa, matrixScaledSub,
    matrixScaledSubRat, Rat.cast_abs] using hij

theorem primaryK11SignedQ3AStarAnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticA
      primaryK11SignedQ3AStarA primaryK11SignedQ3AStarARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11SignedAnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11SignedAnalyticDtheta P0a)
      primaryK11SignedQ3AStarD primaryK11SignedQ3AStarDBaseRadius := by
  have h :=
    matrixDtheta_hbox
      primaryK11SignedAnalyticA primaryK11SignedQ3AStarA
      primaryK11SignedAnalyticP primaryK11P
      P0a primaryK11P0 primaryK11SignedQ3AStarARadius primaryK11PRadius
      primaryK11P0Radius primaryK11Kappa primaryK11Theta
      primaryK11Theta_nonneg primaryK11Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  simpa [primaryK11SignedAnalyticDtheta, primaryK11SignedQ3AStarD,
    primaryK11SignedQ3AStarA, primaryK11SignedQ3AStarARadius,
    primaryK11SignedQ3AStarDBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarD,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarA,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarARadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarDBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.primaryK11SignedQ3AStarDBaseRadiusRat,
    primaryK11PRadius, primaryK11PRadiusRat, primaryK11P0Radius,
    primaryK11P0RadiusRat, primaryK11Kappa, primaryK11KappaRat,
    primaryK11Theta, primaryK11ThetaRat, matrixDtheta, Rat.cast_abs] using hij

theorem controlK9SignedQ3AStarAnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA
      controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9SignedAnalyticRkappa P0a)
      controlK9SignedQ3AStarR controlK9SignedQ3AStarRBaseRadius := by
  have h :=
    matrixRkappa_hbox
      controlK9SignedAnalyticA controlK9SignedQ3AStarA P0a controlK9P0
      controlK9SignedQ3AStarARadius controlK9P0Radius
      controlK9Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [controlK9SignedAnalyticRkappa, controlK9SignedQ3AStarR,
    controlK9SignedQ3AStarA, controlK9SignedQ3AStarARadius,
    controlK9SignedQ3AStarRBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarR,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarA,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarARadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarRBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarRBaseRadiusRat,
    controlK9P0Radius, controlK9P0RadiusRat,
    controlK9Kappa, controlK9KappaRat, matrixRkappa, matrixScaledSub,
    matrixScaledSubRat, Rat.cast_abs] using hij

theorem controlK9SignedQ3AStarAnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticA
      controlK9SignedQ3AStarA controlK9SignedQ3AStarARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9SignedAnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9SignedAnalyticDtheta P0a)
      controlK9SignedQ3AStarD controlK9SignedQ3AStarDBaseRadius := by
  have h :=
    matrixDtheta_hbox
      controlK9SignedAnalyticA controlK9SignedQ3AStarA
      controlK9SignedAnalyticP controlK9P
      P0a controlK9P0 controlK9SignedQ3AStarARadius controlK9PRadius
      controlK9P0Radius controlK9Kappa controlK9Theta
      controlK9Theta_nonneg controlK9Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  simpa [controlK9SignedAnalyticDtheta, controlK9SignedQ3AStarD,
    controlK9SignedQ3AStarA, controlK9SignedQ3AStarARadius,
    controlK9SignedQ3AStarDBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarD,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarA,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarARadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarDBaseRadius,
    CenteredCoeffSignedQ3AStarPayloadImport.controlK9SignedQ3AStarDBaseRadiusRat,
    controlK9PRadius, controlK9PRadiusRat, controlK9P0Radius,
    controlK9P0RadiusRat, controlK9Kappa, controlK9KappaRat,
    controlK9Theta, controlK9ThetaRat, matrixDtheta, Rat.cast_abs] using hij

abbrev primaryK11CanonicalSignedBoundaryNullPSDCert : Prop :=
  DirectBoundaryNullPSDCert
    primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.C
    primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q

abbrev controlK9CanonicalSignedBoundaryNullPSDCert : Prop :=
  DirectBoundaryNullPSDCert
    controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.C
    controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q

noncomputable def primaryK11CanonicalSignedDirectFiniteWeilModel
    (cert : primaryK11CanonicalSignedBoundaryNullPSDCert) :
    CertifiedDirectFiniteWeilModel (Fin 2) CoeffIndex23 (CoeffIndex23 → Complex) where
  C := primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.C
  Q := primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q
  cert := cert
  model :=
    primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.toFiniteWeilMatrixModel

noncomputable def controlK9CanonicalSignedDirectFiniteWeilModel
    (cert : controlK9CanonicalSignedBoundaryNullPSDCert) :
    CertifiedDirectFiniteWeilModel (Fin 2) CoeffIndex23 (CoeffIndex23 → Complex) where
  C := controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.C
  Q := controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q
  cert := cert
  model :=
    controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.toFiniteWeilMatrixModel

theorem primaryK11CanonicalSignedBoundaryNullPSDCert_of_penalty_lower_bound
    (tau floor : Real)
    (hfloor : 0 <= floor)
    (hpenalty : ∀ v : CoeffIndex23 -> Real,
      floor * Q3.Proofs.euclideanEnergy v <=
        Q3.Proofs.penaltyForm
          primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.C
          primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q
          tau v) :
    primaryK11CanonicalSignedBoundaryNullPSDCert :=
  DirectBoundaryNullPSDCert.of_penalty_lower_bound
    (C := primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.C)
    (Q := primaryK11SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q)
    tau floor hfloor hpenalty

theorem controlK9CanonicalSignedBoundaryNullPSDCert_of_penalty_lower_bound
    (tau floor : Real)
    (hfloor : 0 <= floor)
    (hpenalty : ∀ v : CoeffIndex23 -> Real,
      floor * Q3.Proofs.euclideanEnergy v <=
        Q3.Proofs.penaltyForm
          controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.C
          controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q
          tau v) :
    controlK9CanonicalSignedBoundaryNullPSDCert :=
  DirectBoundaryNullPSDCert.of_penalty_lower_bound
    (C := controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.C)
    (Q := controlK9SignedCoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q)
    tau floor hfloor hpenalty

def primaryK11SignedFinitePenaltyLowerBoundCert : Type :=
  Q3.Proofs.FinitePenaltyLowerBoundCert
    primaryK11SignedD primaryK11SignedR primaryK11Q

def controlK9SignedFinitePenaltyLowerBoundCert : Type :=
  Q3.Proofs.FinitePenaltyLowerBoundCert
    controlK9SignedD controlK9SignedR controlK9Q

def primaryK11SignedFinitePenaltyCert_of_lowerBoundCert
    (cert : primaryK11SignedFinitePenaltyLowerBoundCert) :
    Q3.Proofs.FinitePenaltyCert primaryK11SignedD primaryK11SignedR primaryK11Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert cert

def controlK9SignedFinitePenaltyCert_of_lowerBoundCert
    (cert : controlK9SignedFinitePenaltyLowerBoundCert) :
    Q3.Proofs.FinitePenaltyCert controlK9SignedD controlK9SignedR controlK9Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert cert

def primaryK11SignedQ3AStarFinitePenaltyLowerBoundCert : Type :=
  Q3.Proofs.FinitePenaltyLowerBoundCert
    primaryK11SignedQ3AStarD primaryK11SignedQ3AStarR primaryK11Q

def controlK9SignedQ3AStarFinitePenaltyLowerBoundCert : Type :=
  Q3.Proofs.FinitePenaltyLowerBoundCert
    controlK9SignedQ3AStarD controlK9SignedQ3AStarR controlK9Q

def primaryK11SignedQ3AStarFinitePenaltyCert_of_lowerBoundCert
    (cert : primaryK11SignedQ3AStarFinitePenaltyLowerBoundCert) :
    Q3.Proofs.FinitePenaltyCert
      primaryK11SignedQ3AStarD primaryK11SignedQ3AStarR primaryK11Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert cert

def controlK9SignedQ3AStarFinitePenaltyCert_of_lowerBoundCert
    (cert : controlK9SignedQ3AStarFinitePenaltyLowerBoundCert) :
    Q3.Proofs.FinitePenaltyCert
      controlK9SignedQ3AStarD controlK9SignedQ3AStarR controlK9Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert cert

end PSDpd
end Q3
