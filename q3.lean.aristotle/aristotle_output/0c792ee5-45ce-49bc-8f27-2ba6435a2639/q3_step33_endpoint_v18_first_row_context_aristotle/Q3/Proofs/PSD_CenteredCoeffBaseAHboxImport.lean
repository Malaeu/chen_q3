import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffBaseAHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport

/-!
Generated Step33 A base-hbox receiver layer.

The Step22 `A` payloads are Toeplitz/symmetric in `|i-j|`, and the payload
import exposes `A`/`ARadius` through compact absolute-distance tables.  This
file proves the Lean receiver that turns 23 absolute-distance hboxes into the
imported payload hbox for both active primary/control blocks.
-/

theorem centeredBSplineArchKernelProfile_even
    (k : Nat) (ell d : Real) :
    centeredBSplineArchKernelProfile k ell (-d) =
      centeredBSplineArchKernelProfile k ell d := by
  unfold centeredBSplineArchKernelProfile
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  have harg : t * (-d) = -(t * d) := by
    ring
  rw [harg, Real.cos_neg]

theorem primaryK11AnalyticA_entry (i j : CoeffIndex23) :
    primaryK11AnalyticA i j =
      centeredBSplineArchKernelProfile
        11 primaryK11Ell (primaryK11Center j - primaryK11Center i) := by
  simp [primaryK11AnalyticA, primaryK11CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineArchPacketCoeffKernelData]

theorem controlK9AnalyticA_entry (i j : CoeffIndex23) :
    controlK9AnalyticA i j =
      centeredBSplineArchKernelProfile
        9 controlK9Ell (controlK9Center j - controlK9Center i) := by
  simp [controlK9AnalyticA, controlK9CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineArchPacketCoeffKernelData]

private theorem abs_sub_le_of_lower_upper
    (x mid rad : Real)
    (hLower : mid - rad <= x)
    (hUpper : x <= mid + rad) :
    |x - mid| <= rad := by
  rw [abs_sub_le_iff]
  constructor <;> linarith


private theorem primaryK11A_entry_from_abs_distance (i j : CoeffIndex23) :
    primaryK11A i j =
      (primaryK11AAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

private theorem primaryK11ARadius_entry_from_abs_distance (i j : CoeffIndex23) :
    primaryK11ARadius i j =
      (primaryK11ARadiusAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

structure primaryK11AnalyticAAbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) - (primaryK11AAbsDistanceEntryRat (n.1) : Real)| <= (primaryK11ARadiusAbsDistanceEntryRat (n.1) : Real)

def primaryK11AnalyticAAbsDistanceLower (n : CoeffIndex23) : Real :=
  (primaryK11AAbsDistanceEntryRat (n.1) : Real) - (primaryK11ARadiusAbsDistanceEntryRat (n.1) : Real)

def primaryK11AnalyticAAbsDistanceUpper (n : CoeffIndex23) : Real :=
  (primaryK11AAbsDistanceEntryRat (n.1) : Real) + (primaryK11ARadiusAbsDistanceEntryRat (n.1) : Real)

structure primaryK11AnalyticAAbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    primaryK11AnalyticAAbsDistanceLower n <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
  hUpper : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper n

theorem primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
    (cert : primaryK11AnalyticAAbsDistanceIntervalCert) :
    primaryK11AnalyticAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact abs_sub_le_of_lower_upper
    (x := centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)))
    (mid := (primaryK11AAbsDistanceEntryRat (n.1) : Real))
    (rad := (primaryK11ARadiusAbsDistanceEntryRat (n.1) : Real))
    (by simpa [primaryK11AnalyticAAbsDistanceLower] using cert.hLower n)
    (by simpa [primaryK11AnalyticAAbsDistanceUpper] using cert.hUpper n)

structure primaryK11AnalyticAAbsDistanceBoundsCert : Prop where
  hLower0 :
    primaryK11AnalyticAAbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real))
  hUpper0 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23)
  hLower1 :
    primaryK11AnalyticAAbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real))
  hUpper1 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23)
  hLower2 :
    primaryK11AnalyticAAbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real))
  hUpper2 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23)
  hLower3 :
    primaryK11AnalyticAAbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real))
  hUpper3 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23)
  hLower4 :
    primaryK11AnalyticAAbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real))
  hUpper4 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23)
  hLower5 :
    primaryK11AnalyticAAbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real))
  hUpper5 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23)
  hLower6 :
    primaryK11AnalyticAAbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real))
  hUpper6 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23)
  hLower7 :
    primaryK11AnalyticAAbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real))
  hUpper7 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23)
  hLower8 :
    primaryK11AnalyticAAbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real))
  hUpper8 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23)
  hLower9 :
    primaryK11AnalyticAAbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real))
  hUpper9 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23)
  hLower10 :
    primaryK11AnalyticAAbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real))
  hUpper10 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23)
  hLower11 :
    primaryK11AnalyticAAbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real))
  hUpper11 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23)
  hLower12 :
    primaryK11AnalyticAAbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real))
  hUpper12 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23)
  hLower13 :
    primaryK11AnalyticAAbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real))
  hUpper13 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23)
  hLower14 :
    primaryK11AnalyticAAbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real))
  hUpper14 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23)
  hLower15 :
    primaryK11AnalyticAAbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real))
  hUpper15 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23)
  hLower16 :
    primaryK11AnalyticAAbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real))
  hUpper16 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23)
  hLower17 :
    primaryK11AnalyticAAbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real))
  hUpper17 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23)
  hLower18 :
    primaryK11AnalyticAAbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real))
  hUpper18 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23)
  hLower19 :
    primaryK11AnalyticAAbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real))
  hUpper19 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23)
  hLower20 :
    primaryK11AnalyticAAbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real))
  hUpper20 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23)
  hLower21 :
    primaryK11AnalyticAAbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real))
  hUpper21 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23)
  hLower22 :
    primaryK11AnalyticAAbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real))
  hUpper22 :
    centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23)

theorem primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds
    (hLower0 :
      primaryK11AnalyticAAbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)))
    (hUpper0 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23))
    (hLower1 :
      primaryK11AnalyticAAbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)))
    (hUpper1 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23))
    (hLower2 :
      primaryK11AnalyticAAbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)))
    (hUpper2 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23))
    (hLower3 :
      primaryK11AnalyticAAbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)))
    (hUpper3 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23))
    (hLower4 :
      primaryK11AnalyticAAbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)))
    (hUpper4 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23))
    (hLower5 :
      primaryK11AnalyticAAbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)))
    (hUpper5 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23))
    (hLower6 :
      primaryK11AnalyticAAbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)))
    (hUpper6 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23))
    (hLower7 :
      primaryK11AnalyticAAbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)))
    (hUpper7 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23))
    (hLower8 :
      primaryK11AnalyticAAbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)))
    (hUpper8 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23))
    (hLower9 :
      primaryK11AnalyticAAbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)))
    (hUpper9 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23))
    (hLower10 :
      primaryK11AnalyticAAbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)))
    (hUpper10 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23))
    (hLower11 :
      primaryK11AnalyticAAbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)))
    (hUpper11 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23))
    (hLower12 :
      primaryK11AnalyticAAbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)))
    (hUpper12 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23))
    (hLower13 :
      primaryK11AnalyticAAbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)))
    (hUpper13 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23))
    (hLower14 :
      primaryK11AnalyticAAbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)))
    (hUpper14 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23))
    (hLower15 :
      primaryK11AnalyticAAbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)))
    (hUpper15 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23))
    (hLower16 :
      primaryK11AnalyticAAbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)))
    (hUpper16 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23))
    (hLower17 :
      primaryK11AnalyticAAbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)))
    (hUpper17 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23))
    (hLower18 :
      primaryK11AnalyticAAbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)))
    (hUpper18 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23))
    (hLower19 :
      primaryK11AnalyticAAbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)))
    (hUpper19 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23))
    (hLower20 :
      primaryK11AnalyticAAbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)))
    (hUpper20 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23))
    (hLower21 :
      primaryK11AnalyticAAbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)))
    (hUpper21 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23))
    (hLower22 :
      primaryK11AnalyticAAbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)))
    (hUpper22 :
      centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)) <= primaryK11AnalyticAAbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23))
    : primaryK11AnalyticAAbsDistanceIntervalCert := by
  constructor
  · intro n
    fin_cases n
    · simpa using hLower0
    · simpa using hLower1
    · simpa using hLower2
    · simpa using hLower3
    · simpa using hLower4
    · simpa using hLower5
    · simpa using hLower6
    · simpa using hLower7
    · simpa using hLower8
    · simpa using hLower9
    · simpa using hLower10
    · simpa using hLower11
    · simpa using hLower12
    · simpa using hLower13
    · simpa using hLower14
    · simpa using hLower15
    · simpa using hLower16
    · simpa using hLower17
    · simpa using hLower18
    · simpa using hLower19
    · simpa using hLower20
    · simpa using hLower21
    · simpa using hLower22
  · intro n
    fin_cases n
    · simpa using hUpper0
    · simpa using hUpper1
    · simpa using hUpper2
    · simpa using hUpper3
    · simpa using hUpper4
    · simpa using hUpper5
    · simpa using hUpper6
    · simpa using hUpper7
    · simpa using hUpper8
    · simpa using hUpper9
    · simpa using hUpper10
    · simpa using hUpper11
    · simpa using hUpper12
    · simpa using hUpper13
    · simpa using hUpper14
    · simpa using hUpper15
    · simpa using hUpper16
    · simpa using hUpper17
    · simpa using hUpper18
    · simpa using hUpper19
    · simpa using hUpper20
    · simpa using hUpper21
    · simpa using hUpper22

theorem primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
    (cert : primaryK11AnalyticAAbsDistanceBoundsCert) :
    primaryK11AnalyticAAbsDistanceIntervalCert := by
  exact primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds
    cert.hLower0
    cert.hUpper0
    cert.hLower1
    cert.hUpper1
    cert.hLower2
    cert.hUpper2
    cert.hLower3
    cert.hUpper3
    cert.hLower4
    cert.hUpper4
    cert.hLower5
    cert.hUpper5
    cert.hLower6
    cert.hUpper6
    cert.hLower7
    cert.hUpper7
    cert.hLower8
    cert.hUpper8
    cert.hLower9
    cert.hUpper9
    cert.hLower10
    cert.hUpper10
    cert.hLower11
    cert.hUpper11
    cert.hLower12
    cert.hUpper12
    cert.hLower13
    cert.hUpper13
    cert.hLower14
    cert.hUpper14
    cert.hLower15
    cert.hUpper15
    cert.hLower16
    cert.hUpper16
    cert.hLower17
    cert.hUpper17
    cert.hLower18
    cert.hUpper18
    cert.hLower19
    cert.hUpper19
    cert.hLower20
    cert.hUpper20
    cert.hLower21
    cert.hUpper21
    cert.hLower22
    cert.hUpper22

private theorem primaryK11AnalyticA_entry_hbox_row_0_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨0, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨0, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨0, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (5 : Real) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) + ((1292905771430244259 : Real) / (100000000000000000000 : Real))| <= ((496028255231392547 : Real) / (200000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (2 : Real)) + ((1140972789300954103 : Real) / (100000000000000000000 : Real))| <= ((435917043751652541 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_1_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨1, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨1, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨1, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (5 : Real) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) + ((1292905771430244259 : Real) / (100000000000000000000 : Real))| <= ((496028255231392547 : Real) / (200000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_2_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨2, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨2, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨2, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (5 : Real) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_3_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨3, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨3, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨3, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_4_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨4, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨4, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨4, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_5_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨5, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨5, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨5, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_6_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨6, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨6, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨6, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (4 : Real) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_7_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨7, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨7, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨7, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_8_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨8, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨8, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨8, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_9_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨9, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨9, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨9, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_10_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨10, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨10, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨10, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_11_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨11, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨11, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨11, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_12_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨12, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨12, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨12, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_13_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨13, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨13, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨13, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_14_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨14, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨14, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨14, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (2 : Real) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_15_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨15, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨15, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨15, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_16_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨16, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨16, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨16, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_17_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨17, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨17, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨17, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_18_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨18, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨18, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨18, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (1 : Real) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_19_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨19, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨19, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨19, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_20_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨20, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨20, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨20, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_21_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨21, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨21, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨21, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((21 : Real) / (4 : Real))) + ((1292905771430244259 : Real) / (100000000000000000000 : Real))| <= ((496028255231392547 : Real) / (200000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticA_entry_hbox_row_22_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticA (⟨22, by norm_num⟩ : CoeffIndex23) j - primaryK11A (⟨22, by norm_num⟩ : CoeffIndex23) j| <= primaryK11ARadius (⟨22, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (2 : Real))) + ((1140972789300954103 : Real) / (100000000000000000000 : Real))| <= ((435917043751652541 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((21 : Real) / (4 : Real))) + ((1292905771430244259 : Real) / (100000000000000000000 : Real))| <= ((496028255231392547 : Real) / (200000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1465080742557569801 : Real) / (100000000000000000000 : Real))| <= ((435189811757892843 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((332040722895587323 : Real) / (20000000000000000000 : Real))| <= ((778370880521679573 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((23516873749298557 : Real) / (1250000000000000000 : Real))| <= ((135561987386718809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((426404403507505067 : Real) / (20000000000000000000 : Real))| <= ((990970636235687379 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((2416221268183482013 : Real) / (100000000000000000000 : Real))| <= ((415060548232905687 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((2738542581476614141 : Real) / (100000000000000000000 : Real))| <= ((250049130079763179 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3104306607661829961 : Real) / (100000000000000000000 : Real))| <= ((1638453192936618487 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3519755893762420429 : Real) / (100000000000000000000 : Real))| <= ((299846503363812299 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((3992364956689390537 : Real) / (100000000000000000000 : Real))| <= ((3687152412608507489 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((4531358455175713007 : Real) / (100000000000000000000 : Real))| <= ((167314896858748809 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((1287154705071589557 : Real) / (25000000000000000000 : Real))| <= ((77494218541743827 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((1465085298601370191 : Real) / (25000000000000000000 : Real))| <= ((63217781131655259 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((1672541920558649059 : Real) / (25000000000000000000 : Real))| <= ((2955910819797590091 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((7675380274770543521 : Real) / (100000000000000000000 : Real))| <= ((2463849445147715251 : Real) / (250000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((8879834253975839309 : Real) / (100000000000000000000 : Real))| <= ((5817794673437905863 : Real) / (1000000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((10423206576642563 : Real) / (100000000000000000 : Real))| <= ((2428403574990901777 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((627777729522941419 : Real) / (5000000000000000000 : Real))| <= ((3268324211294571 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1588643857122144509 : Real) / (10000000000000000000 : Real))| <= ((138753472468043623 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((223530394922005049 : Real) / (1000000000000000000 : Real))| <= ((12502551002931183 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((1093704458734344881 : Real) / (2500000000000000000 : Real))| <= ((78885308075792783 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticA_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11A_entry_from_abs_distance,
      primaryK11ARadius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      primaryK11AAbsDistanceEntryRat,
      primaryK11ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 11 ((3 : Real) / (10 : Real)) (0 : Real) - ((1233644453639219513 : Real) / (10000000000000000000 : Real))| <= ((7116332121107148949 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11AAbsDistanceEntryRat, primaryK11ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

theorem primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
    (cert : primaryK11AnalyticAAbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe primaryK11AnalyticA primaryK11A primaryK11ARadius := by
  intro i j
  fin_cases i
  · exact primaryK11AnalyticA_entry_hbox_row_0_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_1_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_2_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_3_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_4_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_5_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_6_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_7_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_8_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_9_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_10_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_11_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_12_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_13_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_14_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_15_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_16_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_17_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_18_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_19_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_20_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_21_of_abs_distance_cert cert j
  · exact primaryK11AnalyticA_entry_hbox_row_22_of_abs_distance_cert cert j

private theorem controlK9A_entry_from_abs_distance (i j : CoeffIndex23) :
    controlK9A i j =
      (controlK9AAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

private theorem controlK9ARadius_entry_from_abs_distance (i j : CoeffIndex23) :
    controlK9ARadius i j =
      (controlK9ARadiusAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

structure controlK9AnalyticAAbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) - (controlK9AAbsDistanceEntryRat (n.1) : Real)| <= (controlK9ARadiusAbsDistanceEntryRat (n.1) : Real)

def controlK9AnalyticAAbsDistanceLower (n : CoeffIndex23) : Real :=
  (controlK9AAbsDistanceEntryRat (n.1) : Real) - (controlK9ARadiusAbsDistanceEntryRat (n.1) : Real)

def controlK9AnalyticAAbsDistanceUpper (n : CoeffIndex23) : Real :=
  (controlK9AAbsDistanceEntryRat (n.1) : Real) + (controlK9ARadiusAbsDistanceEntryRat (n.1) : Real)

structure controlK9AnalyticAAbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    controlK9AnalyticAAbsDistanceLower n <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
  hUpper : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper n

theorem controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
    (cert : controlK9AnalyticAAbsDistanceIntervalCert) :
    controlK9AnalyticAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact abs_sub_le_of_lower_upper
    (x := centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)))
    (mid := (controlK9AAbsDistanceEntryRat (n.1) : Real))
    (rad := (controlK9ARadiusAbsDistanceEntryRat (n.1) : Real))
    (by simpa [controlK9AnalyticAAbsDistanceLower] using cert.hLower n)
    (by simpa [controlK9AnalyticAAbsDistanceUpper] using cert.hUpper n)

structure controlK9AnalyticAAbsDistanceBoundsCert : Prop where
  hLower0 :
    controlK9AnalyticAAbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real))
  hUpper0 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23)
  hLower1 :
    controlK9AnalyticAAbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real))
  hUpper1 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23)
  hLower2 :
    controlK9AnalyticAAbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real))
  hUpper2 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23)
  hLower3 :
    controlK9AnalyticAAbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real))
  hUpper3 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23)
  hLower4 :
    controlK9AnalyticAAbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real))
  hUpper4 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23)
  hLower5 :
    controlK9AnalyticAAbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real))
  hUpper5 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23)
  hLower6 :
    controlK9AnalyticAAbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real))
  hUpper6 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23)
  hLower7 :
    controlK9AnalyticAAbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real))
  hUpper7 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23)
  hLower8 :
    controlK9AnalyticAAbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real))
  hUpper8 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23)
  hLower9 :
    controlK9AnalyticAAbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real))
  hUpper9 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23)
  hLower10 :
    controlK9AnalyticAAbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real))
  hUpper10 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23)
  hLower11 :
    controlK9AnalyticAAbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real))
  hUpper11 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23)
  hLower12 :
    controlK9AnalyticAAbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real))
  hUpper12 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23)
  hLower13 :
    controlK9AnalyticAAbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real))
  hUpper13 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23)
  hLower14 :
    controlK9AnalyticAAbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real))
  hUpper14 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23)
  hLower15 :
    controlK9AnalyticAAbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real))
  hUpper15 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23)
  hLower16 :
    controlK9AnalyticAAbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real))
  hUpper16 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23)
  hLower17 :
    controlK9AnalyticAAbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real))
  hUpper17 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23)
  hLower18 :
    controlK9AnalyticAAbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real))
  hUpper18 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23)
  hLower19 :
    controlK9AnalyticAAbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real))
  hUpper19 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23)
  hLower20 :
    controlK9AnalyticAAbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real))
  hUpper20 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23)
  hLower21 :
    controlK9AnalyticAAbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real))
  hUpper21 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23)
  hLower22 :
    controlK9AnalyticAAbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real))
  hUpper22 :
    centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23)

theorem controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds
    (hLower0 :
      controlK9AnalyticAAbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)))
    (hUpper0 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((0 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23))
    (hLower1 :
      controlK9AnalyticAAbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)))
    (hUpper1 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23))
    (hLower2 :
      controlK9AnalyticAAbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)))
    (hUpper2 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((2 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23))
    (hLower3 :
      controlK9AnalyticAAbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)))
    (hUpper3 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23))
    (hLower4 :
      controlK9AnalyticAAbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)))
    (hUpper4 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((4 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23))
    (hLower5 :
      controlK9AnalyticAAbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)))
    (hUpper5 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23))
    (hLower6 :
      controlK9AnalyticAAbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)))
    (hUpper6 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((6 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23))
    (hLower7 :
      controlK9AnalyticAAbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)))
    (hUpper7 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23))
    (hLower8 :
      controlK9AnalyticAAbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)))
    (hUpper8 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((8 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23))
    (hLower9 :
      controlK9AnalyticAAbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)))
    (hUpper9 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23))
    (hLower10 :
      controlK9AnalyticAAbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)))
    (hUpper10 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((10 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23))
    (hLower11 :
      controlK9AnalyticAAbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)))
    (hUpper11 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23))
    (hLower12 :
      controlK9AnalyticAAbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)))
    (hUpper12 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((12 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23))
    (hLower13 :
      controlK9AnalyticAAbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)))
    (hUpper13 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23))
    (hLower14 :
      controlK9AnalyticAAbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)))
    (hUpper14 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((14 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23))
    (hLower15 :
      controlK9AnalyticAAbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)))
    (hUpper15 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23))
    (hLower16 :
      controlK9AnalyticAAbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)))
    (hUpper16 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((16 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23))
    (hLower17 :
      controlK9AnalyticAAbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)))
    (hUpper17 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23))
    (hLower18 :
      controlK9AnalyticAAbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)))
    (hUpper18 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((18 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23))
    (hLower19 :
      controlK9AnalyticAAbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)))
    (hUpper19 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23))
    (hLower20 :
      controlK9AnalyticAAbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)))
    (hUpper20 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((20 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23))
    (hLower21 :
      controlK9AnalyticAAbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)))
    (hUpper21 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23))
    (hLower22 :
      controlK9AnalyticAAbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)))
    (hUpper22 :
      centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((22 : Real) / (4 : Real)) <= controlK9AnalyticAAbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23))
    : controlK9AnalyticAAbsDistanceIntervalCert := by
  constructor
  · intro n
    fin_cases n
    · simpa using hLower0
    · simpa using hLower1
    · simpa using hLower2
    · simpa using hLower3
    · simpa using hLower4
    · simpa using hLower5
    · simpa using hLower6
    · simpa using hLower7
    · simpa using hLower8
    · simpa using hLower9
    · simpa using hLower10
    · simpa using hLower11
    · simpa using hLower12
    · simpa using hLower13
    · simpa using hLower14
    · simpa using hLower15
    · simpa using hLower16
    · simpa using hLower17
    · simpa using hLower18
    · simpa using hLower19
    · simpa using hLower20
    · simpa using hLower21
    · simpa using hLower22
  · intro n
    fin_cases n
    · simpa using hUpper0
    · simpa using hUpper1
    · simpa using hUpper2
    · simpa using hUpper3
    · simpa using hUpper4
    · simpa using hUpper5
    · simpa using hUpper6
    · simpa using hUpper7
    · simpa using hUpper8
    · simpa using hUpper9
    · simpa using hUpper10
    · simpa using hUpper11
    · simpa using hUpper12
    · simpa using hUpper13
    · simpa using hUpper14
    · simpa using hUpper15
    · simpa using hUpper16
    · simpa using hUpper17
    · simpa using hUpper18
    · simpa using hUpper19
    · simpa using hUpper20
    · simpa using hUpper21
    · simpa using hUpper22

theorem controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
    (cert : controlK9AnalyticAAbsDistanceBoundsCert) :
    controlK9AnalyticAAbsDistanceIntervalCert := by
  exact controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds
    cert.hLower0
    cert.hUpper0
    cert.hLower1
    cert.hUpper1
    cert.hLower2
    cert.hUpper2
    cert.hLower3
    cert.hUpper3
    cert.hLower4
    cert.hUpper4
    cert.hLower5
    cert.hUpper5
    cert.hLower6
    cert.hUpper6
    cert.hLower7
    cert.hUpper7
    cert.hLower8
    cert.hUpper8
    cert.hLower9
    cert.hUpper9
    cert.hLower10
    cert.hUpper10
    cert.hLower11
    cert.hUpper11
    cert.hLower12
    cert.hUpper12
    cert.hLower13
    cert.hUpper13
    cert.hLower14
    cert.hUpper14
    cert.hLower15
    cert.hUpper15
    cert.hLower16
    cert.hUpper16
    cert.hLower17
    cert.hUpper17
    cert.hLower18
    cert.hUpper18
    cert.hLower19
    cert.hUpper19
    cert.hLower20
    cert.hUpper20
    cert.hLower21
    cert.hUpper21
    cert.hLower22
    cert.hUpper22

private theorem controlK9AnalyticA_entry_hbox_row_0_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨0, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨0, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨0, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (5 : Real) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) + ((1418280469000953239 : Real) / (100000000000000000000 : Real))| <= ((8270446986287126277 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (2 : Real)) + ((50064572532105861 : Real) / (4000000000000000000 : Real))| <= ((8282698246144176863 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_1_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨1, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨1, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨1, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (5 : Real) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((21 : Real) / (4 : Real)) + ((1418280469000953239 : Real) / (100000000000000000000 : Real))| <= ((8270446986287126277 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_2_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨2, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨2, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨2, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (5 : Real) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_3_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨3, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨3, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨3, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((19 : Real) / (4 : Real)) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_4_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨4, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨4, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨4, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (2 : Real)) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_5_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨5, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨5, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨5, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((17 : Real) / (4 : Real)) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_6_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨6, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨6, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨6, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (4 : Real) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_7_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨7, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨7, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨7, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((15 : Real) / (4 : Real)) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_8_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨8, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨8, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨8, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (2 : Real)) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_9_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨9, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨9, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨9, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((13 : Real) / (4 : Real)) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_10_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨10, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨10, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨10, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_11_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨11, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨11, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨11, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((11 : Real) / (4 : Real)) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_12_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨12, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨12, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨12, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (2 : Real)) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_13_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨13, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨13, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨13, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((9 : Real) / (4 : Real)) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_14_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨14, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨14, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨14, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (2 : Real) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_15_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨15, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨15, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨15, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((7 : Real) / (4 : Real)) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_16_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨16, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨16, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨16, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (2 : Real)) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_17_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨17, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨17, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨17, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((5 : Real) / (4 : Real)) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_18_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨18, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨18, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨18, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (1 : Real) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_19_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨19, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨19, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨19, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((3 : Real) / (4 : Real)) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_20_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨20, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨20, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨20, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (2 : Real)) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_21_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨21, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨21, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨21, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((21 : Real) / (4 : Real))) + ((1418280469000953239 : Real) / (100000000000000000000 : Real))| <= ((8270446986287126277 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) ((1 : Real) / (4 : Real)) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticA_entry_hbox_row_22_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticA (⟨22, by norm_num⟩ : CoeffIndex23) j - controlK9A (⟨22, by norm_num⟩ : CoeffIndex23) j| <= controlK9ARadius (⟨22, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (2 : Real))) + ((50064572532105861 : Real) / (4000000000000000000 : Real))| <= ((8282698246144176863 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((21 : Real) / (4 : Real))) + ((1418280469000953239 : Real) / (100000000000000000000 : Real))| <= ((8270446986287126277 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(5 : Real)) + ((1607151550999931511 : Real) / (100000000000000000000 : Real))| <= ((8272225106809787543 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((19 : Real) / (4 : Real))) + ((1821195908254563331 : Real) / (100000000000000000000 : Real))| <= ((522697379382197681 : Real) / (6250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (2 : Real))) + ((1031893683797450133 : Real) / (50000000000000000000 : Real))| <= ((833022953367268941 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((17 : Real) / (4 : Real))) + ((116938406355193477 : Real) / (5000000000000000000 : Real))| <= ((207347718297293069 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(4 : Real)) + ((66263194286512693 : Real) / (2500000000000000000 : Real))| <= ((8331725389139044151 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((15 : Real) / (4 : Real))) + ((300410731703779077 : Real) / (10000000000000000000 : Real))| <= ((103972926560606109 : Real) / (1250000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (2 : Real))) + ((3405344322235764887 : Real) / (100000000000000000000 : Real))| <= ((845083297962658333 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((13 : Real) / (4 : Real))) + ((3861088483096190849 : Real) / (100000000000000000000 : Real))| <= ((134673834601129871 : Real) / (1562500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(3 : Real)) + ((4379542530481585899 : Real) / (100000000000000000000 : Real))| <= ((855702342466260011 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((11 : Real) / (4 : Real))) + ((994166422379682141 : Real) / (20000000000000000000 : Real))| <= ((1726364825296248313 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (2 : Real))) + ((353000270304563513 : Real) / (6250000000000000000 : Real))| <= ((840410073548849799 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((9 : Real) / (4 : Real))) + ((6428849036841745301 : Real) / (100000000000000000000 : Real))| <= ((27761122012128307 : Real) / (312500000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(2 : Real)) + ((7339349733534716869 : Real) / (100000000000000000000 : Real))| <= ((8572089978111729267 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((7 : Real) / (4 : Real))) + ((8420506225936438827 : Real) / (100000000000000000000 : Real))| <= ((4382264561620783169 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (2 : Real))) + ((9742597050289207583 : Real) / (100000000000000000000 : Real))| <= ((8520175248603988751 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((5 : Real) / (4 : Real))) + ((1143748439686752133 : Real) / (10000000000000000000 : Real))| <= ((4513504666329072089 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-(1 : Real)) + ((689059531184678803 : Real) / (5000000000000000000 : Real))| <= ((8547287468774182193 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((3 : Real) / (4 : Real))) + ((1744899965879780079 : Real) / (10000000000000000000 : Real))| <= ((457195743740703837 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (2 : Real))) + ((1230368028546937609 : Real) / (5000000000000000000 : Real))| <= ((9701174134984211113 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (-((1 : Real) / (4 : Real))) + ((4873092439847854229 : Real) / (10000000000000000000 : Real))| <= ((595177623390520127 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineArchKernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticA_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9A_entry_from_abs_distance,
      controlK9ARadius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      controlK9AAbsDistanceEntryRat,
      controlK9ARadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineArchKernelProfile 9 ((3 : Real) / (10 : Real)) (0 : Real) - ((1312445182938742211 : Real) / (50000000000000000000 : Real))| <= ((418225011179805481 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9AAbsDistanceEntryRat, controlK9ARadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

theorem controlK9AnalyticA_entry_hbox_of_abs_distance_cert
    (cert : controlK9AnalyticAAbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe controlK9AnalyticA controlK9A controlK9ARadius := by
  intro i j
  fin_cases i
  · exact controlK9AnalyticA_entry_hbox_row_0_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_1_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_2_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_3_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_4_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_5_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_6_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_7_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_8_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_9_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_10_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_11_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_12_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_13_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_14_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_15_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_16_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_17_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_18_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_19_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_20_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_21_of_abs_distance_cert cert j
  · exact controlK9AnalyticA_entry_hbox_row_22_of_abs_distance_cert cert j


end CenteredCoeffBaseAHboxImport
end PSDpd
end Q3
