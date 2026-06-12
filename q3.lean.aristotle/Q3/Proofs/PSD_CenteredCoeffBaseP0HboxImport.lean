import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffBaseP0HboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffAnalyticP0Import

/-!
Generated Step33 P0 base-hbox receiver layer.

The Step21/Step22 CSV payloads are Toeplitz/symmetric in `|i-j|`, and the
payload import exposes `P0`/`P0Radius` through compact absolute-distance tables.
This file does not prove the 23 scalar analytic interval enclosures.  Instead,
it proves the Lean receiver that turns those 23 absolute-distance hboxes into
the imported payload hbox.
-/

private theorem centeredBSplineR_even (k : Nat) (x : Real) :
    centeredBSplineR k (-x) = centeredBSplineR k x := by
  unfold centeredBSplineR
  have harg : bsplineScale k * (-x) = -(bsplineScale k * x) := by
    ring
  rw [harg, centeredCardinalBSpline_autocorrDegree_even k]

theorem centeredBSplineP0KernelProfile_even
    (k : Nat) (ell L d : Real) :
    centeredBSplineP0KernelProfile k ell L (-d) =
      centeredBSplineP0KernelProfile k ell L d := by
  unfold centeredBSplineP0KernelProfile
  apply intervalIntegral.integral_congr
  intro a _ha
  change
    Real.exp (a / 2) *
        (centeredBSplineR k ((-d - a) / ell) +
          centeredBSplineR k ((-d + a) / ell)) =
      Real.exp (a / 2) *
        (centeredBSplineR k ((d - a) / ell) +
          centeredBSplineR k ((d + a) / ell))
  have hleft : (-d - a) / ell = -((d + a) / ell) := by
    ring
  have hright : (-d + a) / ell = -((d - a) / ell) := by
    ring
  rw [hleft, hright, centeredBSplineR_even, centeredBSplineR_even]
  ring

def coeffAbsDistanceNat (i j : CoeffIndex23) : Nat :=
  if i.1 ≤ j.1 then j.1 - i.1 else i.1 - j.1

theorem coeffAbsDistanceNat_lt_23 (i j : CoeffIndex23) :
    coeffAbsDistanceNat i j < 23 := by
  unfold coeffAbsDistanceNat
  by_cases h : i.1 ≤ j.1
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le j.1 i.1) j.2
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le i.1 j.1) i.2

def coeffAbsDistanceFin (i j : CoeffIndex23) : CoeffIndex23 :=
  ⟨coeffAbsDistanceNat i j, coeffAbsDistanceNat_lt_23 i j⟩

private theorem abs_sub_le_of_lower_upper
    (x mid rad : Real)
    (hLower : mid - rad <= x)
    (hUpper : x <= mid + rad) :
    |x - mid| <= rad := by
  rw [abs_sub_le_iff]
  constructor <;> linarith


private theorem primaryK11P0_entry_from_abs_distance (i j : CoeffIndex23) :
    primaryK11P0 i j =
      (primaryK11P0AbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

private theorem primaryK11P0Radius_entry_from_abs_distance (i j : CoeffIndex23) :
    primaryK11P0Radius i j =
      (primaryK11P0RadiusAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

structure primaryK11AnalyticP0AbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)) - (primaryK11P0AbsDistanceEntryRat (n.1) : Real)| <= (primaryK11P0RadiusAbsDistanceEntryRat (n.1) : Real)

def primaryK11AnalyticP0AbsDistanceLower (n : CoeffIndex23) : Real :=
  (primaryK11P0AbsDistanceEntryRat (n.1) : Real) - (primaryK11P0RadiusAbsDistanceEntryRat (n.1) : Real)

def primaryK11AnalyticP0AbsDistanceUpper (n : CoeffIndex23) : Real :=
  (primaryK11P0AbsDistanceEntryRat (n.1) : Real) + (primaryK11P0RadiusAbsDistanceEntryRat (n.1) : Real)

structure primaryK11AnalyticP0AbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    primaryK11AnalyticP0AbsDistanceLower n <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real))
  hUpper : ∀ n : CoeffIndex23,
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper n

theorem primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
    (cert : primaryK11AnalyticP0AbsDistanceIntervalCert) :
    primaryK11AnalyticP0AbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact abs_sub_le_of_lower_upper
    (x := centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)))
    (mid := (primaryK11P0AbsDistanceEntryRat (n.1) : Real))
    (rad := (primaryK11P0RadiusAbsDistanceEntryRat (n.1) : Real))
    (by simpa [primaryK11AnalyticP0AbsDistanceLower] using cert.hLower n)
    (by simpa [primaryK11AnalyticP0AbsDistanceUpper] using cert.hUpper n)

structure primaryK11AnalyticP0AbsDistanceBoundsCert : Prop where
  hLower0 :
    primaryK11AnalyticP0AbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real))
  hUpper0 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23)
  hLower1 :
    primaryK11AnalyticP0AbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real))
  hUpper1 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23)
  hLower2 :
    primaryK11AnalyticP0AbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real))
  hUpper2 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23)
  hLower3 :
    primaryK11AnalyticP0AbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real))
  hUpper3 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23)
  hLower4 :
    primaryK11AnalyticP0AbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real))
  hUpper4 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23)
  hLower5 :
    primaryK11AnalyticP0AbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real))
  hUpper5 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23)
  hLower6 :
    primaryK11AnalyticP0AbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real))
  hUpper6 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23)
  hLower7 :
    primaryK11AnalyticP0AbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real))
  hUpper7 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23)
  hLower8 :
    primaryK11AnalyticP0AbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real))
  hUpper8 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23)
  hLower9 :
    primaryK11AnalyticP0AbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real))
  hUpper9 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23)
  hLower10 :
    primaryK11AnalyticP0AbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real))
  hUpper10 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23)
  hLower11 :
    primaryK11AnalyticP0AbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real))
  hUpper11 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23)
  hLower12 :
    primaryK11AnalyticP0AbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real))
  hUpper12 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23)
  hLower13 :
    primaryK11AnalyticP0AbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real))
  hUpper13 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23)
  hLower14 :
    primaryK11AnalyticP0AbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real))
  hUpper14 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23)
  hLower15 :
    primaryK11AnalyticP0AbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real))
  hUpper15 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23)
  hLower16 :
    primaryK11AnalyticP0AbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real))
  hUpper16 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23)
  hLower17 :
    primaryK11AnalyticP0AbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real))
  hUpper17 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23)
  hLower18 :
    primaryK11AnalyticP0AbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real))
  hUpper18 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23)
  hLower19 :
    primaryK11AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real))
  hUpper19 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23)
  hLower20 :
    primaryK11AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real))
  hUpper20 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23)
  hLower21 :
    primaryK11AnalyticP0AbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real))
  hUpper21 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23)
  hLower22 :
    primaryK11AnalyticP0AbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real))
  hUpper22 :
    centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23)

theorem primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds
    (hLower0 :
      primaryK11AnalyticP0AbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)))
    (hUpper0 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23))
    (hLower1 :
      primaryK11AnalyticP0AbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)))
    (hUpper1 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23))
    (hLower2 :
      primaryK11AnalyticP0AbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)))
    (hUpper2 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23))
    (hLower3 :
      primaryK11AnalyticP0AbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)))
    (hUpper3 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23))
    (hLower4 :
      primaryK11AnalyticP0AbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)))
    (hUpper4 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23))
    (hLower5 :
      primaryK11AnalyticP0AbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)))
    (hUpper5 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23))
    (hLower6 :
      primaryK11AnalyticP0AbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)))
    (hUpper6 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23))
    (hLower7 :
      primaryK11AnalyticP0AbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)))
    (hUpper7 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23))
    (hLower8 :
      primaryK11AnalyticP0AbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)))
    (hUpper8 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23))
    (hLower9 :
      primaryK11AnalyticP0AbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)))
    (hUpper9 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23))
    (hLower10 :
      primaryK11AnalyticP0AbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)))
    (hUpper10 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23))
    (hLower11 :
      primaryK11AnalyticP0AbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)))
    (hUpper11 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23))
    (hLower12 :
      primaryK11AnalyticP0AbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)))
    (hUpper12 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23))
    (hLower13 :
      primaryK11AnalyticP0AbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)))
    (hUpper13 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23))
    (hLower14 :
      primaryK11AnalyticP0AbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)))
    (hUpper14 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23))
    (hLower15 :
      primaryK11AnalyticP0AbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)))
    (hUpper15 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23))
    (hLower16 :
      primaryK11AnalyticP0AbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)))
    (hUpper16 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23))
    (hLower17 :
      primaryK11AnalyticP0AbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)))
    (hUpper17 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23))
    (hLower18 :
      primaryK11AnalyticP0AbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)))
    (hUpper18 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23))
    (hLower19 :
      primaryK11AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)))
    (hUpper19 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23))
    (hLower20 :
      primaryK11AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)))
    (hUpper20 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23))
    (hLower21 :
      primaryK11AnalyticP0AbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)))
    (hUpper21 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23))
    (hLower22 :
      primaryK11AnalyticP0AbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)))
    (hUpper22 :
      centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)) <= primaryK11AnalyticP0AbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23))
    : primaryK11AnalyticP0AbsDistanceIntervalCert := by
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

theorem primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
    (cert : primaryK11AnalyticP0AbsDistanceBoundsCert) :
    primaryK11AnalyticP0AbsDistanceIntervalCert := by
  exact primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds
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

private theorem primaryK11AnalyticP0_entry_hbox_row_0_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨0, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨0, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨0, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) - ((2463773412580696931 : Real) / (1000000000000000000 : Real))| <= ((9253202030435209277 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (2 : Real)) - ((348977628896624037 : Real) / (125000000000000000 : Real))| <= ((5604403010317686429 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_1_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨1, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨1, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨1, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) - ((2463773412580696931 : Real) / (1000000000000000000 : Real))| <= ((9253202030435209277 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_2_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨2, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨2, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨2, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_3_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨3, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨3, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨3, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_4_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨4, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨4, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨4, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_5_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨5, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨5, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨5, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_6_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨6, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨6, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨6, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_7_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨7, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨7, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨7, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_8_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨8, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨8, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨8, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_9_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨9, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨9, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨9, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_10_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨10, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨10, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨10, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_11_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨11, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨11, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨11, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_12_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨12, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨12, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨12, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_13_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨13, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨13, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨13, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_14_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨14, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨14, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨14, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_15_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨15, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨15, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨15, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_16_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨16, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨16, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨16, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_17_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨17, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨17, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨17, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_18_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨18, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨18, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨18, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_19_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨19, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨19, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨19, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_20_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨20, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨20, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨20, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_21_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨21, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨21, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨21, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((21 : Real) / (4 : Real))) - ((2463773412580696931 : Real) / (1000000000000000000 : Real))| <= ((9253202030435209277 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem primaryK11AnalyticP0_entry_hbox_row_22_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |primaryK11AnalyticP0 (⟨22, by norm_num⟩ : CoeffIndex23) j - primaryK11P0 (⟨22, by norm_num⟩ : CoeffIndex23) j| <= primaryK11P0Radius (⟨22, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (2 : Real))) - ((348977628896624037 : Real) / (125000000000000000 : Real))| <= ((5604403010317686429 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((21 : Real) / (4 : Real))) - ((2463773412580696931 : Real) / (1000000000000000000 : Real))| <= ((9253202030435209277 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((2174272405272743569 : Real) / (1000000000000000000 : Real))| <= ((286926209254546267 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((959394331514177079 : Real) / (500000000000000000 : Real))| <= ((3006650966749234351 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((1693325051836959583 : Real) / (1000000000000000000 : Real))| <= ((328633297108484623 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1494354113315016219 : Real) / (1000000000000000000 : Real))| <= ((6795721430034862083 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((659381438182525703 : Real) / (500000000000000000 : Real))| <= ((5455195590323629427 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((290951038408927387 : Real) / (250000000000000000 : Real))| <= ((5371570328364229243 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((513526780399300109 : Real) / (500000000000000000 : Real))| <= ((7577641319624932597 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((9063715861932442053 : Real) / (10000000000000000000 : Real))| <= ((2585208999424747837 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((7998701174062246011 : Real) / (10000000000000000000 : Real))| <= ((485364870993489413 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((705882901080969849 : Real) / (1000000000000000000 : Real))| <= ((4997875970954900947 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((1557348684478460643 : Real) / (2500000000000000000 : Real))| <= ((1480031461074829301 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((687177695148217943 : Real) / (1250000000000000000 : Real))| <= ((1281727649872036157 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1212864374987047411 : Real) / (2500000000000000000 : Real))| <= ((613250804657675011 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((856279243345016483 : Real) / (2000000000000000000 : Real))| <= ((3629443967060549967 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((472289862499661317 : Real) / (1250000000000000000 : Real))| <= ((296233322800277733 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((1667177363112222199 : Real) / (5000000000000000000 : Real))| <= ((2110845711487353 : Real) / (488281250000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((367819714751422347 : Real) / (1250000000000000000 : Real))| <= ((1270037810746942753 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((2596798071821437293 : Real) / (10000000000000000000 : Real))| <= ((2412989690332279081 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((1145833127510033911 : Real) / (5000000000000000000 : Real))| <= ((583199010655410923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((252799077418274093 : Real) / (1250000000000000000 : Real))| <= ((1808137720053937253 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      primaryK11AnalyticP0_entry,
      primaryK11Center_sub_eq_index_delta,
      primaryK11P0_entry_from_abs_distance,
      primaryK11P0Radius_entry_from_abs_distance]
    norm_num [
      primaryK11Ell, primaryK11EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      primaryK11P0AbsDistanceEntryRat,
      primaryK11P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 11 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((91759672657030833 : Real) / (500000000000000000 : Real))| <= ((558268856133557453 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [primaryK11P0AbsDistanceEntryRat, primaryK11P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

theorem primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
    (cert : primaryK11AnalyticP0AbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius := by
  intro i j
  fin_cases i
  · exact primaryK11AnalyticP0_entry_hbox_row_0_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_1_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_2_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_3_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_4_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_5_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_6_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_7_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_8_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_9_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_10_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_11_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_12_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_13_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_14_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_15_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_16_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_17_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_18_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_19_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_20_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_21_of_abs_distance_cert cert j
  · exact primaryK11AnalyticP0_entry_hbox_row_22_of_abs_distance_cert cert j

private theorem controlK9P0_entry_from_abs_distance (i j : CoeffIndex23) :
    controlK9P0 i j =
      (controlK9P0AbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

private theorem controlK9P0Radius_entry_from_abs_distance (i j : CoeffIndex23) :
    controlK9P0Radius i j =
      (controlK9P0RadiusAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by
  rfl

structure controlK9AnalyticP0AbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)) - (controlK9P0AbsDistanceEntryRat (n.1) : Real)| <= (controlK9P0RadiusAbsDistanceEntryRat (n.1) : Real)

def controlK9AnalyticP0AbsDistanceLower (n : CoeffIndex23) : Real :=
  (controlK9P0AbsDistanceEntryRat (n.1) : Real) - (controlK9P0RadiusAbsDistanceEntryRat (n.1) : Real)

def controlK9AnalyticP0AbsDistanceUpper (n : CoeffIndex23) : Real :=
  (controlK9P0AbsDistanceEntryRat (n.1) : Real) + (controlK9P0RadiusAbsDistanceEntryRat (n.1) : Real)

structure controlK9AnalyticP0AbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    controlK9AnalyticP0AbsDistanceLower n <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real))
  hUpper : ∀ n : CoeffIndex23,
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper n

theorem controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
    (cert : controlK9AnalyticP0AbsDistanceIntervalCert) :
    controlK9AnalyticP0AbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact abs_sub_le_of_lower_upper
    (x := centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((n.1 : Real) / (4 : Real)))
    (mid := (controlK9P0AbsDistanceEntryRat (n.1) : Real))
    (rad := (controlK9P0RadiusAbsDistanceEntryRat (n.1) : Real))
    (by simpa [controlK9AnalyticP0AbsDistanceLower] using cert.hLower n)
    (by simpa [controlK9AnalyticP0AbsDistanceUpper] using cert.hUpper n)

structure controlK9AnalyticP0AbsDistanceBoundsCert : Prop where
  hLower0 :
    controlK9AnalyticP0AbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real))
  hUpper0 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23)
  hLower1 :
    controlK9AnalyticP0AbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real))
  hUpper1 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23)
  hLower2 :
    controlK9AnalyticP0AbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real))
  hUpper2 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23)
  hLower3 :
    controlK9AnalyticP0AbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real))
  hUpper3 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23)
  hLower4 :
    controlK9AnalyticP0AbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real))
  hUpper4 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23)
  hLower5 :
    controlK9AnalyticP0AbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real))
  hUpper5 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23)
  hLower6 :
    controlK9AnalyticP0AbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real))
  hUpper6 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23)
  hLower7 :
    controlK9AnalyticP0AbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real))
  hUpper7 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23)
  hLower8 :
    controlK9AnalyticP0AbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real))
  hUpper8 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23)
  hLower9 :
    controlK9AnalyticP0AbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real))
  hUpper9 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23)
  hLower10 :
    controlK9AnalyticP0AbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real))
  hUpper10 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23)
  hLower11 :
    controlK9AnalyticP0AbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real))
  hUpper11 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23)
  hLower12 :
    controlK9AnalyticP0AbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real))
  hUpper12 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23)
  hLower13 :
    controlK9AnalyticP0AbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real))
  hUpper13 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23)
  hLower14 :
    controlK9AnalyticP0AbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real))
  hUpper14 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23)
  hLower15 :
    controlK9AnalyticP0AbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real))
  hUpper15 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23)
  hLower16 :
    controlK9AnalyticP0AbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real))
  hUpper16 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23)
  hLower17 :
    controlK9AnalyticP0AbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real))
  hUpper17 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23)
  hLower18 :
    controlK9AnalyticP0AbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real))
  hUpper18 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23)
  hLower19 :
    controlK9AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real))
  hUpper19 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23)
  hLower20 :
    controlK9AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real))
  hUpper20 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23)
  hLower21 :
    controlK9AnalyticP0AbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real))
  hUpper21 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23)
  hLower22 :
    controlK9AnalyticP0AbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real))
  hUpper22 :
    centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23)

theorem controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds
    (hLower0 :
      controlK9AnalyticP0AbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)))
    (hUpper0 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((0 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23))
    (hLower1 :
      controlK9AnalyticP0AbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)))
    (hUpper1 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23))
    (hLower2 :
      controlK9AnalyticP0AbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)))
    (hUpper2 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((2 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23))
    (hLower3 :
      controlK9AnalyticP0AbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)))
    (hUpper3 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23))
    (hLower4 :
      controlK9AnalyticP0AbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)))
    (hUpper4 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((4 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23))
    (hLower5 :
      controlK9AnalyticP0AbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)))
    (hUpper5 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23))
    (hLower6 :
      controlK9AnalyticP0AbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)))
    (hUpper6 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((6 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23))
    (hLower7 :
      controlK9AnalyticP0AbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)))
    (hUpper7 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23))
    (hLower8 :
      controlK9AnalyticP0AbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)))
    (hUpper8 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((8 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23))
    (hLower9 :
      controlK9AnalyticP0AbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)))
    (hUpper9 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23))
    (hLower10 :
      controlK9AnalyticP0AbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)))
    (hUpper10 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((10 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23))
    (hLower11 :
      controlK9AnalyticP0AbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)))
    (hUpper11 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23))
    (hLower12 :
      controlK9AnalyticP0AbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)))
    (hUpper12 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((12 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23))
    (hLower13 :
      controlK9AnalyticP0AbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)))
    (hUpper13 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23))
    (hLower14 :
      controlK9AnalyticP0AbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)))
    (hUpper14 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((14 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23))
    (hLower15 :
      controlK9AnalyticP0AbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)))
    (hUpper15 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23))
    (hLower16 :
      controlK9AnalyticP0AbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)))
    (hUpper16 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((16 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23))
    (hLower17 :
      controlK9AnalyticP0AbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)))
    (hUpper17 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23))
    (hLower18 :
      controlK9AnalyticP0AbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)))
    (hUpper18 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((18 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23))
    (hLower19 :
      controlK9AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)))
    (hUpper19 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23))
    (hLower20 :
      controlK9AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)))
    (hUpper20 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((20 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23))
    (hLower21 :
      controlK9AnalyticP0AbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)))
    (hUpper21 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23))
    (hLower22 :
      controlK9AnalyticP0AbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <= centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)))
    (hUpper22 :
      centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((22 : Real) / (4 : Real)) <= controlK9AnalyticP0AbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23))
    : controlK9AnalyticP0AbsDistanceIntervalCert := by
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

theorem controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
    (cert : controlK9AnalyticP0AbsDistanceBoundsCert) :
    controlK9AnalyticP0AbsDistanceIntervalCert := by
  exact controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds
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

private theorem controlK9AnalyticP0_entry_hbox_row_0_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨0, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨0, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨0, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) - ((540537677993498633 : Real) / (200000000000000000 : Real))| <= ((2059275393876606503 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (2 : Real)) - ((3062547168213292093 : Real) / (1000000000000000000 : Real))| <= ((3817752388981587721 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_1_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨1, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨1, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨1, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((21 : Real) / (4 : Real)) - ((540537677993498633 : Real) / (200000000000000000 : Real))| <= ((2059275393876606503 : Real) / (10000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_2_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨2, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨2, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨2, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (5 : Real) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_3_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨3, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨3, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨3, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((19 : Real) / (4 : Real)) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_4_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨4, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨4, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨4, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (2 : Real)) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_5_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨5, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨5, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨5, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((17 : Real) / (4 : Real)) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_6_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨6, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨6, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨6, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (4 : Real) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_7_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨7, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨7, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨7, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((15 : Real) / (4 : Real)) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_8_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨8, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨8, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨8, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (2 : Real)) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_9_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨9, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨9, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨9, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((13 : Real) / (4 : Real)) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_10_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨10, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨10, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨10, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (3 : Real) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_11_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨11, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨11, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨11, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((11 : Real) / (4 : Real)) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_12_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨12, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨12, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨12, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (2 : Real)) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_13_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨13, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨13, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨13, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((9 : Real) / (4 : Real)) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_14_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨14, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨14, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨14, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (2 : Real) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_15_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨15, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨15, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨15, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((7 : Real) / (4 : Real)) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_16_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨16, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨16, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨16, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (2 : Real)) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_17_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨17, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨17, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨17, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((5 : Real) / (4 : Real)) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_18_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨18, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨18, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨18, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (1 : Real) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_19_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨19, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨19, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨19, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((3 : Real) / (4 : Real)) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_20_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨20, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨20, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨20, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (2 : Real)) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_21_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨21, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨21, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨21, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((21 : Real) / (4 : Real))) - ((540537677993498633 : Real) / (200000000000000000 : Real))| <= ((2059275393876606503 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) ((1 : Real) / (4 : Real)) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

private theorem controlK9AnalyticP0_entry_hbox_row_22_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) (j : CoeffIndex23) :
    |controlK9AnalyticP0 (⟨22, by norm_num⟩ : CoeffIndex23) j - controlK9P0 (⟨22, by norm_num⟩ : CoeffIndex23) j| <= controlK9P0Radius (⟨22, by norm_num⟩ : CoeffIndex23) j := by
  fin_cases j
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (2 : Real))) - ((3062547168213292093 : Real) / (1000000000000000000 : Real))| <= ((3817752388981587721 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨22, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((21 : Real) / (4 : Real))) - ((540537677993498633 : Real) / (200000000000000000 : Real))| <= ((2059275393876606503 : Real) / (10000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨21, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(5 : Real)) - ((1192557066398829857 : Real) / (500000000000000000 : Real))| <= ((715442074769800223 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨20, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((19 : Real) / (4 : Real))) - ((2104855834504677947 : Real) / (1000000000000000000 : Real))| <= ((536792320331487949 : Real) / (2500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨19, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (2 : Real))) - ((464382188584373079 : Real) / (250000000000000000 : Real))| <= ((8923297487517764333 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨18, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((17 : Real) / (4 : Real))) - ((1639263372164658783 : Real) / (1000000000000000000 : Real))| <= ((1539079426279628737 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨17, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(4 : Real)) - ((1446644848455690191 : Real) / (1000000000000000000 : Real))| <= ((144654292348641093 : Real) / (12500000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨16, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((15 : Real) / (4 : Real))) - ((638329798951054017 : Real) / (500000000000000000 : Real))| <= ((60910843484710203 : Real) / (2000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨15, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (2 : Real))) - ((1126648140803505393 : Real) / (1000000000000000000 : Real))| <= ((278227953154128231 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨14, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((13 : Real) / (4 : Real))) - ((2485658736404466329 : Real) / (2500000000000000000 : Real))| <= ((8089321640629275301 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨13, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(3 : Real)) - ((4387172271518561817 : Real) / (5000000000000000000 : Real))| <= ((2661936101359038557 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨12, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((11 : Real) / (4 : Real))) - ((1935832970360077121 : Real) / (2500000000000000000 : Real))| <= ((1698173934277229983 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨11, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (2 : Real))) - ((6833466401055620087 : Real) / (10000000000000000000 : Real))| <= ((3899479727928989399 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨10, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((9 : Real) / (4 : Real))) - ((6030512932847487129 : Real) / (10000000000000000000 : Real))| <= ((2922036304536648173 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨9, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(2 : Real)) - ((1330477246058562879 : Real) / (2500000000000000000 : Real))| <= ((1443430041663033923 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨8, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((7 : Real) / (4 : Real))) - ((4696568194423857423 : Real) / (10000000000000000000 : Real))| <= ((208343014680822057 : Real) / (20000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨7, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (2 : Real))) - ((4144706884356380017 : Real) / (10000000000000000000 : Real))| <= ((4901123068636532101 : Real) / (500000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨6, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((5 : Real) / (4 : Real))) - ((3657690987565554441 : Real) / (10000000000000000000 : Real))| <= ((1497435115808399091 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨5, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-(1 : Real)) - ((3227900967138191413 : Real) / (10000000000000000000 : Real))| <= ((60188913576157657 : Real) / (5000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨4, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((3 : Real) / (4 : Real))) - ((712153151337318463 : Real) / (2500000000000000000 : Real))| <= ((555458858216575963 : Real) / (50000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨3, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (2 : Real))) - ((628472950221042187 : Real) / (2500000000000000000 : Real))| <= ((566816445598532553 : Real) / (25000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨2, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (-((1 : Real) / (4 : Real))) - ((2218519648517359721 : Real) / (10000000000000000000 : Real))| <= ((1213191175077113867 : Real) / (100000000000000000000000000000000000 : Real))
    rw [centeredBSplineP0KernelProfile_even]
    have hcert := cert.h (⟨1, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert
  · rw [
      controlK9AnalyticP0_entry,
      controlK9Center_sub_eq_index_delta,
      controlK9P0_entry_from_abs_distance,
      controlK9P0Radius_entry_from_abs_distance]
    norm_num [
      controlK9Ell, controlK9EllRat,
      activeL3SupportRadius, activeL3SupportRadiusRat,
      controlK9P0AbsDistanceEntryRat,
      controlK9P0RadiusAbsDistanceEntryRat,
      natAbsDiff]
    change |centeredBSplineP0KernelProfile 9 ((3 : Real) / (10 : Real)) (3 : Real) (0 : Real) - ((403691729091567253 : Real) / (2000000000000000000 : Real))| <= ((3530616842813889931 : Real) / (1000000000000000000000000000000000000 : Real))
    have hcert := cert.h (⟨0, by norm_num⟩ : CoeffIndex23)
    norm_num [controlK9P0AbsDistanceEntryRat, controlK9P0RadiusAbsDistanceEntryRat] at hcert
    simpa using hcert

theorem controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
    (cert : controlK9AnalyticP0AbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe controlK9AnalyticP0 controlK9P0 controlK9P0Radius := by
  intro i j
  fin_cases i
  · exact controlK9AnalyticP0_entry_hbox_row_0_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_1_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_2_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_3_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_4_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_5_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_6_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_7_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_8_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_9_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_10_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_11_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_12_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_13_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_14_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_15_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_16_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_17_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_18_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_19_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_20_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_21_of_abs_distance_cert cert j
  · exact controlK9AnalyticP0_entry_hbox_row_22_of_abs_distance_cert cert j


end CenteredCoeffBaseP0HboxImport
end PSDpd
end Q3
