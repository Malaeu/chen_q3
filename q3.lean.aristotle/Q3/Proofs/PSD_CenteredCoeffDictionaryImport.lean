import Q3.Proofs.PSD_CenteredCoeffPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffDictionaryImport

open CenteredCoeffPayloadImport

/-!
Exact dictionary data for the active Step 32F centered coefficient payloads.

The midpoint/radius matrix import records checked numerical matrices.  This
file records the generator-side finite dictionaries that those matrices came
from: the 23 packet centers and the L=3 finite prime-power shifts.

This is not yet a `CertifiedCenteredBSplineCoeffBlock`.  The remaining bridge is
to connect the analytic contract entries, or interval enclosures for them, to
the imported midpoint/radius payload.
-/

abbrev PrimeShiftIndexL3 := Fin 98

def activeL3Ell030Delta025CenterRatEntry : Nat -> Rat
  | 0 => ((-27 : Rat) / 10)
  | 1 => ((-49 : Rat) / 20)
  | 2 => ((-11 : Rat) / 5)
  | 3 => ((-39 : Rat) / 20)
  | 4 => ((-17 : Rat) / 10)
  | 5 => ((-29 : Rat) / 20)
  | 6 => ((-6 : Rat) / 5)
  | 7 => ((-19 : Rat) / 20)
  | 8 => ((-7 : Rat) / 10)
  | 9 => ((-9 : Rat) / 20)
  | 10 => ((-1 : Rat) / 5)
  | 11 => ((1 : Rat) / 20)
  | 12 => ((3 : Rat) / 10)
  | 13 => ((11 : Rat) / 20)
  | 14 => ((4 : Rat) / 5)
  | 15 => ((21 : Rat) / 20)
  | 16 => ((13 : Rat) / 10)
  | 17 => ((31 : Rat) / 20)
  | 18 => ((9 : Rat) / 5)
  | 19 => ((41 : Rat) / 20)
  | 20 => ((23 : Rat) / 10)
  | 21 => ((51 : Rat) / 20)
  | 22 => ((14 : Rat) / 5)
  | _ => 0

/-- The 23 packet centers used by the active L=3, ell=0.30, delta=0.25 blocks. -/
def activeL3Ell030Delta025Center (i : CoeffIndex23) : Real :=
  (activeL3Ell030Delta025CenterRatEntry i.1 : Real)

def activeL3PrimeBaseEntry : Nat -> Nat
  | 0 => 2
  | 1 => 3
  | 2 => 2
  | 3 => 5
  | 4 => 7
  | 5 => 2
  | 6 => 3
  | 7 => 11
  | 8 => 13
  | 9 => 2
  | 10 => 17
  | 11 => 19
  | 12 => 23
  | 13 => 5
  | 14 => 3
  | 15 => 29
  | 16 => 31
  | 17 => 2
  | 18 => 37
  | 19 => 41
  | 20 => 43
  | 21 => 47
  | 22 => 7
  | 23 => 53
  | 24 => 59
  | 25 => 61
  | 26 => 2
  | 27 => 67
  | 28 => 71
  | 29 => 73
  | 30 => 79
  | 31 => 3
  | 32 => 83
  | 33 => 89
  | 34 => 97
  | 35 => 101
  | 36 => 103
  | 37 => 107
  | 38 => 109
  | 39 => 113
  | 40 => 11
  | 41 => 5
  | 42 => 127
  | 43 => 2
  | 44 => 131
  | 45 => 137
  | 46 => 139
  | 47 => 149
  | 48 => 151
  | 49 => 157
  | 50 => 163
  | 51 => 167
  | 52 => 13
  | 53 => 173
  | 54 => 179
  | 55 => 181
  | 56 => 191
  | 57 => 193
  | 58 => 197
  | 59 => 199
  | 60 => 211
  | 61 => 223
  | 62 => 227
  | 63 => 229
  | 64 => 233
  | 65 => 239
  | 66 => 241
  | 67 => 3
  | 68 => 251
  | 69 => 2
  | 70 => 257
  | 71 => 263
  | 72 => 269
  | 73 => 271
  | 74 => 277
  | 75 => 281
  | 76 => 283
  | 77 => 17
  | 78 => 293
  | 79 => 307
  | 80 => 311
  | 81 => 313
  | 82 => 317
  | 83 => 331
  | 84 => 337
  | 85 => 7
  | 86 => 347
  | 87 => 349
  | 88 => 353
  | 89 => 359
  | 90 => 19
  | 91 => 367
  | 92 => 373
  | 93 => 379
  | 94 => 383
  | 95 => 389
  | 96 => 397
  | 97 => 401
  | _ => 0

def activeL3PrimeExponentEntry : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 4
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 2
  | 14 => 3
  | 15 => 1
  | 16 => 1
  | 17 => 5
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 2
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 4
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 1
  | 40 => 2
  | 41 => 3
  | 42 => 1
  | 43 => 7
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 1
  | 51 => 1
  | 52 => 2
  | 53 => 1
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 1
  | 63 => 1
  | 64 => 1
  | 65 => 1
  | 66 => 1
  | 67 => 5
  | 68 => 1
  | 69 => 8
  | 70 => 1
  | 71 => 1
  | 72 => 1
  | 73 => 1
  | 74 => 1
  | 75 => 1
  | 76 => 1
  | 77 => 2
  | 78 => 1
  | 79 => 1
  | 80 => 1
  | 81 => 1
  | 82 => 1
  | 83 => 1
  | 84 => 1
  | 85 => 3
  | 86 => 1
  | 87 => 1
  | 88 => 1
  | 89 => 1
  | 90 => 2
  | 91 => 1
  | 92 => 1
  | 93 => 1
  | 94 => 1
  | 95 => 1
  | 96 => 1
  | 97 => 1
  | _ => 0

/-- Prime base for the L=3 finite prime-power shift dictionary. -/
def activeL3PrimeBase (n : PrimeShiftIndexL3) : Nat :=
  activeL3PrimeBaseEntry n.1

/-- Prime-power exponent for the L=3 finite prime-power shift dictionary. -/
def activeL3PrimeExponent (n : PrimeShiftIndexL3) : Nat :=
  activeL3PrimeExponentEntry n.1

/-- Analytic prime-power shift `r * log p` for the L=3 dictionary. -/
def activeL3PrimeShift (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeExponent n : Real) * Real.log (activeL3PrimeBase n : Real)

/-- Analytic prime weight `log p / p^(r/2)`, written as `log p * exp(-(r log p)/2)`. -/
def activeL3PrimeWeight (n : PrimeShiftIndexL3) : Real :=
  Real.log (activeL3PrimeBase n : Real) * Real.exp (-(activeL3PrimeShift n) / 2)

structure CenteredCoeffDictionaryData where
  center : CoeffIndex23 -> Real
  weight : PrimeShiftIndexL3 -> Real
  shift : PrimeShiftIndexL3 -> Real

/-- Dictionary shared by the active primary and control L=3 blocks. -/
def activeL3Ell030Delta025DictionaryData : CenteredCoeffDictionaryData where
  center := activeL3Ell030Delta025Center
  weight := activeL3PrimeWeight
  shift := activeL3PrimeShift

def primaryK11Center : CoeffIndex23 -> Real := activeL3Ell030Delta025Center
def primaryK11PrimeWeight : PrimeShiftIndexL3 -> Real := activeL3PrimeWeight
def primaryK11PrimeShift : PrimeShiftIndexL3 -> Real := activeL3PrimeShift

def controlK9Center : CoeffIndex23 -> Real := activeL3Ell030Delta025Center
def controlK9PrimeWeight : PrimeShiftIndexL3 -> Real := activeL3PrimeWeight
def controlK9PrimeShift : PrimeShiftIndexL3 -> Real := activeL3PrimeShift

def primaryK11DictionaryData : CenteredCoeffDictionaryData where
  center := primaryK11Center
  weight := primaryK11PrimeWeight
  shift := primaryK11PrimeShift

def controlK9DictionaryData : CenteredCoeffDictionaryData where
  center := controlK9Center
  weight := controlK9PrimeWeight
  shift := controlK9PrimeShift

theorem primaryK11_hk : 0 < 11 := by
  norm_num

theorem controlK9_hk : 0 < 9 := by
  norm_num

theorem primaryK11_hell : 0 < primaryK11Ell := by
  norm_num [primaryK11Ell, primaryK11EllRat]

theorem controlK9_hell : 0 < controlK9Ell := by
  norm_num [controlK9Ell, controlK9EllRat]

/-- Concrete analytic contract generated from the active primary dictionary. -/
noncomputable def primaryK11CoeffAnalyticKernelContract :
    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 -> Complex) :=
  centeredBSplineCoeffAnalyticKernelContract
    11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
    primaryK11_hk primaryK11_hell

def primaryK11AnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11CoeffAnalyticKernelContract.toFormulaContract.C

def primaryK11AnalyticQ : Matrix BoundaryIndex2 CoeffIndex23 Real :=
  primaryK11CoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q

/-- Concrete analytic contract generated from the active control dictionary. -/
noncomputable def controlK9CoeffAnalyticKernelContract :
    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 -> Complex) :=
  centeredBSplineCoeffAnalyticKernelContract
    9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
    controlK9_hk controlK9_hell

def controlK9AnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9CoeffAnalyticKernelContract.toFormulaContract.C

def controlK9AnalyticQ : Matrix BoundaryIndex2 CoeffIndex23 Real :=
  controlK9CoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q

end CenteredCoeffDictionaryImport
end PSDpd
end Q3
