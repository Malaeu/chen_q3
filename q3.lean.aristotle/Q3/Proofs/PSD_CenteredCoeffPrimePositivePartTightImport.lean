import Q3.Proofs.PSD_CenteredCoeffPrimeEntryHboxImport
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_0_249
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_250_499

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 5000000

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimePositivePartTightImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffPrimeDictionaryBoundsImport

/-!
Step33A.1 tight scalar positive-part-power payload.

The coarse payload in `PSD_CenteredCoeffPrimeEntryHboxImport` remains available
as a fallback.  This module builds a sharper symbolic midpoint/radius payload
from certified PrimeCert log intervals for the active L=3 prime dictionary and
feeds the existing positivePartPower -> summand -> cardinal receiver chain.
-/


def activeL3PrimeLogLowerEntry : Nat -> Real
  | 0 => _root_.Q3.Proofs.PrimeCert.l_2
  | 1 => _root_.Q3.Proofs.PrimeCert.l_3
  | 2 => _root_.Q3.Proofs.PrimeCert.l_2
  | 3 => _root_.Q3.Proofs.PrimeCert.l_5
  | 4 => _root_.Q3.Proofs.PrimeCert.l_7
  | 5 => _root_.Q3.Proofs.PrimeCert.l_2
  | 6 => _root_.Q3.Proofs.PrimeCert.l_3
  | 7 => _root_.Q3.Proofs.PrimeCert.l_11
  | 8 => _root_.Q3.Proofs.PrimeCert.l_13
  | 9 => _root_.Q3.Proofs.PrimeCert.l_2
  | 10 => _root_.Q3.Proofs.PrimeCert.l_17
  | 11 => _root_.Q3.Proofs.PrimeCert.l_19
  | 12 => _root_.Q3.Proofs.PrimeCert.l_23
  | 13 => _root_.Q3.Proofs.PrimeCert.l_5
  | 14 => _root_.Q3.Proofs.PrimeCert.l_3
  | 15 => _root_.Q3.Proofs.PrimeCert.l_29
  | 16 => _root_.Q3.Proofs.PrimeCert.l_31
  | 17 => _root_.Q3.Proofs.PrimeCert.l_2
  | 18 => _root_.Q3.Proofs.PrimeCert.l_37
  | 19 => _root_.Q3.Proofs.PrimeCert.l_41
  | 20 => _root_.Q3.Proofs.PrimeCert.l_43
  | 21 => _root_.Q3.Proofs.PrimeCert.l_47
  | 22 => _root_.Q3.Proofs.PrimeCert.l_7
  | 23 => _root_.Q3.Proofs.PrimeCert.l_53
  | 24 => _root_.Q3.Proofs.PrimeCert.l_59
  | 25 => _root_.Q3.Proofs.PrimeCert.l_61
  | 26 => _root_.Q3.Proofs.PrimeCert.l_2
  | 27 => _root_.Q3.Proofs.PrimeCert.l_67
  | 28 => _root_.Q3.Proofs.PrimeCert.l_71
  | 29 => _root_.Q3.Proofs.PrimeCert.l_73
  | 30 => _root_.Q3.Proofs.PrimeCert.l_79
  | 31 => _root_.Q3.Proofs.PrimeCert.l_3
  | 32 => _root_.Q3.Proofs.PrimeCert.l_83
  | 33 => _root_.Q3.Proofs.PrimeCert.l_89
  | 34 => _root_.Q3.Proofs.PrimeCert.l_97
  | 35 => _root_.Q3.Proofs.PrimeCert.l_101
  | 36 => _root_.Q3.Proofs.PrimeCert.l_103
  | 37 => _root_.Q3.Proofs.PrimeCert.l_107
  | 38 => _root_.Q3.Proofs.PrimeCert.l_109
  | 39 => _root_.Q3.Proofs.PrimeCert.l_113
  | 40 => _root_.Q3.Proofs.PrimeCert.l_11
  | 41 => _root_.Q3.Proofs.PrimeCert.l_5
  | 42 => _root_.Q3.Proofs.PrimeCert.l_127
  | 43 => _root_.Q3.Proofs.PrimeCert.l_2
  | 44 => _root_.Q3.Proofs.PrimeCert.l_131
  | 45 => _root_.Q3.Proofs.PrimeCert.l_137
  | 46 => _root_.Q3.Proofs.PrimeCert.l_139
  | 47 => _root_.Q3.Proofs.PrimeCert.l_149
  | 48 => _root_.Q3.Proofs.PrimeCert.l_151
  | 49 => _root_.Q3.Proofs.PrimeCert.l_157
  | 50 => _root_.Q3.Proofs.PrimeCert.l_163
  | 51 => _root_.Q3.Proofs.PrimeCert.l_167
  | 52 => _root_.Q3.Proofs.PrimeCert.l_13
  | 53 => _root_.Q3.Proofs.PrimeCert.l_173
  | 54 => _root_.Q3.Proofs.PrimeCert.l_179
  | 55 => _root_.Q3.Proofs.PrimeCert.l_181
  | 56 => _root_.Q3.Proofs.PrimeCert.l_191
  | 57 => _root_.Q3.Proofs.PrimeCert.l_193
  | 58 => _root_.Q3.Proofs.PrimeCert.l_197
  | 59 => _root_.Q3.Proofs.PrimeCert.l_199
  | 60 => _root_.Q3.Proofs.PrimeCert.l_211
  | 61 => _root_.Q3.Proofs.PrimeCert.l_223
  | 62 => _root_.Q3.Proofs.PrimeCert.l_227
  | 63 => _root_.Q3.Proofs.PrimeCert.l_229
  | 64 => _root_.Q3.Proofs.PrimeCert.l_233
  | 65 => _root_.Q3.Proofs.PrimeCert.l_239
  | 66 => _root_.Q3.Proofs.PrimeCert.l_241
  | 67 => _root_.Q3.Proofs.PrimeCert.l_3
  | 68 => _root_.Q3.Proofs.PrimeCert.l_251
  | 69 => _root_.Q3.Proofs.PrimeCert.l_2
  | 70 => _root_.Q3.Proofs.PrimeCert.l_257
  | 71 => _root_.Q3.Proofs.PrimeCert.l_263
  | 72 => _root_.Q3.Proofs.PrimeCert.l_269
  | 73 => _root_.Q3.Proofs.PrimeCert.l_271
  | 74 => _root_.Q3.Proofs.PrimeCert.l_277
  | 75 => _root_.Q3.Proofs.PrimeCert.l_281
  | 76 => _root_.Q3.Proofs.PrimeCert.l_283
  | 77 => _root_.Q3.Proofs.PrimeCert.l_17
  | 78 => _root_.Q3.Proofs.PrimeCert.l_293
  | 79 => _root_.Q3.Proofs.PrimeCert.l_307
  | 80 => _root_.Q3.Proofs.PrimeCert.l_311
  | 81 => _root_.Q3.Proofs.PrimeCert.l_313
  | 82 => _root_.Q3.Proofs.PrimeCert.l_317
  | 83 => _root_.Q3.Proofs.PrimeCert.l_331
  | 84 => _root_.Q3.Proofs.PrimeCert.l_337
  | 85 => _root_.Q3.Proofs.PrimeCert.l_7
  | 86 => _root_.Q3.Proofs.PrimeCert.l_347
  | 87 => _root_.Q3.Proofs.PrimeCert.l_349
  | 88 => _root_.Q3.Proofs.PrimeCert.l_353
  | 89 => _root_.Q3.Proofs.PrimeCert.l_359
  | 90 => _root_.Q3.Proofs.PrimeCert.l_19
  | 91 => _root_.Q3.Proofs.PrimeCert.l_367
  | 92 => _root_.Q3.Proofs.PrimeCert.l_373
  | 93 => _root_.Q3.Proofs.PrimeCert.l_379
  | 94 => _root_.Q3.Proofs.PrimeCert.l_383
  | 95 => _root_.Q3.Proofs.PrimeCert.l_389
  | 96 => _root_.Q3.Proofs.PrimeCert.l_397
  | 97 => _root_.Q3.Proofs.PrimeCert.l_401
  | _ => 0

def activeL3PrimeLogLower (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogLowerEntry n.1

def activeL3PrimeLogUpperEntry : Nat -> Real
  | 0 => _root_.Q3.Proofs.PrimeCert.u_2
  | 1 => _root_.Q3.Proofs.PrimeCert.u_3
  | 2 => _root_.Q3.Proofs.PrimeCert.u_2
  | 3 => _root_.Q3.Proofs.PrimeCert.u_5
  | 4 => _root_.Q3.Proofs.PrimeCert.u_7
  | 5 => _root_.Q3.Proofs.PrimeCert.u_2
  | 6 => _root_.Q3.Proofs.PrimeCert.u_3
  | 7 => _root_.Q3.Proofs.PrimeCert.u_11
  | 8 => _root_.Q3.Proofs.PrimeCert.u_13
  | 9 => _root_.Q3.Proofs.PrimeCert.u_2
  | 10 => _root_.Q3.Proofs.PrimeCert.u_17
  | 11 => _root_.Q3.Proofs.PrimeCert.u_19
  | 12 => _root_.Q3.Proofs.PrimeCert.u_23
  | 13 => _root_.Q3.Proofs.PrimeCert.u_5
  | 14 => _root_.Q3.Proofs.PrimeCert.u_3
  | 15 => _root_.Q3.Proofs.PrimeCert.u_29
  | 16 => _root_.Q3.Proofs.PrimeCert.u_31
  | 17 => _root_.Q3.Proofs.PrimeCert.u_2
  | 18 => _root_.Q3.Proofs.PrimeCert.u_37
  | 19 => _root_.Q3.Proofs.PrimeCert.u_41
  | 20 => _root_.Q3.Proofs.PrimeCert.u_43
  | 21 => _root_.Q3.Proofs.PrimeCert.u_47
  | 22 => _root_.Q3.Proofs.PrimeCert.u_7
  | 23 => _root_.Q3.Proofs.PrimeCert.u_53
  | 24 => _root_.Q3.Proofs.PrimeCert.u_59
  | 25 => _root_.Q3.Proofs.PrimeCert.u_61
  | 26 => _root_.Q3.Proofs.PrimeCert.u_2
  | 27 => _root_.Q3.Proofs.PrimeCert.u_67
  | 28 => _root_.Q3.Proofs.PrimeCert.u_71
  | 29 => _root_.Q3.Proofs.PrimeCert.u_73
  | 30 => _root_.Q3.Proofs.PrimeCert.u_79
  | 31 => _root_.Q3.Proofs.PrimeCert.u_3
  | 32 => _root_.Q3.Proofs.PrimeCert.u_83
  | 33 => _root_.Q3.Proofs.PrimeCert.u_89
  | 34 => _root_.Q3.Proofs.PrimeCert.u_97
  | 35 => _root_.Q3.Proofs.PrimeCert.u_101
  | 36 => _root_.Q3.Proofs.PrimeCert.u_103
  | 37 => _root_.Q3.Proofs.PrimeCert.u_107
  | 38 => _root_.Q3.Proofs.PrimeCert.u_109
  | 39 => _root_.Q3.Proofs.PrimeCert.u_113
  | 40 => _root_.Q3.Proofs.PrimeCert.u_11
  | 41 => _root_.Q3.Proofs.PrimeCert.u_5
  | 42 => _root_.Q3.Proofs.PrimeCert.u_127
  | 43 => _root_.Q3.Proofs.PrimeCert.u_2
  | 44 => _root_.Q3.Proofs.PrimeCert.u_131
  | 45 => _root_.Q3.Proofs.PrimeCert.u_137
  | 46 => _root_.Q3.Proofs.PrimeCert.u_139
  | 47 => _root_.Q3.Proofs.PrimeCert.u_149
  | 48 => _root_.Q3.Proofs.PrimeCert.u_151
  | 49 => _root_.Q3.Proofs.PrimeCert.u_157
  | 50 => _root_.Q3.Proofs.PrimeCert.u_163
  | 51 => _root_.Q3.Proofs.PrimeCert.u_167
  | 52 => _root_.Q3.Proofs.PrimeCert.u_13
  | 53 => _root_.Q3.Proofs.PrimeCert.u_173
  | 54 => _root_.Q3.Proofs.PrimeCert.u_179
  | 55 => _root_.Q3.Proofs.PrimeCert.u_181
  | 56 => _root_.Q3.Proofs.PrimeCert.u_191
  | 57 => _root_.Q3.Proofs.PrimeCert.u_193
  | 58 => _root_.Q3.Proofs.PrimeCert.u_197
  | 59 => _root_.Q3.Proofs.PrimeCert.u_199
  | 60 => _root_.Q3.Proofs.PrimeCert.u_211
  | 61 => _root_.Q3.Proofs.PrimeCert.u_223
  | 62 => _root_.Q3.Proofs.PrimeCert.u_227
  | 63 => _root_.Q3.Proofs.PrimeCert.u_229
  | 64 => _root_.Q3.Proofs.PrimeCert.u_233
  | 65 => _root_.Q3.Proofs.PrimeCert.u_239
  | 66 => _root_.Q3.Proofs.PrimeCert.u_241
  | 67 => _root_.Q3.Proofs.PrimeCert.u_3
  | 68 => _root_.Q3.Proofs.PrimeCert.u_251
  | 69 => _root_.Q3.Proofs.PrimeCert.u_2
  | 70 => _root_.Q3.Proofs.PrimeCert.u_257
  | 71 => _root_.Q3.Proofs.PrimeCert.u_263
  | 72 => _root_.Q3.Proofs.PrimeCert.u_269
  | 73 => _root_.Q3.Proofs.PrimeCert.u_271
  | 74 => _root_.Q3.Proofs.PrimeCert.u_277
  | 75 => _root_.Q3.Proofs.PrimeCert.u_281
  | 76 => _root_.Q3.Proofs.PrimeCert.u_283
  | 77 => _root_.Q3.Proofs.PrimeCert.u_17
  | 78 => _root_.Q3.Proofs.PrimeCert.u_293
  | 79 => _root_.Q3.Proofs.PrimeCert.u_307
  | 80 => _root_.Q3.Proofs.PrimeCert.u_311
  | 81 => _root_.Q3.Proofs.PrimeCert.u_313
  | 82 => _root_.Q3.Proofs.PrimeCert.u_317
  | 83 => _root_.Q3.Proofs.PrimeCert.u_331
  | 84 => _root_.Q3.Proofs.PrimeCert.u_337
  | 85 => _root_.Q3.Proofs.PrimeCert.u_7
  | 86 => _root_.Q3.Proofs.PrimeCert.u_347
  | 87 => _root_.Q3.Proofs.PrimeCert.u_349
  | 88 => _root_.Q3.Proofs.PrimeCert.u_353
  | 89 => _root_.Q3.Proofs.PrimeCert.u_359
  | 90 => _root_.Q3.Proofs.PrimeCert.u_19
  | 91 => _root_.Q3.Proofs.PrimeCert.u_367
  | 92 => _root_.Q3.Proofs.PrimeCert.u_373
  | 93 => _root_.Q3.Proofs.PrimeCert.u_379
  | 94 => _root_.Q3.Proofs.PrimeCert.u_383
  | 95 => _root_.Q3.Proofs.PrimeCert.u_389
  | 96 => _root_.Q3.Proofs.PrimeCert.u_397
  | 97 => _root_.Q3.Proofs.PrimeCert.u_401
  | _ => 0

def activeL3PrimeLogUpper (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogUpperEntry n.1

theorem activeL3PrimeLogLower_le_log (n : PrimeShiftIndexL3) :
    activeL3PrimeLogLower n <= Real.log (activeL3PrimeBase n : Real) := by
  fin_cases n
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_3 <= Real.log (3 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_3_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_5 <= Real.log (5 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_5_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_7 <= Real.log (7 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_7_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_3 <= Real.log (3 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_3_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_11 <= Real.log (11 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_11_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_13 <= Real.log (13 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_13_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_17 <= Real.log (17 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_17_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_19 <= Real.log (19 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_19_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_23 <= Real.log (23 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_23_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_5 <= Real.log (5 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_5_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_3 <= Real.log (3 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_3_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_29 <= Real.log (29 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_29_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_31 <= Real.log (31 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_31_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_37 <= Real.log (37 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_37_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_41 <= Real.log (41 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_41_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_43 <= Real.log (43 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_43_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_47 <= Real.log (47 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_47_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_7 <= Real.log (7 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_7_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_53 <= Real.log (53 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_53_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_59 <= Real.log (59 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_59_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_61 <= Real.log (61 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_61_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_67 <= Real.log (67 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_67_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_71 <= Real.log (71 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_71_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_73 <= Real.log (73 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_73_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_79 <= Real.log (79 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_79_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_3 <= Real.log (3 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_3_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_83 <= Real.log (83 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_83_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_89 <= Real.log (89 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_89_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_97 <= Real.log (97 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_97_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_101 <= Real.log (101 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_101_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_103 <= Real.log (103 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_103_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_107 <= Real.log (107 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_107_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_109 <= Real.log (109 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_109_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_113 <= Real.log (113 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_113_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_11 <= Real.log (11 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_11_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_5 <= Real.log (5 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_5_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_127 <= Real.log (127 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_127_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_131 <= Real.log (131 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_131_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_137 <= Real.log (137 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_137_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_139 <= Real.log (139 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_139_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_149 <= Real.log (149 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_149_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_151 <= Real.log (151 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_151_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_157 <= Real.log (157 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_157_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_163 <= Real.log (163 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_163_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_167 <= Real.log (167 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_167_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_13 <= Real.log (13 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_13_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_173 <= Real.log (173 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_173_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_179 <= Real.log (179 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_179_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_181 <= Real.log (181 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_181_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_191 <= Real.log (191 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_191_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_193 <= Real.log (193 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_193_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_197 <= Real.log (197 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_197_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_199 <= Real.log (199 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_199_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_211 <= Real.log (211 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_211_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_223 <= Real.log (223 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_223_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_227 <= Real.log (227 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_227_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_229 <= Real.log (229 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_229_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_233 <= Real.log (233 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_233_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_239 <= Real.log (239 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_239_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_241 <= Real.log (241 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_241_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_3 <= Real.log (3 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_3_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_251 <= Real.log (251 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_251_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_2 <= Real.log (2 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_2_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_257 <= Real.log (257 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_257_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_263 <= Real.log (263 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_263_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_269 <= Real.log (269 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_269_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_271 <= Real.log (271 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_271_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_277 <= Real.log (277 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_277_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_281 <= Real.log (281 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_281_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_283 <= Real.log (283 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_283_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_17 <= Real.log (17 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_17_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_293 <= Real.log (293 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_293_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_307 <= Real.log (307 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_307_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_311 <= Real.log (311 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_311_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_313 <= Real.log (313 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_313_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_317 <= Real.log (317 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_317_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_331 <= Real.log (331 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_331_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_337 <= Real.log (337 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_337_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_7 <= Real.log (7 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_7_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_347 <= Real.log (347 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_347_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_349 <= Real.log (349 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_349_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_353 <= Real.log (353 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_353_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_359 <= Real.log (359 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_359_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_19 <= Real.log (19 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_19_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_367 <= Real.log (367 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_367_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_373 <= Real.log (373 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_373_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_379 <= Real.log (379 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_379_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_383 <= Real.log (383 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_383_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_389 <= Real.log (389 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_389_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_397 <= Real.log (397 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_397_le_log
  · change _root_.Q3.Proofs.PrimeCert.l_401 <= Real.log (401 : Real)
    exact _root_.Q3.Proofs.PrimeCert.l_401_le_log

theorem activeL3PrimeLog_le_upper (n : PrimeShiftIndexL3) :
    Real.log (activeL3PrimeBase n : Real) <= activeL3PrimeLogUpper n := by
  fin_cases n
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (3 : Real) <= _root_.Q3.Proofs.PrimeCert.u_3
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_3
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (5 : Real) <= _root_.Q3.Proofs.PrimeCert.u_5
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_5
  · change Real.log (7 : Real) <= _root_.Q3.Proofs.PrimeCert.u_7
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_7
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (3 : Real) <= _root_.Q3.Proofs.PrimeCert.u_3
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_3
  · change Real.log (11 : Real) <= _root_.Q3.Proofs.PrimeCert.u_11
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_11
  · change Real.log (13 : Real) <= _root_.Q3.Proofs.PrimeCert.u_13
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_13
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (17 : Real) <= _root_.Q3.Proofs.PrimeCert.u_17
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_17
  · change Real.log (19 : Real) <= _root_.Q3.Proofs.PrimeCert.u_19
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_19
  · change Real.log (23 : Real) <= _root_.Q3.Proofs.PrimeCert.u_23
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_23
  · change Real.log (5 : Real) <= _root_.Q3.Proofs.PrimeCert.u_5
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_5
  · change Real.log (3 : Real) <= _root_.Q3.Proofs.PrimeCert.u_3
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_3
  · change Real.log (29 : Real) <= _root_.Q3.Proofs.PrimeCert.u_29
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_29
  · change Real.log (31 : Real) <= _root_.Q3.Proofs.PrimeCert.u_31
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_31
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (37 : Real) <= _root_.Q3.Proofs.PrimeCert.u_37
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_37
  · change Real.log (41 : Real) <= _root_.Q3.Proofs.PrimeCert.u_41
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_41
  · change Real.log (43 : Real) <= _root_.Q3.Proofs.PrimeCert.u_43
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_43
  · change Real.log (47 : Real) <= _root_.Q3.Proofs.PrimeCert.u_47
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_47
  · change Real.log (7 : Real) <= _root_.Q3.Proofs.PrimeCert.u_7
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_7
  · change Real.log (53 : Real) <= _root_.Q3.Proofs.PrimeCert.u_53
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_53
  · change Real.log (59 : Real) <= _root_.Q3.Proofs.PrimeCert.u_59
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_59
  · change Real.log (61 : Real) <= _root_.Q3.Proofs.PrimeCert.u_61
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_61
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (67 : Real) <= _root_.Q3.Proofs.PrimeCert.u_67
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_67
  · change Real.log (71 : Real) <= _root_.Q3.Proofs.PrimeCert.u_71
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_71
  · change Real.log (73 : Real) <= _root_.Q3.Proofs.PrimeCert.u_73
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_73
  · change Real.log (79 : Real) <= _root_.Q3.Proofs.PrimeCert.u_79
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_79
  · change Real.log (3 : Real) <= _root_.Q3.Proofs.PrimeCert.u_3
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_3
  · change Real.log (83 : Real) <= _root_.Q3.Proofs.PrimeCert.u_83
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_83
  · change Real.log (89 : Real) <= _root_.Q3.Proofs.PrimeCert.u_89
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_89
  · change Real.log (97 : Real) <= _root_.Q3.Proofs.PrimeCert.u_97
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_97
  · change Real.log (101 : Real) <= _root_.Q3.Proofs.PrimeCert.u_101
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_101
  · change Real.log (103 : Real) <= _root_.Q3.Proofs.PrimeCert.u_103
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_103
  · change Real.log (107 : Real) <= _root_.Q3.Proofs.PrimeCert.u_107
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_107
  · change Real.log (109 : Real) <= _root_.Q3.Proofs.PrimeCert.u_109
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_109
  · change Real.log (113 : Real) <= _root_.Q3.Proofs.PrimeCert.u_113
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_113
  · change Real.log (11 : Real) <= _root_.Q3.Proofs.PrimeCert.u_11
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_11
  · change Real.log (5 : Real) <= _root_.Q3.Proofs.PrimeCert.u_5
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_5
  · change Real.log (127 : Real) <= _root_.Q3.Proofs.PrimeCert.u_127
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_127
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (131 : Real) <= _root_.Q3.Proofs.PrimeCert.u_131
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_131
  · change Real.log (137 : Real) <= _root_.Q3.Proofs.PrimeCert.u_137
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_137
  · change Real.log (139 : Real) <= _root_.Q3.Proofs.PrimeCert.u_139
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_139
  · change Real.log (149 : Real) <= _root_.Q3.Proofs.PrimeCert.u_149
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_149
  · change Real.log (151 : Real) <= _root_.Q3.Proofs.PrimeCert.u_151
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_151
  · change Real.log (157 : Real) <= _root_.Q3.Proofs.PrimeCert.u_157
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_157
  · change Real.log (163 : Real) <= _root_.Q3.Proofs.PrimeCert.u_163
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_163
  · change Real.log (167 : Real) <= _root_.Q3.Proofs.PrimeCert.u_167
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_167
  · change Real.log (13 : Real) <= _root_.Q3.Proofs.PrimeCert.u_13
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_13
  · change Real.log (173 : Real) <= _root_.Q3.Proofs.PrimeCert.u_173
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_173
  · change Real.log (179 : Real) <= _root_.Q3.Proofs.PrimeCert.u_179
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_179
  · change Real.log (181 : Real) <= _root_.Q3.Proofs.PrimeCert.u_181
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_181
  · change Real.log (191 : Real) <= _root_.Q3.Proofs.PrimeCert.u_191
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_191
  · change Real.log (193 : Real) <= _root_.Q3.Proofs.PrimeCert.u_193
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_193
  · change Real.log (197 : Real) <= _root_.Q3.Proofs.PrimeCert.u_197
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_197
  · change Real.log (199 : Real) <= _root_.Q3.Proofs.PrimeCert.u_199
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_199
  · change Real.log (211 : Real) <= _root_.Q3.Proofs.PrimeCert.u_211
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_211
  · change Real.log (223 : Real) <= _root_.Q3.Proofs.PrimeCert.u_223
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_223
  · change Real.log (227 : Real) <= _root_.Q3.Proofs.PrimeCert.u_227
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_227
  · change Real.log (229 : Real) <= _root_.Q3.Proofs.PrimeCert.u_229
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_229
  · change Real.log (233 : Real) <= _root_.Q3.Proofs.PrimeCert.u_233
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_233
  · change Real.log (239 : Real) <= _root_.Q3.Proofs.PrimeCert.u_239
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_239
  · change Real.log (241 : Real) <= _root_.Q3.Proofs.PrimeCert.u_241
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_241
  · change Real.log (3 : Real) <= _root_.Q3.Proofs.PrimeCert.u_3
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_3
  · change Real.log (251 : Real) <= _root_.Q3.Proofs.PrimeCert.u_251
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_251
  · change Real.log (2 : Real) <= _root_.Q3.Proofs.PrimeCert.u_2
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_2
  · change Real.log (257 : Real) <= _root_.Q3.Proofs.PrimeCert.u_257
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_257
  · change Real.log (263 : Real) <= _root_.Q3.Proofs.PrimeCert.u_263
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_263
  · change Real.log (269 : Real) <= _root_.Q3.Proofs.PrimeCert.u_269
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_269
  · change Real.log (271 : Real) <= _root_.Q3.Proofs.PrimeCert.u_271
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_271
  · change Real.log (277 : Real) <= _root_.Q3.Proofs.PrimeCert.u_277
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_277
  · change Real.log (281 : Real) <= _root_.Q3.Proofs.PrimeCert.u_281
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_281
  · change Real.log (283 : Real) <= _root_.Q3.Proofs.PrimeCert.u_283
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_283
  · change Real.log (17 : Real) <= _root_.Q3.Proofs.PrimeCert.u_17
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_17
  · change Real.log (293 : Real) <= _root_.Q3.Proofs.PrimeCert.u_293
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_293
  · change Real.log (307 : Real) <= _root_.Q3.Proofs.PrimeCert.u_307
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_307
  · change Real.log (311 : Real) <= _root_.Q3.Proofs.PrimeCert.u_311
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_311
  · change Real.log (313 : Real) <= _root_.Q3.Proofs.PrimeCert.u_313
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_313
  · change Real.log (317 : Real) <= _root_.Q3.Proofs.PrimeCert.u_317
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_317
  · change Real.log (331 : Real) <= _root_.Q3.Proofs.PrimeCert.u_331
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_331
  · change Real.log (337 : Real) <= _root_.Q3.Proofs.PrimeCert.u_337
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_337
  · change Real.log (7 : Real) <= _root_.Q3.Proofs.PrimeCert.u_7
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_7
  · change Real.log (347 : Real) <= _root_.Q3.Proofs.PrimeCert.u_347
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_347
  · change Real.log (349 : Real) <= _root_.Q3.Proofs.PrimeCert.u_349
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_349
  · change Real.log (353 : Real) <= _root_.Q3.Proofs.PrimeCert.u_353
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_353
  · change Real.log (359 : Real) <= _root_.Q3.Proofs.PrimeCert.u_359
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_359
  · change Real.log (19 : Real) <= _root_.Q3.Proofs.PrimeCert.u_19
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_19
  · change Real.log (367 : Real) <= _root_.Q3.Proofs.PrimeCert.u_367
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_367
  · change Real.log (373 : Real) <= _root_.Q3.Proofs.PrimeCert.u_373
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_373
  · change Real.log (379 : Real) <= _root_.Q3.Proofs.PrimeCert.u_379
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_379
  · change Real.log (383 : Real) <= _root_.Q3.Proofs.PrimeCert.u_383
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_383
  · change Real.log (389 : Real) <= _root_.Q3.Proofs.PrimeCert.u_389
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_389
  · change Real.log (397 : Real) <= _root_.Q3.Proofs.PrimeCert.u_397
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_397
  · change Real.log (401 : Real) <= _root_.Q3.Proofs.PrimeCert.u_401
    exact _root_.Q3.Proofs.PrimeCert.log_le_u_401

def activeL3PrimeShiftLower (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeExponent n : Real) * activeL3PrimeLogLower n

def activeL3PrimeShiftUpper (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeExponent n : Real) * activeL3PrimeLogUpper n

theorem activeL3PrimeShift_tight_bounds (n : PrimeShiftIndexL3) :
    activeL3PrimeShiftLower n <= activeL3PrimeShift n ∧
      activeL3PrimeShift n <= activeL3PrimeShiftUpper n := by
  have hexp_nonneg : 0 <= (activeL3PrimeExponent n : Real) := by positivity
  constructor
  · simpa [activeL3PrimeShift, activeL3PrimeShiftLower] using
      mul_le_mul_of_nonneg_left
        (activeL3PrimeLogLower_le_log n) hexp_nonneg
  · simpa [activeL3PrimeShift, activeL3PrimeShiftUpper] using
      mul_le_mul_of_nonneg_left
        (activeL3PrimeLog_le_upper n) hexp_nonneg

private theorem abs_sub_mid_le_half_width {lo y hi : Real}
    (hlo : lo <= y) (hhi : y <= hi) :
    |y - ((lo + hi) / 2)| <= (hi - lo) / 2 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem positivePartPower_succ_mono (d : Nat) :
    Monotone (positivePartPower (d + 1)) := by
  intro x y hxy
  rw [positivePartPower_succ_eq_max d x, positivePartPower_succ_eq_max d y]
  exact pow_le_pow_left₀ (le_max_right x 0) (max_le_max hxy le_rfl) (d + 1)

private theorem positivePartPower23_mono :
    Monotone (positivePartPower (bsplineAutocorrDegree 11)) := by
  simpa [bsplineAutocorrDegree] using positivePartPower_succ_mono 22

private theorem positivePartPower19_mono :
    Monotone (positivePartPower (bsplineAutocorrDegree 9)) := by
  simpa [bsplineAutocorrDegree] using positivePartPower_succ_mono 18

private theorem positivePartPower_hbox_of_bounds
    {d : Nat} {x lo hi : Real}
    (hmono : Monotone (positivePartPower d))
    (hlo : lo <= x) (hhi : x <= hi) :
    |positivePartPower d x -
      ((positivePartPower d lo + positivePartPower d hi) / 2)| <=
        (positivePartPower d hi - positivePartPower d lo) / 2 :=
  abs_sub_mid_le_half_width (hmono hlo) (hmono hhi)


def activeL3PrimeLogMid (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeLogLower n + activeL3PrimeLogUpper n) / 2

def activeL3PrimeLogRad (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeLogUpper n - activeL3PrimeLogLower n) / 2

def activeL3PrimeExpMid (n : PrimeShiftIndexL3) : Real :=
  Real.exp (-(activeL3PrimeShift n) / 2)

def activeL3PrimeExpRad (_n : PrimeShiftIndexL3) : Real :=
  0

def activeL3PrimeWeightMid (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogMid n * activeL3PrimeExpMid n

def activeL3PrimeWeightRad (n : PrimeShiftIndexL3) : Real :=
  (|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
      activeL3PrimeExpRad n +
    activeL3PrimeLogRad n * |activeL3PrimeExpMid n|

theorem activeL3PrimeLog_hbox_of_tight_payload :
    ∀ n,
      |Real.log (activeL3PrimeBase n : Real) - activeL3PrimeLogMid n| <=
        activeL3PrimeLogRad n := by
  intro n
  simpa [activeL3PrimeLogMid, activeL3PrimeLogRad] using
    abs_sub_mid_le_half_width
      (lo := activeL3PrimeLogLower n)
      (y := Real.log (activeL3PrimeBase n : Real))
      (hi := activeL3PrimeLogUpper n)
      (activeL3PrimeLogLower_le_log n)
      (activeL3PrimeLog_le_upper n)

theorem activeL3PrimeExp_exact_hbox :
    ∀ n,
      |Real.exp (-(activeL3PrimeShift n) / 2) - activeL3PrimeExpMid n| <=
        activeL3PrimeExpRad n := by
  intro n
  simp [activeL3PrimeExpMid, activeL3PrimeExpRad]

theorem activeL3PrimeLogLower_le_upper (n : PrimeShiftIndexL3) :
    activeL3PrimeLogLower n <= activeL3PrimeLogUpper n :=
  le_trans (activeL3PrimeLogLower_le_log n) (activeL3PrimeLog_le_upper n)

theorem activeL3PrimeLogRad_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeLogRad n := by
  have h := activeL3PrimeLogLower_le_upper n
  dsimp [activeL3PrimeLogRad]
  linarith

theorem activeL3PrimeExpMid_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeExpMid n := by
  simpa [activeL3PrimeExpMid] using
    Real.exp_pos (-(activeL3PrimeShift n) / 2)

theorem activeL3PrimeExpMid_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeExpMid n :=
  le_of_lt (activeL3PrimeExpMid_pos n)

theorem activeL3PrimeExpMid_le_one (n : PrimeShiftIndexL3) :
    activeL3PrimeExpMid n <= 1 := by
  have hshift : 0 <= activeL3PrimeShift n :=
    activeL3PrimeShift_nonneg n
  have harg : -(activeL3PrimeShift n) / 2 <= 0 := by
    nlinarith
  have h := (Real.exp_le_exp).2 harg
  simpa [activeL3PrimeExpMid] using h

theorem activeL3PrimeExpMid_bounds_of_shift_exp_bounds
    (n : PrimeShiftIndexL3) {lower upper : Real}
    (hlower : lower <= Real.exp (-activeL3PrimeShiftUpper n / 2))
    (hupper : Real.exp (-activeL3PrimeShiftLower n / 2) <= upper) :
    lower <= activeL3PrimeExpMid n ∧ activeL3PrimeExpMid n <= upper := by
  have hshift := activeL3PrimeShift_tight_bounds n
  simpa [activeL3PrimeExpMid] using
    _root_.Q3.Proofs.PrimeCert.exp_neg_half_bounds_of_bounds
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (lower := lower)
      (upper := upper)
      hshift.1 hshift.2 hlower hupper

theorem activeL3PrimeExpMid_hbox_of_shift_exp_bounds
    (n : PrimeShiftIndexL3) {lower upper : Real}
    (hlower : lower <= Real.exp (-activeL3PrimeShiftUpper n / 2))
    (hupper : Real.exp (-activeL3PrimeShiftLower n / 2) <= upper) :
    |activeL3PrimeExpMid n - ((lower + upper) / 2)| <=
      (upper - lower) / 2 := by
  have hbounds :=
    activeL3PrimeExpMid_bounds_of_shift_exp_bounds
      n hlower hupper
  exact abs_sub_mid_le_half_width hbounds.1 hbounds.2

theorem activeL3PrimeWeight_mid_eq :
    ∀ n,
      activeL3PrimeWeightMid n =
        activeL3PrimeLogMid n * activeL3PrimeExpMid n := by
  intro n
  rfl

theorem activeL3PrimeWeight_rad_bound :
    ∀ n,
      (|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
          activeL3PrimeExpRad n +
        activeL3PrimeLogRad n * |activeL3PrimeExpMid n| <=
          activeL3PrimeWeightRad n := by
  intro n
  dsimp [activeL3PrimeWeightRad]
  exact le_rfl

theorem activeL3PrimeWeightRad_eq_logRad_mul_expMid
    (n : PrimeShiftIndexL3) :
    activeL3PrimeWeightRad n =
      activeL3PrimeLogRad n * activeL3PrimeExpMid n := by
  dsimp [activeL3PrimeWeightRad, activeL3PrimeExpRad]
  rw [abs_of_nonneg (activeL3PrimeExpMid_nonneg n)]
  ring

theorem abs_activeL3PrimeWeightMid_eq
    (n : PrimeShiftIndexL3) :
    |activeL3PrimeWeightMid n| =
      |activeL3PrimeLogMid n| * activeL3PrimeExpMid n := by
  rw [activeL3PrimeWeightMid]
  rw [abs_mul]
  rw [abs_of_nonneg (activeL3PrimeExpMid_nonneg n)]

theorem activeL3PrimeWeightRad_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeWeightRad n := by
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  exact mul_nonneg (activeL3PrimeLogRad_nonneg n)
    (activeL3PrimeExpMid_nonneg n)


private theorem scaled_minus_arg_bounds
    (center shift lo hi ell scale offset m : Real)
    (hell : 0 < ell) (hscale : 0 <= scale)
    (hlo : lo <= shift) (hhi : shift <= hi) :
    scale * ((center - hi) / ell) + offset - m <=
      scale * ((center - shift) / ell) + offset - m ∧
    scale * ((center - shift) / ell) + offset - m <=
      scale * ((center - lo) / ell) + offset - m := by
  have hsub_low : center - hi <= center - shift := by linarith
  have hdiv_low :
      (center - hi) / ell <= (center - shift) / ell :=
    div_le_div_of_nonneg_right hsub_low (le_of_lt hell)
  have hmul_low :
      scale * ((center - hi) / ell) <=
        scale * ((center - shift) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_low hscale
  have hsub_high : center - shift <= center - lo := by linarith
  have hdiv_high :
      (center - shift) / ell <= (center - lo) / ell :=
    div_le_div_of_nonneg_right hsub_high (le_of_lt hell)
  have hmul_high :
      scale * ((center - shift) / ell) <=
        scale * ((center - lo) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_high hscale
  constructor <;> linarith

private theorem scaled_plus_arg_bounds
    (center shift lo hi ell scale offset m : Real)
    (hell : 0 < ell) (hscale : 0 <= scale)
    (hlo : lo <= shift) (hhi : shift <= hi) :
    scale * ((center + lo) / ell) + offset - m <=
      scale * ((center + shift) / ell) + offset - m ∧
    scale * ((center + shift) / ell) + offset - m <=
      scale * ((center + hi) / ell) + offset - m := by
  have hsub_low : center + lo <= center + shift := by linarith
  have hdiv_low :
      (center + lo) / ell <= (center + shift) / ell :=
    div_le_div_of_nonneg_right hsub_low (le_of_lt hell)
  have hmul_low :
      scale * ((center + lo) / ell) <=
        scale * ((center + shift) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_low hscale
  have hsub_high : center + shift <= center + hi := by linarith
  have hdiv_high :
      (center + shift) / ell <= (center + hi) / ell :=
    div_le_div_of_nonneg_right hsub_high (le_of_lt hell)
  have hmul_high :
      scale * ((center + shift) / ell) <=
        scale * ((center + hi) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_high hscale
  constructor <;> linarith



def primaryK11PositivePartPowerTightMinusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 11 *
      (((primaryK11Center j - primaryK11Center i) -
        activeL3PrimeShiftUpper n) / primaryK11Ell) +
    (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
    (m : Real)

def primaryK11PositivePartPowerTightMinusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 11 *
      (((primaryK11Center j - primaryK11Center i) -
        activeL3PrimeShiftLower n) / primaryK11Ell) +
    (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
    (m : Real)

def primaryK11PositivePartPowerTightPlusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 11 *
      (((primaryK11Center j - primaryK11Center i) +
        activeL3PrimeShiftLower n) / primaryK11Ell) +
    (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
    (m : Real)

def primaryK11PositivePartPowerTightPlusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 11 *
      (((primaryK11Center j - primaryK11Center i) +
        activeL3PrimeShiftUpper n) / primaryK11Ell) +
    (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
    (m : Real)


def primaryK11PositivePartPowerTightMinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightMinusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightMinusArgUpper i j n m)) / 2

def primaryK11PositivePartPowerTightMinusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightMinusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightMinusArgLower i j n m)) / 2

def primaryK11PositivePartPowerTightPlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightPlusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightPlusArgUpper i j n m)) / 2

def primaryK11PositivePartPowerTightPlusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightPlusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree 11)
      (primaryK11PositivePartPowerTightPlusArgLower i j n m)) / 2

def primaryK11PositivePartPowerTightMinusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)) *
      primaryK11PositivePartPowerTightMinusMid i j n m

def primaryK11PositivePartPowerTightMinusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)| *
      primaryK11PositivePartPowerTightMinusRad i j n m

def primaryK11PositivePartPowerTightPlusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)) *
      primaryK11PositivePartPowerTightPlusMid i j n m

def primaryK11PositivePartPowerTightPlusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)| *
      primaryK11PositivePartPowerTightPlusRad i j n m

def primaryK11PositivePartPowerTightMinusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
      primaryK11PositivePartPowerTightMinusTermMid i j n m)

def primaryK11PositivePartPowerTightMinusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
      primaryK11PositivePartPowerTightMinusTermRad i j n m)

def primaryK11PositivePartPowerTightPlusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
      primaryK11PositivePartPowerTightPlusTermMid i j n m)

def primaryK11PositivePartPowerTightPlusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
      primaryK11PositivePartPowerTightPlusTermRad i j n m)


private theorem primaryK11PositivePartPowerTightMinusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    primaryK11PositivePartPowerTightMinusArgLower i j n m <=
      bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      primaryK11PositivePartPowerTightMinusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_minus_arg_bounds
      (center := primaryK11Center j - primaryK11Center i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := primaryK11Ell)
      (scale := bsplineScale 11)
      (offset := (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      primaryK11_hell (le_of_lt (bsplineScale_pos 11)) hs.1 hs.2
  simpa [primaryK11PositivePartPowerTightMinusArgLower, primaryK11PositivePartPowerTightMinusArgUpper, primaryK11PrimeShift] using h

private theorem primaryK11PositivePartPowerTightPlusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    primaryK11PositivePartPowerTightPlusArgLower i j n m <=
      bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      primaryK11PositivePartPowerTightPlusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_plus_arg_bounds
      (center := primaryK11Center j - primaryK11Center i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := primaryK11Ell)
      (scale := bsplineScale 11)
      (offset := (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      primaryK11_hell (le_of_lt (bsplineScale_pos 11)) hs.1 hs.2
  simpa [primaryK11PositivePartPowerTightPlusArgLower, primaryK11PositivePartPowerTightPlusArgUpper, primaryK11PrimeShift] using h

private theorem primaryK11PositivePartPowerTightMinus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      primaryK11PositivePartPowerTightMinusMid i j n m| <=
        primaryK11PositivePartPowerTightMinusRad i j n m := by
  have hb := primaryK11PositivePartPowerTightMinusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree 11)
      (x := bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := primaryK11PositivePartPowerTightMinusArgLower i j n m)
      (hi := primaryK11PositivePartPowerTightMinusArgUpper i j n m)
      positivePartPower23_mono hb.1 hb.2
  simpa [primaryK11PositivePartPowerTightMinusMid, primaryK11PositivePartPowerTightMinusRad] using h

private theorem primaryK11PositivePartPowerTightPlus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      primaryK11PositivePartPowerTightPlusMid i j n m| <=
        primaryK11PositivePartPowerTightPlusRad i j n m := by
  have hb := primaryK11PositivePartPowerTightPlusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree 11)
      (x := bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := primaryK11PositivePartPowerTightPlusArgLower i j n m)
      (hi := primaryK11PositivePartPowerTightPlusArgUpper i j n m)
      positivePartPower23_mono hb.1 hb.2
  simpa [primaryK11PositivePartPowerTightPlusMid, primaryK11PositivePartPowerTightPlusRad] using h

theorem primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_tight_positivePartPower_payload :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell)) -
        primaryK11PositivePartPowerTightMinusCardMid i j n| <=
          primaryK11PositivePartPowerTightMinusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell)) -
        primaryK11PositivePartPowerTightPlusCardMid i j n| <=
          primaryK11PositivePartPowerTightPlusCardRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_positivePartPower_hboxes
      primaryK11PositivePartPowerTightMinusMid
      primaryK11PositivePartPowerTightMinusRad
      primaryK11PositivePartPowerTightPlusMid
      primaryK11PositivePartPowerTightPlusRad
      primaryK11PositivePartPowerTightMinusTermMid
      primaryK11PositivePartPowerTightMinusTermRad
      primaryK11PositivePartPowerTightPlusTermMid
      primaryK11PositivePartPowerTightPlusTermRad
      primaryK11PositivePartPowerTightMinusCardMid
      primaryK11PositivePartPowerTightMinusCardRad
      primaryK11PositivePartPowerTightPlusCardMid
      primaryK11PositivePartPowerTightPlusCardRad
      primaryK11PositivePartPowerTightMinus_hbox
      primaryK11PositivePartPowerTightPlus_hbox
      (fun i j n m => by rfl)
      (fun i j n m => by rw [primaryK11PositivePartPowerTightMinusTermRad])
      (fun i j n m => by rfl)
      (fun i j n m => by rw [primaryK11PositivePartPowerTightPlusTermRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightMinusCardRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightPlusCardRad])


def primaryK11PositivePartPowerTightMinusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PositivePartPowerTightMinusCardMid i j n / bsplineAutocorrNorm 11

def primaryK11PositivePartPowerTightMinusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PositivePartPowerTightMinusCardRad i j n / bsplineAutocorrNorm 11

def primaryK11PositivePartPowerTightPlusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PositivePartPowerTightPlusCardMid i j n / bsplineAutocorrNorm 11

def primaryK11PositivePartPowerTightPlusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PositivePartPowerTightPlusCardRad i j n / bsplineAutocorrNorm 11

theorem primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload :
    (∀ i j n,
      |centeredBSplineR 11
          (((primaryK11Center j -
              primaryK11Center i) -
            primaryK11PrimeShift n) /
            primaryK11Ell) -
        primaryK11PositivePartPowerTightMinusRMid i j n| <=
          primaryK11PositivePartPowerTightMinusRRad i j n) ∧
    (∀ i j n,
      |centeredBSplineR 11
          (((primaryK11Center j -
              primaryK11Center i) +
            primaryK11PrimeShift n) /
            primaryK11Ell) -
        primaryK11PositivePartPowerTightPlusRMid i j n| <=
          primaryK11PositivePartPowerTightPlusRRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes
      primaryK11PositivePartPowerTightMinusCardMid
      primaryK11PositivePartPowerTightMinusCardRad
      primaryK11PositivePartPowerTightPlusCardMid
      primaryK11PositivePartPowerTightPlusCardRad
      primaryK11PositivePartPowerTightMinusRMid
      primaryK11PositivePartPowerTightMinusRRad
      primaryK11PositivePartPowerTightPlusRMid
      primaryK11PositivePartPowerTightPlusRRad
      (primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_tight_positivePartPower_payload).1
      (primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_tight_positivePartPower_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightMinusRRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightPlusRRad])

def primaryK11PositivePartPowerTightPrimeTermMid
    (weightMid : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  weightMid n *
    (primaryK11PositivePartPowerTightMinusRMid i j n + primaryK11PositivePartPowerTightPlusRMid i j n)

def primaryK11PositivePartPowerTightPrimeTermRad
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (|weightMid n| + weightRad n) *
      (primaryK11PositivePartPowerTightMinusRRad i j n + primaryK11PositivePartPowerTightPlusRRad i j n) +
    weightRad n *
      |primaryK11PositivePartPowerTightMinusRMid i j n + primaryK11PositivePartPowerTightPlusRMid i j n|

theorem primaryK11AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| <= logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| <= expRad n)
    (hweightMid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hweightRad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| <= weightRad n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          primaryK11PositivePartPowerTightPrimeTermMid weightMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          primaryK11PositivePartPowerTightPrimeTermRad weightMid weightRad i j n) <=
            primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      _root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes
      logMid
      logRad
      expMid
      expRad
      weightMid
      weightRad
      primaryK11PositivePartPowerTightMinusRMid
      primaryK11PositivePartPowerTightMinusRRad
      primaryK11PositivePartPowerTightPlusRMid
      primaryK11PositivePartPowerTightPlusRRad
      (primaryK11PositivePartPowerTightPrimeTermMid weightMid)
      (primaryK11PositivePartPowerTightPrimeTermRad weightMid weightRad)
      hlog
      hexp
      hweightMid
      hweightRad
      (primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload).1
      (primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightPrimeTermRad])
      hmid
      hrad

theorem primaryK11AnalyticP_entry_hbox_of_tight_log_exp_weight_and_sum_checks
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          primaryK11PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n) =
            primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          primaryK11PositivePartPowerTightPrimeTermRad
              activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) <=
            primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      _root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  exact
    primaryK11AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes
      activeL3PrimeLogMid
      activeL3PrimeLogRad
      activeL3PrimeExpMid
      activeL3PrimeExpRad
      activeL3PrimeWeightMid
      activeL3PrimeWeightRad
      activeL3PrimeLog_hbox_of_tight_payload
      activeL3PrimeExp_exact_hbox
      activeL3PrimeWeight_mid_eq
      activeL3PrimeWeight_rad_bound
      hmid
      hrad

theorem primaryK11PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |primaryK11PrimeWeight n -
          weightMid n| <= weightRad n) :
    ∀ i j n,
      |_root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11FinitePrimeProfileTerm i j n -
        primaryK11PositivePartPowerTightPrimeTermMid weightMid i j n| <=
          primaryK11PositivePartPowerTightPrimeTermRad weightMid weightRad i j n := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
      weightMid
      weightRad
      primaryK11PositivePartPowerTightMinusRMid
      primaryK11PositivePartPowerTightMinusRRad
      primaryK11PositivePartPowerTightPlusRMid
      primaryK11PositivePartPowerTightPlusRRad
      (primaryK11PositivePartPowerTightPrimeTermMid weightMid)
      (primaryK11PositivePartPowerTightPrimeTermRad weightMid weightRad)
      hweight
      (primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload).1
      (primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [primaryK11PositivePartPowerTightPrimeTermRad])




def controlK9PositivePartPowerTightMinusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 9 *
      (((controlK9Center j - controlK9Center i) -
        activeL3PrimeShiftUpper n) / controlK9Ell) +
    (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
    (m : Real)

def controlK9PositivePartPowerTightMinusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 9 *
      (((controlK9Center j - controlK9Center i) -
        activeL3PrimeShiftLower n) / controlK9Ell) +
    (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
    (m : Real)

def controlK9PositivePartPowerTightPlusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 9 *
      (((controlK9Center j - controlK9Center i) +
        activeL3PrimeShiftLower n) / controlK9Ell) +
    (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
    (m : Real)

def controlK9PositivePartPowerTightPlusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale 9 *
      (((controlK9Center j - controlK9Center i) +
        activeL3PrimeShiftUpper n) / controlK9Ell) +
    (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
    (m : Real)


def controlK9PositivePartPowerTightMinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightMinusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightMinusArgUpper i j n m)) / 2

def controlK9PositivePartPowerTightMinusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightMinusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightMinusArgLower i j n m)) / 2

def controlK9PositivePartPowerTightPlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightPlusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightPlusArgUpper i j n m)) / 2

def controlK9PositivePartPowerTightPlusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightPlusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree 9)
      (controlK9PositivePartPowerTightPlusArgLower i j n m)) / 2

def controlK9PositivePartPowerTightMinusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)) *
      controlK9PositivePartPowerTightMinusMid i j n m

def controlK9PositivePartPowerTightMinusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)| *
      controlK9PositivePartPowerTightMinusRad i j n m

def controlK9PositivePartPowerTightPlusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)) *
      controlK9PositivePartPowerTightPlusMid i j n m

def controlK9PositivePartPowerTightPlusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)| *
      controlK9PositivePartPowerTightPlusRad i j n m

def controlK9PositivePartPowerTightMinusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
      controlK9PositivePartPowerTightMinusTermMid i j n m)

def controlK9PositivePartPowerTightMinusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
      controlK9PositivePartPowerTightMinusTermRad i j n m)

def controlK9PositivePartPowerTightPlusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
      controlK9PositivePartPowerTightPlusTermMid i j n m)

def controlK9PositivePartPowerTightPlusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
      controlK9PositivePartPowerTightPlusTermRad i j n m)


private theorem controlK9PositivePartPowerTightMinusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    controlK9PositivePartPowerTightMinusArgLower i j n m <=
      bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      controlK9PositivePartPowerTightMinusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_minus_arg_bounds
      (center := controlK9Center j - controlK9Center i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := controlK9Ell)
      (scale := bsplineScale 9)
      (offset := (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      controlK9_hell (le_of_lt (bsplineScale_pos 9)) hs.1 hs.2
  simpa [controlK9PositivePartPowerTightMinusArgLower, controlK9PositivePartPowerTightMinusArgUpper, controlK9PrimeShift] using h

private theorem controlK9PositivePartPowerTightPlusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    controlK9PositivePartPowerTightPlusArgLower i j n m <=
      bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      controlK9PositivePartPowerTightPlusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_plus_arg_bounds
      (center := controlK9Center j - controlK9Center i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := controlK9Ell)
      (scale := bsplineScale 9)
      (offset := (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      controlK9_hell (le_of_lt (bsplineScale_pos 9)) hs.1 hs.2
  simpa [controlK9PositivePartPowerTightPlusArgLower, controlK9PositivePartPowerTightPlusArgUpper, controlK9PrimeShift] using h

private theorem controlK9PositivePartPowerTightMinus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      controlK9PositivePartPowerTightMinusMid i j n m| <=
        controlK9PositivePartPowerTightMinusRad i j n m := by
  have hb := controlK9PositivePartPowerTightMinusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree 9)
      (x := bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := controlK9PositivePartPowerTightMinusArgLower i j n m)
      (hi := controlK9PositivePartPowerTightMinusArgUpper i j n m)
      positivePartPower19_mono hb.1 hb.2
  simpa [controlK9PositivePartPowerTightMinusMid, controlK9PositivePartPowerTightMinusRad] using h

private theorem controlK9PositivePartPowerTightPlus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      controlK9PositivePartPowerTightPlusMid i j n m| <=
        controlK9PositivePartPowerTightPlusRad i j n m := by
  have hb := controlK9PositivePartPowerTightPlusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree 9)
      (x := bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := controlK9PositivePartPowerTightPlusArgLower i j n m)
      (hi := controlK9PositivePartPowerTightPlusArgUpper i j n m)
      positivePartPower19_mono hb.1 hb.2
  simpa [controlK9PositivePartPowerTightPlusMid, controlK9PositivePartPowerTightPlusRad] using h

theorem controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_tight_positivePartPower_payload :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell)) -
        controlK9PositivePartPowerTightMinusCardMid i j n| <=
          controlK9PositivePartPowerTightMinusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell)) -
        controlK9PositivePartPowerTightPlusCardMid i j n| <=
          controlK9PositivePartPowerTightPlusCardRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_positivePartPower_hboxes
      controlK9PositivePartPowerTightMinusMid
      controlK9PositivePartPowerTightMinusRad
      controlK9PositivePartPowerTightPlusMid
      controlK9PositivePartPowerTightPlusRad
      controlK9PositivePartPowerTightMinusTermMid
      controlK9PositivePartPowerTightMinusTermRad
      controlK9PositivePartPowerTightPlusTermMid
      controlK9PositivePartPowerTightPlusTermRad
      controlK9PositivePartPowerTightMinusCardMid
      controlK9PositivePartPowerTightMinusCardRad
      controlK9PositivePartPowerTightPlusCardMid
      controlK9PositivePartPowerTightPlusCardRad
      controlK9PositivePartPowerTightMinus_hbox
      controlK9PositivePartPowerTightPlus_hbox
      (fun i j n m => by rfl)
      (fun i j n m => by rw [controlK9PositivePartPowerTightMinusTermRad])
      (fun i j n m => by rfl)
      (fun i j n m => by rw [controlK9PositivePartPowerTightPlusTermRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightMinusCardRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightPlusCardRad])


def controlK9PositivePartPowerTightMinusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  controlK9PositivePartPowerTightMinusCardMid i j n / bsplineAutocorrNorm 9

def controlK9PositivePartPowerTightMinusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  controlK9PositivePartPowerTightMinusCardRad i j n / bsplineAutocorrNorm 9

def controlK9PositivePartPowerTightPlusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  controlK9PositivePartPowerTightPlusCardMid i j n / bsplineAutocorrNorm 9

def controlK9PositivePartPowerTightPlusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  controlK9PositivePartPowerTightPlusCardRad i j n / bsplineAutocorrNorm 9

theorem controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload :
    (∀ i j n,
      |centeredBSplineR 9
          (((controlK9Center j -
              controlK9Center i) -
            controlK9PrimeShift n) /
            controlK9Ell) -
        controlK9PositivePartPowerTightMinusRMid i j n| <=
          controlK9PositivePartPowerTightMinusRRad i j n) ∧
    (∀ i j n,
      |centeredBSplineR 9
          (((controlK9Center j -
              controlK9Center i) +
            controlK9PrimeShift n) /
            controlK9Ell) -
        controlK9PositivePartPowerTightPlusRMid i j n| <=
          controlK9PositivePartPowerTightPlusRRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_cardinal_hboxes
      controlK9PositivePartPowerTightMinusCardMid
      controlK9PositivePartPowerTightMinusCardRad
      controlK9PositivePartPowerTightPlusCardMid
      controlK9PositivePartPowerTightPlusCardRad
      controlK9PositivePartPowerTightMinusRMid
      controlK9PositivePartPowerTightMinusRRad
      controlK9PositivePartPowerTightPlusRMid
      controlK9PositivePartPowerTightPlusRRad
      (controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_tight_positivePartPower_payload).1
      (controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_tight_positivePartPower_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightMinusRRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightPlusRRad])

def controlK9PositivePartPowerTightPrimeTermMid
    (weightMid : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  weightMid n *
    (controlK9PositivePartPowerTightMinusRMid i j n + controlK9PositivePartPowerTightPlusRMid i j n)

def controlK9PositivePartPowerTightPrimeTermRad
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (|weightMid n| + weightRad n) *
      (controlK9PositivePartPowerTightMinusRRad i j n + controlK9PositivePartPowerTightPlusRRad i j n) +
    weightRad n *
      |controlK9PositivePartPowerTightMinusRMid i j n + controlK9PositivePartPowerTightPlusRMid i j n|

theorem controlK9AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| <= logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| <= expRad n)
    (hweightMid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hweightRad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| <= weightRad n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          controlK9PositivePartPowerTightPrimeTermMid weightMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          controlK9PositivePartPowerTightPrimeTermRad weightMid weightRad i j n) <=
            controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      _root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.controlK9AnalyticP controlK9P controlK9PRadius := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes
      logMid
      logRad
      expMid
      expRad
      weightMid
      weightRad
      controlK9PositivePartPowerTightMinusRMid
      controlK9PositivePartPowerTightMinusRRad
      controlK9PositivePartPowerTightPlusRMid
      controlK9PositivePartPowerTightPlusRRad
      (controlK9PositivePartPowerTightPrimeTermMid weightMid)
      (controlK9PositivePartPowerTightPrimeTermRad weightMid weightRad)
      hlog
      hexp
      hweightMid
      hweightRad
      (controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload).1
      (controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightPrimeTermRad])
      hmid
      hrad

theorem controlK9AnalyticP_entry_hbox_of_tight_log_exp_weight_and_sum_checks
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          controlK9PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n) =
            controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          controlK9PositivePartPowerTightPrimeTermRad
              activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) <=
            controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      _root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.controlK9AnalyticP controlK9P controlK9PRadius := by
  exact
    controlK9AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes
      activeL3PrimeLogMid
      activeL3PrimeLogRad
      activeL3PrimeExpMid
      activeL3PrimeExpRad
      activeL3PrimeWeightMid
      activeL3PrimeWeightRad
      activeL3PrimeLog_hbox_of_tight_payload
      activeL3PrimeExp_exact_hbox
      activeL3PrimeWeight_mid_eq
      activeL3PrimeWeight_rad_bound
      hmid
      hrad

theorem controlK9PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |controlK9PrimeWeight n -
          weightMid n| <= weightRad n) :
    ∀ i j n,
      |_root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9FinitePrimeProfileTerm i j n -
        controlK9PositivePartPowerTightPrimeTermMid weightMid i j n| <=
          controlK9PositivePartPowerTightPrimeTermRad weightMid weightRad i j n := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
      weightMid
      weightRad
      controlK9PositivePartPowerTightMinusRMid
      controlK9PositivePartPowerTightMinusRRad
      controlK9PositivePartPowerTightPlusRMid
      controlK9PositivePartPowerTightPlusRRad
      (controlK9PositivePartPowerTightPrimeTermMid weightMid)
      (controlK9PositivePartPowerTightPrimeTermRad weightMid weightRad)
      hweight
      (controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload).1
      (controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [controlK9PositivePartPowerTightPrimeTermRad])



theorem primaryK11PositivePartPowerTightPrimeTermMid_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    primaryK11PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n =
      activeL3PrimeExpMid n *
        (activeL3PrimeLogMid n *
          (primaryK11PositivePartPowerTightMinusRMid i j n +
            primaryK11PositivePartPowerTightPlusRMid i j n)) := by
  dsimp [primaryK11PositivePartPowerTightPrimeTermMid, activeL3PrimeWeightMid]
  ring

theorem primaryK11PositivePartPowerTightPrimeTermRad_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    primaryK11PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n =
      activeL3PrimeExpMid n *
        ((|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
            (primaryK11PositivePartPowerTightMinusRRad i j n +
              primaryK11PositivePartPowerTightPlusRRad i j n) +
          activeL3PrimeLogRad n *
            |primaryK11PositivePartPowerTightMinusRMid i j n +
              primaryK11PositivePartPowerTightPlusRMid i j n|) := by
  dsimp [primaryK11PositivePartPowerTightPrimeTermRad]
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  rw [abs_activeL3PrimeWeightMid_eq n]
  ring

theorem controlK9PositivePartPowerTightPrimeTermMid_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    controlK9PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n =
      activeL3PrimeExpMid n *
        (activeL3PrimeLogMid n *
          (controlK9PositivePartPowerTightMinusRMid i j n +
            controlK9PositivePartPowerTightPlusRMid i j n)) := by
  dsimp [controlK9PositivePartPowerTightPrimeTermMid, activeL3PrimeWeightMid]
  ring

theorem controlK9PositivePartPowerTightPrimeTermRad_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    controlK9PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n =
      activeL3PrimeExpMid n *
        ((|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
            (controlK9PositivePartPowerTightMinusRRad i j n +
              controlK9PositivePartPowerTightPlusRRad i j n) +
          activeL3PrimeLogRad n *
            |controlK9PositivePartPowerTightMinusRMid i j n +
              controlK9PositivePartPowerTightPlusRMid i j n|) := by
  dsimp [controlK9PositivePartPowerTightPrimeTermRad]
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  rw [abs_activeL3PrimeWeightMid_eq n]
  ring


end CenteredCoeffPrimePositivePartTightImport
end PSDpd
end Q3
