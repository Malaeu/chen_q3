import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend

set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option maxHeartbeats 0

/-!
Generated Step33 Arch A finite/tail arithmetic layer.

This file does not prove the finite-window integral enclosures.
It checks the rational arithmetic showing that the generated finite
window and tail payload data fit inside the synchronized Step22 A
midpoint-radius boxes consumed by the active hbox receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd

open CenteredCoeffPayloadImport

/-- Common finite-window cutoff from the generated Step22 A manifests. -/
def archAFiniteTailCutoff : Real := ((260 : Real))

/-- Common positive-tail-window endpoint from the Step33 A tail probes. -/
def archAPositiveTailWindowEnd : Real := ((520 : Real))

/-- Generated finite-window lower data for primary k=11. -/
def primaryK11AnalyticAFiniteLowerRat : Nat -> Rat
  | 0 => ((616822226819609732566566694116421 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 1 => ((-2187408917468689830237080776790607 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 2 => ((-11176519746100252508543237039290187 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 3 => ((-248225602675335093547863027426649 : Rat) / (1562500000000000000000000000000000 : Rat))
  | 4 => ((-6277777295229414646449600817109679 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 5 => ((-10423206576642563352716169018137069 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 6 => ((-8879834253975839552185078705352699 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 7 => ((-383769013738527194678761601557147 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 8 => ((-3345083841117298231108808977937359 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 9 => ((-5860341194405480939124359678233009 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 10 => ((-5148618820286358405012328186932021 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 11 => ((-1132839613793928302166311934363583 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 12 => ((-1996182478344695369375347638553743 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 13 => ((-3519755893762420595881957383769013 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 14 => ((-15521533038309149840596133451407173 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 15 => ((-2738542581476614256084584099719893 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 16 => ((-12081106340917410150298366559094973 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 17 => ((-333128440240238339098372072436593 : Rat) / (15625000000000000000000000000000000 : Rat))
  | 18 => ((-1881349899943884698159428793394351 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 19 => ((-830101807238968391691903113564277 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 20 => ((-14650807425575698401113787230138473 : Rat) / (1000000000000000000000000000000000000 : Rat))
  | 21 => ((-1292905771430244334049581631552987 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 22 => ((-5704863946504770692011357601588719 : Rat) / (500000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated finite-window upper data for primary k=11. -/
def primaryK11AnalyticAFiniteUpperRat : Nat -> Rat
  | 0 => ((616822226819609777433433305883579 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 1 => ((-2187408917468689689762919223209393 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 2 => ((-11176519746100252391456762960709813 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 3 => ((-248225602675335065827136972573351 : Rat) / (1562500000000000000000000000000000 : Rat))
  | 4 => ((-6277777295229413753550399182890321 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 5 => ((-10423206576642562647283830981862931 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 6 => ((-8879834253975839067814921294647301 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 7 => ((-383769013738527157321238398442853 : Rat) / (5000000000000000000000000000000000 : Rat))
  | 8 => ((-3345083841117298008891191022062641 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 9 => ((-5860341194405480580875640321766991 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 10 => ((-5148618820286358054987671813067979 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 11 => ((-1132839613793928202833688065636417 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 12 => ((-1996182478344695170624652361446257 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 13 => ((-3519755893762420264118042616230987 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 14 => ((-15521533038309149759403866548592827 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 15 => ((-2738542581476614023915415900280107 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 16 => ((-12081106340917409949701633440905027 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 17 => ((-333128440240238329651627927563407 : Rat) / (15625000000000000000000000000000000 : Rat))
  | 18 => ((-1881349899943884421840571206605649 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 19 => ((-830101807238968228308096886435723 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 20 => ((-14650807425575697598886212769861527 : Rat) / (1000000000000000000000000000000000000 : Rat))
  | 21 => ((-1292905771430244185950418368447013 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 22 => ((-5704863946504770307988642398411281 : Rat) / (500000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated tail radius data for primary k=11. -/
def primaryK11AnalyticATailRadiusRat : Nat -> Rat
  | 0 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 1 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 2 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 3 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 4 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 5 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 6 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 7 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 8 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 9 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 10 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 11 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 12 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 13 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 14 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 15 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 16 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 17 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 18 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 19 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 20 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 21 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 22 => ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Common generated tail radius for primary k=11. -/
def primaryK11AnalyticATailRadiusCommonRat : Rat := ((33241136494985823 : Rat) / (25000000000000000000000000000000000 : Rat))

/-- Generated positive-tail-window lower data for primary k=11. -/
def primaryK11AnalyticATailWindowLowerRat : Nat -> Rat
  | 0 => ((359659049143447977 : Rat) / (200000000000000000000000000000000000000 : Rat))
  | 1 => ((-6305551866376207189 : Rat) / (100000000000000000000000000000000000000000 : Rat))
  | 2 => ((-124779554314678433 : Rat) / (625000000000000000000000000000000000000000 : Rat))
  | 3 => ((-861983043357582991 : Rat) / (1250000000000000000000000000000000000000000000000 : Rat))
  | 4 => ((6401079035162446847 : Rat) / (100000000000000000000000000000000000000000000000000000 : Rat))
  | 5 => ((2763730364120544729 : Rat) / (10000000000000000000000000000000000000000000000000000000 : Rat))
  | 6 => ((1602399319764370269 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 7 => ((4867104256348677743 : Rat) / (500000000000000000000000000000000000000000000000000000000 : Rat))
  | 8 => ((-7086019081839863 : Rat) / (390625000000000000000000000000000000000000000000000000 : Rat))
  | 9 => ((-54369022083328911 : Rat) / (2500000000000000000000000000000000000000000000000000000 : Rat))
  | 10 => ((258973164806513383 : Rat) / (4000000000000000000000000000000000000000000000000000000 : Rat))
  | 11 => ((-81073487159237993 : Rat) / (2000000000000000000000000000000000000000000000000000000 : Rat))
  | 12 => ((-2499230713024612927 : Rat) / (50000000000000000000000000000000000000000000000000000000 : Rat))
  | 13 => ((221000628939351957 : Rat) / (2000000000000000000000000000000000000000000000000000000 : Rat))
  | 14 => ((-697450758997275663 : Rat) / (12500000000000000000000000000000000000000000000000000000 : Rat))
  | 15 => ((-471697553891457227 : Rat) / (6250000000000000000000000000000000000000000000000000000 : Rat))
  | 16 => ((1428235690884327907 : Rat) / (10000000000000000000000000000000000000000000000000000000 : Rat))
  | 17 => ((-3008850718309722269 : Rat) / (50000000000000000000000000000000000000000000000000000000 : Rat))
  | 18 => ((-9715450123528218917 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 19 => ((400816319692920069 : Rat) / (2500000000000000000000000000000000000000000000000000000 : Rat))
  | 20 => ((-1374551537370052423 : Rat) / (25000000000000000000000000000000000000000000000000000000 : Rat))
  | 21 => ((-561020035214752187 : Rat) / (5000000000000000000000000000000000000000000000000000000 : Rat))
  | 22 => ((1627623055066903689 : Rat) / (10000000000000000000000000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated positive-tail-window upper data for primary k=11. -/
def primaryK11AnalyticATailWindowUpperRat : Nat -> Rat
  | 0 => ((899147622858619943 : Rat) / (500000000000000000000000000000000000000 : Rat))
  | 1 => ((-3152775933188103547 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 2 => ((-199647286903484813 : Rat) / (1000000000000000000000000000000000000000000 : Rat))
  | 3 => ((-689586434054620793 : Rat) / (1000000000000000000000000000000000000000000000000 : Rat))
  | 4 => ((6401155878556344853 : Rat) / (100000000000000000000000000000000000000000000000000000 : Rat))
  | 5 => ((69135863130420809 : Rat) / (250000000000000000000000000000000000000000000000000000 : Rat))
  | 6 => ((204579321188093977 : Rat) / (12500000000000000000000000000000000000000000000000000000 : Rat))
  | 7 => ((1032615878008123111 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 8 => ((-1760515882149359049 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 9 => ((-535980143437769427 : Rat) / (25000000000000000000000000000000000000000000000000000000 : Rat))
  | 10 => ((324794280885147559 : Rat) / (5000000000000000000000000000000000000000000000000000000 : Rat))
  | 11 => ((-1012487387242997127 : Rat) / (25000000000000000000000000000000000000000000000000000000 : Rat))
  | 12 => ((-9725918738290713 : Rat) / (195312500000000000000000000000000000000000000000000000 : Rat))
  | 13 => ((1105298281018955597 : Rat) / (10000000000000000000000000000000000000000000000000000000 : Rat))
  | 14 => ((-2783777870390532573 : Rat) / (50000000000000000000000000000000000000000000000000000000 : Rat))
  | 15 => ((-7527602995532354013 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 16 => ((715518942151668613 : Rat) / (5000000000000000000000000000000000000000000000000000000 : Rat))
  | 17 => ((-5998562761037059983 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 18 => ((-9689880822991377271 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 19 => ((80233874168579011 : Rat) / (500000000000000000000000000000000000000000000000000000 : Rat))
  | 20 => ((-5471530306837159073 : Rat) / (100000000000000000000000000000000000000000000000000000000 : Rat))
  | 21 => ((-559972236332161349 : Rat) / (5000000000000000000000000000000000000000000000000000000 : Rat))
  | 22 => ((203647846474855229 : Rat) / (1250000000000000000000000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated positive-tail remainder radius data for primary k=11. -/
def primaryK11AnalyticATailRemainderRadiusRat : Nat -> Rat
  | 0 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 1 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 2 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 3 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 4 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 5 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 6 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 7 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 8 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 9 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 10 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 11 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 12 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 13 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 14 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 15 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 16 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 17 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 18 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 19 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 20 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 21 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | 22 => ((8744876245761809 : Rat) / (50000000000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Real-valued finite-window lower data for primary k=11. -/
def primaryK11AnalyticAFiniteLower (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticAFiniteLowerRat n.1 : Real)

/-- Real-valued finite-window upper data for primary k=11. -/
def primaryK11AnalyticAFiniteUpper (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticAFiniteUpperRat n.1 : Real)

/-- Real-valued tail radius data for primary k=11. -/
def primaryK11AnalyticATailRadius (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticATailRadiusRat n.1 : Real)

/-- Real-valued common tail radius for primary k=11. -/
def primaryK11AnalyticATailRadiusCommon : Real :=
  (primaryK11AnalyticATailRadiusCommonRat : Real)

/-- Real-valued positive-tail-window lower data for primary k=11. -/
def primaryK11AnalyticATailWindowLower (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticATailWindowLowerRat n.1 : Real)

/-- Real-valued positive-tail-window upper data for primary k=11. -/
def primaryK11AnalyticATailWindowUpper (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticATailWindowUpperRat n.1 : Real)

/-- Real-valued positive-tail remainder radius data for primary k=11. -/
def primaryK11AnalyticATailRemainderRadius (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticATailRemainderRadiusRat n.1 : Real)

/-- Local proof slack for post-520 primary log-majorant tail comparisons. -/
def primaryK11AnalyticATailProofRemainderRadius (_n : CoeffIndex23) : Real :=
  (1 : Real) / (10 : Real) ^ 21

/-- Real-valued signed two-sided tail lower data for primary k=11. -/
def primaryK11AnalyticASignedTailLower (n : CoeffIndex23) : Real :=
  2 * (primaryK11AnalyticATailWindowLower n - primaryK11AnalyticATailRemainderRadius n)

/-- Real-valued signed two-sided tail upper data for primary k=11. -/
def primaryK11AnalyticASignedTailUpper (n : CoeffIndex23) : Real :=
  2 * (primaryK11AnalyticATailWindowUpper n + primaryK11AnalyticATailRemainderRadius n)

/-- Real-valued signed two-sided tail lower data using the local proof slack. -/
def primaryK11AnalyticASignedTailProofLower (n : CoeffIndex23) : Real :=
  2 * (primaryK11AnalyticATailWindowLower n - primaryK11AnalyticATailProofRemainderRadius n)

/-- Real-valued signed two-sided tail upper data using the local proof slack. -/
def primaryK11AnalyticASignedTailProofUpper (n : CoeffIndex23) : Real :=
  2 * (primaryK11AnalyticATailWindowUpper n + primaryK11AnalyticATailProofRemainderRadius n)

/-- Positive-half finite-window lower target for the folded payload, primary k=11. -/
def primaryK11AnalyticAFinitePositiveLower (n : CoeffIndex23) : Real :=
  primaryK11AnalyticAFiniteLower n / 2

/-- Positive-half finite-window upper target for the folded payload, primary k=11. -/
def primaryK11AnalyticAFinitePositiveUpper (n : CoeffIndex23) : Real :=
  primaryK11AnalyticAFiniteUpper n / 2

theorem primaryK11AnalyticAFinitePositiveLowerBound_generated :
    ∀ n : CoeffIndex23,
      primaryK11AnalyticAFiniteLower n <= 2 * primaryK11AnalyticAFinitePositiveLower n := by
  intro n
  have h :
      2 * primaryK11AnalyticAFinitePositiveLower n = primaryK11AnalyticAFiniteLower n := by
    unfold primaryK11AnalyticAFinitePositiveLower
    ring
  rw [h]

theorem primaryK11AnalyticAFinitePositiveUpperBound_generated :
    ∀ n : CoeffIndex23,
      2 * primaryK11AnalyticAFinitePositiveUpper n <= primaryK11AnalyticAFiniteUpper n := by
  intro n
  have h :
      2 * primaryK11AnalyticAFinitePositiveUpper n = primaryK11AnalyticAFiniteUpper n := by
    unfold primaryK11AnalyticAFinitePositiveUpper
    ring
  rw [h]

/-- Center of the generated finite-window enclosure for primary k=11. -/
def primaryK11AnalyticAFiniteMid (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticAFiniteLower n + primaryK11AnalyticAFiniteUpper n) / 2

/-- Radius of the generated finite-window enclosure for primary k=11. -/
def primaryK11AnalyticAFiniteRadius (n : CoeffIndex23) : Real :=
  (primaryK11AnalyticAFiniteUpper n - primaryK11AnalyticAFiniteLower n) / 2

theorem primaryK11AnalyticAFiniteTailArithmeticBoundsCert_generated :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailArithmeticBoundsCert
      primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  refine { h := ?_ }
  intro n
  fin_cases n <;>
    refine { hLower := ?_, hUpper := ?_ } <;>
    norm_num [
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailArithmeticIntervalCert,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFiniteTailArithmeticCert,
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower,
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper,
      primaryK11AnalyticAFiniteLower,
      primaryK11AnalyticAFiniteUpper,
      primaryK11AnalyticATailRadius,
      primaryK11AnalyticAFiniteLowerRat,
      primaryK11AnalyticAFiniteUpperRat,
      primaryK11AnalyticATailRadiusRat,
      CenteredCoeffPayloadImport.primaryK11AAbsDistanceEntryRat,
      CenteredCoeffPayloadImport.primaryK11ARadiusAbsDistanceEntryRat
    ]

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert_of_analyticAndArithmeticBoundsCert
      analytic primaryK11AnalyticAFiniteTailArithmeticBoundsCert_generated

theorem primaryK11AnalyticATailGrowthBoundsCert_of_commonGeneratedTailRadius
    {C0 C1 : Real}
    (hTail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        11 ((3 : Real) / (10 : Real)) archAFiniteTailCutoff C0 C1 <= primaryK11AnalyticATailRadiusCommon) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailGrowthBoundsCert
      archAFiniteTailCutoff C0 C1 primaryK11AnalyticATailRadius := by
  refine ⟨?_⟩
  intro n
  fin_cases n <;>
    simpa [
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound,
      primaryK11AnalyticATailRadius,
      primaryK11AnalyticATailRadiusRat,
      primaryK11AnalyticATailRadiusCommon,
      primaryK11AnalyticATailRadiusCommonRat
    ] using hTail

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (tailGrowth :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailGrowthBoundsCert
        archAFiniteTailCutoff C0 C1 primaryK11AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  exact primaryK11AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailGrowthBounds
      hC0 hC1 hgrowth (by norm_num [archAFiniteTailCutoff]) finite tailGrowth)

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    {tailLower tailUpper : CoeffIndex23 → Real}
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (tail :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert
        archAFiniteTailCutoff tailLower tailUpper primaryK11AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  exact primaryK11AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
      finite tail)

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (hTail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        11 ((3 : Real) / (10 : Real)) archAFiniteTailCutoff C0 C1 <= primaryK11AnalyticATailRadiusCommon) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  exact primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth hC0 hC1 hgrowth finite
    (primaryK11AnalyticATailGrowthBoundsCert_of_commonGeneratedTailRadius hTail)

theorem primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
    (window :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        primaryK11AnalyticATailWindowLower primaryK11AnalyticATailWindowUpper primaryK11AnalyticATailRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticASignedTailLower primaryK11AnalyticASignedTailUpper primaryK11AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
      (by norm_num [archAFiniteTailCutoff])
      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])
      window
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailLower,
          primaryK11AnalyticASignedTailUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRemainderRadiusRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailLower,
          primaryK11AnalyticASignedTailUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRemainderRadiusRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailLower,
          primaryK11AnalyticASignedTailUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRemainderRadiusRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailLower,
          primaryK11AnalyticASignedTailUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRemainderRadiusRat,
          primaryK11AnalyticATailRadiusRat
          ])

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindow
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        primaryK11AnalyticATailWindowLower primaryK11AnalyticATailWindowUpper primaryK11AnalyticATailRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper primaryK11AnalyticATailRadius := by
  exact primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    finite
    (primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow window)

theorem primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
    (window :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        primaryK11AnalyticATailWindowLower primaryK11AnalyticATailWindowUpper
        primaryK11AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticASignedTailProofLower
      primaryK11AnalyticASignedTailProofUpper primaryK11AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
      (by norm_num [archAFiniteTailCutoff])
      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])
      window
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailProofLower,
          primaryK11AnalyticASignedTailProofUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailProofRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailProofLower,
          primaryK11AnalyticASignedTailProofUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailProofRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailProofLower,
          primaryK11AnalyticASignedTailProofUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailProofRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          primaryK11AnalyticASignedTailProofLower,
          primaryK11AnalyticASignedTailProofUpper,
          primaryK11AnalyticATailWindowLower,
          primaryK11AnalyticATailWindowUpper,
          primaryK11AnalyticATailProofRemainderRadius,
          primaryK11AnalyticATailRadius,
          primaryK11AnalyticATailWindowLowerRat,
          primaryK11AnalyticATailWindowUpperRat,
          primaryK11AnalyticATailRadiusRat
          ])

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        primaryK11AnalyticATailWindowLower primaryK11AnalyticATailWindowUpper
        primaryK11AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper
      primaryK11AnalyticATailRadius := by
  exact primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    finite
    (primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder window)

theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
    (finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        primaryK11AnalyticATailWindowLower primaryK11AnalyticATailWindowUpper
        primaryK11AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper
      primaryK11AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
      finite
      (primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder window)

theorem primaryK11AnalyticARecenterContainment_generated :
    ∀ n : CoeffIndex23,
      primaryK11AnalyticAFiniteRadius n + primaryK11AnalyticATailRadius n +
          |primaryK11AnalyticAFiniteMid n -
            (CenteredCoeffPayloadImport.primaryK11AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.primaryK11ARadiusAbsDistanceEntryRat n.1 : Real) := by
  intro n
  fin_cases n <;>
    norm_num [
      primaryK11AnalyticAFiniteMid,
      primaryK11AnalyticAFiniteRadius,
      primaryK11AnalyticAFiniteLower,
      primaryK11AnalyticAFiniteUpper,
      primaryK11AnalyticATailRadius,
      primaryK11AnalyticAFiniteLowerRat,
      primaryK11AnalyticAFiniteUpperRat,
      primaryK11AnalyticATailRadiusRat,
      CenteredCoeffPayloadImport.primaryK11AAbsDistanceEntryRat,
      CenteredCoeffPayloadImport.primaryK11ARadiusAbsDistanceEntryRat
    ]

theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_to_midRadius
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper
        primaryK11AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      archAFiniteTailCutoff
      (fun n => primaryK11AnalyticAFiniteMid n - primaryK11AnalyticAFiniteRadius n)
      (fun n => primaryK11AnalyticAFiniteMid n + primaryK11AnalyticAFiniteRadius n)
      primaryK11AnalyticATailRadius := by
  refine ⟨?_⟩
  intro n
  have hn := analytic.h n
  refine
    { hFiniteLower := ?_
      hFiniteUpper := ?_
      hTail := hn.hTail }
  · have hLowerEq :
        primaryK11AnalyticAFiniteMid n - primaryK11AnalyticAFiniteRadius n =
          primaryK11AnalyticAFiniteLower n := by
      unfold primaryK11AnalyticAFiniteMid primaryK11AnalyticAFiniteRadius
      ring
    rw [hLowerEq]
    exact hn.hFiniteLower
  · have hUpperEq :
        primaryK11AnalyticAFiniteMid n + primaryK11AnalyticAFiniteRadius n =
          primaryK11AnalyticAFiniteUpper n := by
      unfold primaryK11AnalyticAFiniteMid primaryK11AnalyticAFiniteRadius
      ring
    rw [hUpperEq]
    exact hn.hFiniteUpper

theorem primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper
        primaryK11AnalyticATailRadius) :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
      (T := archAFiniteTailCutoff)
      (finiteMid := primaryK11AnalyticAFiniteMid)
      (finiteRadius := primaryK11AnalyticAFiniteRadius)
      (tailRadius := primaryK11AnalyticATailRadius)
      (primaryK11AnalyticAFiniteTailAnalyticBoundsCert_to_midRadius analytic)
      primaryK11AnalyticARecenterContainment_generated

theorem primaryK11AnalyticA_entry_hbox_of_delta_recenter_checks
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff primaryK11AnalyticAFiniteLower primaryK11AnalyticAFiniteUpper
        primaryK11AnalyticATailRadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      CenteredCoeffPayloadImport.primaryK11A
      CenteredCoeffPayloadImport.primaryK11ARadius := by
  exact
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
      (primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks analytic)

/-- Generated finite-window lower data for control k=9. -/
def controlK9AnalyticAFiniteLowerRat : Nat -> Rat
  | 0 => ((104995614635099371554841632840837 : Rat) / (4000000000000000000000000000000000 : Rat))
  | 1 => ((-4873092439847854368218120316427241 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 2 => ((-2460736057093875348980287054908127 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 3 => ((-17448999658797801702543610396946133 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 4 => ((-13781190623693576355916204351051637 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 5 => ((-11437484396867521765638068208013983 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 6 => ((-4871298525144603854098007927420791 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 7 => ((-8420506225936439190157858807135797 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 8 => ((-733934973353471707971871368149857 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 9 => ((-1607212259210436487796944865981851 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 10 => ((-5648004324873016380729471071367153 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 11 => ((-4970832111898410805452862034611253 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 12 => ((-4379542530481586224652160245470013 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 13 => ((-965272120774047771688537510020211 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 14 => ((-831382891170841063589285937049 : Rat) / (24414062500000000000000000000000 : Rat))
  | 15 => ((-234695884143577410661160971199819 : Rat) / (7812500000000000000000000000000000 : Rat))
  | 16 => ((-5301055542921015600708249439827577 : Rat) / (200000000000000000000000000000000000 : Rat))
  | 17 => ((-1461730079439918501585917171620397 : Rat) / (62500000000000000000000000000000000 : Rat))
  | 18 => ((-10318936837974501824291346277795657 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 19 => ((-910597954127281715393402847465981 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 20 => ((-1004469719374957212408651494723519 : Rat) / (62500000000000000000000000000000000 : Rat))
  | 21 => ((-14182804690009532400757218660963004641 : Rat) / (1000000000000000000000000000000000000000 : Rat))
  | 22 => ((-782258945814154097704363577841817 : Rat) / (62500000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated finite-window upper data for control k=9. -/
def controlK9AnalyticAFiniteUpperRat : Nat -> Rat
  | 0 => ((104995614635099382045158367159163 : Rat) / (4000000000000000000000000000000000 : Rat))
  | 1 => ((-4873092439847854091781879683572759 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 2 => ((-2460736057093875091019712945091873 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 3 => ((-17448999658797799897456389603053867 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 4 => ((-13781190623693575844083795648948363 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 5 => ((-11437484396867520834361931791986017 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 6 => ((-4871298525144603725901992072579209 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 7 => ((-8420506225936438469842141192864203 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 8 => ((-733934973353471666028128631850143 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 9 => ((-1607212259210436162203055134018149 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 10 => ((-5648004324873016039270528928632847 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 11 => ((-4970832111898410594547137965388747 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 12 => ((-4379542530481585575347839754529987 : Rat) / (100000000000000000000000000000000000 : Rat))
  | 13 => ((-965272120774047653311462489979789 : Rat) / (25000000000000000000000000000000000 : Rat))
  | 14 => ((-831382891170841011606026562951 : Rat) / (24414062500000000000000000000000 : Rat))
  | 15 => ((-234695884143577397151339028800181 : Rat) / (7812500000000000000000000000000000 : Rat))
  | 16 => ((-5301055542921015279291750560172423 : Rat) / (200000000000000000000000000000000000 : Rat))
  | 17 => ((-1461730079439918423414082828379603 : Rat) / (62500000000000000000000000000000000 : Rat))
  | 18 => ((-10318936837974500875708653722204343 : Rat) / (500000000000000000000000000000000000 : Rat))
  | 19 => ((-910597954127281614606597152534019 : Rat) / (50000000000000000000000000000000000 : Rat))
  | 20 => ((-1004469719374957175091348505276481 : Rat) / (62500000000000000000000000000000000 : Rat))
  | 21 => ((-14182804690009532399242781339036995359 : Rat) / (1000000000000000000000000000000000000000 : Rat))
  | 22 => ((-782258945814154064795636422158183 : Rat) / (62500000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated tail radius data for control k=9. -/
def controlK9AnalyticATailRadiusRat : Nat -> Rat
  | 0 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 1 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 2 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 3 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 4 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 5 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 6 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 7 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 8 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 9 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 10 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 11 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 12 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 13 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 14 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 15 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 16 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 17 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 18 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 19 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 20 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 21 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | 22 => ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Common generated tail radius for control k=9. -/
def controlK9AnalyticATailRadiusCommonRat : Rat := ((823137126441703061 : Rat) / (10000000000000000000000000000000000 : Rat))

/-- Generated positive-tail-window lower data for control k=9. -/
def controlK9AnalyticATailWindowLowerRat : Nat -> Rat
  | 0 => ((95611003986867883 : Rat) / (40000000000000000000000000000000000 : Rat))
  | 1 => ((-1496392435805403197 : Rat) / (1000000000000000000000000000000000000 : Rat))
  | 2 => ((1554140800354201791 : Rat) / (2500000000000000000000000000000000000 : Rat))
  | 3 => ((-7058157635391009113 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 4 => ((-2359662550523920397 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 5 => ((2573790936828052663 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 6 => ((-8737862637356801481 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 7 => ((-2457244959674866511 : Rat) / (25000000000000000000000000000000000000 : Rat))
  | 8 => ((812770558194979099 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 9 => ((-8679651064084806067 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 10 => ((-2088413513173314701 : Rat) / (50000000000000000000000000000000000000 : Rat))
  | 11 => ((1137653830948299151 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 12 => ((-1654974417538291259 : Rat) / (20000000000000000000000000000000000000 : Rat))
  | 13 => ((-126918296009425153 : Rat) / (12500000000000000000000000000000000000 : Rat))
  | 14 => ((1630406706778533357 : Rat) / (20000000000000000000000000000000000000 : Rat))
  | 15 => ((-7689410156069335989 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 16 => ((394583931044177903 : Rat) / (40000000000000000000000000000000000000 : Rat))
  | 17 => ((2869003902770963819 : Rat) / (50000000000000000000000000000000000000 : Rat))
  | 18 => ((-1744452658606071729 : Rat) / (25000000000000000000000000000000000000 : Rat))
  | 19 => ((2308438688896104387 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 20 => ((3810690383811020543 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 21 => ((-385834099080410627 : Rat) / (6250000000000000000000000000000000000 : Rat))
  | 22 => ((99013448762955427 : Rat) / (3125000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated positive-tail-window upper data for control k=9. -/
def controlK9AnalyticATailWindowUpperRat : Nat -> Rat
  | 0 => ((95611003986867883 : Rat) / (40000000000000000000000000000000000 : Rat))
  | 1 => ((-1496392435805403197 : Rat) / (1000000000000000000000000000000000000 : Rat))
  | 2 => ((1554140800354201791 : Rat) / (2500000000000000000000000000000000000 : Rat))
  | 3 => ((-7058157635391009113 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 4 => ((-2359662550523920397 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 5 => ((2573790936828052663 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 6 => ((-8737862637356801481 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 7 => ((-2457244959674866511 : Rat) / (25000000000000000000000000000000000000 : Rat))
  | 8 => ((812770558194979099 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 9 => ((-8679651064084806067 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 10 => ((-2088413513173314701 : Rat) / (50000000000000000000000000000000000000 : Rat))
  | 11 => ((1137653830948299151 : Rat) / (10000000000000000000000000000000000000 : Rat))
  | 12 => ((-1654974417538291259 : Rat) / (20000000000000000000000000000000000000 : Rat))
  | 13 => ((-126918296009425153 : Rat) / (12500000000000000000000000000000000000 : Rat))
  | 14 => ((1630406706778533357 : Rat) / (20000000000000000000000000000000000000 : Rat))
  | 15 => ((-7689410156069335989 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 16 => ((394583931044177903 : Rat) / (40000000000000000000000000000000000000 : Rat))
  | 17 => ((2869003902770963819 : Rat) / (50000000000000000000000000000000000000 : Rat))
  | 18 => ((-1744452658606071729 : Rat) / (25000000000000000000000000000000000000 : Rat))
  | 19 => ((2308438688896104387 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 20 => ((3810690383811020543 : Rat) / (100000000000000000000000000000000000000 : Rat))
  | 21 => ((-385834099080410627 : Rat) / (6250000000000000000000000000000000000 : Rat))
  | 22 => ((99013448762955427 : Rat) / (3125000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Generated positive-tail remainder radius data for control k=9. -/
def controlK9AnalyticATailRemainderRadiusRat : Nat -> Rat
  | 0 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 1 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 2 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 3 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 4 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 5 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 6 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 7 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 8 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 9 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 10 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 11 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 12 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 13 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 14 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 15 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 16 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 17 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 18 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 19 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 20 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 21 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | 22 => ((866072951420431 : Rat) / (5000000000000000000000000000000000000 : Rat))
  | _ => 0

/-- Real-valued finite-window lower data for control k=9. -/
def controlK9AnalyticAFiniteLower (n : CoeffIndex23) : Real :=
  (controlK9AnalyticAFiniteLowerRat n.1 : Real)

/-- Real-valued finite-window upper data for control k=9. -/
def controlK9AnalyticAFiniteUpper (n : CoeffIndex23) : Real :=
  (controlK9AnalyticAFiniteUpperRat n.1 : Real)

/-- Real-valued tail radius data for control k=9. -/
def controlK9AnalyticATailRadius (n : CoeffIndex23) : Real :=
  (controlK9AnalyticATailRadiusRat n.1 : Real)

/-- Real-valued common tail radius for control k=9. -/
def controlK9AnalyticATailRadiusCommon : Real :=
  (controlK9AnalyticATailRadiusCommonRat : Real)

/-- Real-valued positive-tail-window lower data for control k=9. -/
def controlK9AnalyticATailWindowLower (n : CoeffIndex23) : Real :=
  (controlK9AnalyticATailWindowLowerRat n.1 : Real)

/-- Real-valued positive-tail-window upper data for control k=9. -/
def controlK9AnalyticATailWindowUpper (n : CoeffIndex23) : Real :=
  (controlK9AnalyticATailWindowUpperRat n.1 : Real)

/-- Real-valued positive-tail remainder radius data for control k=9. -/
def controlK9AnalyticATailRemainderRadius (n : CoeffIndex23) : Real :=
  (controlK9AnalyticATailRemainderRadiusRat n.1 : Real)

/-- Local proof slack for post-520 control log-majorant tail comparisons. -/
def controlK9AnalyticATailProofRemainderRadius (_n : CoeffIndex23) : Real :=
  (1 : Real) / (10 : Real) ^ 18

/-- Real-valued signed two-sided tail lower data for control k=9. -/
def controlK9AnalyticASignedTailLower (n : CoeffIndex23) : Real :=
  2 * (controlK9AnalyticATailWindowLower n - controlK9AnalyticATailRemainderRadius n)

/-- Real-valued signed two-sided tail upper data for control k=9. -/
def controlK9AnalyticASignedTailUpper (n : CoeffIndex23) : Real :=
  2 * (controlK9AnalyticATailWindowUpper n + controlK9AnalyticATailRemainderRadius n)

/-- Real-valued signed two-sided tail lower data using the local proof slack. -/
def controlK9AnalyticASignedTailProofLower (n : CoeffIndex23) : Real :=
  2 * (controlK9AnalyticATailWindowLower n - controlK9AnalyticATailProofRemainderRadius n)

/-- Real-valued signed two-sided tail upper data using the local proof slack. -/
def controlK9AnalyticASignedTailProofUpper (n : CoeffIndex23) : Real :=
  2 * (controlK9AnalyticATailWindowUpper n + controlK9AnalyticATailProofRemainderRadius n)

/-- Positive-half finite-window lower target for the folded payload, control k=9. -/
def controlK9AnalyticAFinitePositiveLower (n : CoeffIndex23) : Real :=
  controlK9AnalyticAFiniteLower n / 2

/-- Positive-half finite-window upper target for the folded payload, control k=9. -/
def controlK9AnalyticAFinitePositiveUpper (n : CoeffIndex23) : Real :=
  controlK9AnalyticAFiniteUpper n / 2

theorem controlK9AnalyticAFinitePositiveLowerBound_generated :
    ∀ n : CoeffIndex23,
      controlK9AnalyticAFiniteLower n <= 2 * controlK9AnalyticAFinitePositiveLower n := by
  intro n
  have h :
      2 * controlK9AnalyticAFinitePositiveLower n = controlK9AnalyticAFiniteLower n := by
    unfold controlK9AnalyticAFinitePositiveLower
    ring
  rw [h]

theorem controlK9AnalyticAFinitePositiveUpperBound_generated :
    ∀ n : CoeffIndex23,
      2 * controlK9AnalyticAFinitePositiveUpper n <= controlK9AnalyticAFiniteUpper n := by
  intro n
  have h :
      2 * controlK9AnalyticAFinitePositiveUpper n = controlK9AnalyticAFiniteUpper n := by
    unfold controlK9AnalyticAFinitePositiveUpper
    ring
  rw [h]

/-- Center of the generated finite-window enclosure for control k=9. -/
def controlK9AnalyticAFiniteMid (n : CoeffIndex23) : Real :=
  (controlK9AnalyticAFiniteLower n + controlK9AnalyticAFiniteUpper n) / 2

/-- Radius of the generated finite-window enclosure for control k=9. -/
def controlK9AnalyticAFiniteRadius (n : CoeffIndex23) : Real :=
  (controlK9AnalyticAFiniteUpper n - controlK9AnalyticAFiniteLower n) / 2

theorem controlK9AnalyticAFiniteTailArithmeticBoundsCert_generated :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailArithmeticBoundsCert
      controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  refine { h := ?_ }
  intro n
  fin_cases n <;>
    refine { hLower := ?_, hUpper := ?_ } <;>
    norm_num [
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailArithmeticIntervalCert,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFiniteTailArithmeticCert,
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower,
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper,
      controlK9AnalyticAFiniteLower,
      controlK9AnalyticAFiniteUpper,
      controlK9AnalyticATailRadius,
      controlK9AnalyticAFiniteLowerRat,
      controlK9AnalyticAFiniteUpperRat,
      controlK9AnalyticATailRadiusRat,
      CenteredCoeffPayloadImport.controlK9AAbsDistanceEntryRat,
      CenteredCoeffPayloadImport.controlK9ARadiusAbsDistanceEntryRat
    ]

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert_of_analyticAndArithmeticBoundsCert
      analytic controlK9AnalyticAFiniteTailArithmeticBoundsCert_generated

theorem controlK9AnalyticATailGrowthBoundsCert_of_commonGeneratedTailRadius
    {C0 C1 : Real}
    (hTail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        9 ((3 : Real) / (10 : Real)) archAFiniteTailCutoff C0 C1 <= controlK9AnalyticATailRadiusCommon) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailGrowthBoundsCert
      archAFiniteTailCutoff C0 C1 controlK9AnalyticATailRadius := by
  refine ⟨?_⟩
  intro n
  fin_cases n <;>
    simpa [
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound,
      controlK9AnalyticATailRadius,
      controlK9AnalyticATailRadiusRat,
      controlK9AnalyticATailRadiusCommon,
      controlK9AnalyticATailRadiusCommonRat
    ] using hTail

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (tailGrowth :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailGrowthBoundsCert
        archAFiniteTailCutoff C0 C1 controlK9AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  exact controlK9AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailGrowthBounds
      hC0 hC1 hgrowth (by norm_num [archAFiniteTailCutoff]) finite tailGrowth)

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    {tailLower tailUpper : CoeffIndex23 → Real}
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (tail :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert
        archAFiniteTailCutoff tailLower tailUpper controlK9AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  exact controlK9AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
      finite tail)

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (hTail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        9 ((3 : Real) / (10 : Real)) archAFiniteTailCutoff C0 C1 <= controlK9AnalyticATailRadiusCommon) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  exact controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth hC0 hC1 hgrowth finite
    (controlK9AnalyticATailGrowthBoundsCert_of_commonGeneratedTailRadius hTail)

theorem controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
    (window :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        controlK9AnalyticATailWindowLower controlK9AnalyticATailWindowUpper controlK9AnalyticATailRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert
      archAFiniteTailCutoff controlK9AnalyticASignedTailLower controlK9AnalyticASignedTailUpper controlK9AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
      (by norm_num [archAFiniteTailCutoff])
      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])
      window
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailLower,
          controlK9AnalyticASignedTailUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRemainderRadiusRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailLower,
          controlK9AnalyticASignedTailUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRemainderRadiusRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailLower,
          controlK9AnalyticASignedTailUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRemainderRadiusRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailLower,
          controlK9AnalyticASignedTailUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRemainderRadiusRat,
          controlK9AnalyticATailRadiusRat
          ])

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindow
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        controlK9AnalyticATailWindowLower controlK9AnalyticATailWindowUpper controlK9AnalyticATailRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper controlK9AnalyticATailRadius := by
  exact controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    finite
    (controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow window)

theorem controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
    (window :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        controlK9AnalyticATailWindowLower controlK9AnalyticATailWindowUpper
        controlK9AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert
      archAFiniteTailCutoff controlK9AnalyticASignedTailProofLower
      controlK9AnalyticASignedTailProofUpper controlK9AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
      (by norm_num [archAFiniteTailCutoff])
      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])
      window
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailProofLower,
          controlK9AnalyticASignedTailProofUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailProofRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailProofLower,
          controlK9AnalyticASignedTailProofUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailProofRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailProofLower,
          controlK9AnalyticASignedTailProofUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailProofRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRadiusRat
          ])
      (by
        intro n
        fin_cases n <;>
          norm_num [
          controlK9AnalyticASignedTailProofLower,
          controlK9AnalyticASignedTailProofUpper,
          controlK9AnalyticATailWindowLower,
          controlK9AnalyticATailWindowUpper,
          controlK9AnalyticATailProofRemainderRadius,
          controlK9AnalyticATailRadius,
          controlK9AnalyticATailWindowLowerRat,
          controlK9AnalyticATailWindowUpperRat,
          controlK9AnalyticATailRadiusRat
          ])

theorem controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        controlK9AnalyticATailWindowLower controlK9AnalyticATailWindowUpper
        controlK9AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper
      controlK9AnalyticATailRadius := by
  exact controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailInterval
    finite
    (controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder window)

theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
    (finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper)
    (window :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        archAFiniteTailCutoff archAPositiveTailWindowEnd
        controlK9AnalyticATailWindowLower controlK9AnalyticATailWindowUpper
        controlK9AnalyticATailProofRemainderRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper
      controlK9AnalyticATailRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
      finite
      (controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder window)

theorem controlK9AnalyticARecenterContainment_generated :
    ∀ n : CoeffIndex23,
      controlK9AnalyticAFiniteRadius n + controlK9AnalyticATailRadius n +
          |controlK9AnalyticAFiniteMid n -
            (CenteredCoeffPayloadImport.controlK9AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.controlK9ARadiusAbsDistanceEntryRat n.1 : Real) := by
  intro n
  fin_cases n <;>
    norm_num [
      controlK9AnalyticAFiniteMid,
      controlK9AnalyticAFiniteRadius,
      controlK9AnalyticAFiniteLower,
      controlK9AnalyticAFiniteUpper,
      controlK9AnalyticATailRadius,
      controlK9AnalyticAFiniteLowerRat,
      controlK9AnalyticAFiniteUpperRat,
      controlK9AnalyticATailRadiusRat,
      CenteredCoeffPayloadImport.controlK9AAbsDistanceEntryRat,
      CenteredCoeffPayloadImport.controlK9ARadiusAbsDistanceEntryRat
    ]

theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_to_midRadius
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper
        controlK9AnalyticATailRadius) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      archAFiniteTailCutoff
      (fun n => controlK9AnalyticAFiniteMid n - controlK9AnalyticAFiniteRadius n)
      (fun n => controlK9AnalyticAFiniteMid n + controlK9AnalyticAFiniteRadius n)
      controlK9AnalyticATailRadius := by
  refine ⟨?_⟩
  intro n
  have hn := analytic.h n
  refine
    { hFiniteLower := ?_
      hFiniteUpper := ?_
      hTail := hn.hTail }
  · have hLowerEq :
        controlK9AnalyticAFiniteMid n - controlK9AnalyticAFiniteRadius n =
          controlK9AnalyticAFiniteLower n := by
      unfold controlK9AnalyticAFiniteMid controlK9AnalyticAFiniteRadius
      ring
    rw [hLowerEq]
    exact hn.hFiniteLower
  · have hUpperEq :
        controlK9AnalyticAFiniteMid n + controlK9AnalyticAFiniteRadius n =
          controlK9AnalyticAFiniteUpper n := by
      unfold controlK9AnalyticAFiniteMid controlK9AnalyticAFiniteRadius
      ring
    rw [hUpperEq]
    exact hn.hFiniteUpper

theorem controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper
        controlK9AnalyticATailRadius) :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
      (T := archAFiniteTailCutoff)
      (finiteMid := controlK9AnalyticAFiniteMid)
      (finiteRadius := controlK9AnalyticAFiniteRadius)
      (tailRadius := controlK9AnalyticATailRadius)
      (controlK9AnalyticAFiniteTailAnalyticBoundsCert_to_midRadius analytic)
      controlK9AnalyticARecenterContainment_generated

theorem controlK9AnalyticA_entry_hbox_of_delta_recenter_checks
    (analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        archAFiniteTailCutoff controlK9AnalyticAFiniteLower controlK9AnalyticAFiniteUpper
        controlK9AnalyticATailRadius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      CenteredCoeffPayloadImport.controlK9A
      CenteredCoeffPayloadImport.controlK9ARadius := by
  exact
    CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
      (controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks analytic)

end PSDpd
end Q3
