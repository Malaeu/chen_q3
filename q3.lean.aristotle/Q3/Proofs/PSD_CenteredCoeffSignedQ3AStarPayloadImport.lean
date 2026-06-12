import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffSignedQ3AStarPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffBaseHboxImport

/-!
Signed-Q3.a_star A midpoint payload for Step33 route B.

The legacy Step22 A table is intentionally left untouched.  These
midpoints are the negative full-even `Q3.a_star` candidate rows from
`a_source_convention_audit.json`; radii are doubled positive-window
integration radii from the same audit.
-/

def primaryK11SignedQ3AStarAAbsDistanceEntryRat : Nat -> Rat
  | 0 => ((7889774143023172000000000000 : Rat) / 100000000000000000000000000)
  | 1 => ((-1572542934926196200000000000 : Rat) / 100000000000000000000000000)
  | 2 => ((-7469675830471349000000000000 : Rat) / 1000000000000000000000000000)
  | 3 => ((-5014098991104841400000000000 : Rat) / 1000000000000000000000000000)
  | 4 => ((-3814197667403072000000000000 : Rat) / 1000000000000000000000000000)
  | 5 => ((-3099853932052166600000000000 : Rat) / 1000000000000000000000000000)
  | 6 => ((-2625041772328408200000000000 : Rat) / 1000000000000000000000000000)
  | 7 => ((-2286147436237262000000000000 : Rat) / 1000000000000000000000000000)
  | 8 => ((-2031834749763160800000000000 : Rat) / 1000000000000000000000000000)
  | 9 => ((-1833738446635873000000000000 : Rat) / 1000000000000000000000000000)
  | 10 => ((-1674899668762153400000000000 : Rat) / 1000000000000000000000000000)
  | 11 => ((-1544553150226843600000000000 : Rat) / 1000000000000000000000000000)
  | 12 => ((-1435535257111522600000000000 : Rat) / 1000000000000000000000000000)
  | 13 => ((-1342893748723252400000000000 : Rat) / 1000000000000000000000000000)
  | 14 => ((-1263095614455822800000000000 : Rat) / 1000000000000000000000000000)
  | 15 => ((-1193552793876781400000000000 : Rat) / 1000000000000000000000000000)
  | 16 => ((-1132326241300931400000000000 : Rat) / 1000000000000000000000000000)
  | 17 => ((-1077934686332841200000000000 : Rat) / 1000000000000000000000000000)
  | 18 => ((-1029227272178921000000000000 : Rat) / 1000000000000000000000000000)
  | 19 => ((-9852964852298352600000000000 : Rat) / 10000000000000000000000000000)
  | 20 => ((-9454172459708522000000000000 : Rat) / 10000000000000000000000000000)
  | 21 => ((-9090034253113752000000000000 : Rat) / 10000000000000000000000000000)
  | 22 => ((-8755762330680156800000000000 : Rat) / 10000000000000000000000000000)
  | _ => 0

def primaryK11SignedQ3AStarARadiusAbsDistanceEntryRat : Nat -> Rat
  | 0 => ((6294 : Rat) / 1000000000000000000)
  | 1 => ((7320 : Rat) / 10000000000000000000)
  | 2 => ((13948 : Rat) / 100000000000000000000)
  | 3 => ((3220 : Rat) / 10000000000000000000)
  | 4 => ((8008 : Rat) / 100000000000000000000)
  | 5 => ((15838 : Rat) / 100000000000000000000)
  | 6 => ((11766 : Rat) / 100000000000000000000)
  | 7 => ((2058 : Rat) / 10000000000000000000)
  | 8 => ((3564 : Rat) / 100000000000000000000)
  | 9 => ((4844 : Rat) / 100000000000000000000)
  | 10 => ((19168 : Rat) / 1000000000000000000000)
  | 11 => ((19280 : Rat) / 1000000000000000000000)
  | 12 => ((2692 : Rat) / 100000000000000000000)
  | 13 => ((7030 : Rat) / 100000000000000000000)
  | 14 => ((4052 : Rat) / 100000000000000000000)
  | 15 => ((2276 : Rat) / 100000000000000000000)
  | 16 => ((9522 : Rat) / 100000000000000000000)
  | 17 => ((7304 : Rat) / 100000000000000000000)
  | 18 => ((8578 : Rat) / 100000000000000000000)
  | 19 => ((18852 : Rat) / 1000000000000000000000)
  | 20 => ((16966 : Rat) / 10000000000000000000000)
  | 21 => ((4202 : Rat) / 100000000000000000000)
  | 22 => ((7626 : Rat) / 1000000000000000000000)
  | _ => 0

def primaryK11SignedQ3AStarAEntryRat (i j : Nat) : Rat :=
  primaryK11SignedQ3AStarAAbsDistanceEntryRat (natAbsDiff i j)

def primaryK11SignedQ3AStarARadiusEntryRat (i j : Nat) : Rat :=
  primaryK11SignedQ3AStarARadiusAbsDistanceEntryRat (natAbsDiff i j)

def primaryK11SignedQ3AStarARat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j => primaryK11SignedQ3AStarAEntryRat i.val j.val

def primaryK11SignedQ3AStarA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11SignedQ3AStarARat i j : Real)

def primaryK11SignedQ3AStarARadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j => primaryK11SignedQ3AStarARadiusEntryRat i.val j.val

def primaryK11SignedQ3AStarARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11SignedQ3AStarARadiusRat i j : Real)

def primaryK11SignedQ3AStarR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa primaryK11SignedQ3AStarA primaryK11P0 primaryK11Kappa

def primaryK11SignedQ3AStarD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta primaryK11SignedQ3AStarA primaryK11P primaryK11P0
    primaryK11Kappa primaryK11Theta

def primaryK11SignedQ3AStarRBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    primaryK11SignedQ3AStarARadiusRat i j +
      |primaryK11KappaRat| * primaryK11P0RadiusRat i j

def primaryK11SignedQ3AStarRBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11SignedQ3AStarRBaseRadiusRat i j : Real)

def primaryK11SignedQ3AStarDBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    (1 - primaryK11ThetaRat) * primaryK11SignedQ3AStarARadiusRat i j +
      primaryK11PRadiusRat i j +
        primaryK11ThetaRat * |primaryK11KappaRat| * primaryK11P0RadiusRat i j

def primaryK11SignedQ3AStarDBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11SignedQ3AStarDBaseRadiusRat i j : Real)

def controlK9SignedQ3AStarAAbsDistanceEntryRat : Nat -> Rat
  | 0 => ((7520513017099184000000000000 : Rat) / 100000000000000000000000000)
  | 1 => ((-1732138601963182000000000000 : Rat) / 100000000000000000000000000)
  | 2 => ((-8228638331900756000000000000 : Rat) / 1000000000000000000000000000)
  | 3 => ((-5509349552684056000000000000 : Rat) / 1000000000000000000000000000)
  | 4 => ((-4187531693166952000000000000 : Rat) / 1000000000000000000000000000)
  | 5 => ((-3402043267350283200000000000 : Rat) / 1000000000000000000000000000)
  | 6 => ((-2880395099809516000000000000 : Rat) / 1000000000000000000000000000)
  | 7 => ((-2508251647548807400000000000 : Rat) / 1000000000000000000000000000)
  | 8 => ((-2229071273644481000000000000 : Rat) / 1000000000000000000000000000)
  | 9 => ((-2011647087045394400000000000 : Rat) / 1000000000000000000000000000)
  | 10 => ((-1837334561323877000000000000 : Rat) / 1000000000000000000000000000)
  | 11 => ((-1694304134569279000000000000 : Rat) / 1000000000000000000000000000)
  | 12 => ((-1574686678581520800000000000 : Rat) / 1000000000000000000000000000)
  | 13 => ((-1473043639456833800000000000 : Rat) / 1000000000000000000000000000)
  | 14 => ((-1385495821643334600000000000 : Rat) / 1000000000000000000000000000)
  | 15 => ((-1309202004856731800000000000 : Rat) / 1000000000000000000000000000)
  | 16 => ((-1242033727209003000000000000 : Rat) / 1000000000000000000000000000)
  | 17 => ((-1182365179327440600000000000 : Rat) / 1000000000000000000000000000)
  | 18 => ((-1128933307906596400000000000 : Rat) / 1000000000000000000000000000)
  | 19 => ((-1080742192637241800000000000 : Rat) / 1000000000000000000000000000)
  | 20 => ((-1036996163874817000000000000 : Rat) / 1000000000000000000000000000)
  | 21 => ((-9970520603843846000000000000 : Rat) / 10000000000000000000000000000)
  | 22 => ((-9603845254956077200000000000 : Rat) / 10000000000000000000000000000)
  | _ => 0

def controlK9SignedQ3AStarARadiusAbsDistanceEntryRat : Nat -> Rat
  | 0 => ((3520 : Rat) / 1000000000000000000)
  | 1 => ((5496 : Rat) / 100000000000000000000)
  | 2 => ((7676 : Rat) / 10000000000000000000)
  | 3 => ((2444 : Rat) / 10000000000000000000)
  | 4 => ((15074 : Rat) / 100000000000000000000)
  | 5 => ((4700 : Rat) / 100000000000000000000)
  | 6 => ((4604 : Rat) / 100000000000000000000)
  | 7 => ((3432 : Rat) / 100000000000000000000)
  | 8 => ((3044 : Rat) / 100000000000000000000)
  | 9 => ((18478 : Rat) / 100000000000000000000)
  | 10 => ((2866 : Rat) / 100000000000000000000)
  | 11 => ((10934 : Rat) / 1000000000000000000000)
  | 12 => ((14660 : Rat) / 1000000000000000000000)
  | 13 => ((2186 : Rat) / 100000000000000000000)
  | 14 => ((9222 : Rat) / 100000000000000000000)
  | 15 => ((8758 : Rat) / 100000000000000000000)
  | 16 => ((7454 : Rat) / 100000000000000000000)
  | 17 => ((10164 : Rat) / 100000000000000000000)
  | 18 => ((6776 : Rat) / 100000000000000000000)
  | 19 => ((18854 : Rat) / 1000000000000000000000)
  | 20 => ((6616 : Rat) / 100000000000000000000)
  | 21 => ((4598 : Rat) / 100000000000000000000)
  | 22 => ((7050 : Rat) / 1000000000000000000000)
  | _ => 0

def controlK9SignedQ3AStarAEntryRat (i j : Nat) : Rat :=
  controlK9SignedQ3AStarAAbsDistanceEntryRat (natAbsDiff i j)

def controlK9SignedQ3AStarARadiusEntryRat (i j : Nat) : Rat :=
  controlK9SignedQ3AStarARadiusAbsDistanceEntryRat (natAbsDiff i j)

def controlK9SignedQ3AStarARat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j => controlK9SignedQ3AStarAEntryRat i.val j.val

def controlK9SignedQ3AStarA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9SignedQ3AStarARat i j : Real)

def controlK9SignedQ3AStarARadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j => controlK9SignedQ3AStarARadiusEntryRat i.val j.val

def controlK9SignedQ3AStarARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9SignedQ3AStarARadiusRat i j : Real)

def controlK9SignedQ3AStarR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa controlK9SignedQ3AStarA controlK9P0 controlK9Kappa

def controlK9SignedQ3AStarD : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta controlK9SignedQ3AStarA controlK9P controlK9P0
    controlK9Kappa controlK9Theta

def controlK9SignedQ3AStarRBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    controlK9SignedQ3AStarARadiusRat i j +
      |controlK9KappaRat| * controlK9P0RadiusRat i j

def controlK9SignedQ3AStarRBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9SignedQ3AStarRBaseRadiusRat i j : Real)

def controlK9SignedQ3AStarDBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    (1 - controlK9ThetaRat) * controlK9SignedQ3AStarARadiusRat i j +
      controlK9PRadiusRat i j +
        controlK9ThetaRat * |controlK9KappaRat| * controlK9P0RadiusRat i j

def controlK9SignedQ3AStarDBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9SignedQ3AStarDBaseRadiusRat i j : Real)

end CenteredCoeffSignedQ3AStarPayloadImport
end PSDpd
end Q3
