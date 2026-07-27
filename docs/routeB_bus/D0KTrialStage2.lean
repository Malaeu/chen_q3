import Q3.Proofs.RouteB.D0KTrialStage1

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The D0.5 starred summation map
`E_star(f)(u) = u^(1/2) * sum_{n >= 1} f(n*u)`.

The input is the source's midpoint representative, so the endpoint half-values
are already part of `hTrial_m`; they do not alter the formula of the summation
map itself.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:81-88`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:112-133`;
`literature/zotero/H8ULBMAL/fulltext.md:1262-1267,1293-1297`.
-/
def E_star (hTrial_m : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) *
    ∑' n : ℕ+, hTrial_m ((n : ℕ) * u)

/-- The exact D0.5 multiplicative window packet
`gTrial_m = E_star(hTrial_m)|_[lambda_m⁻¹,lambda_m]` in `H_m`.

The `MemLp` argument is the explicit carrier certificate required by
`MemLp.toLp`; it is not a new mathematical hypothesis about the Route-B roof.
The prolate constructor that supplies the midpoint representative must also
supply this standard membership certificate.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:127-133,141-160,169-180`;
`literature/zotero/H8ULBMAL/fulltext.md:1293-1297,1410-1419`.
-/
def gTrial_m
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i))) :
    H_m i :=
  hE_star.toLp (E_star hTrial_m)

/-- The exact D0.5 finite trial object
`gTrial_(m,N) = P_(m,N)(gTrial_m)` in `E_(m,N)`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:195-212`.
-/
def gTrial_m_N
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i))) :
    E_m_N i :=
  P_m_N i (gTrial_m i hTrial_m hE_star)

#print axioms E_star
#print axioms gTrial_m
#print axioms gTrial_m_N

end Q3.RouteB.D0Pstar
