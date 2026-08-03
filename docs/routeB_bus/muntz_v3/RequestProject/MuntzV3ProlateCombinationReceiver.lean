import RequestProject.MuntzV3SymmetricTrialCrosswalk
import RequestProject.ProlateExport.ProlateCombinationMuntzRegularity
import RequestProject.ProlateExport.ProlateModeRegularity

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace EStarMuntzZeroMassContinuation

/-- Continued Müntz-v3 identity for the canonical two-mode prolate
combination, conditional only on measurability and positive-half Lipschitz
regularity of the supplied modes.  The `ProlatePair` and combination are the
provenance-locked Q3 declarations; this theorem does not construct modes,
certify their normalization, or identify a finite/cofinal ground family. -/
theorem continued_window_identity_prolateCombination_v3Class
    (P : Q3.RouteB.D0Pstar.ProlatePair) (K0 K4 : NNReal)
    (hlambda : 0 ≤ P.pw.lambda)
    (h0meas : Measurable P.h0)
    (h4meas : Measurable P.h4)
    (h0lip : LipschitzOnWith K0 P.h0
      (Set.Ico (0 : ℝ) P.pw.lambda))
    (h4lip : LipschitzOnWith K4 P.h4
      (Set.Ico (0 : ℝ) P.pw.lambda))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin (Q3.RouteB.D0Pstar.prolateCombination P) Λ s =
        ZetaMellinPoleSub
            (Q3.RouteB.D0Pstar.prolateCombination P) (s + 1 / 2) -
          Rminus (Q3.RouteB.D0Pstar.prolateCombination P) Λ s -
          Rplus (Q3.RouteB.D0Pstar.prolateCombination P) Λ s := by
  obtain ⟨K, _heven, hmeas, hsupp, hlip, hmass⟩ :=
    Q3.RouteB.D0Pstar.prolateCombination_muntzRegularity_of_modes
      P K0 K4 h0meas h4meas h0lip h4lip
  exact continued_window_identity_symmetricTrial_v3Class
    (Q3.RouteB.D0Pstar.prolateCombination P) P.pw.lambda K hlambda
    hmeas hsupp hlip hmass Λ hΛ

/-- Continued Müntz-v3 identity for the canonical two-mode prolate
combination, conditional only on positive-half Lipschitz regularity of the two
stored modes.  Mode measurability follows from their stored evenness and
symmetric support; this theorem still does not construct source PSWF modes. -/
theorem continued_window_identity_prolateCombination_v3Class_of_modeLipschitz
    (P : Q3.RouteB.D0Pstar.ProlatePair) (K0 K4 : NNReal)
    (hlambda : 0 ≤ P.pw.lambda)
    (h0lip : LipschitzOnWith K0 P.h0
      (Set.Ico (0 : ℝ) P.pw.lambda))
    (h4lip : LipschitzOnWith K4 P.h4
      (Set.Ico (0 : ℝ) P.pw.lambda))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin (Q3.RouteB.D0Pstar.prolateCombination P) Λ s =
        ZetaMellinPoleSub
            (Q3.RouteB.D0Pstar.prolateCombination P) (s + 1 / 2) -
          Rminus (Q3.RouteB.D0Pstar.prolateCombination P) Λ s -
          Rplus (Q3.RouteB.D0Pstar.prolateCombination P) Λ s := by
  have h0meas : Measurable P.h0 :=
    Q3.RouteB.D0Pstar.measurable_of_even_support_positiveHalfLipschitz
      P.h0 P.pw.lambda K0 P.h0_even P.h0_support h0lip
  have h4meas : Measurable P.h4 :=
    Q3.RouteB.D0Pstar.measurable_of_even_support_positiveHalfLipschitz
      P.h4 P.pw.lambda K4 P.h4_even P.h4_support h4lip
  exact continued_window_identity_prolateCombination_v3Class
    P K0 K4 hlambda h0meas h4meas h0lip h4lip Λ hΛ

#print axioms continued_window_identity_prolateCombination_v3Class
#print axioms continued_window_identity_prolateCombination_v3Class_of_modeLipschitz

end EStarMuntzZeroMassContinuation
