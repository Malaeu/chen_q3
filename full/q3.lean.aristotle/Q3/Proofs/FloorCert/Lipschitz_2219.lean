import Mathlib
import Q3.Proofs.FloorCert.Defs
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

/-!
Lipschitz certificate on Icc[-1/2, 1/2] for t_critical.
Sources:
- output/floor_cert_tcritical_2026-01-25_2219.txt
- output/lipschitz_cert_tcritical_2026-01-25_2350.txt
-/

noncomputable section

namespace Q3.Proofs.FloorCert

/-- Lipschitz certificate on the fundamental domain. -/
axiom P_A_Lipschitz_on_Icc_cert :
    ∀ x y,
      x ∈ Set.Icc (-1/2 : ℝ) (1/2) →
      y ∈ Set.Icc (-1/2 : ℝ) (1/2) →
      |P_A B_min t_critical x - P_A B_min t_critical y| ≤
        floor_cert_L_ub * |x - y|

end Q3.Proofs.FloorCert
