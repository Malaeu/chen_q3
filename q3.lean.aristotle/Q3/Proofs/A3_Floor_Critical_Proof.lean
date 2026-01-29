import Q3.Proofs.A3_Floor_Critical_Goal
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical
import Q3.Proofs.Q_nonneg_t_critical

/-!
A3 Floor at t_critical: direct proof wrapper.

This file bridges FloorGoal to the concrete floor lemma at t_critical.
-/

open Q3

noncomputable section

namespace Q3.Proofs.A3FloorCritical

open Q3

/-! ## Tau=0 rewrite -/

lemma P_A_shift_tau_zero (B t θ : ℝ) :
    Q3.P_A_shift B t 0 θ = P_A B t θ := by
  -- P_A_shift uses phi_shift = fejer_heat_window, which matches w
  simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g, w, Q3.fejer_heat_window]

/-- FloorGoal at t_critical, tau = 0. -/
theorem floor_goal_tcritical : Q3.Proofs.A3FloorCritical.FloorGoal := by
  intro θ hθ
  -- rewrite P_A_critical (tau = 0) to standard P_A
  have hPA : Q3.P_A_critical B_min θ = P_A B_min t_critical θ := by
    -- P_A_critical is defined via P_A_shift at tau = 0
    simpa [Q3.P_A_critical] using (P_A_shift_tau_zero B_min t_critical θ)
  -- floor lemma at t_critical (currently a TODO in Q_nonneg_t_critical.lean)
  have hfloor : Q3.P_A_critical B_min θ ≥ c_star := by
    simpa using (Q3.P_A_ge_c_star_at_t_critical (θ := θ))
  -- conclude FloorGoal
  simpa [hPA] using hfloor

end Q3.Proofs.A3FloorCritical
