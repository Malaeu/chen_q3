/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MuntzV3ExactClassClosure.lean
Source SHA-256: f4ea12e1497b37a809c27db35f95035111d0d126942ea8c7557ec435b0e3ebfd
Body copied byte-for-byte; import paths rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.Unconditional
import Q3.Proofs.RouteB.MuntzV3.GwinExactClass
import Q3.Proofs.RouteB.MuntzV3.RplusExactClass
import Q3.Proofs.RouteB.MuntzV3.HabsExactClass

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

namespace EStarMuntzZeroMassContinuation

/-- The repaired v3 class discharges all four retained analytic suppliers
`hG`, `hRm`, `hRp`, and `habs` for the continued window identity. -/
theorem continued_window_identity_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s :=
  continued_window_identity_unconditional_mellin
    h b K hmeas hsupp hlip hmass Λ
    (gwin_analyticOnNhd_shiftedHalfPlane_v3Class
      h b K hmeas hsupp hlip Λ hΛ)
    (rminus_analyticOnNhd_shiftedHalfPlane_v3Class
      h b K hb hmeas hsupp hlip hmass Λ hΛ)
    (rplus_analyticOnNhd_shiftedHalfPlane_v3Class
      h b K hmeas hsupp hlip Λ hΛ)
    (habs_of_IccZero_IcoLipschitz
      h b K hb hmeas hsupp hlip hmass Λ hΛ)

/-- Away from the removable pole, the exact-class continuation agrees with the raw
zeta-Mellin product. -/
theorem continued_window_identity_raw_off_pole_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re → s ≠ 1 / 2 →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s :=
  continued_window_identity_raw_off_pole h Λ (mellin_one_eq_zero h hmass)
    (continued_window_identity_v3Class
      h b K hb hmeas hsupp hlip hmass Λ hΛ)

/-- At the removable pole, the exact-class continuation has the derivative value. -/
theorem continued_window_identity_pole_value_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Gwin h Λ (1 / 2) =
      deriv (Mellin h) 1 - Rminus h Λ (1 / 2) - Rplus h Λ (1 / 2) :=
  continued_window_identity_pole_value h Λ
    (continued_window_identity_v3Class
      h b K hb hmeas hsupp hlip hmass Λ hΛ)

#print axioms continued_window_identity_v3Class
#print axioms continued_window_identity_raw_off_pole_v3Class
#print axioms continued_window_identity_pole_value_v3Class

end EStarMuntzZeroMassContinuation
