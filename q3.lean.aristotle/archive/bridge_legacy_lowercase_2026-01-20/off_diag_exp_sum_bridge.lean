/-
Off-Diagonal Exponential Sum Bridge v3 (CLEAN)
===============================================

This file bridges the Aristotle proof (in root namespace) to Q3 namespace.

The key insight: both namespaces define xi_n, Nodes, S_K identically.
The Fintype instance needs explicit transfer.

CLOSES: off_diag_exp_sum_axiom
-/

import Q3.Basic.Defs
-- Import the Aristotle proof (uses root namespace xi_n, Nodes, S_K, delta_K)
import Q3.Proofs.off_diag_exp_sum

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical

noncomputable section

namespace Q3.Proofs.OffDiagBridgeV3

/-! ## Definition Equivalences -/

/-- xi_n are definitionally equal -/
lemma xi_n_eq (n : ℕ) : _root_.xi_n n = Q3.xi_n n := rfl

/-- N_K are definitionally equal -/
lemma N_K_eq (K : ℝ) : _root_.N_K K = Q3.N_K K := rfl

/-- delta_K are definitionally equal -/
lemma delta_K_eq (K : ℝ) : _root_.delta_K K = Q3.delta_K K := rfl

/-- S_K are definitionally equal -/
lemma S_K_eq (K t : ℝ) : _root_.S_K K t = Q3.S_K K t := rfl

/-- Nodes sets are definitionally equal -/
lemma Nodes_eq (K : ℝ) : _root_.Nodes K = Q3.Nodes K := rfl

/-! ## Fintype Instance Transfer -/

/-- Fintype instance for Q3.Nodes K, transferred from root namespace -/
noncomputable instance Q3_Nodes_fintype (K : ℝ) : Fintype (Q3.Nodes K) :=
  inferInstanceAs (Fintype (_root_.Nodes K))

/-! ## The Main Theorem -/

/-- The off-diagonal exponential sum bound in Q3 namespace. -/
theorem off_diag_exp_sum_Q3 (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    (i : Q3.Nodes K) :
    ∑ j : Q3.Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)) else 0) ≤ Q3.S_K K t :=
  _root_.off_diag_exp_sum_bound K t hK ht i

end Q3.Proofs.OffDiagBridgeV3

/-!
## Final Bridge to Axiom

This provides the exact signature needed to close off_diag_exp_sum_axiom.
-/

namespace Q3

/-- Fintype instance for Nodes K in Q3 namespace -/
noncomputable instance Nodes_fintype (K : ℝ) : Fintype (Nodes K) :=
  Proofs.OffDiagBridgeV3.Q3_Nodes_fintype K

/-- **CLOSES off_diag_exp_sum_axiom**

This theorem has the exact signature of the axiom in Q3.Axioms. -/
theorem off_diag_exp_sum_closed (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    (i : Nodes K) :
    ∑ j : Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t :=
  Proofs.OffDiagBridgeV3.off_diag_exp_sum_Q3 K t hK ht i

end Q3

end
