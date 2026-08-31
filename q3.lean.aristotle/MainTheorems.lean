/-
Conditional legacy broad-cone compatibility theorems
=====================================================

This standalone file retains conditional legacy broad-cone wrappers.  It does
not provide an unconditional or corrected square-class RH export.

Run: #print axioms Q3.MainTheorems.RH_of_legacyBroadConeAxioms_compat
to see the minimal axiom set.
-/

import Q3.AxiomsTheorems
import Q3.Main

namespace Q3.MainTheorems

/-!
# Verification that Tier-2 axioms are closed by theorems

The theorems in Q3.Theorems have the same types as the axioms in Q3.Axioms.
This means any proof using the axioms can be replicated using the theorems.
-/

-- Check the deprecated compatibility theorem.
#check Q3.Main.RH_of_Weil_and_Q3

/-!
# Retained conditional construction

The following declarations preserve the old compatibility surface:
-/

/-- Q is nonnegative on W_K using theorems -/
theorem Q_nonneg_on_W_K_thm (K : ℝ) (hK : K ≥ 1) : ∀ Φ ∈ Q3.W_K K, Q3.Q Φ ≥ 0 := by
  -- This follows from T5 transfer using:
  -- 1. A1_density_WK (atoms dense in W_K)
  -- 2. Q_Lipschitz (Q is Lipschitz)
  -- 3. Q_nonneg_on_atoms (Q ≥ 0 on atoms)
  exact Q3.T5.T5_transfer K hK

/-- Deprecated broad-cone positivity wrapper. -/
@[deprecated
  Q3.Conditional.LegacyBroadCone.Q_nonneg_on_broadWeilCone_of_primeTermAxiom
  (since := "2026-08-27")]
theorem Q_nonneg_Weil_cone : ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Conditional.LegacyBroadCone.Q_nonneg_on_broadWeilCone_of_primeTermAxiom

/-- Conditional RH compatibility wrapper.

Renamed from RH_proven 2026-08-31; conditional — see #print axioms. -/
theorem RH_of_legacyBroadConeAxioms_compat : Q3.RH := by
  exact Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms

end Q3.MainTheorems

/-!
# Axiom Summary

Run `#print axioms Q3.MainTheorems.RH_of_legacyBroadConeAxioms_compat` to see:

Expected compatibility dependency profile:
- propext (Lean standard)
- Classical.choice (Lean standard)
- Quot.sound (Lean standard)
- Q3.Weil_criterion (Tier-1: Weil 1952)
- Q3.prime_term_le_at_t_critical_axiom
-/

#print axioms Q3.MainTheorems.RH_of_legacyBroadConeAxioms_compat
