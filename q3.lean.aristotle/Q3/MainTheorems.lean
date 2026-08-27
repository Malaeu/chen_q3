/-
Conditional legacy broad-cone compatibility theorems
=====================================================

This file retains compiled broad-cone compatibility wrappers.  It does not
provide an unconditional or corrected square-class RH export.

Fatal square-class audit note (2026-06-25): the broad-cone RH wrappers in this
file are not the corrected Weil-square export route.

Run: #print axioms Q3.MainTheorems.RH_proven
to see the minimal axiom set.
-/

import Q3.AxiomsTheorems
import Q3.Main
import Q3.Proofs.PaperMainlineAtomRoute

namespace Q3.MainTheorems

/-!
# Verification that Tier-2 axioms are closed by theorems

The theorems in Q3.Theorems have the same types as the axioms in Q3.Axioms.
This means any proof using the axioms can be replicated using the theorems.
-/

-- Check retained compatibility names.
#check Q3.Main.RH_of_Weil_and_Q3
#check Q3.RH_of_shifted_atom_route

/-!
# Retained conditional construction

The following declarations preserve the old compatibility surface:
-/

/-- Legacy broad-cone theorem: Q is nonnegative on `W_K` using theorems.

After the 2026-06-25 square-class audit this is not an RH export route.  Its
target is the broad pointwise-nonnegative `Q3.W_K`, not `Q3.W_sq_K`. -/
theorem Q_nonneg_on_W_K_thm (K : ℝ) (hK : K ≥ 1) : ∀ Φ ∈ Q3.W_K K, Q3.Q Φ ≥ 0 := by
  -- This follows from T5 transfer using:
  -- 1. A1_density_WK (atoms dense in W_K)
  -- 2. Q_Lipschitz (Q is Lipschitz)
  -- 3. Q_nonneg_on_atoms (Q ≥ 0 on atoms)
  exact Q3.T5.T5_transfer K hK

/-- Deprecated legacy RH wrapper on the shifted-atom broad-cone route.

This records the old route shape only; it is not the corrected Weil-square RH
export after the 2026-06-25 audit. -/
@[deprecated Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms
  (since := "2026-08-27")]
theorem RH_proven : Q3.RH :=
  Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms

end Q3.MainTheorems

/-!
# Axiom Summary

Run `#print axioms Q3.MainTheorems.RH_proven` to see:

Expected compatibility dependency profile:
- propext (Lean standard)
- Classical.choice (Lean standard)
- Quot.sound (Lean standard)
- Q3.Weil_criterion
- Q3.prime_term_le_at_t_critical_axiom
-/

#print axioms Q3.MainTheorems.RH_proven
