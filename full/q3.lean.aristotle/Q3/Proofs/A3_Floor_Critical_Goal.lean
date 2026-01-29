import Mathlib
import Q3.Axioms
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

open scoped Real

noncomputable section

namespace Q3.Proofs.A3FloorCritical

/-- One-scale A3_FLOOR goal at the critical parameter `t_critical = 3/20`.

This is intentionally packaged as a `Prop` (not an axiom and not a sorry-proof) so we can
reference it in the decision tree / Aristotle prompts without polluting the main chain.
-/
def FloorGoal : Prop :=
  ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
    Q3.c_star ≤ P_A B_min Q3.t_critical θ

end Q3.Proofs.A3FloorCritical
