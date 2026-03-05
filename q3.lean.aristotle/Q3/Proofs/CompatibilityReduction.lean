import Q3.Proofs.Params_Critical
import Q3.Proofs.Q_nonneg_lemmas
import Q3.T5_Transfer

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Proofs.CompatibilityReduction

open Q3

/--
Reduction step for the paper mainline: once `Q` is known to be nonnegative on every
shifted evenized Fejer-heat atom at the critical scale, positivity extends to the entire
fixed-`t₀` atom cone.

This theorem does not solve the remaining scalar estimate. It isolates it.
-/
theorem Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms
    (K : ℝ) (hK : K ≥ 1)
    (h_atom : ∀ B τ, B > 0 → |τ| + B ≤ K →
      Q (Fejer_heat_atom B t0_critical τ) ≥ 0) :
    ∀ g ∈ AtomCone_K_fixed K t0_critical, Q g ≥ 0 :=
  Q3.Proofs.Q_nonneg_lemmas.Q_nonneg_on_atomcone_fixed_of_atoms
    K t0_critical hK t0_critical_pos h_atom

/--
Compact closure theorem at the critical scale, reduced to scalar positivity on shifted
evenized atoms.

This is the exact compatibility statement needed by the paper route:
`A1' density + A2 continuity + positivity on generators`.
-/
theorem Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms
    (K : ℝ) (hK : K ≥ 1)
    (h_atom : ∀ B τ, B > 0 → |τ| + B ≤ K →
      Q (Fejer_heat_atom B t0_critical τ) ≥ 0) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  have hAtoms :
      ∀ g ∈ AtomCone_K_fixed K t0_critical, Q g ≥ 0 :=
    Q_nonneg_on_atomcone_fixed_tcritical_of_shifted_evenized_atoms K hK h_atom
  exact Q3.T5.T5_transfer_of_atoms K hK t0_critical t0_critical_pos hAtoms

end Q3.Proofs.CompatibilityReduction
