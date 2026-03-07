import Q3.Proofs.Params_Critical
import Q3.Proofs.Q_nonneg_lemmas
import Q3.Proofs.Q_nonneg_t_critical
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
Evenized-atom positivity follows already from the weaker symmetric pair condition
`Q(phi_shift τ) + Q(phi_shift (-τ)) ≥ 0`.

This is strictly weaker than asking for each shifted window to be nonnegative
under `Q`, and it matches the actual evenized generator used in A1'.
-/
theorem Q_fejer_heat_atom_nonneg_of_phi_pair_nonneg_tcritical
    (B τ : ℝ) (hB : B > 0)
    (h_pair :
      0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) :
    0 ≤ Q (Fejer_heat_atom B t0_critical τ) := by
  obtain ⟨c, hc_pos, hdecomp⟩ := Q3.Fejer_heat_atom_eq_phi_shifts (B := B) (τ := τ)
  have h_int_f :
      MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical B τ x) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
        (B := B) (t := t_critical) (tau := τ) hB)
  have h_int_g :
      MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical B (-τ) x) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
        (B := B) (t := t_critical) (tau := -τ) hB)
  have h_sum_f :
      Summable (fun k => w_Q k * phi_shift_critical B τ (xi_n k)) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
        (B := B) (t := t_critical) (tau := τ) hB)
  have h_sum_g :
      Summable (fun k => w_Q k * phi_shift_critical B (-τ) (xi_n k)) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
        (B := B) (t := t_critical) (tau := -τ) hB)
  have hQ_scale_add :
      Q (fun x => c * (phi_shift_critical B τ x + phi_shift_critical B (-τ) x)) =
        c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) := by
    simpa using
      (Q3.Proofs.QNonnegAtoms.Q_scale_add
        (f := fun x => phi_shift_critical B τ x)
        (g := fun x => phi_shift_critical B (-τ) x)
        (c := c) h_int_f h_int_g h_sum_f h_sum_g)
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hscaled_nonneg :
      0 ≤ c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) :=
    mul_nonneg hc_nonneg h_pair
  have h_eq :
      Q (Fejer_heat_atom B t0_critical τ) =
        c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) := by
    have hfun :
        (fun x => Fejer_heat_atom B t0_critical τ x) =
          fun x => c * (phi_shift_critical B τ x + phi_shift_critical B (-τ) x) := by
      funext x
      simpa using hdecomp x
    simpa [hfun] using hQ_scale_add
  simpa [h_eq] using hscaled_nonneg

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

/--
Compact closure can already be deduced from the weaker symmetric pair condition on
shifted windows, without proving `Q ≥ 0` for each individual `phi_shift`.
-/
theorem Q_nonneg_on_WK_tcritical_of_phi_pair_nonneg
    (K : ℝ) (hK : K ≥ 1)
    (h_pair : ∀ B τ, B > 0 → |τ| + B ≤ K →
      0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  apply Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms K hK
  intro B τ hB hτB
  exact Q_fejer_heat_atom_nonneg_of_phi_pair_nonneg_tcritical B τ hB
    (h_pair B τ hB hτB)

/--
The older stronger route, which proves nonnegativity of each shifted window separately,
implies the new pair-based closure route immediately.
-/
theorem Q_nonneg_on_WK_tcritical_of_phi_nonneg
    (K : ℝ) (hK : K ≥ 1)
    (h_phi : ∀ B τ, B > 0 → |τ| + B ≤ K → 0 ≤ Q (phi_shift_critical B τ)) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  apply Q_nonneg_on_WK_tcritical_of_phi_pair_nonneg K hK
  intro B τ hB hτB
  have hτB_neg : |(-τ)| + B ≤ K := by
    simpa [abs_neg] using hτB
  exact add_nonneg (h_phi B τ hB hτB) (h_phi B (-τ) hB hτB_neg)

/--
Current direct compact-closure theorem coming from the existing `t_critical`
shifted-window route.

Mathematically this is stronger than what the paper needs. Formally it is useful
because it exposes a theorem-level `W_K` positivity node while the scalar route is
being weakened/refactored. It still inherits the live scalar placeholder through
`Q_phi_shift_nonneg_t_critical`.
-/
theorem Q_nonneg_on_WK_tcritical_current_shift_route
    (K : ℝ) (hK : K ≥ 1) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  apply Q_nonneg_on_WK_tcritical_of_phi_nonneg K hK
  intro B τ hB hτB
  exact Q_phi_shift_nonneg_t_critical K B τ hK hB hτB

/--
The same compact-closure theorem, but routed through the exact paper generator
`Fejer_heat_atom`.

This is the correct paper-facing closure node, but at present it still inherits
the live scalar placeholder through `Q_Fejer_heat_atom_nonneg_t_critical`.
-/
theorem Q_nonneg_on_WK_tcritical_current_atom_route
    (K : ℝ) (hK : K ≥ 1) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  apply Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms K hK
  intro B τ hB hτB
  exact Q_Fejer_heat_atom_nonneg_t_critical K B τ hK hB hτB

end Q3.Proofs.CompatibilityReduction
