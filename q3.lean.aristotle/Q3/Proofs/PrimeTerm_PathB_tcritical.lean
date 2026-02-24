import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- Path B contract at `t_critical`: prime term is bounded by arch term
for all admissible `(K, B, τ)` in the shifted-window setup. -/
def PrimeTermPathBTcritical : Prop :=
  ∀ (K B τ : ℝ), K ≥ 1 → B > 0 → |τ| + B ≤ K →
    prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤
      arch_term (fun ξ => phi_shift B t_critical τ ξ)

/-- Provider interface for the Path B `t_critical` contract. -/
abbrev PrimeTermPathBProvider : Prop := PrimeTermPathBTcritical

/-- Lift a provider into the stable Path B contract. -/
theorem prime_term_pathB_tcritical_from_provider
    (hProvider : PrimeTermPathBProvider) :
    PrimeTermPathBTcritical :=
  hProvider

/-- Contract consumer for downstream files.
This is the stable entrypoint that should remain unchanged when Path B is closed. -/
theorem prime_term_le_at_t_critical_of_pathB
    (hPathB : PrimeTermPathBTcritical)
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤
      arch_term (fun ξ => phi_shift B t_critical τ ξ) :=
  hPathB K B τ hK hB hτB

end Q3
