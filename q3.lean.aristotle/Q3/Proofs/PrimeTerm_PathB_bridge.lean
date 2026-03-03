import Q3.Proofs.PrimeTerm_PathB_tcritical
import Q3.Proofs.PrimeTerm_t_bridge
import Q3.Proofs.RKHS_cap_rayleigh

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-!
Path B bridge skeleton.

This file isolates the remaining obligations needed to replace
the legacy Path B provider with an analytic proof:
1) an RKHS numeric cap at `t_critical` via `exp_tcrit_to_rkhs * rho_oneK`,
2) an archimedean lower bound at the same `(K,B,τ)` point.

Once those two inputs are proved, the final contract
`PrimeTermPathBTcritical` follows without touching downstream wiring.
-/

/-- Temperature-matched Path B bridge at `t_critical`.

This is the preferred API for closing Path B: both prime and arch bounds are
stated at the same scale (`t_critical`), so no `exp_tcrit_to_rkhs K` bridge
factor is needed. -/
theorem prime_term_le_at_t_critical_of_direct_pathB
    (K B τ : ℝ)
    (_hK : K ≥ 1) (_hB : B > 0) (_hτB : |τ| + B ≤ K)
    (hPrimeQuarter :
      prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤ Q3.c_star / 4)
    (hArchQuarter :
      Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)) :
    prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤
      arch_term (fun ξ => phi_shift B t_critical τ ξ) :=
  le_trans hPrimeQuarter hArchQuarter

/-- Contract-level temperature-matched Path B closure.

If both quarter-bounds are available pointwise at `t_critical`, then the full
Path B contract is proved with no RKHS-to-critical scaling factor. -/
theorem prime_term_pathB_tcritical_of_direct_bounds
    (hPrimeQuarter : ∀ (K B τ : ℝ), K ≥ 1 → B > 0 → |τ| + B ≤ K →
      prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤ Q3.c_star / 4)
    (hArchQuarter : ∀ (K B τ : ℝ), K ≥ 1 → B > 0 → |τ| + B ≤ K →
      Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)) :
    PrimeTermPathBTcritical := by
  intro K B τ hK hB hτB
  exact prime_term_le_at_t_critical_of_direct_pathB
    (K := K) (B := B) (τ := τ) hK hB hτB
    (hPrimeQuarter K B τ hK hB hτB)
    (hArchQuarter K B τ hK hB hτB)

/-- Pointwise Path B bridge from existing RKHS/t-bridge lemmas.

Inputs kept explicit:
- `hRhoQuarter`: numeric RKHS cap at `t_critical`,
- `hArchQuarter`: archimedean lower bound at `t_critical`.

This theorem is intentionally assumption-driven: it is the narrow API where
the remaining analytic proofs should be plugged in. -/
theorem prime_term_le_at_t_critical_of_rkhs_pathB
    (K B τ : ℝ) [Fintype (Q3.Nodes K)]
    (_hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K)
    (hRhoQuarter :
      Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤
        Q3.c_star / 4)
    (hArchQuarter :
      Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)) :
    prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤
      arch_term (fun ξ => phi_shift B t_critical τ ξ) := by
  have hsum_eq :
      prime_term (fun ξ => phi_shift B Q3.Proofs.t_rkhs_cap τ ξ) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * phi_shift B Q3.Proofs.t_rkhs_cap τ (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift
        (B := B) (t := Q3.Proofs.t_rkhs_cap) (tau := τ) (K := K) hB hτB)
  have hprime_rkhs :
      prime_term (fun ξ => phi_shift B Q3.Proofs.t_rkhs_cap τ ξ) ≤
        Q3.Proofs.rho_oneK K := by
    exact Q3.Proofs.prime_term_phi_shift_le_rho_oneK (K := K) (B := B) (tau := τ) hB hτB
  have hcap_sum :
      ∑ n : Q3.Nodes K, Q3.w_Q n * phi_shift B Q3.Proofs.t_rkhs_cap τ (Q3.xi_n n) ≤
        Q3.Proofs.rho_oneK K := by
    simpa [hsum_eq] using hprime_rkhs
  have hprime_tcrit :
      prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤
        Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K := by
    exact Q3.Proofs.PrimeTermBridge.prime_term_phi_shift_tcritical_le_cap
      (K := K) (B := B) (tau := τ) (R := Q3.Proofs.rho_oneK K) hB hτB hcap_sum
  exact le_trans hprime_tcrit (le_trans hRhoQuarter hArchQuarter)

/-- Contract-level Path B bridge.

Provide finite-node instances and two global bound families; obtain the full
`PrimeTermPathBTcritical` contract. -/
theorem prime_term_pathB_tcritical_of_rkhs_bounds
    (hFinite : ∀ K : ℝ, Fintype (Q3.Nodes K))
    (hRhoQuarter : ∀ K : ℝ,
      Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤
        Q3.c_star / 4)
    (hArchQuarter : ∀ (K B τ : ℝ), K ≥ 1 → B > 0 → |τ| + B ≤ K →
      Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)) :
    PrimeTermPathBTcritical := by
  intro K B τ hK hB hτB
  letI : Fintype (Q3.Nodes K) := hFinite K
  exact prime_term_le_at_t_critical_of_rkhs_pathB
    (K := K) (B := B) (τ := τ) hK hB hτB (hRhoQuarter K)
    (hArchQuarter K B τ hK hB hτB)

/-- Legacy/diagnostic path through the RKHS-cap bridge factor.

Use this only when a direct `t_critical` cap is unavailable. The preferred
production route is `prime_term_pathB_tcritical_of_direct_bounds`. -/
theorem prime_term_pathB_tcritical_of_rkhs_bounds_legacy
    (hFinite : ∀ K : ℝ, Fintype (Q3.Nodes K))
    (hRhoQuarter : ∀ K : ℝ,
      Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤
        Q3.c_star / 4)
    (hArchQuarter : ∀ (K B τ : ℝ), K ≥ 1 → B > 0 → |τ| + B ≤ K →
      Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)) :
    PrimeTermPathBTcritical :=
  prime_term_pathB_tcritical_of_rkhs_bounds hFinite hRhoQuarter hArchQuarter

end Q3
