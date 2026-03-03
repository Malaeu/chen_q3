import Q3.Proofs.PrimeTerm_PathB_tcritical

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- Math-facing quarter bound on the prime term at `t_critical`.
This is one of the two remaining analytic obligations for full Path B closure. -/
axiom prime_term_tcritical_le_cstar_quarter_mathan
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift B t_critical τ ξ) ≤ Q3.c_star / 4

/-- Math-facing quarter bound on the arch term at `t_critical`.
This is the second analytic obligation for full Path B closure. -/
axiom cstar_quarter_le_arch_term_tcritical_mathan
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q3.c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical τ ξ)

/-- Legacy provider packaged from two explicit math obligations. -/
theorem prime_term_pathB_tcritical_legacy : PrimeTermPathBProvider :=
  by
    intro K B τ hK hB hτB
    exact le_trans
      (prime_term_tcritical_le_cstar_quarter_mathan K B τ hK hB hτB)
      (cstar_quarter_le_arch_term_tcritical_mathan K B τ hK hB hτB)

/-- Compatibility bridge: recover the stable Path B contract from the legacy provider. -/
theorem prime_term_pathB_tcritical_from_legacy : PrimeTermPathBTcritical :=
  prime_term_pathB_tcritical_from_provider prime_term_pathB_tcritical_legacy

end Q3
