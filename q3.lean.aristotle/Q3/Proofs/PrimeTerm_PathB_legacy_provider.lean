import Q3.Proofs.PrimeTerm_PathB_tcritical

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- Legacy off-mainline placeholder providing the full Path B contract. -/
axiom prime_term_pathB_tcritical_legacy : PrimeTermPathBProvider

/-- Compatibility bridge: recover the stable Path B contract from the legacy provider. -/
theorem prime_term_pathB_tcritical_from_legacy : PrimeTermPathBTcritical :=
  prime_term_pathB_tcritical_from_provider prime_term_pathB_tcritical_legacy

end Q3

