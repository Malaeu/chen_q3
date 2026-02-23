/-
A1 density (compatibility wrapper)
================================

This module is intentionally minimal for the active Q3 audit path.
The production A1 route is provided by `Q3.Proofs.A1_density` / A1prime modules.
-/

import Q3.Axioms

set_option linter.mathlibStandardSet false

namespace Q3.Proofs.A1DensityMain

/-- Compatibility wrapper to the current A1 axiom interface (fixed `t0`). -/
theorem A1_density (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0) :
    ∀ Φ ∈ Q3.W_K K, ∀ ε > 0,
      ∃ g ∈ Q3.AtomCone_K_fixed K t0,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε :=
  Q3.A1_density_WK_axiom K hK t0 ht0

/-- Historical alias kept for compatibility with bridge wrappers. -/
theorem closes_A1_density_axiom (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0) :
    ∀ Φ ∈ Q3.W_K K, ∀ ε > 0,
      ∃ g ∈ Q3.AtomCone_K_fixed K t0,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε :=
  A1_density K hK t0 ht0

end Q3.Proofs.A1DensityMain
