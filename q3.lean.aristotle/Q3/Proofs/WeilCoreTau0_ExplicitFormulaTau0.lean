import Q3.Proofs.WeilCoreTau0_API

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Proofs.WeilCoreTau0

/-!
Layer 2 (Explicit Formula): explicit-formula contract on the τ=0 test class.
-/

/-- Explicit-formula identity specialized to the τ=0 core test class. -/
def ExplicitFormulaOnTestClass (t0 B_min B_max : ℝ) : Prop :=
  ∀ Φ ∈ TestClass t0 B_min B_max, Q3.Q Φ = Q3.arch_term Φ - Q3.prime_term Φ

/-- Current route: derive τ=0 explicit-formula identity from global explicit formula. -/
theorem explicit_formula_tau0 (t0 B_min B_max : ℝ) :
    ExplicitFormulaOnTestClass t0 B_min B_max := by
  intro Φ hΦ
  exact Q3.explicit_formula Φ (testClass_subset_weil_cone t0 B_min B_max hΦ)

end Q3.Proofs.WeilCoreTau0

