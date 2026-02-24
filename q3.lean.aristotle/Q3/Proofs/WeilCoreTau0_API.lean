import Q3.AxiomsTheorems

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Proofs.WeilCoreTau0

/-!
Layer 1 (API): minimal τ=0 test-function interface used by mainline.
-/

/-- Minimal τ=0 test-function API consumed by mainline. -/
abbrev TestClass (t0 B_min B_max : ℝ) : Set (ℝ → ℝ) :=
  Q3.Weil_cone_tau0 t0 B_min B_max

/-- Positivity contract on the τ=0 test class. -/
def NonnegOn (t0 B_min B_max : ℝ) : Prop :=
  ∀ Φ ∈ TestClass t0 B_min B_max, Q3.Q Φ ≥ 0

/-- `W_K` functions are admissible Weil-cone test functions. -/
lemma W_K_subset_Weil_cone (K : ℝ) :
    Q3.W_K K ⊆ Q3.Weil_cone := by
  intro Φ hΦ
  rcases hΦ with ⟨hcont, hsupp, heven, hnonneg⟩
  have hsuppIcc : Function.support Φ ⊆ Set.Icc (-K) K :=
    Set.Subset.trans hsupp Set.Ioo_subset_Icc_self
  have hcompact : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsuppIcc
  exact ⟨heven, hnonneg, hcompact, hcont⟩

/-- `W_K_tau0` sits inside the global Weil cone. -/
lemma W_K_tau0_subset_weil_cone (K t0 B_min B_max : ℝ) :
    Q3.W_K_tau0 K t0 B_min B_max ⊆ Q3.Weil_cone := by
  intro Φ hΦ
  exact W_K_subset_Weil_cone K hΦ.1

/-- Exported embedding from τ=0 test class into global Weil cone. -/
lemma testClass_subset_weil_cone (t0 B_min B_max : ℝ) :
    TestClass t0 B_min B_max ⊆ Q3.Weil_cone := by
  intro Φ hΦ
  rcases hΦ with ⟨K, _hK, hΦK⟩
  exact W_K_tau0_subset_weil_cone K t0 B_min B_max hΦK

end Q3.Proofs.WeilCoreTau0

