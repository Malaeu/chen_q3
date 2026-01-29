# A1 Density — FINAL STEP ONLY

## CRITICAL INSTRUCTION

**DO NOT REPROVE ANY LEMMAS!** All lemmas are ALREADY PROVEN in the context file `A1_density_ASSEMBLY_ONLY_aristotle.lean`.

Your ONLY task: Write the FINAL theorem that USES these existing lemmas.

## Available Lemmas (ALREADY PROVEN — just reference them!)

```lean
-- All these are PROVEN and available:
lemma HeatKernel_integral (t : ℝ) (ht : t > 0) : ∫ x, HeatKernel t x = 1
lemma HeatKernel_mass_concentration (δ : ℝ) (hδ : δ > 0) : ...
lemma HeatKernel_nonneg (t : ℝ) (ht : t > 0) (x : ℝ) : 0 ≤ HeatKernel t x
lemma FejerKernel_bounds (B : ℝ) (hB : B > 0) (x : ℝ) : 0 ≤ FejerKernel B x ∧ FejerKernel B x ≤ 1
lemma exists_compact_extension (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ) (hΦ_cont : ContinuousOn Φ (Set.Icc (-K) K)) : ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ x ∈ Set.Icc (-K) K, Ψ x = Φ x
lemma HeatKernel_approx_identity_uniform (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_supp : HasCompactSupport f) (ε : ℝ) (hε : ε > 0) : ∃ t₀ > 0, ∀ t ∈ Set.Ioo 0 t₀, ∀ x, |real_convolution f (HeatKernel t) x - f x| < ε
lemma fejer_sum_approx (K : ℝ) (hK : K > 0) (t : ℝ) (ht : t > 0) (s : Finset ℝ) (w : ℝ → ℝ) ... : ∃ B > 0, ∀ x ∈ Set.Icc (-K) K, |...| < ε
lemma sum_atoms_in_cone (K : ℝ) (s : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ y ∈ s, 0 ≤ w y) (B : ℝ) (hB : B > 0) (t : ℝ) (ht : t > 0) (hs : ∀ y ∈ s, y ∈ Set.Icc (-K) K) (h_sum_pos : ∑ y ∈ s, w y > 0) : (fun x => ∑ y ∈ s, w y * Atom B t y x) ∈ AtomCone_K K
lemma exists_even_compact_extension (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ) (hΦ_cont : ContinuousOn Φ (Set.Icc (-K) K)) (hΦ_even : Even Φ) : ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ Even Ψ ∧ ∀ x ∈ Set.Icc (-K) K, Ψ x = Φ x
lemma HeatKernel_even (t : ℝ) : Even (HeatKernel t)
lemma even_convolution (f g : ℝ → ℝ) (hf : Even f) (hg : Even g) : Even (real_convolution f g)
lemma uniform_riemann_sum (a b : ℝ) (hab : a < b) (X : Set ℝ) (hX : IsCompact X) (F : ℝ → ℝ → ℝ) ... (ε : ℝ) (hε : ε > 0) : ∃ (s : Finset ℝ) (w : ℝ → ℝ), ... ∀ x ∈ X, |(∫ y in Set.Icc a b, F x y) - ∑ y ∈ s, w y * F x y| < ε
lemma sSup_lt_of_compact_image_lt (K : Set ℝ) (hK : IsCompact K) (hK_nonempty : K.Nonempty) (f : ℝ → ℝ) (hf_cont : ContinuousOn f K) (ε : ℝ) (h : ∀ x ∈ K, f x < ε) : sSup (f '' K) < ε
```

## YOUR ONLY OUTPUT

Write ONLY this theorem (about 30-50 lines):

```lean
theorem A1_density_WK (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0, ∃ g ∈ AtomCone_K K, sSup (diff_set Φ g K) < ε := by
  intro Φ hΦ ε hε
  -- Step 1: Get even extension Ψ
  obtain ⟨Ψ, hΨ_cont, hΨ_supp, hΨ_even, hΨ_eq⟩ := exists_even_compact_extension K hK Φ hΦ.1 ⟨_, hΦ.2.1⟩
  -- Step 2: Get t₀ from heat kernel approximation (for ε/3)
  obtain ⟨t₀, ht₀_pos, ht₀_approx⟩ := HeatKernel_approx_identity_uniform Ψ hΨ_cont hΨ_supp (ε/3) (by linarith)
  -- Step 3: Use uniform_riemann_sum to get finite approximation (for ε/3)
  -- Step 4: Use fejer_sum_approx to replace with atoms (for ε/3)
  -- Step 5: Use sum_atoms_in_cone to show result is in cone
  -- Step 6: Use sSup_lt_of_compact_image_lt with triangle inequality
  sorry
```

## Proof Strategy

The key insight is triangle inequality:

```
|Φ(x) - g(x)| = |Ψ(x) - g(x)|                          (by hΨ_eq on [-K,K])
             ≤ |Ψ(x) - (Ψ*H_t)(x)|                     (heat approx: < ε/3)
             + |(Ψ*H_t)(x) - Σ w_i·H_t(x-y_i)|         (Riemann sum: < ε/3)
             + |Σ w_i·H_t(x-y_i) - g(x)|               (Fejér approx: < ε/3)
             < ε
```

Where g = Σ w_i · Atom(B,t,y_i) which is in AtomCone_K by sum_atoms_in_cone.

## DO NOT

- Do NOT reprove HeatKernel_integral
- Do NOT reprove exists_even_compact_extension
- Do NOT reprove uniform_riemann_sum
- Do NOT reprove ANY lemma from the context file
- ONLY write theorem A1_density_WK using existing lemmas

## Expected Size

About 30-80 lines of Lean code for the theorem proof.
