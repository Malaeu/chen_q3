# A1 Density via Hat Interpolation (Full Request)

Goal: provide Lean proofs for both `hat_interpolation_approx` and the final A1 density theorem using the fixed-t hat interpolation strategy (Lemma 6.4 style). If this is too large, see `A1_density_hat_only_v1.md` (fallback).

## Lean Context

```lean
import Mathlib
import Q3.Axioms

open scoped BigOperators Real Classical Pointwise

noncomputable def FejerKernel (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

noncomputable def HeatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1:ℝ)/2) * Real.exp (-x^2 / (4 * t))

noncomputable def Atom (B t τ : ℝ) (x : ℝ) : ℝ :=
  FejerKernel B (x - τ) * HeatKernel t (x - τ) +
  FejerKernel B (x + τ) * HeatKernel t (x + τ)

abbrev W_K (K : ℝ) : Set (ℝ → ℝ) := Q3.W_K K
abbrev AtomCone_K (K : ℝ) : Set (ℝ → ℝ) := Q3.AtomCone_K K
```

## Available Lemmas (already in repo)

You may use these as already proven in `Q3/Proofs/A1_density.lean`:

```lean
axiom HeatKernel_LipschitzOn (t : ℝ) (ht : t > 0) (R : ℝ) (hR : R > 0) :
  ∃ L > 0,
    ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
      |HeatKernel t x - HeatKernel t y| ≤ L * |x - y|

axiom FejerKernel_eq_zero_of_abs_ge {B x : ℝ} (hB : B > 0) (hx : |x| ≥ B) :
  FejerKernel B x = 0

axiom sum_atoms_in_cone (K : ℝ) (hK : K > 0) (s : Finset ℝ) (w : ℝ → ℝ)
  (hw : ∀ y ∈ s, 0 ≤ w y) (B : ℝ) (hB : B > 0) (t : ℝ) (ht : t > 0)
  (hτB : ∀ y ∈ s, |y| + B ≤ K)
  (h_sum_pos : ∑ y ∈ s, w y > 0)
  (hg_cont : Continuous (fun x => ∑ y ∈ s, w y * Atom B t y x))
  (hg_supp : Function.support (fun x => ∑ y ∈ s, w y * Atom B t y x) ⊆ Set.Icc (-K) K)
  (hg_even : Q3.IsEven (fun x => ∑ y ∈ s, w y * Atom B t y x))
  (hg_nonneg : ∀ x, 0 ≤ (fun x => ∑ y ∈ s, w y * Atom B t y x) x) :
  (fun x => ∑ y ∈ s, w y * Atom B t y x) ∈ AtomCone_K K
```

## Lemma 1: Hat interpolation (prove)

```lean
/-- Hat interpolation approximation: for continuous f, ||h - f||∞ ≤ ε
    using midpoint grid and FejerKernel hats. -/
lemma hat_interpolation_approx (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K))
    (hf_supp : Function.support f ⊆ Set.Icc (-K) K)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (δ : ℝ),
      n > 0 ∧ δ > 0 ∧
      (∀ i, τ i ∈ Set.Icc (-K) K) ∧
      (∀ i, |τ i| + δ ≤ K) ∧
      ∀ x ∈ Set.Icc (-K) K,
        |∑ i, f (τ i) * FejerKernel δ (x - τ i) - f x| < ε := by
  -- Use uniform continuity on compact [-K,K].
  -- Choose δ small and a midpoint grid τ_i = -K + (i+1/2)δ.
  -- Show only two hats are nonzero at each x; their weights sum to 1.
  -- Bound by modulus of continuity to get the ε-approximation.
  sorry
```

## Lemma 2: A1 density (prove using Lemma 1)

```lean
/-- A1 Density Theorem: Fejer×heat atoms are dense in W_K. -/
theorem A1_density_WK_thm (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0,
      ∃ g ∈ AtomCone_K K,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε := by
  -- Outline:
  -- 1) From Φ ∈ W_K, get continuity + support + even + nonneg.
  -- 2) Apply hat_interpolation_approx to get (n, τ, δ) and h(x) = Σ f(τ_i) Λ_δ(x-τ_i).
  -- 3) Fix any t > 0 (e.g. t = 1). Use HeatKernel_LipschitzOn on [-K,K].
  -- 4) Define g(x) = Σ f(τ_i) * Atom δ t τ_i x / HeatKernel t 0.
  --    Then g is a finite nonnegative sum of atoms with |τ_i|+δ ≤ K.
  -- 5) Use Lipschitz bound to show |g - h| < ε/2 on Icc.
  -- 6) Combine with Lemma 1 (|h - f| < ε/2) via triangle inequality.
  -- 7) Use sum_atoms_in_cone to show g ∈ AtomCone_K K (continuity, support, evenness, nonneg).
  sorry
```

## Notes / Hints

- You may introduce helper lemmas for: partition-of-unity of hats, two-hat support,
  or bounding `∑ i FejerKernel δ (x - τ i)` on `[-K,K]`.
- Keep the proof Lean-accepted (no `sorry`, no `exact?`).
- The hat interpolation should be midpoint-grid based (strict interior, margin condition).
