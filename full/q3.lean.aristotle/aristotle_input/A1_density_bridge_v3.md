# A1 Density Bridge (Final Assembly)

Goal: finish the *final assembly* proof of A1 density using already‑proved helper lemmas.
No new analytic lemmas; only combine them.

## Lean Context

```lean
import Mathlib
import Q3.Axioms

open scoped BigOperators Real Classical Pointwise
open MeasureTheory

noncomputable def real_convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (x - y)

-- Use Q3 definitions for kernels/atoms
noncomputable def HeatKernel (t : ℝ) (x : ℝ) : ℝ := Q3.heat_kernel_A1 t x
noncomputable def FejerHeatKernel (B t : ℝ) (x : ℝ) : ℝ :=
  Q3.Fejer_kernel B x * Q3.heat_kernel_A1 t x
noncomputable def Atom (B t τ : ℝ) (x : ℝ) : ℝ := Q3.Fejer_heat_atom B t τ x

-- Helper lemmas already proven in Q3/Proofs/A1_density.lean
axiom exists_compact_extension (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
  (hΦ : ContinuousOn Φ (Set.Icc (-K) K)) :
  ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧
    ∀ x ∈ Set.Icc (-K) K, Ψ x = Φ x

axiom FejerHeatKernel_approx_identity_uniform (B : ℝ) (hB : B > 0)
  (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
  (ε : ℝ) (hε : ε > 0) :
  ∃ t₀ > 0, ∀ t ∈ Set.Ioo 0 t₀, ∀ x,
    |real_convolution f (FejerHeatKernel B t) x - f x| < ε

axiom convolution_approx_by_sum_fejer (K : ℝ) (hK : K > 0) (B : ℝ) (hB : B > 0)
  (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Set.Icc (-K) K))
  (hf_supp : Function.support f ⊆ Set.Icc (-K) K)
  (hf_nonneg : ∀ x, 0 ≤ f x) (t : ℝ) (ht : t > 0)
  (ε : ℝ) (hε : ε > 0) :
  ∃ (s : Finset ℝ) (w : ℝ → ℝ),
    (∀ y ∈ s, w y ≥ 0) ∧ (∀ y ∈ s, y ∈ Set.Icc (-K) K) ∧
    ∀ x ∈ Set.Icc (-K) K,
      |real_convolution f (FejerHeatKernel B t) x - ∑ y ∈ s, w y * FejerHeatKernel B t (x - y)| < ε

axiom sum_atoms_in_cone (K : ℝ) (hK : K > 0) (s : Finset ℝ) (w : ℝ → ℝ)
  (hw : ∀ y ∈ s, 0 ≤ w y) (B : ℝ) (hB : B > 0) (hBK : B ≤ K)
  (t : ℝ) (ht : t > 0) (hs : ∀ y ∈ s, y ∈ Set.Icc (-K) K)
  (h_sum_pos : ∑ y ∈ s, w y > 0)
  (hg_cont : ContinuousOn (fun x => ∑ y ∈ s, w y * Atom B t y x) (Set.Icc (-K) K))
  (hg_supp : Function.support (fun x => ∑ y ∈ s, w y * Atom B t y x) ⊆ Set.Icc (-K) K)
  (hg_even : Q3.IsEven (fun x => ∑ y ∈ s, w y * Atom B t y x))
  (hg_nonneg : ∀ x, 0 ≤ (fun x => ∑ y ∈ s, w y * Atom B t y x) x) :
  (fun x => ∑ y ∈ s, w y * Atom B t y x) ∈ Q3.AtomCone_K K
```

## Target Theorem (prove this)

```lean
theorem A1_density_WK_thm (K : ℝ) (hK : K > 0) :
  ∀ Φ ∈ Q3.W_K K, ∀ ε > 0,
    ∃ g ∈ Q3.AtomCone_K K,
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε
```

## Proof Outline (high level)

1. From `Φ ∈ W_K K`, extract continuity on `Icc`, support ⊆ `Icc`, evenness, nonneg.
2. Use `exists_compact_extension` to get `Ψ` continuous on ℝ with compact support and `Ψ=Φ` on `Icc`.
3. Fix `B := K` (so `B ≤ K`). Use `FejerHeatKernel_approx_identity_uniform` with `ε/3` to choose `t>0` so convolution with `FejerHeatKernel B t` approximates `Ψ` uniformly.
4. Use `convolution_approx_by_sum_fejer` with `ε/3` to approximate that convolution by a finite sum over `s` with weights `w ≥ 0`.
5. Let `g(x) = ∑ y ∈ s, w y * (FejerHeatKernel B t (x - y) + FejerHeatKernel B t (x + y))`. Then `g = ∑ y ∈ s, w y * Atom B t y x`.
6. Show `g ∈ AtomCone_K K` using `sum_atoms_in_cone` (continuity, support, evenness, nonneg are straightforward for sums of atoms; use `B ≤ K`).
7. Combine the `ε/3` bounds (triangle inequality) to obtain the final `sSup` bound on `Icc`.

Important: keep the proof in Lean, no `sorry`/`exact?`.
