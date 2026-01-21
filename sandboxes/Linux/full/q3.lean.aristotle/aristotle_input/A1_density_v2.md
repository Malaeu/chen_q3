# A1' Density Theorem (with definitions)

## Lean 4 Definitions

```lean
import Mathlib

noncomputable def FejerKernel (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

noncomputable def HeatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1:ℝ)/2) * Real.exp (-x^2 / (4 * t))

def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | ContinuousOn Φ (Set.Icc (-K) K) ∧
       Function.support Φ ⊆ Set.Icc (-K) K ∧
       Even Φ ∧
       ∀ x, 0 ≤ Φ x}

noncomputable def Atom (B t τ : ℝ) (x : ℝ) : ℝ :=
  FejerKernel B (x - τ) * HeatKernel t (x - τ) +
  FejerKernel B (x + τ) * HeatKernel t (x + τ)

def AtomSet (K : ℝ) : Set (ℝ → ℝ) :=
  {g | ∃ B > 0, ∃ t > 0, ∃ τ ∈ Set.Icc (-K) K, g = Atom B t τ}

def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  Convex.toCone (convexHull ℝ (AtomSet K)) (convex_convexHull ℝ (AtomSet K))

def diff_set (Φ : ℝ → ℝ) (g : ℝ → ℝ) (K : ℝ) : Set ℝ :=
  (fun x ↦ |Φ x - g x|) '' Set.Icc (-K) K

def IsDenseInWK (K : ℝ) : Prop :=
  ∀ Φ ∈ W_K K, ∀ ε > 0, ∃ g ∈ AtomCone_K K, sSup (diff_set Φ g K) < ε

noncomputable def real_convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, f t * g (x - t)
```

## Theorem to Prove

```lean
theorem A1_density_WK (K : ℝ) (hK : K > 0) : IsDenseInWK K
```

## Proof Strategy

The proof has 4 steps:

**Step 1 (Mollification):**
- Given f ∈ W_K, convolve with HeatKernel t
- Heat kernel is positive approximate identity
- For small t: ‖f * ρ_t - f‖_∞ < ε/3

**Step 2 (Riemann Sums):**
- Approximate mollified function by positive Riemann sums
- g_R(ξ) = Σ_j g(τ_j) · ρ_t(ξ - τ_j) · Δτ
- For small mesh: ‖g_R - g‖_∞ < ε/3

**Step 3 (Fejér Truncation):**
- Replace ρ_t with Λ_B · ρ_t (Fejér truncated)
- |Λ_B(x) - 1| ≤ |x|/B for |x| ≤ B
- For large B: ‖h - g_R‖_∞ < ε/3

**Step 4 (Triangle Inequality):**
- h ∈ AtomCone_K by construction
- ‖h - f‖_∞ < ε by triangle inequality

## Key Lemmas

1. FejerKernel_nonneg: ∀ B x, 0 ≤ FejerKernel B x
   (Already proven: le_max_left 0 _)

2. HeatKernel_nonneg: ∀ t > 0, ∀ x, 0 ≤ HeatKernel t x
   (Proof: exp is nonneg, power of positive is positive)

3. HeatKernel_approx_identity: Heat convolution converges uniformly on compacts

4. FejerKernel_approx_one: For large B, Λ_B ≈ 1 on compacts
