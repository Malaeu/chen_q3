# A1' Density Theorem - Final Task

## Goal
Prove that AtomCone_K is dense in W_K in the uniform norm.

## Definitions (use these exactly)

```lean
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

## Available Lemmas (already proven, use freely)

### Heat Kernel Properties

```lean
lemma HeatKernel_integral (t : ℝ) (ht : t > 0) : ∫ x, HeatKernel t x = 1

lemma HeatKernel_mass_concentration (δ : ℝ) (hδ : δ > 0) :
  Filter.Tendsto (fun t => ∫ x in {y | |y| > δ}, HeatKernel t x)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

lemma HeatKernel_nonneg (t : ℝ) (ht : t > 0) (x : ℝ) : 0 ≤ HeatKernel t x
```

### Fejer Kernel Properties

```lean
lemma FejerKernel_bounds (B : ℝ) (hB : B > 0) (x : ℝ) :
  0 ≤ FejerKernel B x ∧ FejerKernel B x ≤ 1

lemma FejerKernel_approx_one (K : ℝ) (B : ℝ) (hB : B > K) (x : ℝ) (hx : x ∈ Set.Icc (-K) K) :
  1 - K / B ≤ FejerKernel B x
```

### Extension and Approximation

```lean
lemma exists_compact_extension (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hΦ : ContinuousOn Φ (Set.Icc (-K) K)) :
  ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ x ∈ Set.Icc (-K) K, Ψ x = Φ x

lemma HeatKernel_approx_identity_uniform (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_supp : HasCompactSupport f) (ε : ℝ) (hε : ε > 0) :
  ∃ t₀ > 0, ∀ t ∈ Set.Ioo 0 t₀, ∀ x, |real_convolution f (HeatKernel t) x - f x| < ε
```

### Riemann Sum Approximation

```lean
lemma uniform_riemann_sum (a b : ℝ) (hab : a < b) (X : Set ℝ) (hX : IsCompact X)
    (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) (X ×ˢ Set.Icc a b))
    (ε : ℝ) (hε : ε > 0) :
  ∃ (s : Finset ℝ) (w : ℝ → ℝ), (∀ y ∈ s, w y > 0) ∧ (∀ y ∈ s, y ∈ Set.Icc a b) ∧
  ∀ x ∈ X, |(∫ y in Set.Icc a b, F x y) - ∑ y ∈ s, w y * F x y| < ε

lemma convolution_approx_by_sum (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K))
    (hf_supp : Function.support f ⊆ Set.Icc (-K) K)
    (hf_nonneg : ∀ x, 0 ≤ f x) (t : ℝ) (ht : t > 0) (ε : ℝ) (hε : ε > 0) :
  ∃ (s : Finset ℝ) (w : ℝ → ℝ), (∀ y ∈ s, w y ≥ 0) ∧ (∀ y ∈ s, y ∈ Set.Icc (-K) K) ∧
  ∀ x ∈ Set.Icc (-K) K, |real_convolution f (HeatKernel t) x - ∑ y ∈ s, w y * HeatKernel t (x - y)| < ε
```

### Fejer Sum and Atom Cone

```lean
lemma fejer_sum_approx (K : ℝ) (hK : K > 0) (t : ℝ) (ht : t > 0) (s : Finset ℝ)
    (w : ℝ → ℝ) (hw_nonneg : ∀ y ∈ s, w y ≥ 0) (hs_subset : ∀ y ∈ s, y ∈ Set.Icc (-K) K)
    (ε : ℝ) (hε : ε > 0) :
  ∃ B > 0, ∀ x ∈ Set.Icc (-K) K,
  |∑ y ∈ s, w y * Atom B t y x - (∑ y ∈ s, w y * HeatKernel t (x - y) +
    ∑ y ∈ s, w y * HeatKernel t (x + y))| < ε

lemma sum_atoms_in_cone (K : ℝ) (s : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ y ∈ s, 0 ≤ w y)
    (B : ℝ) (hB : B > 0) (t : ℝ) (ht : t > 0) (hs : ∀ y ∈ s, y ∈ Set.Icc (-K) K)
    (h_sum_pos : ∑ y ∈ s, w y > 0) :
  (fun x => ∑ y ∈ s, w y * Atom B t y x) ∈ AtomCone_K K

lemma even_convolution (f g : ℝ → ℝ) (hf : Even f) (hg : Even g) :
  Even (real_convolution f g)
```

## Main Theorem to Prove

```lean
theorem A1_density (K : ℝ) (hK : K > 0) : IsDenseInWK K
```

## Proof Sketch

The proof proceeds in several steps:

1. **Take any Φ ∈ W_K K and ε > 0**. We need to find g ∈ AtomCone_K K with sSup (diff_set Φ g K) < ε.

2. **Extend Φ to Ψ on ℝ** using `exists_compact_extension`. Since Φ is continuous on [-K, K], we get Ψ continuous with compact support, agreeing with Φ on [-K, K].

3. **Approximate Ψ by convolution with heat kernel**. By `HeatKernel_approx_identity_uniform`, for small enough t > 0:
   |real_convolution Ψ (HeatKernel t) x - Ψ x| < ε/3 for all x.

4. **Approximate the convolution by a Riemann sum**. By `convolution_approx_by_sum`, we can find a finite set s and weights w such that:
   |real_convolution Ψ (HeatKernel t) x - ∑ y ∈ s, w y * HeatKernel t (x - y)| < ε/3.

5. **Approximate the heat kernel sum by atoms**. By `fejer_sum_approx`, for large enough B > 0:
   |∑ y ∈ s, w y * Atom B t y x - (heat kernel sum)| < ε/3.

6. **The atom sum is in AtomCone_K**. By `sum_atoms_in_cone`, g := ∑ y ∈ s, w y * Atom B t y ∈ AtomCone_K K (assuming positive total weight; handle the zero case separately).

7. **Triangle inequality**. Combining steps 3-5:
   |Φ x - g x| = |Ψ x - g x| ≤ |Ψ x - conv| + |conv - sum| + |sum - g| < ε.

8. **Conclude**. Since this holds for all x ∈ [-K, K], we have sSup (diff_set Φ g K) < ε.

## Notes

- The case when Φ = 0 can be handled separately (take g = 0 or any small atom).
- The evenness of Φ and atoms ensures g is also even.
- All the intermediate approximations preserve non-negativity.
