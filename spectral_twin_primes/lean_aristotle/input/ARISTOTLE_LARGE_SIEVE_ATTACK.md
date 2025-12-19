# Minor Arcs via Large Sieve

## Description

Attack the minor arcs bound using the Large Sieve inequality.

**Key Idea:** The Large Sieve controls the sum of |F(α)|² over well-spaced points. Combined with smoothing, this bounds the integral over minor arcs.

## Definitions

```
-- Standard definitions
def χ₄ (n : ℤ) : ℤ :=
  if n % 2 = 0 then 0
  else if n % 4 = 1 then 1
  else -1

noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)
noncomputable def Λ : ℕ → ℝ := ArithmeticFunction.vonMangoldt

noncomputable def F (X : ℝ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range ⌊X⌋₊, (Λ n : ℂ) * (χ₄ n : ℂ) * e (n * α)

-- Well-spaced points: |αᵢ - αⱼ| ≥ δ for i ≠ j
def well_spaced (S : Finset ℝ) (δ : ℝ) : Prop :=
  ∀ α β ∈ S, α ≠ β → |α - β| ≥ δ
```

## Large Sieve Inequality

```
-- Classical Large Sieve (additive form)
-- For well-spaced {αᵣ} with spacing δ and any sequence (aₙ):
-- Σᵣ |Σₙ aₙ e(n αᵣ)|² ≤ (N + δ⁻¹) Σₙ |aₙ|²

theorem large_sieve_additive (N : ℕ) (S : Finset ℝ) (δ : ℝ) 
    (a : ℕ → ℂ) (hδ : δ > 0) (h_spaced : well_spaced S δ) :
  ∑ α in S, ‖∑ n in Finset.range N, a n * e (n * α)‖^2 
  ≤ (N + 1/δ) * ∑ n in Finset.range N, ‖a n‖^2 := by
  sorry

-- Integral version via smoothing
theorem large_sieve_integral (N : ℕ) (a : ℕ → ℂ) :
  ∫ α in Set.Icc 0 1, ‖∑ n in Finset.range N, a n * e (n * α)‖^2 
  = ∑ n in Finset.range N, ‖a n‖^2 := by
  -- This is Parseval/Plancherel
  sorry
```

## Application to F(α)

```
-- The coefficients of F
noncomputable def F_coeff (X : ℝ) (n : ℕ) : ℂ := (Λ n : ℂ) * (χ₄ n : ℂ)

-- Sum of squared coefficients
lemma F_coeff_L2 (X : ℝ) (hX : X > 0) :
  ∑ n in Finset.range ⌊X⌋₊, ‖F_coeff X n‖^2 ≤ 2 * X * Real.log X := by
  -- |Λ(n)|² ≤ log²n, sum over primes ~ X log X
  sorry

-- Parseval for F
theorem F_parseval (X : ℝ) (hX : X > 0) :
  ∫ α in Set.Icc 0 1, ‖F X α‖^2 ≤ 2 * X * Real.log X := by
  -- Direct from large_sieve_integral and F_coeff_L2
  sorry
```

## Minor Arcs Bound

```
-- Key: the Fourier coefficient with phase e(-2α)
-- ∫ |F(α)|² e(-2α) dα = T_χ₄(X) (exact identity)

-- On minor arcs, the oscillation of e(-2α) causes partial cancellation
-- relative to just |F(α)|²

lemma minor_oscillation_bound (X : ℝ) (hX : X > 100) :
  |∫ α in {α | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, ‖F X α‖^2 * (e (-2 * α)).re|
  ≤ ∫ α in {α | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, ‖F X α‖^2 := by
  -- |e(-2α).re| ≤ 1
  sorry

-- Major arcs capture most of the L² mass near peaks
-- But minor arcs still have ~ X log X total mass (by Parseval)

-- The KEY: e(-2α) oscillates on minor arcs and averages out
-- Unlike |F|² which is always positive

theorem minor_fourier_small (X : ℝ) (hX : X > 100) :
  |∫ α in {α | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, ‖F X α‖^2 * e (-2 * α)|
  ≤ X / Real.log X := by
  -- The oscillatory integral is smaller than the L² integral
  -- by a factor of log X due to cancellation
  sorry
```

## Alternative: Character Sum Large Sieve

```
-- Large sieve for Dirichlet characters
-- Σ_q Σ_χ(mod q) |Σ_n a_n χ(n)|² ≤ (N + Q²) Σ_n |a_n|²

theorem large_sieve_characters (N Q : ℕ) (a : ℕ → ℂ) :
  ∑ q in Finset.range Q, ∑ χ : DirichletCharacter ℂ q,
    ‖∑ n in Finset.range N, a n * χ n‖^2
  ≤ (N + Q^2) * ∑ n in Finset.range N, ‖a n‖^2 := by
  sorry

-- Apply to our sum with χ₄ fixed
-- This gives bounds on correlations with other characters
-- which control minor arcs via Poisson summation
```

## Target

```
theorem minor_arcs_bound_large_sieve (X : ℝ) (hX : X > 100) :
  |∫ α in {α | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, 
    ‖F X α‖^2 * (e (-2 * α)).re|
  ≤ X / Real.log X := by
  sorry
```

## Hints

1. **Parseval** is the key starting point: ∫|F|² = Σ|a_n|² ~ X log X

2. **Major arcs** contain the peaks where |F| ~ X. Their contribution to ∫|F|² is ~ X² · (1/X) = X.

3. **Minor arcs** have |F| ≪ X/log²X (from Vinogradov). So ∫_{minor}|F|² ≪ (X/log²X)² · 1 = X²/log⁴X.

4. **But we need the FOURIER coefficient**, not just L². The phase e(-2α) oscillates and causes cancellation.

5. The oscillatory integral ∫ f·e(-2α) is bounded by ‖f‖_1/‖e'‖ (integration by parts flavor).
