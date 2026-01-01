# Minor Arcs via Vinogradov Method

## Description

Attack the minor arcs bound using classical Vinogradov exponential sum estimates.

**Key Idea:** On minor arcs, α is NOT close to any rational a/q with small q. Therefore the exponential sum F(α) exhibits cancellation due to equidistribution of {nα} mod 1.

## Definitions

```
-- Dirichlet character mod 4
def χ₄ (n : ℤ) : ℤ :=
  if n % 2 = 0 then 0
  else if n % 4 = 1 then 1
  else -1

-- Exponential e(x) = exp(2πix)
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

-- Von Mangoldt
noncomputable def Λ : ℕ → ℝ := ArithmeticFunction.vonMangoldt

-- The weighted exponential sum
noncomputable def F (X : ℝ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range ⌊X⌋₊, (Λ n : ℂ) * (χ₄ n : ℂ) * e (n * α)

-- Dirichlet approximation: for any α, ∃ a/q with |α - a/q| < 1/(qQ)
def has_dirichlet_approx (α : ℝ) (Q : ℝ) (a q : ℕ) : Prop :=
  q ≤ Q ∧ Nat.Coprime a q ∧ |α - a/q| < 1/(q * Q)

-- Minor arc condition: α not close to simple rationals
def is_minor (α : ℝ) (X : ℝ) : Prop :=
  ∀ a q : ℕ, q ≤ Real.log X → |α - a/q| > 1/(q * X)
```

## Key Lemmas

```
-- Vinogradov's lemma: exponential sums over primes
-- If α = a/q + β with (a,q)=1 and |β| < 1/(qQ), then
-- |Σ_{p≤X} log(p) e(pα)| ≪ X(log X)^4 (q^{-1/2} + X^{-1/2} + q^{1/2}X^{-1})

lemma vinogradov_prime_sum (X : ℝ) (α : ℝ) (a q : ℕ) (β : ℝ)
    (hX : X > 100)
    (hq : q ≥ 1)
    (hcop : Nat.Coprime a q)
    (happrox : α = a/q + β)
    (hbeta : |β| < 1/(q * X)) :
  ‖∑ p in (Finset.filter Nat.Prime (Finset.range ⌊X⌋₊)), 
    (Real.log p : ℂ) * e (p * α)‖ 
  ≤ X * (Real.log X)^4 * (1/Real.sqrt q + 1/Real.sqrt X + Real.sqrt q / X) := by
  sorry

-- On minor arcs, q must be large (≥ log X)
lemma minor_arc_large_q (X : ℝ) (α : ℝ) (hX : X > 100) (h_minor : is_minor α X) :
  ∀ a q : ℕ, has_dirichlet_approx α X a q → q > Real.log X := by
  sorry

-- Combine: on minor arcs, F(α) is small
theorem F_minor_bound (X : ℝ) (α : ℝ) (hX : X > 100) (h_minor : is_minor α X) :
  ‖F X α‖ ≤ X / (Real.log X)^2 := by
  -- Use vinogradov_prime_sum with the Dirichlet approximation
  -- Since q > log X on minor arcs, get cancellation
  sorry
```

## Main Result

```
-- The χ₄ weighting doesn't hurt (bounded by 1)
lemma chi4_bounded (n : ℕ) : |χ₄ n| ≤ 1 := by
  sorry

-- F with χ₄ also bounded on minor arcs
theorem F_chi4_minor_bound (X : ℝ) (α : ℝ) (hX : X > 100) (h_minor : is_minor α X) :
  ‖F X α‖ ≤ X / (Real.log X)^2 := by
  sorry

-- Integrate over minor arcs
theorem minor_arcs_integral_bound (X : ℝ) (hX : X > 100) :
  ∫ α in {α : ℝ | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, ‖F X α‖^2 
  ≤ X^2 / (Real.log X)^4 := by
  -- |F|² ≤ (X/log²X)² on minor arcs, measure ≤ 1
  sorry

-- The Fourier coefficient bound
theorem minor_arcs_fourier_bound (X : ℝ) (hX : X > 100) :
  |∫ α in {α : ℝ | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, 
    ‖F X α‖^2 * (e (-2 * α)).re| 
  ≤ X^2 / (Real.log X)^4 := by
  -- Bound by the integral of |F|²
  sorry
```

## Target

```
theorem minor_arcs_bound_vinogradov (X : ℝ) (hX : X > 100) :
  |∫ α in {α : ℝ | is_minor α X ∧ 0 ≤ α ∧ α ≤ 1}, 
    ‖F X α‖^2 * (e (-2 * α)).re| 
  ≤ X / Real.log X := by
  -- This is weaker than X²/log⁴X, so follows from above
  sorry
```

## Hints

1. **Dirichlet approximation theorem** is in Mathlib: every real has good rational approximations.

2. **Weyl differencing:** Sum of e(nα) can be bounded by iterating differences.

3. **Type I/II sums:** Decompose the sum over primes using Vaughan's identity.

4. The key insight: minor arcs have |α - a/q| > 1/(q·X) for all q ≤ log X, forcing q to be large in any good approximation, which gives cancellation.
