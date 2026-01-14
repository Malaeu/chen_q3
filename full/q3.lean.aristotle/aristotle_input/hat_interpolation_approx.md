# Hat Interpolation Approximation (Lemma for A1_density)

## §0. Theorem Title and Status
- **Statement:** For any uniformly continuous function f on [-K, K] and ε > 0, there exists a hat interpolation h(ξ) = Σⱼ f(τⱼ) Λ_δ(ξ - τⱼ) with ||h - f||∞ < ε.
- **Status:** Standard approximation theory (piecewise linear interpolation).

## §1. Formal Statement (Lean 4)

```lean
lemma hat_interpolation_approx (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K)) (hf_nonneg : ∀ x ∈ Set.Icc (-K) K, 0 ≤ f x)
    (hf_boundary : f (-K) = 0 ∧ f K = 0)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (δ : ℝ),
      n > 0 ∧ δ > 0 ∧
      (∀ i, τ i ∈ Set.Ioo (-K) K) ∧   -- grid points strictly inside
      (∀ i, |τ i| + δ ≤ K) ∧           -- margin condition for atoms
      (∀ x ∈ Set.Icc (-K) K,
        |∑ i, f (τ i) * FejerKernel δ (x - τ i) - f x| < ε) ∧
      (∀ x ∈ Set.Icc (-K) K,
        0 ≤ ∑ i, f (τ i) * FejerKernel δ (x - τ i))
```

## §2. Definitions and Notation

- **K > 0:** Half-width of the interval [-K, K].
- **FejerKernel δ x := max(1 - |x|/δ, 0):** Tent (hat) function with width δ.
- **τⱼ:** Grid points in (-K, K) with spacing approximately δ.
- **ContinuousOn f (Set.Icc (-K) K):** f continuous on closed interval.
- **UniformContinuousOn:** On compact set, continuous implies uniformly continuous.
- **Modulus of continuity ω_f(δ):** sup{|f(x) - f(y)| : |x - y| ≤ δ}.

## §3. Dependencies

| Fact | Source | Status |
|------|--------|--------|
| Compact → uniformly continuous | Mathlib `isCompact_Icc.uniformContinuousOn_of_continuous` | Standard |
| FejerKernel ≥ 0 | Q3/Proofs/A1_density.lean | Proven |
| FejerKernel ≤ 1 | Q3/Proofs/A1_density.lean | Proven |
| FejerKernel = 0 outside [-δ, δ] | Q3/Proofs/A1_density.lean `FejerKernel_eq_zero_of_abs_ge` | Proven |
| FejerKernel(0) = 1 | Direct from definition | Trivial |

## §4. Proof Plan

1. Use uniform continuity to get δ₀ such that |x - y| < δ₀ ⟹ |f(x) - f(y)| < ε/2.
2. Choose δ = min(δ₀, K)/2 and n = ⌈2K/δ⌉.
3. Define grid τᵢ = -K + (i + 1/2) · (2K/n) for i = 0, ..., n-1.
4. Use hf_boundary to handle the boundary (hats vanish at ±K).
5. Show hat functions form approximate partition of unity on [-K, K].
5. At each x, at most 2 hats are nonzero; weighted average approximates f(x).
6. Nonnegativity: f ≥ 0 and FejerKernel ≥ 0 ⟹ sum ≥ 0.

## §5. Key Lemmas

**Lemma 5.1 (Partition property).** For grid points τᵢ with spacing δ:
- At most 2 terms FejerKernel δ (x - τᵢ) are nonzero for any x.
- Sum of weights ≤ 2 (actually = 1 at grid midpoints).

**Lemma 5.2 (Approximation).** If |x - τⱼ| ≤ δ for some j, then:
|Σᵢ f(τᵢ) · Λ_δ(x - τᵢ) - f(x)| ≤ Σᵢ |f(τᵢ) - f(x)| · Λ_δ(x - τᵢ)
                                 ≤ ω_f(δ) · Σᵢ Λ_δ(x - τᵢ)
                                 ≤ 2 · ω_f(δ)

**Lemma 5.3 (Margin).** Grid points τᵢ ∈ (-K, K) with |τᵢ| + δ ≤ K when δ ≤ K/2.

## §6. Main Proof Sketch

1. From hf_cont and compact [-K, K], get UniformContinuousOn.
2. From Metric.uniformContinuousOn_iff, get δ₀ > 0 with |x - y| < δ₀ ⟹ |f(x) - f(y)| < ε/2.
3. Set δ := min(δ₀, K) / 2, so δ > 0 and δ ≤ K/2.
4. Set n := Nat.ceil (2 * K / δ) + 1, ensuring enough grid points.
5. Define τᵢ := -K + δ/2 + i · δ for i ∈ Fin n.
6. Verify: all τᵢ ∈ (-K, K) and |τᵢ| + δ ≤ K (margin condition).
7. For any x ∈ [-K, K], at most 2 tent functions overlap.
8. Weighted sum approximates f(x) within ε/2 · 2 = ε.
9. Nonnegativity follows from f ≥ 0 and Λ_δ ≥ 0.

## §7. Audit-Edge Check

| Issue | Location | Verification |
|-------|----------|--------------|
| Hidden quantifiers | §6 | All explicit: for all x ∈ [-K, K] |
| Boundary cases | §6 step 4 | hf_boundary handles f(±K)=0 |
| Division by zero | §2 | δ > 0 ensured |
| Partition unity | §5.1 | At most 2 overlaps, sum ≤ 2 |
| Nonnegativity | §6 step 9 | Product of nonneg terms |

## §8. References

- A1prime.tex, Lemma 6.4 (Fixed-t₀ cone density), lines 81-104.
- Standard approximation theory: piecewise linear interpolation.
- Mathlib: `isCompact_Icc.uniformContinuousOn_of_continuous`.
