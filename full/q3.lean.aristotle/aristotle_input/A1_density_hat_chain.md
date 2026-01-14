# A1 Density via Hat-Chain (Lemma 6.4)

## §0. Theorem Title and Status
- **Statement:** For any Φ ∈ W_K and ε > 0, there exists g ∈ AtomCone_K with ||Φ - g||∞ < ε.
- **Status:** Standard approximation theory using hat interpolation.

## §1. Formal Statement (Lean 4)

### Part 1: Boundary Vanishing Lemma

```lean
/-- Functions in W_K vanish at boundaries due to global continuity and support condition. -/
lemma W_K_boundary_vanish (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ) (hΦ : Φ ∈ W_K K) :
    Φ (-K) = 0 ∧ Φ K = 0
```

### Part 2: Main Theorem (Hat-Chain Version)

```lean
/-- A1 Density: AtomCone_K is dense in W_K via hat interpolation. -/
theorem A1_density_WK_hat (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0,
      ∃ g ∈ AtomCone_K K,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε
```

## §2. Definitions and Notation

From Q3/Proofs/A1_density.lean:

```lean
-- W_K: test function space
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Continuous Φ ∧
       Function.support Φ ⊆ Set.Icc (-K) K ∧
       IsEven Φ ∧
       IsNonneg Φ}

-- Fejér kernel (hat function)
noncomputable def FejerKernel (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

-- AtomCone_K: cone of Fejér×heat atoms
-- (exact definition in Q3/Proofs/A1_density.lean)
```

## §3. Dependencies

| Fact | Source | Status |
|------|--------|--------|
| hat_interpolation_approx | Q3/Proofs/HatInterpolation.lean | PROVEN |
| Function.support definition | Mathlib | {x : f x ≠ 0} |
| Continuous limits | Mathlib | Standard |
| FejerKernel properties | Q3/Proofs/A1_density.lean | PROVEN |

## §4. Proof Plan

### Part 1: W_K_boundary_vanish
1. Extract Φ continuous (globally) and support Φ ⊆ [-K, K]
2. support ⊆ [-K, K] implies Φ = 0 outside [-K, K]
3. For boundary -K: Φ = 0 on (-∞, -K), so by left-continuity Φ(-K) = 0
4. For boundary K: Φ = 0 on (K, +∞), so by right-continuity Φ(K) = 0

### Part 2: A1_density_WK_hat
1. Given Φ ∈ W_K, extract continuity, support, evenness, nonnegativity
2. Apply W_K_boundary_vanish to get Φ(-K) = 0 ∧ Φ K = 0
3. Apply hat_interpolation_approx to Φ with ε
4. Get n, τ, δ with approximation bound and margin condition
5. Build g := ∑ᵢ Φ(τᵢ) * FejerKernel δ (x - τᵢ)
6. Show g ∈ AtomCone_K (nonneg weights, margin condition, etc.)
7. Return ⟨g, hg_mem, h_approx⟩

## §5. Key Lemmas

**Lemma 5.1 (Boundary vanishing).** For continuous f : ℝ → ℝ with support f ⊆ S (closed set):
- If x₀ is a boundary point of S and f = 0 on one side of x₀
- Then by continuity, f(x₀) = lim f = 0

**Lemma 5.2 (Support outside implies zero).** For f : ℝ → ℝ:
- Function.support f ⊆ [-K, K] means {x : f x ≠ 0} ⊆ [-K, K]
- Equivalently: x ∉ [-K, K] → f x = 0
- So f = 0 on (-∞, -K) and f = 0 on (K, +∞)

**Lemma 5.3 (hat_interpolation_approx already proven).** Given:
- f continuous on [-K, K]
- f nonnegative
- f(-K) = 0 ∧ f(K) = 0
Then exists hat interpolation with ||h - f||∞ < ε.

## §6. Main Proof Sketch

### W_K_boundary_vanish:
```
1. Let hΦ_cont : Continuous Φ, hΦ_supp : support Φ ⊆ [-K, K]
2. For x < -K: x ∉ [-K, K], so x ∉ support Φ, so Φ x = 0
3. Sequence xₙ → (-K)⁻ with xₙ < -K: Φ(xₙ) = 0 for all n
4. By continuity: Φ(-K) = lim Φ(xₙ) = 0
5. Similarly for K (using x > K)
```

### A1_density_WK_hat:
```
1. From Φ ∈ W_K, extract: hΦ_cont, hΦ_supp, hΦ_even, hΦ_nonneg
2. hΦ_boundary := W_K_boundary_vanish K hK Φ hΦ
3. Apply hat_interpolation_approx:
   obtain ⟨n, τ, δ, hn, hδ, hτ_in, hτ_margin, h_approx, h_nonneg⟩
4. Define g x := ∑ i, Φ (τ i) * FejerKernel δ (x - τ i)
5. Show g ∈ AtomCone_K:
   - Weights cᵢ := Φ(τᵢ) are nonneg (from hΦ_nonneg)
   - Each τᵢ satisfies |τᵢ| + δ ≤ K (from hτ_margin)
   - Sum is continuous, even, nonneg, support in [-K,K]
6. h_approx gives ||Φ - g||∞ < ε on [-K, K]
```

## §7. Audit-Edge Check

| Issue | Location | Verification |
|-------|----------|--------------|
| Hidden quantifiers | §1 | All explicit: ∀ Φ ∈ W_K, ∀ ε > 0 |
| Boundary continuity | §5.1 | Global continuity of Φ ensures limits |
| Support definition | §5.2 | Mathlib: {x : f x ≠ 0}, NOT closure |
| hat_interpolation input | §6 | Φ(-K)=0, Φ(K)=0 from boundary lemma |
| AtomCone membership | §6 step 5 | Need to verify all conditions |

## §8. References

- Q3/Proofs/A1_density.lean — existing definitions
- Q3/Proofs/HatInterpolation.lean — hat_interpolation_approx (PROVEN)
- A1prime.tex, Lemma 6.4 (Fixed-t₀ cone density)
- Mathlib: Function.support, Continuous.tendsto

## §9. Integration Notes

This theorem should REPLACE the current A1_density_WK_thm proof in A1_density.lean.
The current proof uses convolution + Riemann sum which has architectural issues (B vs B', asymmetric sums).
The hat-chain approach is cleaner and matches Lemma 6.4 from the paper.
