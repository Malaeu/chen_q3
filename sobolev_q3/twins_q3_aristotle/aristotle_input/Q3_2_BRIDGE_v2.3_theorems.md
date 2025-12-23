# Q3-2 Bridge: Theorems

## Context
The attached Lean file contains complete definitions for the Q3-2 Bridge formalization.
All definitions compile with 0 sorry.

## Task
Add the following theorems to prove Q3_2 ⇒ Q3_1:

### Theorem 1: Operator Norm Bound Implies Sum Bound
```
theorem Q3_2_implies_bounded_bilinear :
  ∀ (t K Q : ℕ → ℝ), BridgeRepV2 t K Q → Q3_2 →
    ∃ (C : ℝ) (delta : ℝ) (N0 : ℕ), delta > 0 ∧
    ∀ N ≥ N0, ∀ (alpha : ℝ), (alpha : UnitAddCircle) ∈ MinorArcs N (Q N) →
      ‖dotProduct (star (u N)) ((B N (t N) (K N) alpha) ^ (J N) *ᵥ (v N))‖
        ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 - delta)
```

### Theorem 2: Main Implication Q3_2 ⇒ Q3_1
```
theorem Q3_2_implies_Q3_1 :
  ∀ (t K Q : ℕ → ℝ), BridgeRepV2 t K Q → Q3_2 → Q3_1 Q
```

### Theorem 3: Spectral Gap Geometric Decay
```
theorem spectral_gap_geometric_decay :
  ∀ (rho : ℝ) (hrho : rho < 1) (J : ℕ),
    ∀ (B : Matrix n n ℂ), ‖B‖ ≤ rho → ‖B ^ J‖ ≤ rho ^ J
```

### Theorem 4: Bilinear Form Bound
```
theorem bilinear_bound :
  ∀ (u v : n → ℂ) (M : Matrix n n ℂ),
    ‖dotProduct (star u) (M *ᵥ v)‖ ≤ ‖M‖ * l2Norm u * l2Norm v
```

## Proof Strategy
1. Use `spectral_gap_geometric_decay` to bound ‖B^J‖ ≤ ρ^J
2. Use `bilinear_bound` to get |⟨u, B^J v⟩| ≤ ρ^J · ‖u‖ · ‖v‖
3. With J ≥ c₀ log N and ρ < 1: ρ^J ≤ N^(-c₀ log(1/ρ))
4. Combined with ‖u‖·‖v‖ ≤ C√N gives |S| ≤ C' N^(1/2 - δ)

## Notes
- Use Matrix.norm for operator norm
- Use Mathlib's Matrix.PosSemidef properties
- The key insight is ρ^(c₀ log N) = N^(-c₀ log(1/ρ)) = N^(-δ) where δ = c₀ log(1/ρ) > 0
