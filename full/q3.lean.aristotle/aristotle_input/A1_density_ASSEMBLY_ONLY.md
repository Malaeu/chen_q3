# A1 Density — ASSEMBLY ONLY

## CRITICAL: ONLY ONE THEOREM NEEDED!

All supporting lemmas are ALREADY PROVEN in the context file. DO NOT reprove them!

## YOUR ONLY TASK

Prove this ONE theorem using the lemmas from the context file:

```lean
theorem A1_density_WK (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0, ∃ g ∈ AtomCone_K K, sSup (diff_set Φ g K) < ε := by
  intro Φ hΦ ε hε
  -- Step 1: Extend Φ to Ψ with compact support (use exists_even_compact_extension)
  obtain ⟨Ψ, hΨ_cont, hΨ_supp, hΨ_even, hΨ_eq⟩ := exists_even_compact_extension K hK Φ hΦ.1 ⟨_, hΦ.2.1⟩
  -- Step 2: Choose t for heat kernel approximation (use HeatKernel_approx_identity_uniform)
  obtain ⟨t₀, ht₀_pos, ht₀_approx⟩ := HeatKernel_approx_identity_uniform Ψ hΨ_cont hΨ_supp (ε/3) (by linarith)
  -- Step 3: Approximate convolution by finite sum (use convolution_approx_by_sum)
  -- Step 4: Replace heat sum with atom sum (use fejer_sum_approx)
  -- Step 5: The atom sum is in the cone (use sum_atoms_in_cone)
  -- Step 6: Triangle inequality to combine errors
  sorry
```

## Available Lemmas (in context file)

1. `HeatKernel_integral` — ∫ HeatKernel t x = 1
2. `HeatKernel_mass_concentration` — mass concentrates at 0
3. `HeatKernel_nonneg` — HeatKernel ≥ 0
4. `FejerKernel_bounds` — 0 ≤ Fejér ≤ 1
5. `exists_compact_extension` — Tietze extension
6. `HeatKernel_approx_identity_uniform` — convolution approximation
7. `sum_atoms_in_cone` — weighted sums in cone
8. `exists_even_compact_extension` — even extension
9. `HeatKernel_even` — heat kernel is even
10. `even_convolution` — convolution preserves evenness

## Proof Strategy

The proof combines these lemmas via triangle inequality:

```
|Φ(x) - g(x)| ≤ |Φ(x) - (Ψ*H)(x)| + |(Ψ*H)(x) - sum| + |sum - g(x)|
             ≤      ε/3           +      ε/3        +     ε/3
             = ε
```

Where:
- First term: HeatKernel_approx_identity_uniform
- Second term: Riemann sum approximation (may need additional lemma)
- Third term: fejer_sum_approx + sum_atoms_in_cone

## Expected Output

ONLY the theorem `A1_density_WK` with a complete proof (no sorry).

DO NOT reprove any lemmas — they are in the context file!
