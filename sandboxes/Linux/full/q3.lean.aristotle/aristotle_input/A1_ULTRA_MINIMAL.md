# A1 Density — ULTRA MINIMAL

## ONLY ONE THING TO DO

All lemmas are proven. Just write ONE theorem using them:

```lean
theorem A1_density_WK (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0, ∃ g ∈ AtomCone_K K, sSup (diff_set Φ g K) < ε := by
  intro Φ hΦ ε hε
  -- Use exists_even_compact_extension to get Ψ
  -- Use HeatKernel_approx_identity_uniform for ε/3
  -- Use convolution_eq_Icc_of_compact_support + uniform_riemann_sum for ε/3
  -- Use fejer_sum_approx for ε/3
  -- Use sum_atoms_in_cone for cone membership
  -- Use sSup_lt_of_compact_image_lt with triangle inequality
  sorry
```

Use these EXACT lemmas from context:
- `exists_even_compact_extension`
- `HeatKernel_approx_identity_uniform`
- `convolution_eq_Icc_of_compact_support`
- `uniform_riemann_sum`
- `fejer_sum_approx`
- `sum_atoms_in_cone`
- `sSup_lt_of_compact_image_lt`

Output: ONLY the theorem, 30-50 lines max.
