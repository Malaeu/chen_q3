# Periodization Lemma

## Goal

Prove the periodization lemma: the integral of P_A over [-1/2, 1/2] equals arch_term(Φ).

```lean
theorem periodization_lemma (B t : ℝ) (hB : B > 0) (ht : t > 0) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ = Q3.arch_term (Q3.fejer_heat_window B t)
```

## Key Definitions (Already in Project)

```lean
-- P_A is 2π times periodized g
P_A (B t θ : ℝ) : ℝ := 2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)

-- g = a · w (product of archimedean function and window)
g (B t ξ : ℝ) : ℝ := a ξ * w B t ξ

-- arch_term = ∫ a* · Φ = ∫ 2π·a · Φ over ℝ
Q3.arch_term (Φ : ℝ → ℝ) : ℝ := ∫ ξ : ℝ, Q3.a_star ξ * Φ ξ

-- a_star = 2π · a
Q3.a_star (ξ : ℝ) : ℝ := 2 * Real.pi * Q3.a ξ
```

## Available Lemmas (use these, don't reprove!)

```lean
-- g = a · fejer_heat_window
lemma g_eq_a_mul_window (B t ξ : ℝ) :
    g B t ξ = Q3.a ξ * Q3.fejer_heat_window B t ξ

-- P_A reduces to a finite sum (terms vanish beyond cutoff)
lemma tsum_eq_finite_sum_g (B t θ : ℝ) (hB : B > 0)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), g B t (θ + m) =
      ∑ m ∈ Finset.Icc (-(periodization_cutoff B : ℤ)) (periodization_cutoff B),
        g B t (θ + m)

-- g has compact support in [-B, B]
lemma g_support (B t ξ : ℝ) (hB : B > 0) (hξ : |ξ| > B) : g B t ξ = 0
```

## Proof Strategy

1. **Rewrite P_A as finite sum**: By `tsum_eq_finite_sum_g`, P_A is locally a finite sum.

2. **Integral of finite sum = sum of integrals**: Use `integral_finset_sum`.

3. **Change of variables**: Each `∫_{-1/2}^{1/2} g(θ+m) dθ = ∫_{m-1/2}^{m+1/2} g(ξ) dξ`.

4. **Sum of disjoint intervals = integral over ℝ**: The intervals `[m-1/2, m+1/2]` partition ℝ,
   and g has compact support in [-B, B], so the sum over m covers the support.

5. **Conclude**:
   ```
   ∫ P_A = 2π · ∫_ℝ g = 2π · ∫_ℝ a·Φ = ∫_ℝ (2π·a)·Φ = ∫_ℝ a*·Φ = arch_term(Φ)
   ```

## Mathlib Lemmas to Use

- `intervalIntegral.integral_comp_add_right` — change of variables θ ↦ θ + m
- `MeasureTheory.integral_finset_sum` — integral of finite sum
- `integral_Ioc_eq_integral_Ioo_of_le` — interval endpoint technicalities
- `MeasureTheory.integral_eq_integral_Icc_of_support_subset` — support argument

## Key Calculation

```
∫_{-1/2}^{1/2} P_A(θ) dθ
  = ∫_{-1/2}^{1/2} 2π · ∑'_m g(θ+m) dθ           [def of P_A]
  = 2π · ∫_{-1/2}^{1/2} ∑_m g(θ+m) dθ            [tsum = finite sum]
  = 2π · ∑_m ∫_{-1/2}^{1/2} g(θ+m) dθ            [integral_finset_sum]
  = 2π · ∑_m ∫_{m-1/2}^{m+1/2} g(ξ) dξ           [change of vars]
  = 2π · ∫_ℝ g(ξ) dξ                              [disjoint intervals cover support]
  = 2π · ∫_ℝ a(ξ) · Φ(ξ) dξ                       [g = a·Φ]
  = ∫_ℝ (2π·a(ξ)) · Φ(ξ) dξ                       [pull constant]
  = ∫_ℝ a*(ξ) · Φ(ξ) dξ                           [a* = 2π·a]
  = arch_term(Φ)                                  [def]
```

## Hints for Difficult Steps

### Step 2-3: Integral of tsum
The standard approach when P_A is only locally a finite sum:
- Use that the integrand is continuous
- Use that the domain is compact
- Apply `integral_congr_ae` to rewrite tsum as finite sum a.e.

### Step 4: Partition Argument
For compact-supported g, the intervals [m-1/2, m+1/2] for |m| ≤ N cover the support.
Use `MeasureTheory.integral_eq_sum_of_disjoint` or accumulate via `integral_add_adjacent_intervals`.

## Tactic Preferences

AVOID: `exact?`, heavy `aesop`
PREFER: `nlinarith`, `positivity`, `gcongr`, explicit lemma applications
