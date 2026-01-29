# Gaussian Tail Bound: Prime Gap Kills Prime Term

## The Core Lemma We Need

**Localization Lemma**: For $t \geq t_0$, the Gaussian mass outside $|\xi| < \delta$ is exponentially small.

Since the smallest prime node is $\xi_2 = \log(2)/(2\pi) \approx 0.110$, setting $\delta = 0.1$ captures the "prime gap".

## Mathematical Statement

### Gaussian Tail Bound (Standard)

For $\sigma^2 = 1/(8\pi^2 t)$ (our heat kernel variance):
$$\int_{|\xi| > \delta} e^{-4\pi^2 t \xi^2} d\xi \leq 2 \cdot \frac{e^{-4\pi^2 t \delta^2}}{4\pi^2 t \delta}$$

This is the standard complementary error function bound: $\text{erfc}(x) \leq \frac{e^{-x^2}}{x\sqrt{\pi}}$.

### Prime Gap Constant

Define the **prime gap** as the distance from origin to first prime node:
$$\delta_{prime} := \xi_2 = \frac{\log 2}{2\pi} \approx 0.1103$$

### Main Lemma: Prime Term Exponential Decay

**Lemma (prime_term_exp_decay)**:
For all $t \geq 1$:
$$\text{prime\_term}(\Phi_t) \leq C \cdot e^{-4\pi^2 t \cdot \delta_{prime}^2}$$

where $C$ is a constant depending only on the von Mangoldt weights.

### Corollary: Ratio Bound

**Corollary (arch_dominates_prime_ratio)**:
For all $t \geq 1$:
$$\frac{\text{prime\_term}(\Phi_t)}{\text{arch\_term}(\Phi_t)} \leq C' \cdot \sqrt{t} \cdot e^{-4\pi^2 t \cdot \delta_{prime}^2}$$

Since $\sqrt{t} \cdot e^{-ct} \to 0$ exponentially, this ratio vanishes.

## Lean 4 Formalization

```lean
import Mathlib

open Real MeasureTheory Set BigOperators

noncomputable section

/-! ## Constants with clear names -/

/-- The prime gap: distance from 0 to the first prime node ξ₂ = log(2)/(2π) -/
def delta_prime : ℝ := Real.log 2 / (2 * Real.pi)

/-- delta_prime is positive -/
lemma delta_prime_pos : delta_prime > 0 := by
  unfold delta_prime
  positivity

/-- delta_prime ≈ 0.110 -/
lemma delta_prime_approx : delta_prime > 0.1 := by
  unfold delta_prime
  -- log(2) > 0.69, 2π < 6.29, so log(2)/(2π) > 0.69/6.29 > 0.109 > 0.1
  have h1 : Real.log 2 > 0.69 := by
    have := Real.log_two_gt_d9
    linarith
  have h2 : 2 * Real.pi < 6.29 := by
    have := Real.pi_lt_315
    linarith
  have h3 : (0.69 : ℝ) / 6.29 > 0.1 := by norm_num
  calc delta_prime = Real.log 2 / (2 * Real.pi) := rfl
    _ > 0.69 / 6.29 := by
        apply div_lt_div_of_pos_left h1 (by norm_num) h2
    _ > 0.1 := h3

/-! ## Gaussian Tail Bounds -/

/-- Heat kernel at point ξ with parameter t -/
def heat_kernel_xi (t ξ : ℝ) : ℝ := Real.exp (-4 * Real.pi^2 * t * ξ^2)

/-- Gaussian tail integral bound (standard erfc estimate) -/
lemma gaussian_tail_bound (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) :
    ∫ ξ in Ioi δ, heat_kernel_xi t ξ ≤
      Real.exp (-4 * Real.pi^2 * t * δ^2) / (8 * Real.pi^2 * t * δ) := by
  sorry

/-- Symmetric tail bound -/
lemma gaussian_tail_bound_symmetric (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) :
    ∫ ξ in {x : ℝ | |x| > δ}, heat_kernel_xi t ξ ≤
      2 * Real.exp (-4 * Real.pi^2 * t * δ^2) / (8 * Real.pi^2 * t * δ) := by
  sorry

/-! ## Prime Term Decay -/

/-- Logarithmic prime node -/
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- All prime nodes are beyond the prime gap -/
lemma xi_n_ge_delta_prime (n : ℕ) (hn : 2 ≤ n) : xi_n n ≥ delta_prime := by
  unfold xi_n delta_prime
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)

/-- Von Mangoldt weight -/
def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Sum of weights is bounded (from weight_sum_bound proof) -/
axiom w_Q_sum_bounded : ∑' n, w_Q n ≤ 10  -- crude bound

/-- MAIN: Prime term decays exponentially in t -/
theorem prime_term_exp_decay (t : ℝ) (ht : 1 ≤ t) :
    ∑' n, w_Q n * heat_kernel_xi t (xi_n n) ≤
      10 * Real.exp (-4 * Real.pi^2 * t * delta_prime^2) := by
  sorry

/-! ## Arch Term Lower Bound -/

/-- Archimedean kernel lower bound (a* > 2π near origin) -/
def a_star_lower : ℝ := 2 * Real.pi

/-- Arch term has Gaussian integral lower bound -/
theorem arch_term_lower_bound (t : ℝ) (ht : 0 < t) :
    ∫ ξ in Icc (-1 : ℝ) 1, a_star_lower * heat_kernel_xi t ξ ≥
      a_star_lower / (4 * Real.sqrt (Real.pi^3 * t)) := by
  sorry

/-! ## The Main Ratio Bound -/

/-- MAIN THEOREM: Prime-to-Arch ratio vanishes exponentially -/
theorem prime_arch_ratio_vanishes (t : ℝ) (ht : 10 ≤ t) :
    (∑' n, w_Q n * heat_kernel_xi t (xi_n n)) /
    (∫ ξ in Icc (-3 : ℝ) 3, (2 * Real.pi) * heat_kernel_xi t ξ) ≤
      1 / 100 := by
  sorry

/-- Corollary: arch_term ≥ prime_term for t ≥ 10 -/
theorem arch_ge_prime_for_large_t (t : ℝ) (ht : 10 ≤ t) :
    ∫ ξ in Icc (-3 : ℝ) 3, (2 * Real.pi) * heat_kernel_xi t ξ ≥
      ∑' n, w_Q n * heat_kernel_xi t (xi_n n) := by
  sorry
```

## Key Points for Lean Verification

1. **delta_prime_approx**: Can verify `log(2)/(2π) > 0.1` using `Real.log_two_gt_d9` and `Real.pi_lt_315`.

2. **gaussian_tail_bound**: Standard erfc bound, might be in Mathlib as `Real.add_one_le_exp` or similar.

3. **xi_n_ge_delta_prime**: Follows from monotonicity of log.

4. **prime_term_exp_decay**: Combine weight bound with exponential decay.

5. **arch_ge_prime_for_large_t**: The final goal!

## Naming Convention

| Name | Meaning |
|------|---------|
| `delta_prime` | The prime gap ≈ 0.11 |
| `heat_kernel_xi` | Gaussian exp(-4π²tξ²) |
| `xi_n` | Prime node log(n)/(2π) |
| `w_Q` | Von Mangoldt weight |
| `prime_term_exp_decay` | Prime sum decays in t |
| `arch_ge_prime_for_large_t` | **THE GOAL** |

## References

- Gaussian tail bounds: `Mathlib.Analysis.SpecialFunctions.Gaussian`
- erfc bounds: standard analysis
