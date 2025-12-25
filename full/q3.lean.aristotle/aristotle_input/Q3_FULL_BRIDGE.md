# Q3 Full Bridge: Weil Positivity via Toeplitz-RKHS Framework

## Overview
This is the complete formalization of the Q3 proof chain:
**T0 → A1' → A2 → A3 → RKHS → T5 → Main Positivity → RH**

We use the **pointwise floor** approach with `c_* = 1.5` (not mean-modulus).

---

## Part 1: Core Definitions (Already Proven)

These definitions are established from previous Aristotle run:

```lean
import Mathlib

noncomputable section

-- Digamma function
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)

-- Archimedean density
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * (ξ : ℂ))).re

-- Fejér×heat window
def w_B (B t_sym ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

-- Periodized symbol (period 1)
def g (B t_sym ξ : ℝ) : ℝ := a ξ * w_B B t_sym ξ

-- Archimedean symbol on T = [-1/2, 1/2]
def P_A (B t_sym θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' m : ℤ, g B t_sym (θ + m)

-- Fixed parameters
def B_min : ℝ := 3
def t_sym_val : ℝ := 3 / 50

-- Uniform floor constant
def c_star : ℝ := 1.5
```

---

## Part 2: Key Lemmas to Prove

### Lemma 1: Strict Monotonicity of a(ξ)

**Statement:**
```lean
theorem a_strict_mono : StrictAntiOn a (Set.Ici 0) := by sorry
```

**Proof outline:**
The derivative satisfies:
$$a'(\xi) = -\pi \cdot \text{Im}\, \psi'\left(\frac{1}{4} + i\pi\xi\right) < 0$$
for $\xi > 0$, using the trigamma positivity on the right half-plane.

---

### Lemma 2: Logarithmic Growth Bound

**Statement:**
```lean
theorem a_log_bound (ξ : ℝ) (hξ : ξ ≥ 1) :
    |a ξ| ≤ a 0 + (11/10) * Real.log (1 + ξ) := by sorry
```

**Proof outline:**
For $\xi \geq 1$, the asymptotic expansion gives:
$$|a(\xi)| \leq |a(1)| + \frac{11}{10}\log\xi \leq a(0) + \frac{11}{10}\log(1+\xi)$$

---

### Lemma 3: Sample-Point Bounds

**Statement:**
```lean
theorem a_sample_half : a (1/2) ≥ 0.68 := by sorry
theorem a_sample_three_half : a (3/2) ≥ -0.45 := by sorry
theorem a_sample_five_half : a (5/2) ≥ -1.00 := by sorry
```

**Proof outline:**
Use the series representation:
$$\text{Re}\,\psi\left(\frac{1}{4}+i\pi\xi\right) = -\gamma + \sum_{n\geq 0}\left(\frac{1}{n+1} - \frac{n+\frac{1}{4}}{(n+\frac{1}{4})^2+\pi^2\xi^2}\right)$$

The summand is nonpositive for $n \geq \lceil \frac{4}{3}\pi^2\xi^2 - \frac{1}{4} \rceil$.
Truncating at $n=100$ gives rigorous lower bounds.

---

### Lemma 4: Window Bounds

**Statement:**
```lean
theorem w_bound_half : w_B B_min t_sym_val (1/2) ≥ 0.45 := by sorry
theorem w_bound_one : w_B B_min t_sym_val 1 ≥ 0.06 := by sorry
theorem w_bound_two : w_B B_min t_sym_val 2 ≥ 2e-5 := by sorry
```

**Proof outline:**
With $\pi^2 < 10$ and $B_{\min} = 3$, $t_{\text{sym}} = 3/50$:
- $w(1/2) \geq \frac{5}{6}e^{-0.6} > 0.45$
- $w(1) \geq \frac{2}{3}e^{-2.4} > 0.06$
- $w(2) \geq \frac{1}{3}e^{-9.6} > 2 \times 10^{-5}$

---

### Lemma 5: Tail Bound

**Statement:**
```lean
theorem tail_bound :
    4 * Real.pi * ∫ ξ in Set.Ici (5/2), |a ξ| * Real.exp (-4 * Real.pi^2 * t_sym_val * ξ^2) ≤ 1e-5 := by sorry
```

**Proof outline:**
Using $|a(\xi)| \leq 8$ for $\xi \geq 5/2$ (from log bound) and Gaussian tail:
$$\int_R^\infty e^{-\alpha\xi^2}\,d\xi \leq \frac{e^{-\alpha R^2}}{2\alpha R}$$

---

## Part 3: Main Theorems

### Theorem: Uniform Archimedean Floor (CRITICAL)

**Statement:**
```lean
theorem uniform_arch_floor (B : ℝ) (hB : B ≥ B_min) (θ : ℝ) (hθ : θ ∈ Set.Icc (-1/2) (1/2)) :
    P_A B t_sym_val θ ≥ c_star := by sorry
```

**Proof outline:**
For $\theta \in [0, 1/2]$ and $B \geq 3$:
$$P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g(\theta + m) \geq 2\pi(g(\theta) + 2g(\theta+1) + 2g(\theta+2)) - \mathcal{T}$$

Using monotonicity and sample bounds:
- $g(\theta) \geq 0.68 \cdot w(1/2)$
- $g(\theta+1) \geq -0.45 \cdot w(1)$
- $g(\theta+2) \geq -1.00 \cdot w(2)$
- $\mathcal{T} \leq 10^{-5}$

Combining with $2\pi > 6.28$:
$$P_A(\theta) \geq 2\pi(0.68 \cdot 0.45 - 2 \cdot 0.45 \cdot 0.06 - 2 \cdot 1.00 \cdot 2 \cdot 10^{-5}) - 10^{-5} > 1.5$$

Evenness extends to all of $\mathbb{T}$.

---

### Theorem: RKHS Prime Cap

**Statement:**
```lean
-- Prime sample nodes
def ξ_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

-- RKHS weights
def w_RKHS (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

-- Uniform cap function
def ρ (t : ℝ) : ℝ :=
  2 * ∫ y in Set.Ici 0, y * Real.exp (y/2) * Real.exp (-4 * Real.pi^2 * t * y^2)

theorem rho_decreasing : StrictAntiOn ρ (Set.Ioi 0) := by sorry
theorem rho_limit : Filter.Tendsto ρ Filter.atTop (nhds 0) := by sorry

-- There exists t_rkhs_unif such that ρ(t) ≤ c_star/4
theorem exists_t_rkhs_unif :
    ∃ t_unif > 0, ∀ t ≥ t_unif, ρ t ≤ c_star / 4 := by sorry
```

---

### Theorem: Uniform Discretization

**Statement:**
```lean
-- Szegő-Böttcher constant
def C_SB : ℝ := 4

-- Uniform Lipschitz constant
def L_star : ℝ := sorry  -- supremum of L_A(B, t_sym) over B ≥ B_min

-- Discretization threshold
def M_0_unif : ℕ := Nat.ceil (C_SB * L_star / c_star)

theorem uniform_discretization (B : ℝ) (hB : B ≥ B_min) (M : ℕ) (hM : M ≥ M_0_unif) :
    -- λ_min(T_M[P_A]) ≥ c_star / 2
    sorry := by sorry
```

---

### Theorem: A3 Bridge

**Statement:**
```lean
-- Toeplitz operator T_P (prime sampling)
def T_P : sorry := sorry

theorem A3_bridge (M : ℕ) (hM : M ≥ M_0_unif) (t_rkhs : ℝ) (ht : t_rkhs ≥ t_rkhs_unif) :
    -- λ_min(T_M[P_A] - T_P) ≥ c_star / 4
    sorry := by sorry
```

**Proof outline:**
$$\lambda_{\min}(T_M[P_A] - T_P) \geq c_* - \frac{c_*}{2} - \frac{c_*}{4} = \frac{c_*}{4}$$

---

### Theorem: Main Positivity (GOAL)

**Statement:**
```lean
-- Weil functional
def Q (Φ : ℝ → ℝ) : ℝ := sorry

-- Weil class
def WeilClass : Set (ℝ → ℝ) := sorry

theorem main_positivity (Φ : ℝ → ℝ) (hΦ : Φ ∈ WeilClass) : Q Φ ≥ 0 := by sorry
```

**Proof outline:**
1. By A3 bridge: $Q(\Phi) \geq 0$ on Fejér×heat cone in $\mathcal{W}_K$
2. By A1' density: cone is dense in $\mathcal{W}_K$
3. By A2 continuity: extends to all of $\mathcal{W}_K$
4. Taking union over $K$: $Q \geq 0$ on $\mathcal{W}$
5. By T0: this is the Weil criterion ⟹ **RH**

---

## Numerical Constants Summary

| Constant | Value | Source |
|----------|-------|--------|
| $B_{\min}$ | 3 | Bandwidth threshold |
| $t_{\text{sym}}$ | 3/50 = 0.06 | Symbol heat parameter |
| $c_*$ | 1.5 | Pointwise Archimedean floor |
| $C_{\text{SB}}$ | 4 | Szegő-Böttcher constant |
| $\rho(t) \to 0$ | as $t \to \infty$ | Prime cap decreases |

---

## Priority Order for Proofs

1. **a_strict_mono** - Foundation for everything
2. **a_sample_**** bounds - Needed for floor
3. **uniform_arch_floor** - THE critical result (c_* = 1.5)
4. **rho_decreasing + exists_t_rkhs_unif** - RKHS cap
5. **A3_bridge** - Combines floor and cap
6. **main_positivity** - Final goal

---

## Context from Previous Runs

The following definitions are already established (from dbfa2c26):
- `digamma`, `a`, `A_0`, `L_int`
- `A_star`, `L_star`, `c_star` (mean-modulus versions)
- `M_0_unif`, `t_rkhs_unif` (draft versions)

**This run should:**
1. Prove the **pointwise** floor instead of mean-modulus
2. Complete the sample-point bounds
3. Chain everything to main_positivity
