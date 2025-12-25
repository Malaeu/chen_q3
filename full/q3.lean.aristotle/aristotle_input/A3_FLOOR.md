# A3: Uniform Archimedean Floor (c_* = 1.5)

## Goal
Prove that the Archimedean symbol P_A has a **pointwise floor** c_* = 1.5 on the entire circle.

---

## Part 1: Definitions

```lean
import Mathlib

noncomputable section

open Real Complex MeasureTheory Set
open scoped BigOperators

-- Digamma function
def digamma (z : ℂ) : ℂ := (deriv Gamma z) / (Gamma z)

-- Archimedean density a(ξ)
def a (ξ : ℝ) : ℝ := log π - (digamma (1/4 + I * π * ξ)).re

-- Fixed parameters
def B_min : ℝ := 3
def t_sym : ℝ := 3 / 50  -- = 0.06

-- Fejér×heat window
def w (B t ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * exp (-4 * π^2 * t * ξ^2)

-- Weighted density
def g (B t ξ : ℝ) : ℝ := a ξ * w B t ξ

-- Archimedean symbol (periodized)
def P_A (B t θ : ℝ) : ℝ :=
  2 * π * ∑' (m : ℤ), g B t (θ + m)

-- Uniform floor constant
def c_star : ℝ := 1.5
```

---

## Part 2: Monotonicity of a(ξ)

### Theorem 2.1: a is strictly decreasing on [0, ∞)

```lean
theorem a_strict_mono : StrictAntiOn a (Ici 0) := by sorry
```

**Proof outline:**

The derivative of a(ξ) is:
$$a'(\xi) = -\pi \cdot \text{Im}\,\psi'\left(\frac{1}{4} + i\pi\xi\right)$$

where ψ' is the trigamma function. For z in the right half-plane (Re z > 0):
- ψ'(z) = Σ_{n≥0} 1/(z+n)²
- For z = 1/4 + iπξ with ξ > 0, Im(ψ'(z)) > 0

Therefore a'(ξ) < 0 for all ξ > 0, so a is strictly decreasing.

---

## Part 3: Sample-Point Bounds

We need bounds at three specific points.

### Theorem 3.1: a(1/2) ≥ 0.68

```lean
theorem a_half_bound : a (1/2) ≥ 0.68 := by sorry
```

### Theorem 3.2: a(3/2) ≥ -0.45

```lean
theorem a_three_half_bound : a (3/2) ≥ -0.45 := by sorry
```

### Theorem 3.3: a(5/2) ≥ -1.00

```lean
theorem a_five_half_bound : a (5/2) ≥ -1.00 := by sorry
```

**Proof method for all three:**

Use the series representation:
$$\text{Re}\,\psi\left(\frac{1}{4}+i\pi\xi\right) = -\gamma + \sum_{n=0}^{\infty}\left(\frac{1}{n+1} - \frac{n+\frac{1}{4}}{(n+\frac{1}{4})^2+\pi^2\xi^2}\right)$$

Key observation: For $n \geq \lceil \frac{4}{3}\pi^2\xi^2 - \frac{1}{4} \rceil$, the summand is **non-positive**.

Therefore truncating at n = 100 gives a **rigorous lower bound** (since we're dropping negative terms).

Explicit computation:
- At ξ = 1/2: truncated sum gives Re ψ ≤ some value → a(1/2) ≥ 0.68
- At ξ = 3/2: truncated sum gives Re ψ ≤ some value → a(3/2) ≥ -0.45
- At ξ = 5/2: truncated sum gives Re ψ ≤ some value → a(5/2) ≥ -1.00

---

## Part 4: Window Bounds

With B = B_min = 3 and t = t_sym = 3/50:

### Theorem 4.1: w(1/2) ≥ 0.45

```lean
theorem w_half_bound : w B_min t_sym (1/2) ≥ 0.45 := by sorry
```

**Proof:**
$$w(1/2) = \left(1 - \frac{1/2}{3}\right) \cdot e^{-4\pi^2 \cdot \frac{3}{50} \cdot \frac{1}{4}}$$
$$= \frac{5}{6} \cdot e^{-\frac{3\pi^2}{50}} \geq \frac{5}{6} \cdot e^{-0.6} > 0.45$$

(using π² < 10)

### Theorem 4.2: w(1) ≥ 0.06

```lean
theorem w_one_bound : w B_min t_sym 1 ≥ 0.06 := by sorry
```

**Proof:**
$$w(1) = \left(1 - \frac{1}{3}\right) \cdot e^{-4\pi^2 \cdot \frac{3}{50}}$$
$$= \frac{2}{3} \cdot e^{-\frac{12\pi^2}{50}} \geq \frac{2}{3} \cdot e^{-2.4} > 0.06$$

### Theorem 4.3: w(2) ≥ 2×10⁻⁵

```lean
theorem w_two_bound : w B_min t_sym 2 ≥ 2e-5 := by sorry
```

**Proof:**
$$w(2) = \left(1 - \frac{2}{3}\right) \cdot e^{-4\pi^2 \cdot \frac{3}{50} \cdot 4}$$
$$= \frac{1}{3} \cdot e^{-\frac{48\pi^2}{50}} \geq \frac{1}{3} \cdot e^{-9.6} > 2 \times 10^{-5}$$

---

## Part 5: Tail Bound

### Theorem 5.1: Tail contribution is negligible

```lean
theorem tail_bound :
    4 * π * ∫ ξ in Ici (5/2 : ℝ), |a ξ| * exp (-4 * π^2 * t_sym * ξ^2) ≤ 1e-5 := by sorry
```

**Proof outline:**

1. By logarithmic growth (from monotonicity + asymptotics):
   $$|a(\xi)| \leq a(0) + \frac{11}{10}\log(1+\xi) \leq 8 \quad \text{for } \xi \geq 5/2$$

2. Gaussian tail bound:
   $$\int_R^\infty e^{-\alpha\xi^2}\,d\xi \leq \frac{e^{-\alpha R^2}}{2\alpha R}$$

3. With R = 5/2, α = 4π² · (3/50) ≈ 2.4:
   $$\int_{5/2}^\infty e^{-2.4\xi^2}\,d\xi \leq \frac{e^{-15}}{12} < 10^{-7}$$

4. Therefore:
   $$4\pi \cdot 8 \cdot 10^{-7} < 10^{-5}$$

---

## Part 6: Main Floor Theorem (GOAL)

### Theorem 6.1: Uniform Archimedean Floor

```lean
theorem uniform_arch_floor (B : ℝ) (hB : B ≥ B_min) (θ : ℝ) (hθ : θ ∈ Icc (-1/2) (1/2)) :
    P_A B t_sym θ ≥ c_star := by sorry
```

**Proof:**

For θ ∈ [0, 1/2] (the case θ ∈ [-1/2, 0] follows by evenness of P_A):

**Step 1:** Decompose the sum
$$P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g(\theta + m)$$
$$\geq 2\pi \left( g(\theta) + 2g(\theta+1) + 2g(\theta+2) \right) - \mathcal{T}$$

where the factor 2 accounts for m = ±1, ±2, and T is the tail from |m| ≥ 3.

**Step 2:** Apply monotonicity bounds

Since a is decreasing and θ ∈ [0, 1/2]:
- g(θ) = a(θ) · w(θ) ≥ a(1/2) · w(1/2) ≥ 0.68 · 0.45
- g(θ+1) = a(θ+1) · w(θ+1) ≥ a(3/2) · w(1) ≥ -0.45 · 0.06
- g(θ+2) = a(θ+2) · w(θ+2) ≥ a(5/2) · w(2) ≥ -1.00 · 2×10⁻⁵

**Step 3:** Combine

$$P_A(\theta) \geq 2\pi \left( 0.68 \cdot 0.45 - 2 \cdot 0.45 \cdot 0.06 - 2 \cdot 1.00 \cdot 2 \times 10^{-5} \right) - 10^{-5}$$

$$= 2\pi \left( 0.306 - 0.054 - 0.00004 \right) - 10^{-5}$$

$$= 2\pi \cdot 0.25196 - 10^{-5}$$

$$\geq 6.28 \cdot 0.25196 - 10^{-5}$$

$$> 1.58 - 10^{-5} > 1.5 = c_*$$

**Step 4:** Evenness

P_A(θ) = P_A(-θ) by symmetry of a (since a(ξ) = a(-ξ)) and the window.

Therefore P_A(θ) ≥ 1.5 for all θ ∈ [-1/2, 1/2]. ∎

---

## Summary of Dependencies

```
a_strict_mono
      ↓
a_half_bound, a_three_half_bound, a_five_half_bound
      ↓
w_half_bound, w_one_bound, w_two_bound
      ↓
tail_bound
      ↓
uniform_arch_floor  ← MAIN GOAL
```

---

## Output for Next Module

After this is proven, for T5_BRIDGE.md use:

```lean
-- Proven in A3_FLOOR
axiom A3_floor : ∀ B ≥ B_min, ∀ θ ∈ Icc (-1/2) (1/2), P_A B t_sym θ ≥ c_star

-- Where:
-- B_min = 3
-- t_sym = 3/50
-- c_star = 1.5
```
