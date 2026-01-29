# Rigorous arch_term ≥ prime_term via Heat Localization

## Goal

Prove that for the Fejér×heat window at large t:
$$\int_{\mathbb{R}} a^*(\xi) \Phi_{B,t}(\xi) \, d\xi \geq \sum_{n \geq 2} w_Q(n) \cdot \Phi_{B,t}(\xi_n)$$

where:
- $\Phi_{B,t}(\xi) = \max(0, 1 - |\xi|/B) \cdot e^{-4\pi^2 t \xi^2}$
- $\xi_n = \frac{\log n}{2\pi}$ (prime nodes, T0 normalization)
- $w_Q(n) = \frac{2\Lambda(n)}{\sqrt{n}}$ (von Mangoldt weights)
- $a^*(\xi) > 0$ is the digamma-derived symbol

## Key Insight: π-Cancellation

The magic: $4\pi^2 \xi_n^2 = (\log n)^2$ exactly because:
$$4\pi^2 \cdot \frac{(\log n)^2}{(2\pi)^2} = (\log n)^2$$

Therefore $\Phi(\xi_n) \leq e^{-t(\log n)^2}$, and at $n=2$, $t=40$:
$$\Phi(\xi_2) \approx e^{-19.2} \approx 4.5 \times 10^{-9}$$

## Part 1: Upper Bound on Prime Sum

### Lemma (prime_sum_tail_bound)
For $t > 0$ and weights $w_Q(n) = 2\Lambda(n)/\sqrt{n}$:
$$\sum_{n \geq 2} w_Q(n) \cdot e^{-t(\log n)^2} \leq C_{\text{prime}}(t)$$

where $C_{\text{prime}}(t) \to 0$ exponentially as $t \to \infty$.

### Proof Strategy
1. Split sum: $n \in [2, N_0]$ (finite) and $n > N_0$ (tail)
2. For finite part: direct computation, dominated by $n=2$
3. For tail: use $\Lambda(n) \leq \log n$ and integral comparison

**Finite part** ($n \leq N_0 = 100$):
$$\sum_{n=2}^{N_0} w_Q(n) e^{-t(\log n)^2} \leq \sum_{n=2}^{N_0} \frac{2\log n}{\sqrt{n}} e^{-t(\log 2)^2} \leq C_0 \cdot e^{-t(\log 2)^2}$$

where $C_0 = \sum_{n=2}^{100} \frac{2\log n}{\sqrt{n}} \approx 30$.

**Tail part** ($n > N_0$):
$$\sum_{n > N_0} w_Q(n) e^{-t(\log n)^2} \leq \sum_{n > N_0} \frac{2\log n}{\sqrt{n}} e^{-t(\log n)^2}$$

Change variable $u = \log n$, so $n = e^u$, $dn/du = e^u$:
$$\leq 2 \int_{\log N_0}^{\infty} u \cdot e^{-u/2} \cdot e^{-tu^2} \, du$$

For $t \geq 1$, this integral is $O(e^{-t(\log N_0)^2})$.

**Combined**:
$$C_{\text{prime}}(t) \leq C_0 \cdot e^{-t(\log 2)^2} + O(e^{-t(\log 100)^2})$$

At $t = 40$: $C_{\text{prime}}(40) \lesssim 30 \cdot 4.5 \times 10^{-9} \approx 1.4 \times 10^{-7}$.

## Part 2: Lower Bound on Arch Term

### Lemma (arch_term_lower_bound)
For $B \geq 1$, $t > 0$, and $a^*(0) > 0$:
$$\int_{\mathbb{R}} a^*(\xi) \Phi_{B,t}(\xi) \, d\xi \geq \frac{c_{\text{arch}}}{\sqrt{t}}$$

for some constant $c_{\text{arch}} > 0$ depending only on $a^*(0)$.

### Proof Strategy
1. Use $a^*(\xi) \geq a^*(0)/2$ on $|\xi| \leq \delta$ for small $\delta$ (continuity)
2. Restrict integral to $[-\delta, \delta]$
3. Use Fejér hat $\geq 1 - \delta/B \geq 1/2$ for $\delta \leq B/2$
4. Compute Gaussian integral

**Step 1**: By continuity of $a^*$ and $a^*(0) > 0$, there exists $\delta > 0$ such that:
$$a^*(\xi) \geq \frac{a^*(0)}{2} \quad \text{for } |\xi| \leq \delta$$

**Step 2**: Restrict:
$$\int_{\mathbb{R}} a^*(\xi) \Phi_{B,t}(\xi) d\xi \geq \int_{-\delta}^{\delta} a^*(\xi) \Phi_{B,t}(\xi) d\xi$$

**Step 3**: For $|\xi| \leq \delta \leq B/2$:
$$\Phi_{B,t}(\xi) = (1 - |\xi|/B) e^{-4\pi^2 t \xi^2} \geq \frac{1}{2} e^{-4\pi^2 t \xi^2}$$

**Step 4**: Therefore:
$$\geq \frac{a^*(0)}{4} \int_{-\delta}^{\delta} e^{-4\pi^2 t \xi^2} d\xi$$

For $\delta \sqrt{t} \geq 1$, the integral is approximately:
$$\int_{-\infty}^{\infty} e^{-4\pi^2 t \xi^2} d\xi = \frac{1}{2\pi\sqrt{t}}$$

So:
$$c_{\text{arch}} = \frac{a^*(0)}{8\pi}$$

## Part 3: Comparison

### Theorem (arch_ge_prime)
For all $t \geq t_0$ where $t_0$ depends on $a^*(0)$ and $B$:
$$\int_{\mathbb{R}} a^*(\xi) \Phi_{B,t}(\xi) d\xi \geq \sum_{n \geq 2} w_Q(n) \Phi_{B,t}(\xi_n)$$

### Proof
We need:
$$\frac{c_{\text{arch}}}{\sqrt{t}} \geq C_0 \cdot e^{-t(\log 2)^2}$$

Taking logs:
$$\log c_{\text{arch}} - \frac{1}{2}\log t \geq \log C_0 - t(\log 2)^2$$

Rearranging:
$$t(\log 2)^2 - \frac{1}{2}\log t \geq \log C_0 - \log c_{\text{arch}}$$

For large $t$, the LHS grows as $t(\log 2)^2 \approx 0.48t$, which dominates.

**Explicit threshold**: Solve $0.48t - 0.5\log t = \log(30) + \log(8\pi/a^*(0))$.

For $a^*(0) \approx 1$: $t_0 \approx 15$ suffices.

At $t = 40$:
- arch_term $\geq \frac{1}{8\pi\sqrt{40}} \approx 0.005$
- prime_term $\leq 1.4 \times 10^{-7}$

Ratio $\approx 36000$.

## Lean 4 Skeleton

```lean
import Mathlib

/-- Prime nodes in T0 normalization -/
noncomputable def xi (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Von Mangoldt weights -/
noncomputable def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Fejér × heat window -/
noncomputable def Phi (B t : ℝ) (xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)

/-- Key: π-cancellation lemma -/
lemma pi_cancellation (n : ℕ) (hn : 2 ≤ n) :
    4 * Real.pi^2 * (xi n)^2 = (Real.log n)^2 := by
  simp only [xi]
  ring

/-- Upper bound on prime sum -/
lemma prime_sum_bound (t : ℝ) (ht : 0 < t) :
    ∑' n, w_Q n * Real.exp (-t * (Real.log n)^2) ≤ 30 * Real.exp (-t * (Real.log 2)^2) := by
  sorry

/-- Lower bound on arch integral -/
lemma arch_integral_lower (B t : ℝ) (hB : 1 ≤ B) (ht : 0 < t) (ha : 0 < a_star 0) :
    ∫ xi, a_star xi * Phi B t xi ≥ a_star 0 / (8 * Real.pi * Real.sqrt t) := by
  sorry

/-- Main theorem: arch ≥ prime for large t -/
theorem arch_ge_prime (B t : ℝ) (hB : 1 ≤ B) (ht : 40 ≤ t) (ha : 0 < a_star 0) :
    ∫ xi, a_star xi * Phi B t xi ≥ ∑' n, w_Q n * Phi B t (xi n) := by
  calc ∫ xi, a_star xi * Phi B t xi
      ≥ a_star 0 / (8 * Real.pi * Real.sqrt t) := arch_integral_lower B t hB (by linarith) ha
    _ ≥ _ := by
        -- arch term ≥ 0.005 at t=40
        -- prime term ≤ 1.4e-7
        sorry
```

## Notes

1. The proof uses $a^*(0) > 0$ which is an axiom (`a_star_pos`)
2. Continuity of $a^*$ (`a_star_continuous`) gives the $\delta$ neighborhood
3. The threshold $t_0 \approx 15$ is conservative; $t = 40$ gives huge margin
4. This does NOT resolve (2M+1) normalization in Toeplitz setting

## Expected Output

A complete Lean 4 proof of `arch_ge_prime` with:
- `pi_cancellation` (algebraic, should be easy)
- `prime_sum_bound` (PNT-style, may need helper lemmas)
- `arch_integral_lower` (Gaussian integral + continuity)
- Final comparison (nlinarith with computed bounds)
