# Q3-2: The Operator Bridge (RKHS Prime Contraction → Additive Bounds)

## Overview

This document formalizes Hypothesis Q3-2: the transfer principle from RKHS operator norms to exponential sum bounds. This is the "narrow waist" connecting multiplicative (zeta) and additive (circle method) structures.

## Core Construction

### 1. The RKHS Space H_{t,K}

Define the heat kernel RKHS on the window W_K = [-K, K]:

```lean
-- Heat kernel
noncomputable def heat_kernel (t : ℝ) (x y : ℝ) : ℝ :=
  Real.exp (-(x - y)^2 / (4 * t))

-- The RKHS is the completion of span{k_t(·, y) : y ∈ W_K}
-- with inner product ⟨k_t(·,x), k_t(·,y)⟩ = k_t(x,y)
```

**Key property:** k_t(x,y) → δ(x-y) as t → 0 (localization).

### 2. Prime Sampling Nodes

For primes p ≤ N, define log-frequency nodes:

```lean
noncomputable def prime_node (p : ℕ) : ℝ := Real.log p / (2 * Real.pi)

-- Nodes in window W_K
def nodes_in_window (K : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n =>
    Nat.Prime n ∧ |prime_node n| ≤ K)
```

### 3. Prime Weights

The von Mangoldt weight normalized for L² analysis:

```lean
noncomputable def prime_weight (n : ℕ) : ℝ :=
  if Nat.Prime n then Real.log n / Real.sqrt n else 0

-- Key bound: w(n) ≤ 2/e for all n (the "prime cap")
lemma prime_weight_bound (n : ℕ) (hn : Nat.Prime n) (hn3 : n ≥ 3) :
  prime_weight n ≤ 2 / Real.exp 1 := by sorry
```

### 4. The Gram Matrix

```lean
noncomputable def gram_matrix (t : ℝ) (nodes : Finset ℕ) : Matrix (Fin nodes.card) (Fin nodes.card) ℝ :=
  fun i j => heat_kernel t (prime_node (nodes.toList[i])) (prime_node (nodes.toList[j]))
```

**Explicit form:**
$$G_{mn} = \exp\left(-\frac{\log^2(m/n)}{16\pi^2 t}\right)$$

### 5. The Twisted Prime Operator T_{P,α}

The key operator with phase modulation:

```lean
-- Matrix elements of T_{P,α} in the RKHS basis
noncomputable def twisted_prime_matrix (t α : ℝ) (nodes : Finset ℕ) :
    Matrix (Fin nodes.card) (Fin nodes.card) ℂ :=
  fun i j =>
    let m := nodes.toList[i]
    let n := nodes.toList[j]
    (prime_weight n : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * α * prime_node n) *
    (gram_matrix t nodes i j : ℂ)
```

**Explicit form:**
$$[T_{P,\alpha}]_{mn} = \frac{\log n}{\sqrt{n}} \cdot n^{i\alpha} \cdot \exp\left(-\frac{\log^2(m/n)}{16\pi^2 t}\right)$$

## The Bridge Theorem

### Statement

**Theorem (Q3_2_bridge):** For the twisted prime operator on minor arcs:

```lean
theorem Q3_2_bridge :
  ∃ (ρ : ℝ) (C : ℝ), ρ < 1 ∧ C > 0 ∧
  ∀ (K : ℝ) (t : ℝ) (N : ℕ) (α : ℝ),
    K > 0 → t > 0 → N > 100 →
    α ∈ minor_arcs N →
    ‖twisted_prime_matrix t α (nodes_in_window K N)‖ ≤ ρ := by
  sorry
```

### Minor Arcs Definition

```lean
def minor_arcs (N : ℕ) : Set ℝ :=
  {α : ℝ | ∀ (a : ℤ) (q : ℕ), q ≤ N^(1/10 : ℝ) → |α - a/q| > 1/(q * N)}
```

## Mechanism: Why Minor Arcs Give Contraction

### Phase Cancellation Analysis

On minor arcs, the phases n^{iα} = e^{iα log n} are "spread out":

**Lemma (phase_spread):** If α ∈ minor arcs, then for distinct primes p, q:
$$|p^{i\alpha} - q^{i\alpha}| \geq c \cdot |\log(p/q)|$$
for some c > 0 depending on the minor arc parameters.

```lean
lemma phase_spread (α : ℝ) (hα : α ∈ minor_arcs N) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
  ∃ c > 0, Complex.abs (p^(Complex.I * α) - q^(Complex.I * α)) ≥
    c * |Real.log p - Real.log q| := by
  sorry
```

### Operator Norm Bound

The key insight: Gram matrix G provides decay, phase provides cancellation.

**Lemma (operator_norm_split):**
$$\|T_{P,\alpha}\|^2 \leq \sum_m \sum_n |w(n)|^2 |G_{mn}|^2$$

But with phase on minor arcs, we get additional decay:
$$\|T_{P,\alpha}\|^2 \leq \rho_K^2 \cdot \sum_m \sum_n |w(n)|^2 |G_{mn}|^2$$

where ρ_K < 1 comes from the separation of nodes.

## Connection to Exponential Sums

### From Operator to Sum

The exponential sum S(α) can be expressed via the resolvent:

```lean
-- S(α) = Σ_{n≤N} Λ(n) e(αn) relates to operator trace
lemma exp_sum_operator_connection (α : ℝ) (N : ℕ) :
  ∃ (v : Vector ℂ) (M : Matrix _ _ ℂ),
    Complex.abs (∑ n in Finset.range (N+1),
      (if Nat.Prime n then Real.log n else 0) * Complex.exp (2 * Real.pi * Complex.I * α * n))
    ≤ ‖M‖ * ‖v‖^2 := by
  sorry
```

### The Neumann Series Bound

If ‖T_{P,α}‖ < 1, then (I - T_{P,α})^{-1} exists and:
$$\|(I - T_{P,\alpha})^{-1}\| \leq \frac{1}{1 - \|T_{P,\alpha}\|}$$

This gives controlled summability of the operator's contributions.

## Implications

### Q3-2 implies Q3-1

**Theorem:** If Q3_2_bridge holds with ρ < 1, then Q3-1 (uniform additive gap) holds:

```lean
theorem Q3_2_implies_Q3_1 (h : Q3_2_bridge) :
  ∃ (δ : ℝ) (C : ℝ), δ > 0 ∧ C > 0 ∧
  ∀ N : ℕ, N > 100 →
  ∀ α : ℝ, α ∈ minor_arcs N →
    Complex.abs (∑ n in Finset.range (N+1),
      (if Nat.Prime n then Real.log n else 0) * Complex.exp (2 * Real.pi * Complex.I * α * n))
    ≤ C * N^(1/2 - δ) := by
  sorry
```

## Key Parameters

| Parameter | Meaning | Constraint |
|-----------|---------|------------|
| K | Window size | K ~ log N |
| t | Heat smoothing | t = t_min(K) from node separation |
| ρ_K | Contraction rate | ρ_K < 1, depends on δ_K (gap between nodes) |
| Q | Minor arc threshold | Q ~ N^{1/10} |

## References

1. RH_Q3.pdf - Original RKHS prime operator construction
2. A3 (Toeplitz bridge) - Connection to Toeplitz operators
3. Hardy-Littlewood circle method - Classical minor/major arc decomposition
