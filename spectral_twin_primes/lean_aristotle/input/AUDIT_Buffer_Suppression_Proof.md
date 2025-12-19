# Buffer Suppression Theorem (Schur Test Proof)

## Context

This theorem is part of the Q3 → MAS → TPC chain from Formal Audit Document 25.
The statement `Buffer_Suppression_Statement` already exists in Q3_MAS_CHAIN.
We need to PROVE it using the Schur test.

## Setup

We have:
- Heat kernel: $K_t(x,y) = \sqrt{2\pi t} \cdot e^{-(x-y)^2/(4t)}$
- Spectral coordinates: $\alpha_n = \log(n)/(2\pi)$
- Index sets: $I_K = \{n : \alpha_n \in [-K, K]\}$
- Major core $M \subseteq [-K, K]$
- Minor core $m = \{x \in [-K,K] : \text{dist}(x, M) \geq D\}$
- Buffer distance $D > 0$
- Minimum separation $\delta_K = \min_{n \neq m \in I_K} |\alpha_n - \alpha_m|$
- Maximum weight $w_{\max} = \max_{n \in I_K} |w_n|$ where $w_n = \Lambda(n)/\sqrt{n}$

The cross-block operator:
$$H_{mM} = P_m \circ H \circ P_M$$

where $H = T_A - T_P$ is the Q3 Hamiltonian, $P_m$ projects onto $V_m$, $P_M$ projects onto $V_M$.

## Theorem (Buffer Suppression)

For $t > 0$, $K > 0$, $D > 0$:
$$\|H_{mM}\| \leq w_{\max}(K) \cdot S(t; K, D)$$

where the bound function is:
$$S(t; K, D) = \frac{2 \cdot e^{-D^2/(4t)}}{1 - e^{-\delta_K^2/(4t)}}$$

## Proof Sketch

**Step 1: Kernel bound**

For $\alpha_n \in m$ and $\alpha_p \in M$, since $|\alpha_n - \alpha_p| \geq D$:
$$|K_t(\alpha_n, \alpha_p)| \leq \sqrt{2\pi t} \cdot e^{-D^2/(4t)}$$

**Step 2: Schur test setup**

The matrix elements of $H_{mM}$ in the kernel basis satisfy:
$$|[H_{mM}]_{np}| \leq |w_p| \cdot |K_t(\alpha_n, \alpha_p)|$$

**Step 3: Row sum bound**

For each $n \in I_m$:
$$\sum_{p \in I_M} |[H_{mM}]_{np}| \leq w_{\max} \cdot \sum_{p \in I_M} e^{-(\alpha_n - \alpha_p)^2/(4t)}$$

Since points in $I_M$ are separated by at least $\delta_K$ and $|\alpha_n - \alpha_p| \geq D$:
$$\sum_{p \in I_M} e^{-(\alpha_n - \alpha_p)^2/(4t)} \leq \sum_{k=0}^{\infty} e^{-(D + k\delta_K)^2/(4t)}$$

**Step 4: Geometric series bound**

Using $e^{-(D + k\delta_K)^2/(4t)} \leq e^{-D^2/(4t)} \cdot e^{-k\delta_K \cdot D/(2t)}$:
$$\sum_{k=0}^{\infty} e^{-(D + k\delta_K)^2/(4t)} \leq e^{-D^2/(4t)} \cdot \frac{1}{1 - e^{-\delta_K D/(2t)}}$$

For $D \geq \delta_K$, this simplifies to $\leq 2 \cdot e^{-D^2/(4t)} / (1 - e^{-\delta_K^2/(4t)})$.

**Step 5: Schur test conclusion**

By symmetric argument for column sums, Schur test gives:
$$\|H_{mM}\| \leq w_{\max}(K) \cdot S(t; K, D)$$

## Expected Lean Formalization

```lean
theorem Buffer_Suppression (t K D : ℝ) (k : ℝ → H) (T_A : H →L[ℂ] H)
    (hK : 0 < K) (ht : 0 < t) (hD : 0 < D) (M : Set ℝ)
    [CompleteSpace (V_M t K k M)] [CompleteSpace (V_m t K D k M)] :
  ‖H_mM t K D k T_A hK M‖ ≤ w_max K * S_bound t K D := by
  -- Apply Schur test
  -- Use kernel decay from buffer distance
  -- Sum geometric series
  sorry
```

## Dependencies

- Definitions from Q3_MAS_CHAIN: H_mM, w_max, S_bound, V_m, V_M
- Schur test for operator norms (in Mathlib)
- Geometric series bounds
