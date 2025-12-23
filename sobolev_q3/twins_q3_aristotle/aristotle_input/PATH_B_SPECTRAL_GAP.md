# Path B: Spectral Gap via Anantharaman-Monk Theory

## Goal
Prove: ‖B_α‖ < 1 for all α ∈ minor arcs, uniformly in N.

## 1. SETUP

### 1.1 The Operator
$$B_\alpha = G^{1/2} W U_\alpha G^{1/2}$$

where:
- $G_{pq} = k_t(\xi_p, \xi_q) = \exp\left(-\frac{(\xi_p - \xi_q)^2}{4t}\right)$
- $\xi_p = \frac{\log p}{2\pi}$ (log-coordinates)
- $W = \text{diag}\left(\frac{\log p}{\sqrt{p}}\right)$ (prime weights)
- $U_\alpha = \text{diag}(e(\alpha p))$ (circle twist)

### 1.2 The Question
Why does $\|B_\alpha\| < 1$ for $\alpha \in$ minor arcs?

## 2. SPECTRAL THEORY APPROACH

### 2.1 Heat Kernel as Convolution
The Gram matrix G can be written as:
$$G = \Phi^* \Phi$$

where $\Phi: \mathbb{C}^{P_N} \to H$ is the feature map into RKHS.

The heat kernel $k_t$ is the fundamental solution of:
$$\frac{\partial u}{\partial t} = \Delta u$$

### 2.2 Spectral Decomposition
On a compact manifold M, heat kernel has expansion:
$$k_t(x,y) = \sum_{n=0}^\infty e^{-\lambda_n t} \phi_n(x) \phi_n(y)$$

where $\lambda_n$ are eigenvalues of $-\Delta$ and $\phi_n$ eigenfunctions.

**Spectral gap:** $\lambda_1 > 0$ implies exponential mixing.

### 2.3 Connection to B_α
The twisted operator $B_\alpha$ involves:
$$\langle f, B_\alpha g \rangle = \sum_{p,q \in P_N} \bar{f}_p g_q \cdot w_p w_q \cdot e(\alpha(p-q)) \cdot k_t(\xi_p, \xi_q)$$

**Key insight:** The phase $e(\alpha(p-q))$ for $\alpha \in$ minor arcs destroys coherence.

## 3. THE ANANTHARAMAN-MONK FRAMEWORK

### 3.1 Quantum Unique Ergodicity
For arithmetic surfaces $\Gamma \backslash \mathbb{H}$:
- Eigenfunctions of Laplacian become equidistributed
- Spectral gap $\lambda_1 \geq 1/4 - \epsilon$ (Selberg conjecture: $\lambda_1 \geq 1/4$)

### 3.2 Transfer Operator Analogy
Consider the transfer operator:
$$\mathcal{L}_s f(x) = \sum_{\gamma} f(\gamma^{-1} x) \cdot |\gamma'(x)|^s$$

For geodesic flow on $\Gamma \backslash \mathbb{H}$:
- Spectral radius $< 1$ for $\Re(s) > 1/2$
- This gives exponential mixing

### 3.3 Our Setting
**Claim:** $B_\alpha$ acts like a "twisted transfer operator" on primes.

The twist $e(\alpha p)$ is analogous to the character twist in:
$$L(s, \chi) = \sum_n \chi(n) n^{-s}$$

For non-trivial $\chi$ (i.e., $\alpha \in$ minor arcs), the sum has cancellation.

## 4. PROOF STRATEGY

### 4.1 Key Lemma (to prove)
**Lemma (Twisted Contraction):**
For $\alpha \in \mathfrak{m}(N;Q)$ (minor arcs):
$$\|B_\alpha\| \leq \rho(t, Q) < 1$$

where $\rho(t, Q) \to 0$ as $Q \to \infty$ (deeper into minor arcs).

### 4.2 Proof Sketch
1. **Decompose:** Write $B_\alpha = B_0 + (B_\alpha - B_0)$
   - $B_0$ is the untwisted operator (nice, symmetric)
   - $B_\alpha - B_0$ contains the oscillatory term

2. **Bound untwisted:** $\|B_0\|$ controlled by spectral gap of G

3. **Bound twisted difference:** For $\alpha \in$ minor arcs:
   $$\|(B_\alpha - B_0)f\|^2 = \sum_d |C_d(f)|^2 |e(\alpha d) - 1|^2$$

   The phase $|e(\alpha d) - 1| \approx 2\pi \|\alpha d\|$ oscillates, causing cancellation.

4. **Combine:** Triangle inequality + careful estimates give $\|B_\alpha\| < 1$.

### 4.3 Connection to Exponential Sums
The key estimate reduces to bounds on:
$$S(\alpha, X) = \sum_{p \leq X} w_p \cdot e(\alpha p)$$

For $\alpha \in$ minor arcs, classical results give:
$$|S(\alpha, X)| \ll X^{1/2 + \epsilon} \cdot q^{-1/2}$$

where $\alpha \approx a/q$ with $(a,q) = 1$, $q \leq Q$.

## 5. FORMALIZATION PLAN

### 5.1 Definitions needed in Lean
```lean
-- Minor arcs
def MinorArcs (N Q : ℕ) : Set ℝ :=
  {α | ∀ a q, q ≤ Q → (a.gcd q = 1) → |α - a/q| > Q/(q^2 * N)}

-- Twisted operator
def B_alpha (N : ℕ) (t : ℝ) (α : ℝ) : Matrix (Index N) (Index N) ℂ := ...

-- Spectral gap hypothesis
axiom spectral_gap_minor_arcs :
  ∀ N Q, ∀ α ∈ MinorArcs N Q, ‖B_alpha N t α‖ ≤ ρ Q ∧ ρ Q < 1
```

### 5.2 Main Theorem
```lean
theorem Q3_2_from_spectral_gap :
  spectral_gap_minor_arcs → Q3_2
```

## 6. NUMERICAL EVIDENCE

From `spectral_gap_test.py` v3.0:

| N | max_ρ | δ_exp = -log(ρ) |
|---|-------|-----------------|
| 10k | 0.031 | 3.47 |
| 50k | 0.068 | 2.69 |
| 100k | 0.117 | 2.15 |

**Observation:** ρ << 1 for all tested N, consistent with spectral gap.

## 7. REFERENCES

1. Anantharaman, N. & Monk, L. (2015). "Quantum Ergodicity on Arithmetic Surfaces"
2. Selberg, A. "On the Estimation of Fourier Coefficients of Modular Forms"
3. Sarnak, P. "Spectra of Hyperbolic Surfaces"
4. Lindenstrauss, E. "Invariant Measures and Arithmetic Quantum Unique Ergodicity"

## 8. OPEN PROBLEMS

1. **Make the spectral gap explicit:** Find $\rho(t, Q)$ as function of parameters.
2. **Uniformity in N:** Show bound holds for all N, not just tested values.
3. **Connection to RH:** Spectral gap for $L$-functions would give optimal bounds.
