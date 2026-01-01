# THE GAP: Growth Target P(X)

## Context (what we already proved)

We have a sequence of $N$ twin prime pairs up to $X$:
$$\mathcal{T}(X) = \{p \le X : p \text{ and } p+2 \text{ both prime}\}$$

Define spectral coordinates:
$$\xi_p = \frac{\log p}{2\pi}$$

Define the Gaussian kernel ($t > 0$ fixed):
$$K_{pq} = 2\pi t \cdot \exp\left(-\frac{(\xi_p - \xi_q)^2}{4t}\right) > 0$$

Define the commutator matrix:
$$A_{pq} = (\xi_q - \xi_p) \cdot K_{pq}$$

Define the Gram matrix (also Gaussian, strictly positive definite):
$$G_{pq} = \sqrt{2\pi t} \cdot \exp\left(-\frac{(\xi_p - \xi_q)^2}{8t}\right) > 0$$

Define commutator energy matrix:
$$Q = A^\top A$$

Define the Rayleigh quotient for any vector $\lambda \in \mathbb{R}^N$:
$$R(\lambda) = \frac{\lambda^\top Q \lambda}{\lambda^\top G \lambda} = \frac{\|A\lambda\|^2}{\lambda^\top G \lambda}$$

## What we already PROVED (you may use these)

**Lemma 1 (Cone-Kernel Separation):**
For strictly increasing $\xi_1 < \xi_2 < \cdots < \xi_N$ and $K_{pq} > 0$ for $p \neq q$:
$$\mathcal{C} \cap \ker(A) = \{0\}$$
where $\mathcal{C} = \{\lambda \geq 0, \lambda \neq 0\}$ is the positive cone.

**Lemma 2 (Cone Positivity):**
$$\inf_{\lambda \in \mathcal{C}_1} R(\lambda) = c_1(N) > 0$$
where $\mathcal{C}_1$ is the normalized cone.

**Lemma 3 (Universal Scaling):**
$$\mathrm{Sum}(Q) = \sum_{i,j} Q_{ij} \geq c \cdot N^2 \cdot \mathrm{span}^2$$
where $\mathrm{span} = \xi_N - \xi_1$.

**Lemma 4 (Finite Stabilization SC2):**
If twin primes are finite, then for $X$ large enough, the twin vector $\Phi_X$ is constant, hence $R(\Phi_X) = O(1)$.

## THE OPEN PROBLEM (what we need to prove)

**Growth Target P(X):**
Prove that there exists $\delta > 0$ such that for the uniform vector $\mathbf{1} = (1, 1, \ldots, 1)$:
$$R(\mathbf{1}) = \frac{\mathrm{Sum}(Q)}{\mathrm{Sum}(G)} \geq c \cdot N^\delta$$
for some constant $c > 0$.

## What we KNOW numerically (hints for the prover)

Numerical experiments show:
- $R(\mathbf{1}) \sim 0.08 \cdot N^{0.92}$ (strong growth!)
- $\mathrm{Sum}(Q) \sim N^{2.94}$
- $\mathrm{Sum}(G) \sim N^{2.00}$
- Therefore $R(\mathbf{1}) \sim N^{0.94}$

## Why this matters

If $R(\mathbf{1}) \geq c \cdot N^\delta$ for any $\delta > 0$, combined with SC2 (Lemma 4), we get:
- If twins finite → $R = O(1)$ (by SC2)
- If twins infinite → $N \to \infty$ → $R \geq c \cdot N^\delta \to \infty$

These are INCOMPATIBLE, therefore **infinitely many twin primes exist**.

## Proof Strategy Hints

**Possible approach 1:** From Lemma 3, we have $\mathrm{Sum}(Q) \geq c \cdot N^2 \cdot \mathrm{span}^2$.
If we can show $\mathrm{Sum}(G) \leq C \cdot N^2$ (which is true: $G_{ij} \leq \sqrt{2\pi t}$, so $\mathrm{Sum}(G) \leq N^2 \cdot \sqrt{2\pi t}$),
then $R(\mathbf{1}) \geq (c/C) \cdot \mathrm{span}^2$.
For twin primes, $\mathrm{span} = \xi_N - \xi_1 \sim \log N$, so $R(\mathbf{1}) \geq c' \cdot (\log N)^2$.

**Possible approach 2:** Analyze the row sums of $A$. We proved $\mathrm{row}_0(A) \geq c_0 \cdot N \cdot \mathrm{span}$.
This gives $\mathrm{Sum}(Q) \geq (\mathrm{row}_0(A))^2 \geq c_0^2 \cdot N^2 \cdot \mathrm{span}^2$.

**Possible approach 3:** Use eigenvalue bounds. Since $Q$ is PSD and $\mathcal{C} \cap \ker(Q) = \{0\}$,
the minimum eigenvalue restricted to the cone is positive.

## Formal Statement to Prove

**Theorem (Growth Target):**
Let $N \geq 2$, let $\xi_1 < \xi_2 < \cdots < \xi_N$ be strictly increasing, and let $Q$, $G$ be as above.
Then:
$$\frac{\sum_{i,j} Q_{ij}}{\sum_{i,j} G_{ij}} \geq c \cdot (\xi_N - \xi_1)^2$$
for some universal constant $c > 0$ depending only on $t$.

**Corollary:** If $\xi_N - \xi_1 \to \infty$ as $N \to \infty$ (which happens for primes), then $R(\mathbf{1}) \to \infty$.
