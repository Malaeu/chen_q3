# Universal Energy Scaling

## Setup
Let $\xi_0 < \xi_1 < \cdots < \xi_{N-1}$ be $N$ strictly increasing points on $\mathbb{R}$.
Define the spectral span: $\mathrm{span} = \xi_{N-1} - \xi_0$.

Let $K \in \mathbb{R}^{N \times N}$ be the Gaussian kernel:
$$K_{ij} = 2\pi t \cdot \exp\left(-\frac{(\xi_i - \xi_j)^2}{4t}\right)$$
where $t > 0$ is a fixed parameter.

Define the commutator matrix $A \in \mathbb{R}^{N \times N}$ by:
$$A_{ij} = (\xi_j - \xi_i) \cdot K_{ij}$$

Define $Q = A^\top A$ (the commutator energy matrix).

Define $\mathrm{Sum}(Q) = \sum_{i,j} Q_{ij}$.

Define the row sum of $A$:
$$\mathrm{row}_k(A) = \sum_{j=0}^{N-1} A_{kj}$$

## Key Algebraic Identity
Prove that:
$$\mathrm{Sum}(Q) = \sum_{i,j} Q_{ij} = \sum_k \left(\mathrm{row}_k(A)\right)^2$$

## Proof of Identity
Since $Q = A^\top A$, we have $Q_{ij} = \sum_k A_{ki} A_{kj}$.
Therefore:
$$\mathrm{Sum}(Q) = \sum_{i,j} Q_{ij} = \sum_{i,j} \sum_k A_{ki} A_{kj}
= \sum_k \sum_i A_{ki} \sum_j A_{kj} = \sum_k \left(\sum_i A_{ki}\right)^2
= \sum_k \left(\mathrm{row}_k(A)\right)^2$$

## Boundary Row Lower Bound (Lemma)
Prove that the first row satisfies:
$$\mathrm{row}_0(A) = \sum_{j=1}^{N-1} (\xi_j - \xi_0) K_{0j} \geq c_0 \cdot N \cdot \mathrm{span}$$
for some constant $c_0 > 0$ depending only on the kernel parameter $t$.

## Proof Sketch for Lemma
1. All terms in the sum are positive: $(\xi_j - \xi_0) > 0$ for $j > 0$, and $K_{0j} > 0$.
2. For a lower bound, note that $\xi_j - \xi_0 \geq (j/N) \cdot \mathrm{span}$ on average.
3. The Gaussian factor $K_{0j} \geq 2\pi t \cdot e^{-\mathrm{span}^2/(4t)}$ is bounded below.
4. Summing: $\mathrm{row}_0(A) \geq \sum_{j=1}^{N-1} (j \cdot \mathrm{span}/N) \cdot K_{\min}
   \geq K_{\min} \cdot \frac{\mathrm{span}}{N} \cdot \frac{N(N-1)}{2} \geq c_0 \cdot N \cdot \mathrm{span}$.

## Main Theorem (Universal Energy Scaling)
Prove that:
$$\mathrm{Sum}(Q) \geq c \cdot N^2 \cdot \mathrm{span}^2$$
for a constant $c > 0$ depending only on the kernel parameter $t$.

## Proof of Main Theorem
Using the algebraic identity and the boundary row lemma:
$$\mathrm{Sum}(Q) = \sum_k \left(\mathrm{row}_k(A)\right)^2 \geq \left(\mathrm{row}_0(A)\right)^2
\geq (c_0 \cdot N \cdot \mathrm{span})^2 = c_0^2 \cdot N^2 \cdot \mathrm{span}^2$$
Setting $c = c_0^2$ completes the proof.
