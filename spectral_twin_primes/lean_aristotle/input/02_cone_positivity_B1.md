# Cone Positivity (B₁-strong)

## Setup (from previous lemma)
We have the Cone-Kernel Separation lemma established:
- $\xi_1 < \xi_2 < \cdots < \xi_N$ strictly increasing points
- $K \in \mathbb{R}^{N \times N}$ symmetric with $K_{pq} > 0$ for $p \neq q$
- $A_{pq} = (\xi_q - \xi_p) \cdot K_{pq}$
- $\mathcal{C} = \{\lambda \in \mathbb{R}^N : \lambda_p \geq 0, \lambda \neq 0\}$ (positive cone)
- **Proven:** $\mathcal{C} \cap \ker(A) = \{0\}$

## Additional Definitions
Define the Gram matrix $G \in \mathbb{R}^{N \times N}$ to be symmetric positive definite.

Define the commutator energy:
$$E_{\mathrm{comm}}(\lambda) = \lambda^\top A^\top A \lambda = \|A\lambda\|^2$$

Define the lattice energy:
$$E_{\mathrm{lat}}(\lambda) = \lambda^\top G \lambda$$

Define the Rayleigh quotient:
$$R(\lambda) = \frac{E_{\mathrm{comm}}(\lambda)}{E_{\mathrm{lat}}(\lambda)}$$

Define the normalized cone:
$$\mathcal{C}_1 = \{\lambda \in \mathcal{C} : E_{\mathrm{lat}}(\lambda) = 1\}$$

## Corollary (Cone Positivity B₁-strong)
Prove that:
1. Let $Q = A^\top A$. Then $\mathcal{C} \cap \ker(Q) = \{0\}$.
2. The Rayleigh quotient $R(\lambda)$ achieves a positive infimum $c_1 > 0$ on $\mathcal{C}_1$.

## Proof Sketch
1. **Kernel equivalence:** $\ker(A^\top A) = \ker(A)$ (standard linear algebra).
   Proof: If $A^\top A x = 0$, then $x^\top A^\top A x = \|Ax\|^2 = 0$, so $Ax = 0$.
   Conversely, $Ax = 0$ implies $A^\top Ax = 0$.

2. **Apply Cone-Kernel Separation:** By the established lemma,
   $\mathcal{C} \cap \ker(A) = \{0\}$, hence $\mathcal{C} \cap \ker(Q) = \{0\}$.

3. **Positivity on $\mathcal{C}_1$:**
   - $E_{\mathrm{comm}}(\lambda) = \|A\lambda\|^2 > 0$ for all $\lambda \in \mathcal{C}_1$
     (since $\lambda \notin \ker(A)$ by step 2)
   - $E_{\mathrm{lat}}(\lambda) = 1$ on $\mathcal{C}_1$ by definition
   - So $R(\lambda) > 0$ for all $\lambda \in \mathcal{C}_1$

4. **Infimum is positive:** The normalized cone $\mathcal{C}_1$ is a closed bounded
   subset of a compact set (the unit sphere in the $G$-norm). Since $R$ is continuous
   and strictly positive on $\mathcal{C}_1$, its infimum $c_1 = \inf_{\mathcal{C}_1} R > 0$.
