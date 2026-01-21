# Cone-Kernel Separation Lemma

## Setup
Let $\xi_1 < \xi_2 < \cdots < \xi_N$ be strictly increasing points on $\mathbb{R}$.
Let $K \in \mathbb{R}^{N \times N}$ be a symmetric matrix with $K_{pq} > 0$ for all $p \neq q$.
Define $A \in \mathbb{R}^{N \times N}$ by $A_{pq} = (\xi_q - \xi_p) \cdot K_{pq}$.
Let $\mathcal{C} = \{\lambda \in \mathbb{R}^N : \lambda_p \geq 0, \lambda \neq 0\}$ be the positive cone.

## Theorem
Prove that $\mathcal{C} \cap \ker(A) = \{0\}$.

## Proof Sketch
Let $\lambda \in \mathcal{C} \setminus \{0\}$ and let $S = \{p : \lambda_p > 0\}$.
Choose $p^* \in S$ with maximum $\xi_{p^*}$.
Consider $(A\lambda)_{p^*} = \sum_q (\xi_q - \xi_{p^*}) K_{p^*q} \lambda_q$.
- For $q > p^*$: $\lambda_q = 0$ by choice of $p^*$.
- For $q = p^*$: factor is zero.
- For $q < p^*$: each term is $\leq 0$.

Case (a): If $S = \{p^*\}$, then for any $p < p^*$: $(A\lambda)_p = (\xi_{p^*} - \xi_p) K_{p,p^*} \lambda_{p^*} > 0$.
Case (b): If there exists $q < p^*$ with $\lambda_q > 0$, then $(A\lambda)_{p^*} < 0$.

In both cases, $A\lambda \neq 0$.
