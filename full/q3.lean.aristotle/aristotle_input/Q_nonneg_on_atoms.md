# Q Nonnegativity on Atom Cone

## Setup

Define the spectral coordinate:
$$\xi_n = \frac{\log n}{2\pi}$$

Define the prime weight:
$$w_{\text{RKHS}}(n) = \frac{\Lambda(n)}{\sqrt{n}}$$

where $\Lambda$ is the von Mangoldt function.

Define the node set for compact parameter $K$:
$$\text{Nodes}(K) = \{n \in \mathbb{N} : |\xi_n| \leq K, n \geq 2\}$$

Define the archimedean kernel $a^*(\xi) > 0$ (positive for all $\xi$).

Define the archimedean constant:
$$c_0(K) = \inf_{|\xi| \leq K} a^*(\xi) > 0$$

Define the Fejér kernel:
$$\Lambda_B(x) = \max(1 - |x|/B, 0)$$

Define the heat kernel:
$$\rho_t(x) = \frac{1}{\sqrt{4\pi t}} \exp\left(-\frac{x^2}{4t}\right)$$

Define Fejér-heat atoms as symmetrized products:
$$\phi_{B,t,\tau}(\xi) = \Lambda_B(\xi - \tau) \cdot \rho_t(\xi - \tau) + \Lambda_B(\xi + \tau) \cdot \rho_t(\xi + \tau)$$

Define the atom cone:
$$\text{AtomCone}_K = \left\{ g : g = \sum_{i=1}^n c_i \cdot \phi_{B_i, t_i, \tau_i}, \text{ where } c_i \geq 0, B_i > 0, t_i > 0, |\tau_i| \leq K \right\}$$

Define the Q functional:
$$Q(g) = \int a^*(\xi) \cdot g(\xi) \, d\xi - \sum_{n \geq 2} w_Q(n) \cdot g(\xi_n)$$

where $w_Q(n) = 2 \cdot w_{\text{RKHS}}(n)$.

## Assumptions

Assume the A3 Bridge property holds:
There exist $M_0 \in \mathbb{N}$ and $t > 0$ such that for all $M \geq M_0$ and all nonzero vectors $v \in \mathbb{R}^M$:
$$\frac{\sum_{i,j} v_i v_j \left( T_M[a^*]_{ij} - \sqrt{w_{\text{RKHS}}(i)} \sqrt{w_{\text{RKHS}}(j)} e^{-(\xi_i - \xi_j)^2/(4t)} \right)}{\sum_i v_i^2} \geq \frac{c_0(K)}{4}$$

Assume the RKHS contraction property holds:
There exist $t > 0$ and $\rho < 1$ such that for any finite node set and corresponding matrix $T_P$ defined by:
$$T_P[i,j] = \sqrt{w_{\text{RKHS}}(i)} \sqrt{w_{\text{RKHS}}(j)} \exp\left(-\frac{(\xi_i - \xi_j)^2}{4t}\right)$$
we have $\|T_P\| \leq \rho$.

## Theorem

Prove that: For all $K \geq 1$, if the A3 Bridge property holds and the RKHS contraction property holds, then for all $g \in \text{AtomCone}_K$:
$$Q(g) \geq 0$$

## Proof Sketch

1. For a single atom $\phi_{B,t,\tau}$, the arch term gives a positive contribution due to $a^*(\xi) > 0$.

2. The prime term is bounded by the RKHS contraction: since $\|T_P\| < 1$, the prime sampling cannot dominate.

3. The A3 bridge ensures that the Toeplitz approximation to the archimedean part dominates the prime part by at least $c_0(K)/4$.

4. By linearity of $Q$ and nonnegativity of coefficients in atom cone, $Q(g) \geq 0$ for all $g$ in the cone.
