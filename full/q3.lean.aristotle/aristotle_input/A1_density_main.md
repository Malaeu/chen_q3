# A1 Density Theorem

## Setup

Define the Fejér kernel:
$$\Lambda_B(x) = \max(1 - |x|/B, 0)$$

Define the heat kernel:
$$\rho_t(x) = \frac{1}{\sqrt{4\pi t}} \exp\left(-\frac{x^2}{4t}\right)$$

Define Fejér-heat atoms as symmetrized products:
$$\phi_{B,t,\tau}(\xi) = \Lambda_B(\xi - \tau) \cdot \rho_t(\xi - \tau) + \Lambda_B(\xi + \tau) \cdot \rho_t(\xi + \tau)$$

Define the space $W_K$ of test functions:
$$W_K = \{ \Phi : \mathbb{R} \to \mathbb{R} \mid \Phi \text{ is continuous on } [-K,K], \text{supp}(\Phi) \subseteq [-K,K], \Phi(-x) = \Phi(x), \Phi(x) \geq 0 \}$$

Define the atom cone:
$$\text{AtomCone}_K = \left\{ g : g = \sum_{i=1}^n c_i \cdot \phi_{B_i, t_i, \tau_i}, \text{ where } c_i \geq 0, B_i > 0, t_i > 0, |\tau_i| \leq K, B_i \leq K \right\}$$

## Known Lemmas

The following are already proven:
1. Heat kernel integrates to 1: $\int \rho_t(x) dx = 1$
2. Heat kernel mass concentration: For any $\delta > 0$, $\int_{|x| > \delta} \rho_t(x) dx \to 0$ as $t \to 0$
3. Heat kernel is nonnegative: $\rho_t(x) \geq 0$
4. Fejér kernel bounds: $0 \leq \Lambda_B(x) \leq 1$
5. Fejér kernel approximates 1: If $B > K$ then $\Lambda_B(x) = 1$ for $x \in [-K, K]$

## Theorem

Prove that: For all $K > 0$, for all $\Phi \in W_K$, for all $\varepsilon > 0$, there exists $g \in \text{AtomCone}_K$ such that:
$$\sup_{x \in [-K, K]} |\Phi(x) - g(x)| < \varepsilon$$

## Proof Sketch

1. Since $\Phi$ is continuous on the compact set $[-K, K]$, it is uniformly continuous.

2. Use the heat kernel as an approximate identity: the convolution $\Phi * \rho_t$ converges uniformly to $\Phi$ as $t \to 0$.

3. Approximate the convolution integral by a Riemann sum: choose points $\tau_1, \ldots, \tau_n$ in $[-K, K]$ and weights $c_i = \Phi(\tau_i) \cdot \Delta$ where $\Delta$ is the mesh size.

4. This gives an approximation of the form $\sum_i c_i \cdot \rho_t(\cdot - \tau_i)$.

5. To ensure the approximant is in $\text{AtomCone}_K$, multiply each term by the Fejér kernel $\Lambda_B$ with $B$ large enough. Since $\Lambda_B = 1$ on $[-K, K]$ for $B > K$, this doesn't change the values on $[-K, K]$.

6. Symmetrize to ensure evenness: replace $\rho_t(\xi - \tau)$ with $\frac{1}{2}(\rho_t(\xi - \tau) + \rho_t(\xi + \tau))$.
