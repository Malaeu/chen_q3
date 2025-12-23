# Q3-2: The Operator Bridge (Circle Edition, v2.2)

## 0. Conventions (do-not-break rules)

- **Circle phase**: we write **e(x) := exp(2π i x)**.
  Hence **Re e(x) = cos(2π x)**.
  ⚠️ If you compute cos(·) you MUST carry **2π**.

- **Frequency parameter**: **α ∈ ℝ/ℤ**, i.e. α is taken **mod 1**.
  If you plug a real number like ln(6), the actual circle-frequency is
  **α = frac(ln(6))**, the fractional part in [0,1).

- **Minor arcs** live in the α-world of **e(α n)** (additive), not in **e^{i α log n}** (Mellin).

- We never use **Hilbert–Schmidt / Frobenius** norms to claim cancellation:
  they take absolute values and kill phase interference.
  Interference must be analyzed via **TT\*** / **Rayleigh quotient**.

> Goal of Q3-2: turn **uniform operator contraction on minor arcs**
> into a **uniform minor-arc bound** for the exponential sum S(α).

---

## 1. RKHS environment (finite window model)

### 1.1 Heat-kernel RKHS
Fix parameters **t > 0** and **K > 0**.

- Window: **W_K := [0, K]** (log-scale window).
- Kernel (**heat kernel**):
  $$k_t(u,v) := \exp\!\Big( -\frac{(u-v)^2}{4t} \Big).$$

Let **ℋ_{t,K}** be the finite-dimensional subspace
$$ℋ_{t,K}(N) := \mathrm{span}\{\, k_t(\cdot, \xi_p)\ :\ p \le N,\ \xi_p \le K \,\},$$
where nodes are on the **log scale**
$$\xi_p := \frac{\log p}{2\pi}.$$
(Choosing K ≍ log N / (2π) includes all p ≤ N.)

### 1.2 Feature map + Gram matrix
Let **P_{N,K}** be the index set of primes in the window:
$$P_{N,K} := \{\,p \text{ prime} : p \le N,\ \xi_p \le K\,\}.$$

Define the **feature map** (**Φ**) by
$$Φ : \mathbb{C}^{P_{N,K}} \to ℋ_{t,K}(N),\quad Φ e_p := k_t(\cdot,\xi_p).$$

Define the **Gram matrix** (**G**) by
$$G := Φ^\* Φ,\qquad G_{pq} = \langle k_t(\cdot,\xi_p), k_t(\cdot,\xi_q)\rangle = k_t(\xi_p,\xi_q).$$

Key geometry: since
$$G_{pq} = \exp\!\Big(-\frac{(\xi_p-\xi_q)^2}{4t}\Big) = \exp\!\Big(-\frac{\log^2(p/q)}{16\pi^2 t}\Big),$$
G is near-diagonal in the **multiplicative metric** (p ≈ q).

---

## 2. Prime weights (von Mangoldt sampling)

Define weights (as in RH_Q3-style prime sampling)
$$w(p) := \frac{\Lambda(p)}{\sqrt{p}} = \frac{\log p}{\sqrt{p}}\qquad (p\ \text{prime}),$$
and the diagonal matrix
$$W := \mathrm{diag}( w(p) )_{p\in P_{N,K}}.$$

---

## 3. Additive circle twist (THIS is the correct twist)

For α ∈ ℝ/ℤ define the diagonal **circle twist**
$$U_\alpha := \mathrm{diag}\big( e(\alpha p) \big)_{p\in P_{N,K}}.$$

Define the **twisted prime operator** on the RKHS window:
$$T_\alpha := Φ\, W U_\alpha \, Φ^\* \ :\  ℋ_{t,K}(N) \to ℋ_{t,K}(N).$$

### 3.1 No fake diagonality
Even though **U_α** is diagonal in coefficient space, **T_α is NOT diagonal**
in the kernel vectors {k(·,ξ_p)} because that family is not orthonormal.
All α-dependence is transported through the **Gram geometry**.

### 3.2 Matrix model for the operator norm (the clean object)
Define the "balanced" matrix
$$B_\alpha := G^{1/2}\, W U_\alpha \, G^{1/2}.$$
Then
$$\|T_\alpha\|_{\mathrm{op}} = \|B_\alpha\|_2,$$
where ‖·‖_2 is the usual spectral norm on matrices.

---

## 4. Interference lives in TT*

Define the **energy operator** (positive):
$$Q_\alpha := T_\alpha T_\alpha^\* \ \succeq\ 0.$$

In the balanced matrix model:
$$B_\alpha B_\alpha^\* = G^{1/2} W U_\alpha \, G \, U_\alpha^\* W G^{1/2}.$$

This is the correct place to see phase cancellation:
off-diagonal terms contain the factor **e(α(p-q))**.

⚠️ We do NOT use Gershgorin circles to claim cancellation:
**Gershgorin** uses ∑|off-diagonal|, which destroys phase information.

---

## 5. Minor arcs (Circle Method definition)

Fix a parameter **Q = Q(N)** (typical: Q = N^θ with small θ > 0).

Define **major arcs**:
$$\mathfrak{M}(N;Q) := \bigcup_{1 \le q \le Q} \bigcup_{\substack{1 \le a \le q\\(a,q)=1}} \left\{ \alpha \in \mathbb{R}/\mathbb{Z} : \left|\alpha - \frac{a}{q}\right| \le \frac{Q}{qN}\right\}.$$

Define **minor arcs**:
$$\mathfrak{m}(N;Q) := (\mathbb{R}/\mathbb{Z}) \setminus \mathfrak{M}(N;Q).$$

---

## 6. Hypothesis Q3-2 (Operator Contraction on Minor Arcs)

(**Q3-2 / Circle Edition**)
There exist constants **ρ < 1**, **N₀**, and admissible parameter choices
(t, K, Q(N)) such that for all N ≥ N₀ and all α ∈ 𝔪(N;Q),
$$\|T_\alpha\|_{\mathrm{op}} \le ρ.$$

Interpretation:
- α in minor arcs ⇒ phases **e(α(p-q))** oscillate fast for p≠q,
  suppressing off-diagonal coherence relative to the diagonal mass.

---

## 7. Bridge lemma (Q3-2 ⇒ Q3-1)

### 7.1 The object we must bound (Circle Method sum)
Let
$$S(\alpha;N) := \sum_{n \le N} \Lambda(n)\, e(\alpha n).$$
Q3-1 is the target:
$$\forall \alpha \in \mathfrak{m}(N;Q):\quad |S(\alpha;N)| \ll N^{1/2-\delta}.$$

### 7.2 Representation axiom (the actual "bridge")
To connect S(α;N) to the RKHS operator, we assume a multi-scale representation:

(**Rep(N)**) There exist
- an iteration count **J(N) ≥ c₀ log N** (c₀>0),
- vectors **u_N, v_N** in the coefficient/RKHS model with
  $$\|u_N\|,\ \|v_N\| \ll N^{1/2},$$
- and an error term **Err(α;N)** negligible on minor arcs,

such that for all α in minor arcs:
$$S(\alpha;N) = \langle u_N,\ B_\alpha^{\,J(N)} v_N\rangle + \mathrm{Err}(\alpha;N).$$

("J(N) ≍ log N" encodes the **log-scale / renormalization** idea:
the RKHS window captures one multiplicative scale-step, and repeating it
climbs to size N.)

### 7.3 Deduction (one-line kill)
Assuming **Q3-2** and **Rep(N)**, for α ∈ 𝔪(N;Q):
$$|S(\alpha;N)| \le \|u_N\|\ \|B_\alpha\|^{J(N)}\ \|v_N\| + |\mathrm{Err}(\alpha;N)| \ll N^{1/2}\, ρ^{c₀\log N} + o(N^{1/2}) = N^{1/2-\delta} + o(N^{1/2}),$$
where
$$\delta := c₀\cdot (-\log ρ)\ >\ 0.$$

Thus **Q3-2 ⇒ Q3-1** (minor-arc bound) once the representation axiom is established.

---

## 8. What is left to prove (clean separation of responsibilities)

To complete the program, we need two independent proofs:

1) **Operator side**: prove **Q3-2** (uniform contraction ‖T_α‖ ≤ ρ for α∈minor arcs),
   using interference in **TT\***, not HS norms.

2) **Bridge side**: prove **Rep(N)** (the multi-scale representation of S(α;N)
   via iterates of B_α), typically via smoothing + scale decomposition.

This separation prevents circular logic and makes the pipeline audit-friendly.

---

## Glossary (fast decode)

- **RKHS**: a Hilbert space where evaluation is an inner product with a kernel vector.
- **Heat kernel** k_t: Gaussian localization; enforces near-diagonal Gram geometry.
- **Feature map** Φ: sends a coordinate basis vector to a kernel "atom".
- **Gram matrix** G = Φ*Φ: measures non-orthogonality of kernel atoms.
- **von Mangoldt** Λ(n): weights primes (and prime powers); standard in analytic number theory.
- **Circle Method**: analyzes additive patterns via integrals over α of exponential sums.
- **Major/Minor arcs**: α near rationals a/q vs everything else.
- **TT\***: energy operator that preserves phase interference; correct tool for cancellation.
- **Hilbert–Schmidt/Frobenius** norm: ∑|A_ij|²; kills phase cancellation (do not use for interference).
- **Spectral norm** ‖·‖₂: largest singular value; equals operator norm in finite-dimensional model.
- **Representation axiom Rep(N)**: the explicit bridge from S(α;N) to operator iterates.
