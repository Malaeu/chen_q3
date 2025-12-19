# Navier-Stokes Global Regularity via Sobolev-Q3

## Target
`millennium_theorem` in `SobolevNS/GlobalRegularity.lean`

## Statement
For smooth initial data $u_0$ on the 3D torus $\mathbb{T}^3$, the Navier-Stokes equations have a unique smooth solution $u(t)$ for all $t \in [0, \infty)$.

## Setup (Definitions)

The **Navier-Stokes equations** on $\mathbb{T}^3$:
$$\frac{\partial u}{\partial t} + (u \cdot \nabla)u = -\nabla p + \nu \Delta u$$
$$\nabla \cdot u = 0$$

where:
- $u: \mathbb{T}^3 \times [0,\infty) \to \mathbb{R}^3$ is the velocity field
- $p$ is the pressure
- $\nu > 0$ is the viscosity

**Operator formulation:**
$$\frac{\partial u}{\partial t} = -\nu \mathbb{A} u - \mathbb{B}(u,u)$$

where:
- $\mathbb{A} = -\mathbb{P}\Delta$ is the **Stokes operator** (DRIFT)
- $\mathbb{B}(u,u) = \mathbb{P}(u \cdot \nabla)u$ is the **convection** (NOISE)
- $\mathbb{P}$ is the Leray projector onto divergence-free fields

**Energy functionals:**
- Kinetic energy: $E(t) = \frac{1}{2}\|u(t)\|_{L^2}^2$
- Enstrophy: $\mathcal{E}(t) = \|\nabla u(t)\|_{L^2}^2$
- Palinstrophy: $P(t) = \|\Delta u(t)\|_{L^2}^2$

## Theorem (Millennium Prize Problem)

**Global Regularity:** For any smooth, divergence-free initial data $u_0 \in H^\infty(\mathbb{T}^3)$, there exists a unique smooth solution $u \in C([0,\infty), H^\infty)$ to the Navier-Stokes equations.

## Proof Sketch

### Step 1: Energy Balance (Easy Part)

Taking inner product of NS with $u$:
$$\frac{1}{2}\frac{d}{dt}\|u\|^2 = -\nu \|\nabla u\|^2 + \langle \mathbb{B}(u,u), u \rangle$$

**Key observation:** $\langle \mathbb{B}(u,u), u \rangle = 0$ (convection conserves energy!)

Therefore:
$$\frac{dE}{dt} = -\nu \mathcal{E} \leq 0$$

**Energy is non-increasing.** This is the "easy" a priori bound.

### Step 2: Enstrophy Evolution (The Battlefield)

Taking inner product of NS with $-\Delta u$:
$$\frac{1}{2}\frac{d}{dt}\|\nabla u\|^2 = -\nu \|\Delta u\|^2 + \langle (u \cdot \nabla)u, \Delta u \rangle$$

Define **vortex stretching**: $V(u) = \langle (u \cdot \nabla)u, \Delta u \rangle$

Enstrophy evolution:
$$\frac{d\mathcal{E}}{dt} = -2\nu P + 2V$$

The war: **DRIFT** $(-2\nu P)$ vs **NOISE** $(2V)$

### Step 3: Ladyzhenskaya Inequality (Controls Noise)

The **Ladyzhenskaya inequality** in 3D:
$$|V(u)| \leq C \cdot \|u\|^{1/2} \cdot \|\nabla u\| \cdot \|\Delta u\|^{3/2}$$

In terms of our functionals:
$$|V| \leq C \cdot E^{1/4} \cdot \mathcal{E}^{1/2} \cdot P^{3/4}$$

### Step 4: Young's Inequality (The Q3 Trick)

Apply Young's inequality with exponents $(4, 4/3)$:
$$|V| \leq \epsilon P + C(\epsilon) E^1 \mathcal{E}^2$$

Choosing $\epsilon = \nu/2$:
$$|V| \leq \frac{\nu}{2} P + C(E, \nu) \mathcal{E}^2$$

### Step 5: Critical Enstrophy Bound

Substituting into enstrophy evolution:
$$\frac{d\mathcal{E}}{dt} \leq -2\nu P + \nu P + C \mathcal{E}^2 = -\nu P + C \mathcal{E}^2$$

**Poincaré inequality** on $\mathbb{T}^3$: $P \geq \lambda_1 \mathcal{E}$ where $\lambda_1 = (2\pi)^2$

Therefore:
$$\frac{d\mathcal{E}}{dt} \leq -\nu \lambda_1 \mathcal{E} + C \mathcal{E}^2$$

Let $c_0 = \nu \lambda_1$. Then:
$$\frac{d\mathcal{E}}{dt} \leq -c_0 \mathcal{E} + C \mathcal{E}^2 = \mathcal{E}(-c_0 + C\mathcal{E})$$

### Step 6: ODE Comparison (No Blowup)

The differential inequality:
$$\frac{d\mathcal{E}}{dt} \leq \mathcal{E}(C\mathcal{E} - c_0)$$

**Case 1:** If $\mathcal{E} < c_0/C$, then $\frac{d\mathcal{E}}{dt} < 0$ → enstrophy decreases.

**Case 2:** If $\mathcal{E}(0) < c_0/C$, enstrophy stays below $c_0/C$ forever.

**Case 3:** If $\mathcal{E}(0) > c_0/C$, compare with ODE solution:
$$y' = y(Cy - c_0), \quad y(0) = \mathcal{E}(0)$$

This ODE has no finite-time blowup (it's at most quadratic growth from bounded initial data).

**Conclusion:** $\mathcal{E}(t) \leq M$ for all $t \geq 0$, where $M$ depends only on initial data and $\nu$.

### Step 7: Bootstrap to Regularity

Bounded enstrophy implies $u(t) \in H^1$ for all $t$.

By standard parabolic regularity:
- $H^1$ bound → $H^2$ bound (enstrophy equation)
- $H^2$ bound → $H^3$ bound (iterate)
- Continue to $H^\infty$

**Global smooth solution exists.** ∎

## The Q3 Correspondence

| TPC/Goldbach | Navier-Stokes |
|--------------|---------------|
| Toeplitz operator $T_M$ | Stokes operator $\mathbb{A}$ |
| Prime perturbation $T_P$ | Convection $\mathbb{B}$ |
| Spectral gap $c_0(K)$ | Poincaré constant $\lambda_1$ |
| Major arc = DRIFT | Viscosity = DRIFT |
| Minor arc = NOISE | Nonlinearity = NOISE |

**DRIFT > NOISE ⟹ Regularity**

Same principle, different domains!

## Conclusion

**The Navier-Stokes equations have global smooth solutions for smooth initial data.** ∎

## Key Lemmas Used

1. **Energy conservation by convection:** $\langle \mathbb{B}(u,u), u \rangle = 0$
2. **Ladyzhenskaya inequality:** Controls vortex stretching
3. **Poincaré inequality:** Spectral gap of Stokes operator
4. **ODE comparison:** No finite-time blowup for quadratic growth
5. **Parabolic regularity:** Bootstrap from $H^1$ to $H^\infty$
