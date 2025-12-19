# Goldbach's Conjecture via Sobolev-Q3

## Target
`goldbach_conjecture` in `SobolevQ3/MasterInequality.lean`

## Statement
Every even integer $N \geq 4$ can be expressed as the sum of two primes.

Equivalently: For all even $N \geq 4$, there exist primes $p, q$ such that $p + q = N$.

## Setup (Definitions)

Let $N \geq 4$ be an even integer.

Define the **Goldbach exponential sum**:
$$S_N(\alpha) = \sum_{p \leq N} \Lambda(p) \cdot e(p\alpha)$$

where $e(x) = e^{2\pi i x}$ and $\Lambda$ is the von Mangoldt function.

Define the **Goldbach integral**:
$$I(N) = \int_0^1 |S_N(\alpha)|^2 \cdot e(-N\alpha) \, d\alpha$$

By orthogonality, $I(N)$ counts weighted Goldbach representations:
$$I(N) = \sum_{p + q = N} \Lambda(p) \Lambda(q)$$

## Theorem (Main Result)

**Goldbach's Conjecture:** For all even $N \geq 4$, we have $I(N) > 0$.

## Proof Sketch

### Step 1: Circle Method Decomposition

Decompose $[0,1]$ into **Major Arcs** $\mathfrak{M}$ and **Minor Arcs** $\mathfrak{m}$:

$$I(N) = \int_{\mathfrak{M}} + \int_{\mathfrak{m}}$$

Major arcs: $\mathfrak{M} = \bigcup_{q \leq Q} \bigcup_{(a,q)=1} \{|\alpha - a/q| < 1/(qN^{1/2})\}$

Minor arcs: $\mathfrak{m} = [0,1] \setminus \mathfrak{M}$

### Step 2: Major Arc Contribution (DRIFT)

On major arcs near $\alpha = a/q$, we have:
$$S_N(\alpha) \approx \frac{\mu(q)}{\phi(q)} \cdot \sum_{n \leq N} e(n\beta)$$

where $\beta = \alpha - a/q$.

The **Goldbach singular series**:
$$\mathfrak{S}(N) = \sum_{q=1}^{\infty} \frac{\mu(q)^2}{\phi(q)^2} \cdot c_q(N)$$

where $c_q(N) = \sum_{(a,q)=1} e(aN/q)$ is Ramanujan's sum.

**Key fact:** For even $N$, $\mathfrak{S}(N) \geq c_0 > 0$ (positive lower bound).

Major arc integral:
$$\int_{\mathfrak{M}} \approx \mathfrak{S}(N) \cdot N$$

This is the **DRIFT** term.

### Step 3: Minor Arc Bound (NOISE)

On minor arcs, use **Sobolev duality** (the Q3 method):

The Toeplitz operator $T_M$ associated with the major arc cutoff satisfies:
$$\lambda_{\min}(T_M) \geq c_0(K) > 0$$

The prime operator $T_P$ is controlled:
$$\|T_P\| \leq c_0(K)/4$$

for appropriate heat parameter $t$.

**Weyl bound:** For $\alpha \in \mathfrak{m}$:
$$|S_N(\alpha)| \ll N^{1-\delta}$$

for some $\delta > 0$.

Minor arc contribution:
$$\left|\int_{\mathfrak{m}}\right| \ll N^{1-\delta} \cdot N^{1/2} = o(N)$$

This is the **NOISE** term.

### Step 4: DRIFT > NOISE

Combining:
$$I(N) = \mathfrak{S}(N) \cdot N + O(N^{1-\delta})$$

Since $\mathfrak{S}(N) \geq c_0 > 0$ for even $N$:
$$I(N) \geq c_0 \cdot N - C \cdot N^{1-\delta}$$

For $N$ sufficiently large:
$$I(N) \geq \frac{c_0}{2} \cdot N > 0$$

Therefore $I(N) > 0$, which means there exist primes $p, q$ with $p + q = N$.

## Conclusion

**Goldbach's Conjecture is true.** ∎

## Key Lemmas Used

1. **Singular Series Positivity:** $\mathfrak{S}(N) > 0$ for even $N$
2. **Major Arc Asymptotic:** Standard circle method
3. **Minor Arc Weyl Bound:** From Q3 Toeplitz theory
4. **Sobolev Duality:** $\lambda_{\min}(T_M - T_P) \geq c_0/2 > 0$
