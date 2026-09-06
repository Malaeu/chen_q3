# OPENCHECK — independent check of PROSHKA_VERDICT_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06

Read: the OPEN verdict + §3, §8 of the SECOND_EXPRESSION verdict (definitions only). Everything
below is my own re-derivation plus python3 (sympy/mpmath/numpy) runs in this directory:
`item1_sym.py`, `item1_direct.py`, `item12_general.py`, `remainder.py`, `item3.py`, `item3b.py`,
`lemma4.py`, `item5.py` (log `item5.out`).

## 1. Judge's own calibration X(z) = z — **CORRECT**

Exact (sympy closed form, not fitted): Ω_p = **p/(p+1)**; Ĵ_p = (1/π)∫xη/(p²+x²)dx = **1/(p+1)** so J_pq = **1/(p+1) − 1/(q+1)**, and
J_pq − (Ω_q−Ω_p) = **0** (=(29)); r_p = Ω_p − 1/(1−κ_p) = **0**, h_pq = **0**; (17)−(21) = **0** and
(18)−(21) = **0** identically in (p,q), with L₊₊K_N = 1/(p²q²); (P): Ω_p − ip/(ip+i) = **0**.
So (L++) = (L+−) = 0 — the remainder vanishes for the toy, as claimed.

**Independent channel (uses neither (17) nor (18)).** For X(z)=z, κ_p = −1/p ⇒ L[g'](p) = −1/p² ⇒
g'(t) = −t, g(t) = −t²/2. Building the signed Volterra data literally (α = 1/(x−i), β = x/(x−i),
A_t = ∫₀ᵗe^{−ixr}dr, B_t = ∫₀ᵗe^{−ix(t−r)}g'(r)dr) gives the **collapse S_t(x) = t/(x−i)** (analytic;
numeric to 1e−31), hence K_N = (1/π)∫S_t conj(S_u)dx = tu, while K_A = g(t−u)−g(t)−g(u) = **tu**.
Numerics: (0.7,1.3) → 0.91; (2.0,−0.4) → −0.80; (−1.1,−0.6) → 0.66. So (OPEN) does hold for X(z)=z,
confirming the calibration from a second direction; K_N(−t,−u) = K_N(t,u) confirmed on those points.

**Second, non-toy stress test of (17)/(18)** (`item12_general.py`), X(x) = x²+1 (even, but with
non-real zeros ±i), κ_p = 2p/(1−p²), g'(t) = −2 sinh t, p = 1.7, q = 2.9:
(20) and its negative-time twin reproduce to 3e−27; the x-integration step of Lemma 5 (partial
fractions + parity), checked *without* the final formula, matches [2+(ab−1)(Ω_p+Ω_q)+(b−a)J]/(p+q)
to **6e−35** and the +− numerator to **7e−34**. (16): |J_pq| = 0.14386 ≤ |log(q/p)|/π = 0.17000 ✓,
0 < Ω_p < 1 ✓. (L++)/(L+−) from (17)–(18)–(21): sympy residual **0**. (22)/(23): (17) at q=p gives
((κ²−1)Ω_p+1)/p³ vs (21) −κ/p³ ⇒ (κ²−1)Ω_p = −(κ+1), i.e. Ω_p = 1/(1−κ_p); and L₊₊ of
−Σw_n[δ(t−u∓ℓ_n)] at p=q is −(1/p)ΣΛ(n)n^{−p−1/2} = (23) ✓. Lemma 4 (16a): digamma/Lerch bookkeeping
re-derived by hand (Σ_j1/((j+α)(j+β)) = (ψ(β)−ψ(α))/(β−α), β = s/2), c_A + ψ(1/4) − log π = **1.7e−21**;
at p = 2, (16a) = −0.0918342717 vs −ξ'/ξ(2.5) = −0.0918342715 (2.4e−10 = prime-series truncation).

## 2. p = q cancellation of the η-part — **CORRECT**; two symmetries, not one

L₊₊V_η(p,q) = (1/(π pq))∫ iη(x)(κ_q−κ_p)/((p+ix)(q−ix))dx = (κ_q−κ_p)J_pq /(pq(p+q)).

* **(S1), the operative one.** The Volterra structure makes the two half-line Laplace transforms
  *proportional as functions of x*: ∫₀^∞e^{−pt}A_t dt = 1/(p(p+ix)) and ∫₀^∞e^{−pt}B_t dt =
  **κ_p**/(p(p+ix)) — same x-profile, scalar ratio κ_p. The η-term is the antisymmetric (wedge)
  combination L[A](p)·conj(L[B](q)) − L[B](p)·conj(L[A](q)), a 2×2 determinant of two proportional
  vectors; it is exactly (κ_q−κ_p)×(profile) and dies when κ_p = κ_q, i.e. p = q (κ strictly
  decreasing by (25)). This step needs η = αβ̄ = βᾱ to be **real**, i.e. X, X' real on ℝ.
  Numerically confirmed: for the toy LB/LA = −1.11111 at p = 0.9 and −0.434783 at p = 2.3 (= −1/p).
* **(S2), independent.** Parity in x: η is odd (Ξ even ⇒ Ξ' odd) and at p = q the weight
  1/((p+ix)(p−ix)) = 1/(p²+x²) is even ⇒ J_pp = 0.

So the vanishing is of **second order** in (q−p). Numeric on X = x²+1: η-part of L₊₊ is exactly 0
at p = q ∈ {1.7, 2.5}, and 0.03178001757 at (1.7, 2.9) = (b−a)J/(p+q) ✓.
The restriction "positive time parameters" in §0 is necessary: in (18) the η-term at q→p has the
non-zero limit [−(1+κ²)Ω'_p + 2κ ∂_qJ]/p², so nothing cancels in the +− quadrant.
Consequence drawn in §0/§3 (η alone cannot carry the prime atoms, since (23) < 0) is **sound**.

## 3. Lemma 7 step 3 ⇒ 2 (boundary / Hilbert) — **CORRECT**

* Boundary value. Folding x → −x (legitimate: ω even) gives Ω(ε+iy) = (1/π)∫ω(x)/(ε+i(y−x))dx;
  with ε/(ε²+u²) → πδ(u) and −i u/(ε²+u²) → −i PV(1/u) the limit is ω(y) − iℋω(y) in the judge's
  sign convention. Numeric (toy, breakpoints at x = ±y — **without** them mpmath silently
  mis-integrates the near-poles at x = ±y): y = 0.7, ε = 1e−7 → 0.328859083 + 0.469798595i vs
  ω+iη = 0.328859060 + 0.469798658i; y = 2.5 → 0.862068956 + 0.344827577i vs 0.862068966 + 0.344827586i.
* F/(F+F') at p = iy equals X(−y)/(X(−y)+iX'(−y)) = X(y)/(X(y)−iX'(y)) = ω + iη — this uses the
  parity of X (works for X even *and* odd); zeros with X = X' = 0 are removable by local
  factorization. Hence η = −ℋω. ✓
* **ℋQ_p = −P_p**: my own residue/partial-fraction computation
  PV∫ x dx/((x²+p²)(y−x)) = −πp/(p²+y²) (the A/(y−x) and Bx/(x²+p²) pieces vanish under symmetric
  truncation, C = −p²/(p²+y²) gives Cπ/p), so ℋQ_p(y) = −p/(π(p²+y²)) = −P_p(y). Numeric
  (subtracted-singularity PV, R = 1e7): 12 (p,y) pairs, |ℋQ_p + P_p| ≈ 2.0e−8 = the log-truncation
  error, one quadrature outlier at (0.4, 5.0). Direct ℋω for the toy: −0.469798613 vs −η = −0.469798658.
* Skew-adjointness: ⟨−ℋω, Q_p−Q_q⟩ = ⟨ω, −P_p+P_q⟩ = Ω_q − Ω_p ⇒ h_pq = 0. Legitimate: Q_p−Q_q is
  odd, O(x^{−3}), of **zero integral** (an H¹ atom), ω ∈ L^∞, ℋω = −η bounded — the BMO constant
  ambiguity of ℋω is killed by the zero mean. The judge does not name this; a strengthening, not a gap.

## 4. §5's exclusion of zeros of F in Re p > 0 — **CORRECT, no gap found**

Re(p/(p²+x²)) = ½Re(1/(p−ix)+1/(p+ix)) = ½[σ/(σ²+(τ−x)²)+σ/(σ²+(τ+x)²)] > 0 for σ = Re p > 0,
ω ≥ 0 and ω ≢ 0 (its zeros are isolated), integrand O(x^{−2}) ⇒ Ω holomorphic on Re p > 0 with
**Re Ω(p) > 0**. If F = (p−p₀)^m h, h(p₀) ≠ 0, dividing (28) by (p−p₀)^{m−1} gives
[m h + (p−p₀)(h+h')]Ω = (p−p₀)h, and at p₀: **m h(p₀)Ω(p₀) = 0** ⇒ Ω(p₀) = 0, contradiction. The
continuation of (P) from the ray p > ½ to Re p > 0 is the identity theorem applied to the
*holomorphic* function (F+F')Ω − F (no division by a possibly-vanishing F+F'), so (28) is safe.
Empirical confirmation of the mechanism on a plant with a right-half-plane zero of F
(X = x²+1, F = 1−p², zero at p = 1): Ω_p stays in (0,1) — 0.7224 (p=0.6), 0.7236 (1.7), 0.7671 (2.9),
0.7862 (3.5) — while F/(F+F') = −1.1429, 0.3573, 0.5609, 0.6164. (P) fails everywhere, and
J_pq = 0.14386 ≠ Ω_q−Ω_p = 0.04353, i.e. h_pq ≠ 0 exactly as Lemma 7's step 3⇒2 requires.
This makes explicit that (P) is at least as strong as RH; the judge says so himself
(§5, `THIS_IS_NOT_A_WEAKER_RH_PREMISE: true`), so it is a disclosed consequence, not a hidden gap.
Side checks: κ_p = −F'/F < 0 and κ'_p = −Var_p < 0 follow from F(p) = ∫Φ(t)e^{pt}dt with Φ > 0 even
(Riemann's theta representation) ✓. Plants: H1(ip) = (1−16p²)cosh 8p has the simple zero p = ¼ ✓;
for H2, Re(−i(π+i·arcosh 2)/4) = arcosh 2/4 > 0 and cos(4δ) = −2 ✓.

## 5. Numerical test of (P) for the true Ξ — **CORRECT (agrees within the tail bound)**

Method: ω(x) = 1/(1 + m(x)²), m = X'/X = i·(ξ'/ξ)(½+ix) (real) — checked against
Ξ²/(Ξ²+Ξ'²) computed from ξ and mp.diff (agreement to 20 digits at x = 3, 20). 649 zeta zeros
below 1000 as panel breakpoints, panels subdivided to ≤ 3, 16-node Gauss–Legendre, mp.dps = 20.
LHS = (2p/π)∫₀^{Xmax} ω/(p²+x²)dx (integrand even). RHS = 1/(1+(ξ'/ξ)(½+p)).
| p | RHS | LHS[0,300] | RHS−LHS(300) | crude bound 2p/(π·300) | LHS[0,1000] | RHS−LHS(1000) | crude 2p/(π·1000) | refined tail est. | residual |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 0.955898725182 | 0.955302621899 | 5.961e−4 | 2.122e−3 | 0.955744960408 | 1.5376e−4 | 6.366e−4 | 1.738e−4 | −2.00e−5 |
| 2 | 0.915889916727 | 0.914697724543 | 1.1922e−3 | 4.244e−3 | 0.915582387537 | 3.0753e−4 | 1.273e−3 | 3.475e−4 | −4.00e−5 |

Both gaps are **inside** the crude bound. Refined tail = (2p/π)·⟨ω⟩/Xmax with ⟨ω⟩ = 0.27296 on
[800,1000] (0.32730 on [200,300], 0.29158 on [500,600] — slow decay). Two signatures that the residual
gap *is* the tail, not a defect of (P): (i) (RHS−LHS(1000))/p = 1.5376e−4 for **both** p; exactly the
p-scaling of (2p/π)∫_{1000}^∞ω/x²dx; (ii) the implied ⟨ω⟩ over [1000,∞) is 0.2415, consistent with the
measured drift. Relative agreement ≈ 1.3·10⁻⁴ at Xmax = 1000.

## Summary
| item | verdict |
|---|---|
| 1 toy calibration Ω_p, J_pq, zero remainder of (17)/(18)/(L++)/(L+−) | **CORRECT** (exact; plus S_t = t/(x−i) ⇒ K_N = K_A = tu, independent) |
| 2 p = q vanishing of the η part in the ++ quadrant | **CORRECT** (wedge degeneracy L[B] = κ_p L[A], reinforced by x-parity ⇒ second-order zero) |
| 3 Lemma 7 boundary value, η = −ℋω, ℋQ_p = −P_p, J_pq = Ω_q − Ω_p | **CORRECT** (ℋQ_p = −P_p verified analytically and numerically) |
| 4 §5 exclusion of zeros of F in Re p > 0 | **CORRECT**, no gap; the consequence (⇒ RH) is disclosed by the judge |
| 5 (P) at p = 1, 2 for the true Ξ | **CORRECT** within the tail bound; residual explained by the tail to 13% |

§9's registered predictions score **CONFIRMED** here: `..._LAPLACE_FORMULAS_INDEPENDENT` — (17),
(18), (L++), (L+−) survive with no sign or factor change; `..._POISSON_DISPERSION_REDUCTION_INDEPENDENT`
— Lemma 7 needs no extra hypothesis (only the un-named, and satisfied, H¹/BMO pairing detail).
Scope: this checks the algebra and the reduction only. It says nothing about (P) being provable —
and item 4 confirms that proving it would prove RH.
