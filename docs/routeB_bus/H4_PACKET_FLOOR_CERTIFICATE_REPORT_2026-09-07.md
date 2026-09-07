# Packet floor certificate — the lower matrix **F** and a certified floor on the test span

**RESULT CODE: `SCALARFLOOR_PACKET_SOURCE_LOWER_MATRIX_CERTIFIED`** (on the 3-dim span of the requested packet). Name formed after `SCALARFLOOR_H4_SOURCE_LOWER_CERTIFIED` of v1 §9; the verdicts define no packet code.

```
span{h4,h5,h6} = span of the requested packet {h4,h5,h6,h4z}   (rank 3, §1)
   certified  0.00115759847705 <= lambda_min(H^-1/2 F H^-1/2) <= 0.00137842121694
   1/1000 = 0.001                          lambda_min >= 1/1000 : TRUE
   F >= 0 on that span: CERTIFIED (§6)  =>  m(h) >= 0 for every h in the span
span{h4,h5,h6,h7} (genuine 4-dim, h7 added here): NOT CERTIFIED at X = 4000 (§8)
```

Every interval below is a numerical certificate (python-flint 0.8 / arb, ball arithmetic throughout, no `float` on the certificate path), CONDITIONAL on the paper theorems of §9. Anything that is not such an interval is **DIAGNOSTIC_NEVER_A_PROOF**.

## 1. The packet, and its exact rank

Each test is `h = eta'' - eta/4`, `eta = eta(z)`, `z = x/delta`, `delta = (log3-log2)/8`, support `[-delta,delta]`, `N = 1` (v1 §7.2: the normalized functional is scale invariant).

| name | eta | k = order of the zero at z = ±1 | deg_z h | m = k−2 |
|---|---|---|---|---|
| h4 | (1−z²)⁴ | 4 | 8 | 2 |
| h5 | (1−z²)⁵ | 5 | 10 | 3 |
| h6 | (1−z²)⁶ | 6 | 12 | 4 |
| h4z | z²(1−z²)⁴ | 4 | 10 | 2 |
| h7 | (1−z²)⁷ | 7 | 14 | 5 |

**The four requested tests are linearly dependent.** (1−z²)⁵ = (1−z²)⁴ − z²(1−z²)⁴, so η₅ = η₄ − η₄z, and since η ↦ η″−η/4 is linear, **h₅ = h₄ − h₄z exactly** — verified as an identity between exact rationals in u = δ^{−2} (`packarb.py`: every coefficient of h₅−h₄+h₄z is `Fraction(0,1)`), not numerically. All four lie in (1−z²)⁴·span{1, 1−z², (1−z²)², z²} = (1−z²)⁴·span{1,z²,z⁴}, **3-dimensional**; η ↦ η″−η/4 is injective on polynomials (η_zz = (δ²/4)η forces a degree drop, so η = 0), hence dim span{h₄,h₅,h₆,h₄z} = 3 and the requested 4×4 **F** and **H** are both exactly singular with kernel c = (1,−1,0,−1).

So "λ_min of the pencil on the 4-dimensional span" is, for the requested packet, a floor on a **3-dimensional** span. Since ℓ₂ at a node is ≈99 % of the cost and is reused across all pairs, a fifth test is nearly free, so **η₇ = (1−z²)⁷ was added** (contributing (1−z²)⁴·z⁶) to attempt a genuine 4-dim statement. Both are reported; only the 3-dim one is certified.

**Pole-nullity.** ∫h e^{±x/2}dx = 0 for every test as an algebraic identity: two integrations by parts move both derivatives onto e^{±x/2}, (e^{±x/2})″ = e^{±x/2}/4 annihilates the integrand, and the boundary terms vanish because η, η′ vanish at z = ±1 (k ≥ 2 for all five). arb confirmation: |∫h e^{±x/2}dx| ≤ 8.6e−115, all five tests, both signs.

## 2. Conventions and the packet objects

Identical to the h₄ report §2 (a = log 2, r = 2^{−1/2}, nonunitary ĥ, γ₂ from RESONANCE (2), t₂ from RESONANCE (10) with p = 2, ℓ₂ = 2Re(γ₂t₂)), re-using the same code (`h4arb.py`, `evalf.py`, `budget.py`). The packet objects are the **unnormalized** ones of v1 §2 (8) / v2 Cor. 1 (6), with w_a = 1 − cos aξ:

    M_ij = −∫ w_a conj(ĥ_i) ĥ_j d₂,  F_ij = −∫ w_a conj(ĥ_i) ĥ_j ℓ₂,  H_ij = <h_i,h_j>,
    M − F ⪰ 0  (v1 (8));   m(Σ c_j h_j) = c*Mc / c*Hc  (v2 (6)).

All h are real and even, so ĥ is real and even and F, M, H are real symmetric (conj(ĥ_i) = ĥ_i). Hence **a certified F ⪰ 0 proves m ≥ 0 on the whole span**, and λ_min of the pencil (F,H) is a certified floor for m there, by v1 Theorem 1 (5)–(6) applied to each Σc_jh_j.

## 3. What is computed rigorously, per entry

    F_ij = [−∫_{|ξ|≤X} w_a ĥ_i ĥ_j ℓ₂^{[J₀]}] + R_euler^{ij} + R_freq^{ij},   X = 4000, J₀ = 90

**(a) ĥ_i — exact.** ĥ_i(ξ) = 2δ Σ_j A_j^i ∫₀¹ z^{2j}cos(δξz)dz, each factor by its entire power series with an enclosed alternating tail. The eight cos-moments j = 0..7 are computed **once per node** and shared by all five tests; only the A-combination differs.

**(b) Euler-sum truncation.** |γ₂| = 1 on ℝ gives |ℓ₂ − ℓ₂^{[J₀]}| ≤ 2ε_{J₀} (v1 (32) with the proved uniform C = 256 of v1 Thm 4 (31)); then, w_a ≥ 0, by Cauchy–Schwarz

    |R_euler^{ij}| ≤ 2ε_{J₀}∫w_a|ĥ_i||ĥ_j| ≤ 2ε_{J₀}(∫w_a|ĥ_i|²)^{1/2}(∫w_a|ĥ_j|²)^{1/2}
                   = 2ε_{J₀}·2π√(H_iH_j) = 4π ε_{J₀} √(H_ii H_jj).

**∫ w_a|ĥ|² = 2πH is exact**: Parseval gives ∫|ĥ|² = 2πH, and ∫cos(aξ)|ĥ|²dξ = 2π(h⋆h)(a) = 0 because the autocorrelation of h lives in [−2δ,2δ] and 2δ = 0.101 < a = log 2. Normalized, the Euler cost is 4πε_{J₀} = 9.4726921e−10 for **every** entry.

**(c) Frequency tail — two rigorous branches, the sharper taken.** η has a zero of order k at z = ±1, η″ one of order k−2, so h = η″−η/4 has one of order exactly **m = k−2** (no cancellation: the η/4 term has order k > m). Then h,…,h^{(m−1)} vanish at ±δ, m integrations by parts give ĥ(ξ) = (iξ)^{−m}∫h^{(m)}e^{−iξx}dx with no boundary term, and one more pair of parts gives

    |ĥ(ξ)| ≤ C_a/|ξ|^{m+1} + C_b/|ξ|^{m+2},   C_a = 2|p^{(m)}(1)| δ^{−m},
    C_b = [2|p^{(m+1)}(1)| + ∫_{−1}^1|p^{(m+2)}|] δ^{−(m+1)},
    ∫_{−1}^1|p^{(t)}| ≤ Σ_{2j≥t}|A_j|(2j)!/(2j−t)!·2/(2j−t+1)   (sharp monomial integral).

m = 2 reproduces (B₃,B₄) of the h₄ report §3(f) to all printed digits (1.16387735517e8, 8.03769798335e10). Using the true m instead of m = 2 is what makes X affordable: for h₆ it turns ξ^{−4} into ξ^{−5} decay and the normalized tail at X = 2000 falls from 1.4e−3 to 1.1e−8. With |ℓ₂| ≤ 2T (T = 13.9371046604, h₄ report §3(f)) and w_a ≤ 2,

    |R_freq^{ij}| ≤ 2T ν_X^{ij},  ν_X^{ij} = 4∫_X^∞ (C_a^i/ξ^{P_i}+C_b^i/ξ^{P_i+1})(C_a^j/ξ^{P_j}+C_b^j/ξ^{P_j+1})dξ,  P = m+1

(the task's formula omits the w_a ≤ 2 factor; it is kept, so the diagonal row is the h₄ report's 2Tμ_X times H_i). **Second, sharper branch**, from the same Cauchy–Schwarz plus the mass identity of (b):

    |R_freq^{ij}| ≤ 2T √(D_i D_j),  D_i := ∫_{|ξ|>X} w_a|ĥ_i|² = 2πH_i − ∫_{|ξ|≤X} w_a|ĥ_i|²,

the compact mass computed on the same nodes with its own Bernstein error. This makes the mass check load-bearing rather than diagnostic and is 5–12× sharper here (§5). The ledger takes the minimum of the two branches per entry.

**(d) Compact quadrature.** Composite Clenshaw–Curtis, panel width w = 0.5, degree n = 36 (37 nodes/panel), doubled by evenness; same rule and same analyticity argument as the h₄ report §3(e) (f analytic on |Im ξ| < 1/2). The **rule does not depend on ρ** — ρ enters only the Trefethen/ATAP Thm 8.2 bound |I−I_n| ≤ 8Mρ^{−n}/(ρ−1) — so the bound was re-derived post hoc (`packequad.py`) from the finished run with ρ optimized and with the semi-**minor** axis R_min = (w/4)(ρ−1/ρ) used for every factor measuring distance to the singularities at Im ξ = ±1/2, the semi-major R_maj = (w/4)(ρ+1/ρ) only for the real extent:

    M_ij(panel) = (1+cosh(a R_min))·‖h_i‖₁‖h_j‖₁ e^{2δR_min}·2 max|γ₂(±ξ)|·(J₀+2)/(2π(½−R_min)²)

with γ₂ enclosed over the rectangle |Re ξ−m| ≤ R_maj, |Im ξ| ≤ R_min and ‖h_i‖₁ ≤ √(2δH_ii). Sweep (1 s per ρ over 8000 panels): ρ = 3.0 → 4.30e−7, 3.4 → 2.70e−8, 3.6 → 9.14e−9, 3.8 → 5.15e−9, **3.9 → 5.02305e−9 (best)**, 4.0 → 6.67e−9 (R_min = 0.469 approaches ½). Against the in-run value 5.136e−6 (ρ = 3, R_maj used as the Im bound) that is a **factor 1023**, at zero cost. Since ‖h_i‖₁‖h_j‖₁/√(H_iiH_jj) = 2δ for every (i,j), the normalized quadrature cost is the same number, 5.1e−10, for all 15 entries.

## 4. The matrices and the ledger

**H** (Gram, exact rational in δ; radii ≤ 5e−11 are pure evaluation width):

```
        h4              h5              h6              h4z             h7
 h4   301750.4468602  335275.9287323  354996.6148082   -33525.4818721  366206.0911109
 h5   335275.9287323  394438.6092387  435956.0770636   -59162.6805064  465018.1461027
 h6   354996.6148082  435956.0770636  498232.3368073   -80959.4622553  545887.0396371
 h4z  -33525.4818721  -59162.6805064  -80959.4622553    25637.1986344  -98812.0549918
 h7   366206.0911109  465018.1461027  545887.0396371   -98812.0549918  611390.6405700
```

**F** (interval: midpoint = rule value, radius = E_quad + E_euler + E_freq + rule ball):

```
 h4    1058.7768 ± 0.298    1134.4038 ± 7.40e-3  1176.4986 ± 2.19e-3   -75.6270 ± 0.447    1198.0097 ± 1.08e-3
 h5    1134.4038 ± 7.40e-3  1260.9338 ± 4.49e-3  1345.4767 ± 9.25e-4  -126.5300 ± 3.26e-3  1401.5229 ± 8.21e-4
 h6    1176.4986 ± 2.19e-3  1345.4767 ± 9.25e-4  1468.5712 ± 8.92e-4  -168.9781 ± 5.14e-4  1558.2303 ± 1.14e-3
 h4z    -75.6270 ± 0.447    -126.5300 ± 3.26e-3  -168.9781 ± 5.14e-4    50.9030 ± 0.0767   -203.5132 ± 5.90e-4
 h7    1198.0097 ± 1.08e-3  1401.5229 ± 8.21e-4  1558.2303 ± 1.14e-3  -203.5132 ± 5.90e-4  1678.8605 ± 1.38e-3
```

**Full ledger** — I_compact is the rule value, the three columns are rigorous upper bounds, E_freq is the min of the two branches of §3(c) (ν-branch shown for comparison):

| entry | I_compact | E_quad | E_euler | E_freq | (ν branch) |
|---|---|---|---|---|---|
| h4,h4 | `1058.7767974790 ± 1.68e-11` | 1.536e-4 | 2.858e-4 | **7.377e-2** | 3.862e-1 |
| h4,h5 | `1134.4038018618 ± 2.56e-11` | 1.757e-4 | 3.268e-4 | 3.088e-3 | 1.868e-2 |
| h4,h6 | `1176.4986155157 ± 4.70e-11` | 1.974e-4 | 3.673e-4 | 2.331e-4 | 1.319e-3 |
| h4,h4z | `-75.62700438281 ± 5.38e-12` | 4.478e-5 | 8.332e-5 | 7.372e-2 | 5.880e-1 |
| h4,h7 | `1198.0096821427 ± 4.94e-11` | 2.187e-4 | 4.069e-4 | 1.354e-4 | 1.354e-4 |
| h5,h5 | `1260.9337825690 ± 1.99e-11` | 2.008e-4 | 3.736e-4 | 1.292e-4 | 9.325e-4 |
| h5,h6 | `1345.4767313145 ± 4.38e-11` | 2.257e-4 | 4.199e-4 | 9.758e-6 | 6.748e-5 |
| h5,h4z | `-126.52998070719 ± 4.66e-12` | 5.120e-5 | 9.526e-5 | 3.086e-3 | 2.870e-2 |
| h5,h7 | `1401.5229018312 ± 4.29e-11` | 2.500e-4 | 4.652e-4 | 7.054e-6 | 7.054e-6 |
| h6,h6 | `1468.5711650848 ± 6.52e-11` | 2.537e-4 | 4.720e-4 | 7.368e-7 | 4.979e-6 |
| h6,h4z | `-168.97811579879 ± 7.18e-12` | 5.755e-5 | 1.071e-4 | 2.330e-4 | 2.041e-3 |
| h6,h7 | `1558.2303259842 ± 5.00e-11` | 2.810e-4 | 5.228e-4 | 5.284e-7 | 5.284e-7 |
| h4z,h4z | `50.90297632438 ± 2.07e-12` | 1.305e-5 | 2.429e-5 | 7.368e-2 | 8.976e-1 |
| h4z,h7 | `-203.51321968856 ± 6.21e-12` | 6.375e-5 | 1.186e-4 | 1.875e-4 | 2.106e-4 |
| h7,h7 | `1678.8604876911 ± 2.61e-11` | 3.113e-4 | 5.792e-4 | 5.676e-8 | 5.676e-8 |

**Diagonal normalized floors F_ii/H_ii** (reference): h4 `[0.0035085369272565, 0.0035090288001811]`; h5 `[0.0031967790273484, 0.0031967826180335]`; h6 `[0.0029475614610419, 0.0029475643932528]`; h4z `[0.0019826370844385, 0.0019883877612301]`; h7 `[0.0027459687480587, 0.0027459716839076]`. All ≥ 1/1000; all but h4z ≥ 1/500.

## 5. Verification

* **V1 — mass, now load-bearing.** Deficits D_i ≤ 2.64645e−3 (h4), 4.63627e−6 (h5), 2.64333e−8 (h6), 2.64324e−3 (h4z), 1.71180e−8 (h7); all in [0, ν_ii] except h7, where the ball noise floor (2.2e−8, float transport over 8000 panels) exceeds the tiny ν₇₇ = 2.04e−9 — there the ν-branch is taken, so nothing is lost. The measured deficits are **5.2× (h4) to 12.2× (h4z) below** the analytic transform tail; that gap is what made the certificate go through.
* **V2 — exact rank identity as a quadrature check.** h₄z = h₄ − h₅ forces I[h₄z,j] = I[h₄,j] − I[h₅,j] for all five j. All five hold inside the computed balls (agreement ~1e−10 on values of order 10²–10³): five independent constraints tying the h₄z row to the h₄ and h₅ rows. H satisfies the same identity exactly.
* **V3 — second quadrature, entirely different node set.** Band [0,1000] under w = 0.5, n = 36 (main) vs w = 0.4, n = 28, ρ = 2.8, 2500 panels, 72 500 nodes, 497.9 s. **All 15 entries overlap**, agreeing to every printed digit (|diff| ≤ 1.4e−10 on values up to 1.7e3).
* **V4 — h₄ diagonal vs the earlier scalar certificate.** F₄₄/H₄₄ ⊂ `[0.0034393623002775, 0.0035782034198665]`, **282.3× tighter** and contained. Consistency check passed.
* **V5 — pole moments** ≤ 8.6e−115 (§1). Max panel ball radius over the whole run **2.56e−26**.
* **V6 — certificate machinery against a foreign channel.** The bisection + interval-Cholesky λ_min routine reproduces `scipy.linalg.eigh(F,H)[0]` to 15 digits on the float diagnostic matrices, fails just above the true value, and degrades correctly when entry balls are widened.

## 6. Positivity certificate — method and result

Plain interval Cholesky is **too lossy for this packet**: F is nearly singular in absolute units (λ_min(F₃) = 0.50121 against entries ~1.5e3, because H₃ itself is nearly singular, λ_min(H₃) = 344.70), so the Schur complements amplify the entry radii ~20× and the third pivot straddles zero. Method used instead — split F = F₀ + Δ, F₀ the (thin) midpoint matrix, |Δ| ≤ R entrywise, then

    lambda_min(F) >= lambda_min(F0) − ‖Δ‖₂,   ‖Δ‖₂ ≤ ‖R‖₂ ≤ min(‖R‖_F, ‖R‖_inf)

(Weyl; for |B| ≤ R entrywise the spectral radius of |B| is dominated by that of R, and ‖R‖₂ ≤ ‖R‖_inf for symmetric R). λ_min(F₀) > s is certified by an interval Cholesky of F₀ − sI, lossless here because F₀ is thin at 400 bits. Success proves **every** symmetric matrix in the hull is positive definite — the exact F included.

| matrix | ok | ‖R‖₂ ≤ | shifted pivots |
|---|---|---|---|
| H span3 | **True** | 1.40e-109 | 3.0175e5, 21912.4, 1928.06 |
| H span4 | **True** | 9.08e-109 | 3.0175e5, 21912.4, 1928.06, 174.875 |
| **F span3** | **True** | 0.0744018 | 1058.70, 45.3412, **2.29573** |
| F span4 | False | 0.0744306 | 1058.70, 45.3412, 2.29557, **−0.868810** |
| F requested 4×4 | False (expected) | — | exactly singular, kernel c = (1,−1,0,−1) |

Kernel check on the requested 4×4: c\*Fc = `[± 0.310]`, c\*Hc = `[± 6.89e-110]`, both contain 0. Plain interval Cholesky on span3 *without* the midpoint split gives a third pivot `[± 3.46]` — it fails, which is why the split is used. Since **F₃ ≻ 0** and the requested packet's span is span{h₄,h₅,h₆}, this also certifies F ⪰ 0 on the requested 4-dim coefficient space: F₄ = LᵀF₃L with L = [[1,0,0,1],[0,1,0,−1],[0,0,1,0]] (columns h₄,h₅,h₆,h₄z), because Σc_ih_i = (c₁+c₄)h₄ + (c₂−c₄)h₅ + c₃h₆.

## 7. Certified pencil floor, and the weakest combinations

    span3 = span{h4,h5,h6} = the requested packet's span
       0.00115759847705 <= lambda_min(H^-1/2 F H^-1/2) <= 0.00137842121694
    span4 = span{h4,h5,h6,h7}: NOT CERTIFIED at X = 4000

The lower endpoint is a bisection on λ with the §6 certificate applied to F − λH (midpoint F₀−λH₀, radius R_F+λR_H); the upper endpoint is the ball-arithmetic Rayleigh quotient of the float minimizing eigenvector, so λ_min is bracketed to 16 % — the gap is entirely the E_freq(h4,h4) row.

**Weakest combinations (float, DIAGNOSTIC_NEVER_A_PROOF).** span3 pencil eigenvalues 0.00134435, 0.00199513, 0.00378886; weakest direction **h4:+0.46088, h5:−1.00000, h6:+0.54725** — an alternating second difference of the family, a narrower and more oscillatory profile than any single member, not any one test. span4 eigenvalues 0.00103194, 0.00134439, 0.00202696, 0.00385199; weakest h4:−0.23569, h5:+0.84065, h6:−1.00000, h7:+0.39450 — again alternating. Enlarging the packet lowers the floor monotonically (3 dims 0.001344 → 4 dims 0.001032 → 5 dims 0.00078 in the float diagnostic).

## 8. Why span4 is not certified, and what would fix it

λ_min(F₄) = 0.0145637 (the extra test makes the family still more collinear: λ_min(H₄) = 13.312) while ‖R‖₂ ≤ 0.07443. The radius is dominated by a **single** entry, E_freq(h4,h4) = 7.377e−2 = 2T·D₄ with D₄ = 2.6e−3 the measured h₄ tail mass beyond X = 4000. Since D₄ ~ X^{−5}, reaching ‖R‖₂ ≈ 0.01 needs D₄ smaller by ~7×, i.e. **X ≈ 5900** — at the observed cost profile (panels near ξ = 4000 take ≈ 30 s of core time each) about 3 further core-hours. Nothing else matters: E_quad and E_euler are ~3e−4 each after §3(d).

## 9. What remains unproved — CONDITIONALs

Unchanged from the h₄ report §7: (1) RESONANCE Lemma 2 (6) and the source identity for ℓ₂; (2) SCALARFLOOR Theorem 1 (5)–(6); (3) SCALARFLOOR Theorem 4 (31), used twice (Euler tail, uniform T) and **not** re-derived here; (4) Trefethen ATAP Thm 8.2; (5) RESONANCE (2)/(10) as the correct source objects at cutoff λ = 1. One addition: **(6) v1 §2 (8) / v2 Corollary 1 (6)** — that M − F ⪰ 0 and m(Σc_jh_j) = c\*Mc/c\*Hc. Without (6) a certified F ⪰ 0 says nothing about m on the span; the verdicts' proof (c\*(M−F)c = ∫w_a|Σc_jĥ_j|²R₂ ≥ 0) is taken as given and was not re-derived here.

Not certified here: plant survival, the frozen PHASEPROOF eta event, m ≥ 0 on the phase class or on any infinite-dimensional subclass, anything about the operator part of d₂. The certificate is inverse-free — no A₂ diagonalization, no dropped mode, no fitted constant.

## 10. Runtime, files, reproduction

Main run: X = 4000, w = 0.5, n = 36, J₀ = 90, 8000 panels × 37 nodes = **296 000 rigorous node evaluations** (2 999 188 J-series calls), 22 processes, **4364.6 s wall** (≈ 26.7 core-hours), `systemd-run --user --unit=pkt_main`. Cross-check run 497.9 s. ρ sweep, assembly, verification: seconds each. ℓ₂ is evaluated once per node and reused for all 15 pairs, and the ĥ_i share one cos-moment cache — that sharing is why a 15-entry packet costs about what one scalar cost.

Scripts (nothing committed; nothing else in the tree touched): `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/h4_cert/packet/` — `packarb.py` (profiles, Gram, tails, exact rank/vanishing identities), `packbudget.py` (ε_J, T, ν_X), `packcert.py` (panel loop, band split, mass), `packequad.py` (post-hoc ρ-optimized Bernstein bound), `packassemble.py` (ledger, positivity, pencil floor), `packverify.py`, `run.sh`. Raw outputs in `.../packet/out/` (`main.txt`, `xcheck.txt`, `assemble.txt`, `verify.txt`, `profiles.txt`, `budget.txt`); job logs in `/home/chirurgie/.claude/jobs/4b35770d/tmp/h4_packet/`.

## 11. Honest gaps in *this* work

* The requested packet is rank 3; the certified statement is a 3-dim span floor, not the 4-dim one the request names. The genuine 4-dim attempt (η₇ added) **fails** at X = 4000.
* A packet floor is evidence about one specific span, gives no bound for the class, and is not monotone-improving: every enlargement of the packet lowered λ_min (§7).
* The earlier h₄ certificate at X = 2000 was correct but loose: the same ρ-optimization and mass-deficit tail applied there would tighten it ~280× at zero cost, so both its `2Tμ_X` and `E_quadrature` rows are improvable as stated.
* `E_freq` still dominates, and is dominated by h₄ alone, whose Gram norm is 12× smaller than h₆'s while its transform tail is the largest (m = 2). The packet's conditioning, not the arithmetic, is the binding constraint — the verdict's "semilocal conditioning" theme showing up in the finite cell.
* The scripts are not registered in `docs/cartographer/TOOLS.yaml` (the task said touch nothing else); by the project's registry rule they "do not exist" until that entry is made.
