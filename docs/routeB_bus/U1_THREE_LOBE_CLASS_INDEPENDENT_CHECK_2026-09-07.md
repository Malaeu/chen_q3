# U1CHECK — independent audit of Theorem U1 (PROSHKA_VERDICT_..._REGIONAL_ENERGY_2026-09-07)

Method: own re-derivation of §2–§7 from (U1)=(C1) plus own symbolic (sympy; exact `sqrt2/3/6`, `log`) and numeric (mpmath,
dps 18–30) computation. Scripts `s1 s1b s2f s2g s345 s7b s8 .py` in `/home/chirurgie/.claude/jobs/4b35770d/tmp/u1check/`.
Read set: the verdict, CHAIN §1 (C1) through CHAIN_INDEPENDENT_CHECK, THREE_LOBE_PREFLIGHT. Nothing else opened.
**VERDICT: Theorem U1 is CORRECT as a paper theorem.** Every constant, factor of two and the whole budget reproduce; no
arithmetic error, sign error or dropped term found in §2–§7.

## 1. §2.1 (U3)–(U4) regional log-energy — **CORRECT**

*Polynomial division (sympy, exact).* Splitting `int_{-1}^x` / `int_x^1` of `(x^j-y^j)/(x-y) = sum_r x^{j-1-r}y^r` gives
`L(x^j) = 2H_j x^j - sum_{r=0}^{j-1}(1+(-1)^{r+1})/(r+1) x^{j-1-r}`; I derived it and checked `L_exact - L_formula == 0`
symbolically for `j = 1..5`. Correction terms survive only for odd `r` (degrees `j-2, j-4, ...`), so `L` preserves `P_j`.

*Triangularity + symmetry.* `<f,Lg> = (1/2) int int conj(f(x)-f(y))(g(x)-g(y))/|x-y|` (one-line polarization, asserted in
the text, verified). `L` symmetric on `L^2(J)` and `L(P_{j-1}) ⊂ P_{j-1}` ⟹ `L` preserves `P_{j-1}^perp ∩ P_j = span(l_j)`
⟹ `l_j` eigenvector with the leading multiplier `2H_j`. Numerics: `L(l_j)/l_j` at `x = 0.3, -0.7, 0.91` equals `2H_j` to
15 digits for `j = 1..4` (`2.0, 3.0, 3.666667, 4.166667`). Scale invariance of `L_J` verified by hand (`d/2` in `dy`
cancels `d/2` in `|x-y|`).

*The factor 1/2.* `T := int int_{y<x}|h(x)-h(y)|^2/(2(x-y)) = (1/4) int int_{J^2}|..|^2/|x-y| = (1/2)<h,Lh> = sum_{j>=1}
H_j|<l_j,h>|^2`. On `d = 13/125` both sides agree to `<3e-31` relative for `h = x` (`9.3738666666666667e-5`), `h = x^2`
(`1.0138774186666667e-7`) and `h = 3/7+2x-5x^2/3+7x^3` (`3.7951089651237641e-4`); `2T = <h,Lh>` confirmed separately.
**The factor 1/2 is right.**

*(U4), constant 1, sharpness.* `H_j >= 1` (`j>=1`) ⟹ `T >= ||h||^2 - |int h|^2/d`. On `h = x`: `T = ||h||^2 = d^3/12 =
9.3738666666666667e-5`, mean 0 — attained, so `1` cannot be `2`. ✓ *Only asserted step here:* the `C^1`-polynomial
approximation extending (U3) to `C_c^inf`. It is safe: only the `>=` of (U4) is load-bearing and follows from `T(p_n) ->
T(h)` (`|Δ(h-p)|^2/(2Δ) <= ||(h-p)'||_inf^2 Δ/2`) plus convergence of norm and mean. No gap.

## 2. §2.2 (U5)–(U8) exterior energy — **CORRECT**

*(U5) derived, not copied.* For zero-extended `h`, `||U_t h - h||^2` splits into (both points in `J`), (`x in J`, `x-t <
-d/2` ⟺ `t > x+d/2`) and (`y = x-t in J`, `x > d/2` ⟺ `t > d/2-y`); the last two give exactly `int_J[int_{x+d/2}^inf A +
int_{d/2-x}^inf A]|h|^2 = int_J beta_J|h|^2`. ✓ Numeric check on an asymmetric bump `e^{-1/(1-(t/s)^2)}(1+2t)`, `s =
delta/2`. Refined `(t,y)`-coordinate run: `regional = 0.00398502192884573287`, `exterior = 0.0199102257499775512`,
`D_split = 0.0238952476788233`, `D_direct = 0.0238952476787805` — **rel diff `1.79e-12`**, so (U5) is an identity, not an
inequality, and the exterior term is 83 % of `D` on this bump.

*`beta_J` minimal at the midpoint.* `beta_J'(x) = A(d/2-x) - A(d/2+x) > 0` for `x > 0` because `A` decreases — the text's
one-liner is right. `beta_J(0) = 5.88766150827`, `beta_J(±d/4) = 6.03151882`, `+inf` at the endpoints. ✓

*`A(t) >= 1/(2t)` on `(0,1]`.* `A = e^{t/2}/(2 sinh t)`; `sinh t/t <= cosh t <= e^{t^2/2} <= e^{t/2}` for `t <= 1`.
Verified `min_{(0,1]}(A - 1/(2t)) = 0.20146341 > 0`; here `x-y in (0,d)`, `d = 0.104`. ✓

*(U6) exact.* `int_s^inf A = artanh(w)+arctan(w)`, `w = e^{-s/2}` (from `A = sum_j e^{-(2j+1/2)t}` and `4 sum
w^{4j+1}/(4j+1) = 2(artanh w + arctan w)`); `2 artanh(e^{-d/4}) = log coth(d/8)`; Gudermannian `2 arctan(e^{-d/4}) = pi/2
- arctan(sinh(d/4))`. Hence `2 int_{d/2}^inf A - c_A = log(coth(d/8)/(8pi)) - gamma_E - arctan(sinh(d/4))` — reproduced
**independently**; both sides `0.515478089040232318`, difference `1.3e-18`, `> 1/2`. ✓ Rational chain in exact `Fraction`:
`(1000/13)/(8·22/7) = 875/286` exactly; `log_lower(875/286,3) > 111/100`; `sinh(13/500) <= (13/500)/(1-(13/500)^2) <
27/1000`; `gamma_E < H_4 - log(9/2) = 0.5791766 < 29/50` (the correct justification of the printed convexity line is that
`H_n - log(n+1/2)` decreases to `gamma_E`); `log_lower(9/2,7) > 451/300`; `111/100-29/50-27/1000 = 503/1000 > 1/2`. ✓

*(U7)–(U8).* `D - c_A||h||^2 = [T + int int (A - 1/(2Δ))] + int(beta_J - c_A)|h|^2` and `T = (||h||^2 - |int h|^2/d) +
sum_{j>=2}(H_j-1)|<l_j,h>|^2` give exactly (U7) with remainder (U8). All three remainder terms `>= 0`; the third has slack
`beta_min - c_A - 1/2 = 0.0154780890 > 0`. ✓

## 3. §3 cross terms — **CORRECT**

*No mean / mean-zero cross term.* `<h_i,h_j> = conj(mu_i)mu_j + <g_i,g_j>` since `<1_J,g_j> = 0` and `||d^{-1/2}1_J|| =
1`; the prime pairing at lag `log2` is exactly `Re<h_0,h_1>`, at `log3` exactly `Re<h_0,h_2>` — plain inner products — so
`h*Pi h = mu*Pi mu + g*Pi g`. ✓ Confirmed as asked. `spec(Pi) = {0, ±sqrt(a^2/2+b^2/3)} = {0, ±0.801587691540958} <
81/100`; rational route `389/600 < (81/100)^2` holds. Lag `b-a = log(3/2)` has an archimedean entry and **no** prime atom;
`b+d = 1.2026 < log4 = 1.3863` excludes `k >= 4`. ✓

*Archimedean cross, exact.* Expanding `||U_t v - v||^2` with disjoint lobes, the `t = 0` and `<U_t·,U_t·>` pieces vanish
and only `-2Re sum_{i<j} int int A(x_j-x_i+y-x) conj(h_i(x))h_j(y)` survives — re-derived from (U1). ✓

*Error of the centre replacement.* `x,y in J` ⟹ `|u-(x_j-x_i)| <= d`; MVT gives `|A(u)-A(Δ)| <= d sup|A'|`; `int
int|h_i||h_j| <= ||h_i||_1||h_j||_1 <= d||h_i||||h_j||`, so the entry error is `<= d^2 sup|A'| ||h_i||||h_j||` and the
total `2 sum_{i<j} e_ij ||h_i||||h_j||`. **The prompt's reading is the right one**: the `d^2` is `d` from the MVT × `d`
from the two `L^1 -> L^2` factors, not `d^2` from a length-`2d` argument range. `e_ij = d^2 sup_{|u-Δ|<=d}|A'(u)|` ✓.

*Derivative bounds.* `|A'(t)| = A(t)(1/2 + 2e^{-2t}/(1-e^{-2t}))`, decreasing (from `A = sum e^{-(2j+1/2)t}`), so the sup
sits at the lower endpoint. `|A'(a-d)| = 1.49503412`, chain `(250/237)(5/7)(16/11)(31/22) = 1.5442938 < 8/5` ✓; `|A'(b-d)|
= 0.57559227`, chain `(250/237)(3/5)(36/31)(51/62) = 0.6045917 < 2/3` ✓; `|A'(b-a-d)| = 5.54084527`, chain
`(250/237)(5/6)(9/4)·3 = 5.9335443 < 6` ✓ (tight). Each chain is `e^{d/2}·e^{-Δ/2}` × `1/(1-e^{-2t})` × `(1/2 +
2e^{-2t}/(1-e^{-2t}))` with `e^{2d} < 5/4` — reconstructed. `e_01 = 0.016170 < 1/50`, `e_02 = 0.006226 < 1/100`, `e_12 =
0.059930 < 7/100`. ✓ `E = [[0,1/50,1/100],[1/50,0,7/100],[1/100,7/100,0]]` has `||E||_2 = 0.07595167 < 9/100` ✓ (with the
true sups, `0.06388038`).

*(U11)–(U12).* Summing (U7) over the lobes gives `(3/2)H - ||mu||^2 = (3/2)||g||^2 + (1/2)||mu||^2` — that is the origin
of `I_3/2` in `M` — plus `mu*(Pi - dN)mu` from the prime and archimedean means, minus `(81/100)||g||^2` and `(9/100)H`;
`3/2 - 81/100 = 69/100`. **(U12) reproduces exactly.** ✓

## 4. §4 kernel and moment error — **CORRECT**

`Vz = (0,0)` exactly, `||z||^2 = 12`, sympy `nullspace` is 1-dimensional ⟹ `ker V = span(u)`. ✓ `V mu = -e` derived from
`M_±(v) = sum_i e^{±x_i/2}(m_i + int h_i(e^{±x/2}-1)) = 0`, divided by `sqrt d`. **`47/6` reconstructed:** `|e_±| <= eta
(sum_i e^{±x_i})^{1/2} sqrt H` with `sum e^{x_i} = 1+2+3 = 6` and `sum e^{-x_i} = 1+1/2+1/3 = 11/6`, so `||e||^2 <= eta^2
H (6+11/6)`. ✓ `VV* = [[6,3],[3,11/6]]`, `det(VV*-I/4) = 5/48 > 0`, `spec(VV*) = {0.264232, 7.569101}` ⟹ `sigma_min >
1/2`. ✓ `eta = e^{d/4}-1 = 0.0263409485 <= 13/487`, `sqrt(47/6) = 2.79880927 < 14/5`, `2 eta sqrt(47/6) = 0.147446582 <
3/20`; the printed `2(13/487)(14/5) = 0.14948665 < 0.15` holds with 0.35 % slack. (U13) ✓. `tau` genuinely unconstrained —
confirmed, no small-mean assumption.

## 5. §5 (U14)–(U15) — **CORRECT (exact symbolic match)**

`A(log2) = 2sqrt2/3`, `A(log3) = 3sqrt3/8`, `A(log(3/2)) = 3sqrt6/5` — sympy `simplify(diff) == 0`. ✓ `z*Pi z/12 =
(2a-b)/6 = log(4/3)/6`; `z*Nz = -1049/60` ⟹ `-d z*Nz/12 = +1049d/720`. sympy: `u*Mu - [1/2 + log(4/3)/6 + 1049d/720] == 0`
**exactly**; value `0.69946923429751904 > 69/100` (rational route `1/2+1/21+1049d/720 = 0.69914127`). ✓ `M =
[[.5,-.58818121,-.70183408],[-.58818121,.5,-.15284816],[-.70183408,-.15284816,.5]]`, `||M||_2 = 1.34402437 < 2` (max abs
row sum `1.79001529`; printed row bounds `1/2+d`, `33/50+21d/32`, `3d/2` all hold). `Mz` matches `(b-2a-1/2-37d/24,
sqrt2(1+a/2+37d/15), sqrt3(b/3-1/2-81d/40))` **symbolically**; numerically `(-0.948015, 2.267136, -0.596511)`, `||Mu||^2 =
0.53287187 < 1` (printed envelope `((6/5)^2+(5/2)^2+1)/12 = 0.72416667 < 1`). ✓

## 6. §6 (U16) budget — **CORRECT**

`mu*Mmu >= (69/100)|tau|^2 - 2|tau|·||Mu||·||r|| - ||M||·||r||^2 >= (69/100)|tau|^2 - 2|tau|||r|| - 2||r||^2`. With
`(69/100)(||g||^2+|tau|^2) = (69/100)(H - ||r||^2)`, `|tau| <= sqrt H`, `||r||^2 <= (9/400)H`, the `||g||^2` terms cancel
identically and `Q >= [69/100 - 9/100 - 3/10 - (69/100)(9/400) - 2(9/400)]H = [69/100-9/100-3/10-(69/100+2)(9/400)]H`.
Both groupings evaluate in exact `Fraction` to **`9579/40000 = 0.239475 > 1/5`**. ✓ I ran the appendix ledger myself:
**all 22 asserts pass**, `EXACT_RATIONAL_LEDGER_PASS 9579/40000`. Geometry also exact: `2delta = 0.1013663 < d = 0.104`
(needs `log(3/2) < 52/125`, true, 2.6 % margin), `d < b-a`, `d < 2a-b = 0.2876821`, `b+d < log4`, `2/3 < a < 7/10`, `1 < b
< 11/10`. ✓

## 7. Consistency with the certified packet — **CONSISTENT**

The preflight's frozen 7-dim packet (`phi_0 = eta, phi_1 = eta', phi_2 = eta''-eta/4` on `|x| < delta/2 ⊂ I`,
total-moment-null) is a subspace of U1's class. Certified `lam_min = 1.7443269450324643 ± 2.7e-19` vs. the theorem's
guaranteed `0.239475` — the theorem's constant sits **7.28× below** the certified floor, as it must. The unrestricted
9-dim `lam_min = 1.0124107` is also far above. On the preflight's own mean vector `z ⊗ phi_0`, `Q/||f||^2 = 1.8131597` vs
guaranteed `>= 0.2395` ✓ (ratio 7.57). No conflict: the budget is a coarse envelope, not the true constant. **Own
independent floor** on a different, wider profile family (`phi_p = eta·P_p(x/delta)`, `p = 0,1,2`, half-width `delta` not
`delta/2`; 9 generators, exact 7-dim total-moment kernel, `cond(G_7) = 33`): `lam(Q,G) = 1.119913 … 3.413400`, **floor
`1.1199 > 9579/40000`** (4.7× margin); unrestricted 9-dim floor `0.50187`; `z⊗phi_0` gives `1.165708` here against the
preflight's `1.813160` — expected, the bump is twice as wide, not a discrepancy. Theorem U1 holds on a packet the
preflight never touched.

## 8. §7 (U17)–(U19) localization — **CORRECT**

`Theta = 1 - sum chi_j(x)chi_j(y) = (1/2) sum (chi_j(x)-chi_j(y))^2 >= 0` needs and uses `sum chi_j^2 = 1`. ✓ `sum_j
C_{chi_j f}(t) = C_f(t) - C_{Theta,f}(t)`, hence: norms cancel the `c_A` term; archimedean adds `+2 int A C_Theta`; primes
add `+2 sum w_k C_Theta(log k)`; the pole, via **`2Re(M_+ conj(M_-)) = 2 int_R e^{t/2}C_f(t)dt = 4 int_0^inf
cosh(t/2)C_f(t)dt`** (re-derived here from `M_+conj(M_-) = int e^{t/2}R(t)dt` with `R(-t) = conj R(t)`), subtracts `4 int
cosh(t/2)C_Theta`. (U18) reproduces exactly; `Theta = O(t^2)` kills the `1/(2t)` singularity.

*Numeric end-to-end confirmation*, printed bump, `chi = (cos,sin)` (`Theta(x,x+t) = 1-cos t`; no prime atoms):

    Q(f) = 0.005982994424777188   Q(f cos) = 0.005982637288181289   Q(f sin) = 6.880849207e-7
    sum_j Q(chi_j f) - Q(f) = 3.309483247838961e-07   (direct, from (U1))
    E_chi via (U18)         = 3.309483247838961e-07   (formula)   -- 16 digits

`||f||^2 = sum||chi_j f||^2 = 0.00332715302112` ✓. `min_{(0,1/20]}(A - 2cosh(t/2)) = 8.2482553 > 2`, so `E >= 4
int_0^{1/20}(1-cos t)C_f = 2.4349772e-8`: the printed envelope holds with 13.6× slack and `Q(f) - sum_j Q(chi_j f) =
-3.3095e-7 < 0`. **(U19)'s sign logic is right.** Two caveats, both already in the document: `chi = (cos,sin)` is a
partition of unity but not a *local* one, so what is refuted is the literal shape `Q(f) >= sum Q(chi_j f)`; the structural
obstruction (`Theta = 1` beyond the cover diameter; `M_±(f) = 0` does not give `M_±(chi_j f) = 0`) is the substantive
point and is correctly stated. `Q(f) > 0` here — no RH bearing, as claimed.

## 9. (U20) regularizer monotonicity — **CORRECT**

`d/dε (B+ε)^{-1} = -(B+ε)^{-2}` ⟹ `dS/dε = G + E*(B+ε)^{-2}E ≻ 0` (needs only `G ≻ 0`). Scalar example `S(ε) =
1+ε-4/(1+ε)`: `S(0) = -3`, `S(0.999) = -0.0020005`, `S(1) = 0`, `S(2) = 5/3 > 0` — positivity propagates **upward** in `ε`
only; automatic descent to `1/n` is falsified. ✓

## 10. Overall

**Theorem U1 is CORRECT as a paper theorem.** No CRITICAL/HIGH/MEDIUM/LOW defect found; the proof is self-contained given
(C1) and imports no positivity, no RH surrogate, no numerical eigenvalue. **First asserted-not-derived step.** Literally
first: the symmetry identity for `L` in §2.1 (one-line polarization, true). First *substantive* one: the
`C^1`-polynomial-approximation / completion passage carrying (U3)–(U4) from polynomials to `C_c^inf(I)` — three sentences,
load-bearing for all of §2. I verified it: the needed direction is only `T(h) = lim T(p_n) >= lim(||p_n||^2 - |int
p_n|^2/d)`, elementary; the full identity (U3) off polynomials is never used. Other asserted-but-true one-liners: (U5)
itself, `beta_J` minimal at the midpoint, `|A'|` decreasing. All four re-derived here.

**Tight spots (no failures, no room either).** `2(13/487)(14/5) = 0.1494867 < 3/20` (0.35 %); `(250/237)(5/6)(9/4)·3 =
5.9335 < 6` (1.1 %); `log(3/2) = 0.405465 < 52/125` for `2delta < d` (2.6 %). A referee who perturbs `d` or `delta` breaks
these three first.

**Scope, plainly.** The class is infinite-dimensional in the *profiles* but the *geometry is frozen*: three lobes at `0,
log2, log3`, half-width `delta = (log3-log2)/8`, `J` of length `13/125`. "Whole declared infinite-dimensional space" must
not be read as "all supports". The document says so (§8) and does not overclaim: `UNIVERSAL_SIGN_PROVED: false`,
`PX_RH_CLAIM: NOT_MADE`, `RH_CLAIM: false` are accurate. `THREE_LOBE_LOWER_BOUND: 1/5`, `EXACT_RATIONAL_BUDGET:
9579/40000`, `LOSSLESS_LOCALIZATION_PROPAGATION: REFUTED_THEOREM_SHAPE`, `SOURCE_LOCALIZATION_DEFECT_IDENTITY:
PROVED_PAPER`, `REGULARIZER_MONOTONICITY_PROVES_TARGET: false` are all justified by what I checked. `CLOSES:
CHAIN_C22_..._at_PAPER_level` is justified; CHAIN (C22) may be marked PAPER-proved.

**Registrations — my adjudication.**
- `P_REGIONAL_LOG_LEGENDRE_CONSTANT_SURVIVES` (0.94) — **ACCEPT**. Every factor of two checked independently (`2H_j`; the
  `1/2` in (U3); the `1` in (U4) and its sharpness on `h = x`; the two boundary halves of `beta_J`). 0.94 is too low; on
  this evidence ~0.99.
- `P_THREE_LOBE_ONE_FIFTH_FLOOR_SURVIVES` (0.82) — **ACCEPT**. (U2), (U9)–(U16) hold for arbitrary complex profiles under
  only the two total moment equations; `tau` never set to zero, the `b-a` archimedean entry never deleted, budget
  reproduced in exact rationals. 0.82 is too low; ~0.97. The residual risk is not the sign but the three tight rational
  margins above.
- `P_LOCALIZATION_SOURCE_DEFECT_SURVIVES` (0.96) — **ACCEPT**. (U17)–(U18) confirmed to 16 digits end-to-end **including
  the full pole term**, which I re-derived rather than copied.

**What this does not do.** Nothing here touches (U21), the full `S_1`, or RH; U1's three short intervals are not the full
test space; the (C25) computational receipt remains a different event, as the document itself says.
