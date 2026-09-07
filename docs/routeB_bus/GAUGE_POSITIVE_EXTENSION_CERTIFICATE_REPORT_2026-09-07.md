# GAUGE POSITIVE-EXTENSION CERTIFICATE — (20) holds for the pole-gauged remainder

**RESULT CODE: `GAUGE_SOURCE_POSITIVE_EXTENSION_CERTIFIED`**

Rigorous ball-arithmetic (arb, 300 bits) certificate that

    p(xi) + FT(chi R_g)(xi) > 0    for every real xi,      R_g = R + 2 alpha cosh(t/2),  alpha = 519/1000,

with `R = K_T - c S` the remainder of the Schur kernel identity (6) of
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07.md`
and `chi` the verdict's own fixed quintic smoothstep (= 1 on `[-2delta,2delta]`, = 0 outside `(-d0,d0)`).
The whole line is covered by a strictly positive lower envelope; no band is left straddling zero.
Conventions: `a = log 2`, `d0 = a/4`, `delta = (log3-log2)/8`, `I = (-delta,delta)`,
`c = cosh(a/2)-1`, `c_* = 2 pi c a`, `hhat(xi) = int h e^{-i xi x} dx`.

---

## 1. The gauge lemma (exact algebra)

**Lemma 1 (pole gauge).** Let `H_00 = { h in L^2(I) : int h e^{x/2} = int h e^{-x/2} = 0 }`. For every
real `alpha` the two translation-invariant kernels `K_T(t)` and `K_T(t) + 2 alpha cosh(t/2)` define the
**same** quadratic form on `H_00`.

*Proof.* `2 cosh((x-y)/2) = e^{(x-y)/2} + e^{-(x-y)/2} = e^{x/2} e^{-y/2} + e^{-x/2} e^{y/2}`. Both summands
are rank one and factor across the two arguments, so

    int int 2 alpha cosh((x-y)/2) h(x) conj(h(y)) dx dy
      = alpha (int h(x) e^{x/2} dx)(int conj(h(y)) e^{-y/2} dy)
      + alpha (int h(x) e^{-x/2} dx)(int conj(h(y)) e^{y/2} dy)
      = alpha [ M_+ conj(M_-) + M_- conj(M_+) ],   M_± = int h(x) e^{±x/2} dx.

On `H_00` both moments vanish, so the added form is identically zero. QED.

**Lemma 2 (gauged (13)).** For `h in H_00` supported in `I`,

    ||h||^2 F(h) = (1/2pi) int [ p(xi) + FT(chi R_g)(xi) ] |hhat(xi)|^2 dxi,      (13g)

for every `alpha`. *Proof.* (13) of the verdict is (6) plus the fact that the compressed forms of two
kernels agree whenever the kernels agree on `I - I = (-2delta, 2delta)`; here `2delta = 0.1013663 < d0 =
0.1732868`, so `chi = 1` on `I - I`. Apply the gauge **before** the cutoff: `K_T + 2 alpha cosh` has
remainder `R_g` in (6), `chi R_g` still lies in `W^{1,1}_c`, and the compressed form is unchanged by
Lemma 1. QED.

Consequence: `(20)` for `R_g` is a **sufficient** condition for `F(h) >= 0` on the whole of `H_00`, exactly
as `(20)` for `R` is in the verdict — but with one free real parameter that the ungauged statement lacks.
This matters because `(20)` for `R` is numerically **false** (`SCHUR_INDEPENDENT_CHECK_2026-09-07`
headline 3: `R` is essentially constant `-1.02`, `||chi R||_1 = 0.28476`, and `p + FT(chi R) < 0` on
roughly `[0.13, 110]`). The gauge cancels precisely that constant.

## 2. alpha, fixed before the rigorous run

`alpha = 519/1000` — the minimiser of `||chi R_g||_1` in the float sweep of
`gauge/gauge_test.py`, rounded to three decimals, then **frozen**. It is not tuned to the certificate.
The certificate has slack for every `alpha` in roughly `[0.505, 0.535]`; the reported margins are for
`519/1000` only (`2 alpha = 1.038` against `-R(0) = 1.0481361`).

## 3. Certificate logic — two constants, no band scan

Write `F(xi) = FT(chi R_g)(xi) = 2 int_0^{d0} chi(t) R_g(t) cos(xi t) dt` (even, real). Put

    A := || chi R_g ||_{L1(R)}        =>  |F(xi)| <= A          (trivially)
    B := || (chi R_g)' ||_{L1(R)}     =>  |F(xi)| <= B / |xi|   (one integration by parts; no boundary term)

Verdict (12) gives `p(xi) >= c_* / (2pi + |xi|)` for all `xi`, and `p(xi) >= c_* / |xi|` for `|xi| >= 2pi`.
Hence

* `|xi| <= 2pi`:  `p + F >= c_*/(4pi) - A > 0`  provided `A < c_*/(4 pi)`;
* `|xi| >= 2pi`:  `p + F >= (c_* - B)/|xi| > 0`  provided `B < c_*`.

The two half-lines meet at `2pi`, so **two scalar inequalities certify the entire real line**. `xi = 0` is
covered because `p` blows up logarithmically there. This replaces the verdict's `(21)/(22)` route
(truncation index `J`, `D_J`, `e_J`, plus a compact-band enclosure): the gauge makes `A` small enough that
the compact band disappears.

## 4. The enclosure of R and R'

`R` is not evaluated from `(5)` directly — the log singularities of `K_T` and `c S` only cancel in the
limit. The exact regrouping (7) is used, re-derived here and matched against `(5)`:

    R(t)  = (c/2) Q(t) - (sqrt2/4) G(t) - 2 pi Ntilde(t)
    Q(t)  = sum_{j>=0} [ q_{b_j}(t) + q_{b_j}(-t) ],   q_b(t) = e^{t/2} L(b(e^t-1)) - L(b t),  b_j = 2 pi 2^j
    G(t)  = e^{t/2} L(2pi(1-e^t)) + e^{-t/2} L(2pi(1-e^{-t}))
    Ntilde= N_0 - (1/2) N_+ - (1/2) N_-,   N_s = the double series (5) at u = t+s, s in {0,+a,-a},
            with the exactly resonant difference terms (i,j >= 0, i-j = ± s/a) deleted.

`Q = D - 2S` because `L` is even and `L(b(1-e^t)) = L(b(e^t-1))`. The coefficient collection that the
verdict leaves to the reader, `1 - r/2 - sqrt2/2 = -c`, is what produces `(c/2)` here.

**Bounds used (all re-derived, all conservative).** From `|Si| <= Si(pi) = 1.851937` and
`L = Si(z)/z = int_0^1 (-log u) cos(zu) du`:

    |L(z)|   <= min(1, 4/|z|)
    |L'(z)|  <= min(|z|/9, 5/z^2)
    |L''(z)| <= min(1/9, (1 + 6.7038/|z|)/z^2)

and, for `0 < |t| <= d0` (using `|e^t-1| >= 0.91813|t|`, `|e^t-1-t| <= 0.59461 t^2`):

    |q_b(t)|                 <= 5.91/b                                     (tail of Q)
    |q'_b(t) - q'_b(-t)|     <= 4.76/(b|t|) + 25.4/(b t^2)                 (tail of Q')

Separation of the nonresonant pairs: with `kappa = (e^{-d0} - 1/2)/2 = 0.1704482`,
`|b_i - b_j e^{u}| >= kappa max(b_i,b_j)` and `b_i + b_j e^{u} >= 0.42042 max(b_i,b_j)` for every
nonresonant `(i,j)` and every `|t| <= d0`, `s in {0,±a}`. All exact resonances involving the index `-1`
have max index `<= 0`, hence sit inside the retained finite part. With `2n+3` pairs at max index `n`:

    per-pair value bound      <= 1.83350 * 2^{-n}          (script uses 1.834)
    per-pair derivative bound <= 32.89735 * 2^{-n}         (script uses 32.90)
    tails of -2 pi Ntilde, Ntilde'  <= 2pi * 2 * const * (2 J_N + 7) 2^{-J_N}

`J_N = 24`. `L` and `L'` are evaluated by the entire power series for `|z| <= 4` and by arb's `si` for
`|z| >= 0.4`; for `|z| >= 10^8` the bounds `4/|z|`, `5/z^2` are used directly. The series threshold is `4`,
not `12`: at `|z| ~ 10` the alternating series loses ~2 orders to interval dependency (this was the first
run's failure — mid-values correct, radii of order 1).

**Region I, `t in [0, 10^-3]`.** Ball evaluation of `Q'` is useless near `0` (the terms
`b L'(b(e^t-1))` and `b L'(bt)` are individually of size `b` and cancel). Instead, three pointwise bounds
on `|q'_b(s)|` are combined and integrated in closed form:

    B1 = 0.5453 + 0.3231 b^2 s^2 ;   B2 = 1.2507 + 16.693/(b|s|) ;   B3 = 13.917/(b|s|) + 10.933/(b s^2)

split at `s_1 = min(t2, 1/b)` and `s_2 = min(t2, 3.1/sqrt(b))`. Summed over `j`:
`sum_j int_0^{t2} |w_{b_j}| <= 0.0990554`. `G'` and `Ntilde'` have no small-`t` pathology and are enclosed
by a **single** ball evaluation on `[-t2, t2]`. This yields `int_0^{t2} |R'| <= 0.00337356`, and
`|R_g| <= |R_g(t2)| + int_0^{t2}|R'|` gives the region-I part of `A`.

**Region II, `t in [10^-3, d0]`.** Graded grid, `2579` cells, relative half-width `phi = 0.001`
(`t_{k+1}/t_k = 1.002002`), with `2delta` forced as a node. Each cell: one ball `t = [mid ± halfwidth]`,
`R` and `R'` enclosed as above with an adaptive `J_q` (`52` at `t = 10^-3`) chosen so the `Q'` truncation
tail is below `10^-9`, `chi` and `chi'` enclosed on the same ball, and

    dA = 2 w * sup |chi R_g| ,      dB = 2 w * sup |chi' R_g + chi R_g'| .

Only upper bounds are needed, so the whole computation is one directed sum.

## 5. Ledger

| quantity | rigorous enclosure | threshold | ratio | verdict |
|---|---|---|---|---|
| `A = ||chi R_g||_1` | `<= 0.00346180830291` | `c_*/(4 pi) = 0.0210232135207` | `0.16467` | PASS |
| `B = ||(chi R_g)'||_1` | `<= 0.122854776540` | `c_* = 0.264185492606` | `0.46503` | PASS |
| region I `[0,10^-3]` | `A_I <= 2.803e-5`, `B_I <= 0.00674764` | | | |
| region II `[10^-3,d0]` | `A_II <= 0.00343378`, `B_II <= 0.11610713` | | | |

Constants (arb, 25 digits): `a = 0.6931471805599453094172321`, `d0 = 0.1732867951399863273543080`,
`delta = 0.05068313851352054774725164`, `c = 0.06066017177982128660126654`,
`c_* = 0.2641854926063318675554258`, `kappa = 0.1704482076268572715155627`.

Run: arb `prec = 300` bits, `J_N = 24`, `2579` cells, `233 s`, zero crude `L`-fallbacks.
Raw per-cell balls: `/home/chirurgie/.claude/jobs/4b35770d/tmp/gauge_cert/out/gauge_cert.txt` (2598 lines).

**Margins.** The certificate's own margins are `1 - A/thr_A = 0.835` on `|xi| <= 2pi` and
`1 - B/c_* = 0.535` on `|xi| >= 2pi`. The *true* margin is much better: the float diagnostic gives
`min (p+F)/p = 0.8082 at xi = 27.27`, `p + F > 0` on `[10^-3, 10^5]` with no negative grid point, and
`min (p+F) = 2.62e-6 at xi ~ 10^5` (that is `p` itself). Tail ratio `B/c_* = 0.465`.

## 6. Verification by other channels

| # | channel | result |
|---|---|---|
| (i) | gauge lemma on random moment-null `h` (float, 3 draws) | added form `3e-38 … 3e-37` against `\|\|h\|\|^2 ~ 0.2` — invisible |
| (ii) | `R` vs the independent checker's spot values | `R(2delta) = -1.030388` (checker `-1.03039`), `R(10^-6) = -1.048136` (checker `-1.04814`) |
| (ii') | `(7)`-decomposition vs direct `(5)` evaluation, `J = 70` | agree to `2.0e-12` at `t = 10^-4 … d0` |
| (ii'') | arb enclosure vs the numpy/scipy float path | `R(0.05) = -1.0430`, `R(0.1) = -1.0308`, `R(0.15) = -1.0121`, `R'(0.05) = 0.187`, `R'(0.15) = 0.454` — agree |
| (iii) | `h4` end-to-end through `(13g)` | `(1/2pi) int [p+F] \|h4hat\|^2 / \|\|h4\|\|^2 = 0.0035088` vs the ratified scalar floor `0.0035088`; identical **with and without** the gauge |
| (iv) | `\|\|chi R\|\|_1` without gauge | `0.284761` (checker `0.28476`) |

(iii) is the strong test: it closes the loop through `p`, through `FT(chi R_g)`, through `(13)`, and
through the independently ratified `h4` floor, and it shows the gauge is invisible on `H_00` at the level
of an actual test function.

## 7. Conditionals — what is PAPER and not kernel-verified

1. The kernel identity `(5)`–`(8)` and the representation `(13)` are **Proshka PAPER derivations**
   (`NEW_DERIVATIONS: SCOPE ABSTRACT, VERIFIER PAPER, LEAN_KERNEL_VERIFIED false`). They have been
   re-derived and checked end-to-end numerically twice (independent checker 2026-09-07; here again), but
   they are not Lean-verified. Everything below `(13)` in this report is rigorous **given** `(13)`.
2. Bound `(3)` on `L, L', L''` is re-derived here from `|Si| <= Si(pi)` and the integral representation;
   the constants used are strictly weaker than the sharp ones.
3. The floor value `0.0035088` for `h4` is quoted from the ratified scalar-floor line, used only as a
   cross-check, never as an input.
4. Arithmetic is arb ball arithmetic throughout the certificate path; no float value enters `A`, `B`, or
   the thresholds. Floats appear only in the diagnostics of §6 and in the `alpha` sweep of §2.

## 8. What is proved and what is not

**Proved (modulo the conditionals of §7).** `p + FT(chi R_g) >= 0` on all of `R`. By Lemma 2 and
verdict `(13)`, for every `h in H_00` supported in `I`,

    ||h||^2 F(h) = (1/2pi) || sqrt(p + FT(chi R_g)) hhat ||_2^2  >= 0 ,

i.e. the scalar floor `F(h) = - int (1 - cos a xi) ell_2 |hhat|^2 / ||h||^2` is **nonnegative on the entire
moment-null class**, not only on the eight frozen tests or the high-modulation family. This is verdict
`(24)`, the minimal original scalar inequality, and it turns
`DECISIONS: WHOLE_CLASS_SCALAR_POSITIVITY: NOT_PROVED` into a positive statement for this class. Adding
the second source square of `(2)`, `m(h) = F(h) + ||T_{v_h} D_2||_{HS}^2 >= 0` on the whole pole-null
minus class. It is the first **class-level** result on this front; every earlier positive statement was a
finite packet or an asymptotic family.

**Not proved.** (a) Nothing outside `H_00` on the fixed window `I` — no other window, no other Euler
factor, no removal of the two pole constraints. (b) Not RH: `ROUTE: CHALLENGER_NOT_RH`,
`PX_RH_CLAIM: NOT_MADE` are unchanged. The chain from `(24)` to the published Weil criterion on all
compact smooth tests is not closed by this. (c) Nothing about the sign of `I + K_rel` of verdict Theorem 2
beyond what `(20)` implies; the finite negative inertia question is answered *for this class* and left
open in general. (d) `(20)` for the **ungauged** `R` remains false — the positive extension is a property
of the gauged kernel and of `H_00`, and would not survive relaxing the moment conditions.

**On the free parameter.** Only `alpha` is available for a translation-invariant extension: the kernels
`e^{±(x+y)/2}` are not difference kernels and cannot be absorbed into `K_T(x-y)`. The extension need not
be translation-invariant in principle; it was not needed here.

## 9. Files

    scripts   /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/h4_cert/gauge/gauge_cert_core.py
              /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/h4_cert/gauge/gauge_cert.py
              (pre-existing float diagnostics: gauge_test.py, item8_ext.py)
    raw balls /home/chirurgie/.claude/jobs/4b35770d/tmp/gauge_cert/out/gauge_cert.txt
    logs      /home/chirurgie/.claude/jobs/4b35770d/tmp/gauge_cert/run2.log
    float     /home/chirurgie/.claude/jobs/4b35770d/tmp/gauge_cert/{float_probe.py,float_B.py,verify.py,margin.py}

Reproduce: `PHI=0.001 JN=24 .venv/bin/python .../gauge/gauge_cert.py` (233 s, single core).
