# GAUGECHECK — independent check of GAUGE_POSITIVE_EXTENSION_CERTIFICATE_REPORT_2026-09-07

Sources read: the report, `gauge_cert_core.py`, `gauge_cert.py`, verdict §1–§4.2, SCHUR_INDEPENDENT_CHECK.
All numbers produced here (`/home/chirurgie/.claude/jobs/4b35770d/tmp/gaugecheck/`: `l1.py p.py lbnd.py
qb.py tail.py reg1.py direct2.py AB.py h4b.py`). Constants reproduced: `a=0.69314718056`,
`d0=0.17328679514`, `delta=0.05068313851`, `2delta=0.10136627703`, `c=0.06066017178`,
`c_*=0.26418549261`, `c_*/(4pi)=0.02102321352`, `kappa=0.17044820763`.
## 1. Lemma 1 (pole gauge) — **CORRECT**

`2cosh((x-y)/2)=e^{x/2}e^{-y/2}+e^{-x/2}e^{y/2}` verified (exact 0 in mpmath); the rank-one
factorisation gives `alpha[M_+ conj(M_-)+M_- conj(M_+)]`, zero on `H_00`. Numerics: complex random `h`
on 4001 nodes over `I`, both moments removed exactly by solving the 2x2 Gram system against `e^{±x/2}`;
direct double integral of `2cosh((x-y)/2)h(x)conj(h(y))`:

| trial | \|M_+\| | \|M_-\| | double integral | \|\|h\|\|^2 | ratio |
|---|---|---|---|---|---|
| 0 | 3.4e-16 | 3.3e-16 | 2.40e-21 | 0.19753 | 1.2e-20 |
| 1 | 1.4e-16 | 1.4e-16 | 1.26e-21 | 0.20449 | 6.2e-21 |
| 2 | 7.6e-17 | 7.5e-17 | 8.86e-22 | 0.19847 | 4.5e-21 |

Zero to the accuracy of the moment projection. Exact algebra, no gap.
## 2. Lemma 2 (gauged (13)) — **CORRECT**

`2delta = 0.101366277 < d0 = 0.173286795`, so `chi = 1` on `I-I`. "Gauge before cutoff" is right:
`K_T + 2 alpha cosh(t/2) = cS + R_g`; `cosh` is smooth so `chi R_g in W^{1,1}_c`; `chi R_g = R_g` on
`I-I`, so the compressed forms agree on tests supported in `I`; and by Lemma 1 the compressed form of
`K_T + 2 alpha cosh` equals that of `K_T` on `H_00`. Hence (13g) for every `alpha`. Confirmed on a real
test function in item 6 (gauged = ungauged to 8 digits).
## 3. Certificate logic §3 — **CORRECT**, and conservative by a factor 2 below `2pi`

From (10) directly: for `|xi| <= 2pi` every `j>=0` contributes and geometric summation gives
`p(xi) = c(log(2pi/|xi|)+a)`, decreasing, so `min_{[0,2pi]} p = p(2pi) = c a = c_*/(2pi) = 0.0420464`
— **twice** the threshold `c_*/(4pi) = 0.0210232` used. `p >= c_*/(2pi+|xi|)` and `p >= c_*/|xi|`
(`|xi|>=2pi`) hold on a 4000-point log grid `1e-4..1e6`: min ratios `1.00017`, `1.00001`. Series (10)
equals (11) to 1e-32 at `T=2pi..1e5`; `sup|xi|p = 0.2804265 = C_*`.
`|F|<=A` trivial. `|F|<=B/|xi|`: `chi R_g` is AC on `R` with compact support in `[-d0,d0]` (`R` bounded
there — my float gives `R(d0) = -1.00111`), so one integration by parts has no boundary term. The two
thresholds `A < c_*/(4pi)`, `B < c_*` therefore certify the whole line. **No gap.** `xi=0` is covered by
`p -> +inf`; strictly the boxed claim should read `>0 for xi != 0`.
## 4. §4 enclosures — **CORRECT**, three defects (all immaterial here, one latent)

**Regrouping (7).** `sum_j q_{b_j}(t) = e^{t/2}S(1-e^t) - S(t)` (using `L` even), so `Q = D - 2S` exactly
and `R = (c/2)Q - (sqrt2/4)G - 2pi Ntilde` matches verdict (7) term for term; coefficient collection
`1 - r/2 - sqrt2/2 = -0.06066017 = -c`. The code's deletion rule (`res1: i-j==k1` on `beta_i-beta_j e^u`,
`res2: i-j==-k1` on `beta_i-beta_j e^{-u}`, only for `i,j>=0`) matches the verdict. Index `-1` resonances
(`(i,j)=(-1,-1)` at `s=0`, `(-1,0)` at `s=-a`) are single entire `L` terms retained in the finite part and
land on the `|z|<=4` series branch — correct.

**Bounds (3).** 40000-point grid (`1e-8..4` dense + log `4..1e6`), `L''` re-derived as
`(cos z - sin z/z)/z^2 - 2(sin z - Si z)/z^3`: `max|L|/min(1,4/|z|) = 1.0000`,
`max|L'|/min(|z|/9,5/z^2) = 1.0000`, `max|L''|/min(1/9,(1+6.7038/|z|)/z^2) = 1.0000` (and `= 1.0000`
against the verdict's `min(1/9,12/z^2)`). Never exceeded. `max|Si| = 1.851936 = Si(pi)`.

**`q_b`.** `max b|q_b|` on `|t|<=d0`: `0.4523 (b=2pi)`, `0.5039 (2pi 2^5)`, `0.5003 (2pi 2^10)`,
`0.5000 (2pi 2^20)` — claimed `5.91/b` (code `6/b`) holds with 12x slack.
`|q'_b(t)-q'_b(-t)|` vs `4.76/(b|t|)+25.4/(bt^2)`: max ratio `0.00009 / 0.146 / 0.156 / 0.157` — 6x slack.
Region-I: `max |q'_b(s)|/min(B1,B2,B3) = 0.918`, tightest as `s->0` (`q'_b(0)=1/2` vs `B1(0)=0.5453`),
for every `b` tested up to `2pi 2^40`. Each of `B1,B2,B3` is separately valid, so the split is legitimate.

**kappa.** The code comment is right: `(e^{-d0}-1/2)/2 = e^{-a-d0}(1-e^{d0}/2)` because `e^{-a}=1/2`
(agree to 3e-42). I scanned **all** nonresonant pairs at max index `n`, for `k = s/a in {0,+1,-1}`, both
the `e^u` and `e^{-u}` branch, 241 values of `t` in `[-d0,d0]` — i.e. **including the pairs near the
translates ±a**. Result `min |beta_i - beta_j e^u|/max(beta_i,beta_j) = 0.17044820762685728`, attained at
`k=+1, i=j-2, t=+d0` (the `e^{-u}` branch, `|1/4 - e^{-d0}/2|`). **kappa is a valid lower bound over all
occurring pairs, and it is sharp.** Sum branch: `min = 0.4204482 >= 0.42042` (claimed) — valid.

**Per-pair constants.** Using only (3) plus those separations: `sup 2^n|v|/(4pi) = 0.3082` vs the script's
`1.834`, and `sup 2^n|v'|/(4pi) = 0.8716` vs `32.90`. Valid, by 6x and 38x. Count `2n+3` at max index `n`
re-derived; `sum_{n>J}(2n+3)2^{-n} = (2J+7)2^{-J}` exact for `J=2,5,10,24` (`3.27825546e-6` at `J_N=24`).
The factor `2` in `tot + arb(0,(2*tl))` is `sum_s|w| = 1+1/2+1/2`. Correct.

**Region I.** `region1_Q()` reproduced in mpmath: `sum_j int_0^{t2}|w_b| = 0.09905545` (report
`0.0990554`); each closed-form cell integral matches `mp.quad` to 12 digits. `G'`, `Ntilde'` are genuinely
regular on `[-t2,t2]`. `V1 <= 0.00337356` against my float `int_{1e-6}^{1e-3}|R'| = 3.7e-5` — ~90x
conservative, but valid.

**Region II — no Lipschitz transfer is used.** The premise of the question does not match the code: there
is no "midpoint value ± sup|R'| * half-width". Each cell gets one interval argument
`tb = arb(((tl+tr)/2).mid(), ((tr-tl)/2).upper())`, which provably contains `[tl,tr]` (the node balls'
radii are added in), and `R, R'` are enclosed **on that whole ball**:
`R, Rp = R_and_Rp(tb, tl, Jq, JN, KK)` … `aI = 2*w*(ch*Rg).abs_upper()`,
`bI = 2*w*(chp*Rg + ch*Rgp).abs_upper()` — a rigorous sup over the cell, stronger than a Lipschitz
transfer. 2579 cells, `2delta` forced as a node, widths sum to `d0-t2` exactly.

**Defect (a), latent.** `_Lseries` adds `e = arb(0, arb(2)**-900)` with the comment *"with N=70, |z|<=12
it is < 2^-1000"*. False: the first omitted term at `|z|=4` is `4^140/(140!*141^2) = 7.26e-162`, at
`|z|=12` ~`5e-112`; `2^-900 = 1.18e-271`. Harmless **at prec=300** only because the accumulated arb
rounding radius of the same evaluation is `1.7e-89` >> `7.3e-162` (checked: `_Lseries(arb(4))` returns
`[0.439550784737263264526389825840 +/- 3.75e-31]`, which does contain `Si(4)/4`). Above ~535 bits the
enclosure would become invalid. A hole in the justification, not in this run's numbers.

**Defect (b), negligible.** `A_I = 2*t2*(arb(Rg_at_t2) + V1)` uses `V1 >= int_0^{t2}|R'|`, but needs
`int_0^{t2}|R_g'|`, larger by at most `alpha*t2*sinh(t2/2) = 1.3e-10`; omitted contribution to `A` is
`2.6e-13` against `A = 3.46e-3`.

**Defect (c), conservative.** `if tr <= two_dl` is never True in python-flint ball semantics
(`two_dl <= two_dl` is `False`). Checked: the shortcut still fires for every cell whose right node is
strictly below `2delta`; it fails only for the single cell `k=2309` ending *at* `2delta`, where the
smoothstep formula returns `chi = [1.0000000 +/- 1.14e-8]`, `chi' = [+/- 4.54e-4]` instead of `(1,0)`.
Both balls contain the true values; effect on `A,B` is <1e-7 upward. No unsoundness.

**Floats in `A`,`B`: none.** `flt()` appears only in the printed ledger; `abs_upper()`, `upper()`, `mid()`
all return `arb`; `PHI = arb('0.001')` is a correct enclosure used only to lay out a grid whose nodes are
balls. §7.4 of the report is accurate.

**Reproduction.** Re-ran `PHI=0.001 JN=24 gauge_cert.py` (270 s): `A <= 0.00346180830291`,
`B <= 0.122854776540`, `A_I <= 2.8030733e-5`, `B_I <= 0.0067476424`, `A_II <= 0.003433777570`,
`B_II <= 0.1161071341`, 2579 cells, 0 crude `Lpair` fallbacks, `A/thr = 0.164666`, `B/thr = 0.465032`,
`RESULT: GAUGE_SOURCE_POSITIVE_EXTENSION_CERTIFIED`. Identical to the report's ledger.

## 5. Independent `A`, `B` by a different method — **CORRECT**, ratios 0.69 and 0.63

`R`, `R'` built from the **direct double series (5)** in float/numpy (`J=48`, arguments formed as
`2pi 2^j (2^{i-j} - 2^k e^t)` with `expm1` wherever exponents cancel, `L=Si/z`, `L'=(sin z - Si z)/z^2`
from `scipy.special.sici`), never touching the (7) regrouping or arb:

| t | my direct (5) | arb core `R_and_Rp` | report |
|---|---|---|---|
| 1e-6 | -1.04813615 | — | -1.048136 |
| 2delta | -1.03038793 | [-1.030 +/- 4.7e-4] | -1.030388 |
| 0.05 | -1.04298553, `R'=0.187332` | [-1.043 +/- 9.7e-5], `R'=[0.19 +/- 4e-3]` | -1.0430 / 0.187 |
| 0.10 | -1.03079772, `R'=0.291606` | [-1.0308 +/- 8.4e-5] | -1.0308 |
| 0.15 | -1.01205451, `R'=0.454230` | [-1.012 +/- 1.4e-4], `R'=[0.45 +/- 5.6e-3]` | -1.0121 / 0.454 |

Integrating on a 24000-node graded grid `1e-6..d0`, `alpha = 0.519`:

| quantity | my float | rigorous bound | ratio | threshold | float/threshold |
|---|---|---|---|---|---|
| `A = \|\|chi R_g\|\|_1` | `0.00238971` | `0.00346180830` | **0.690** | `0.02102321` | 0.114 |
| `B = \|\|(chi R_g)'\|\|_1` | `0.07774039` | `0.12285478` | **0.633** | `0.26418549` | 0.294 |

(`B` recomputed as total variation: `0.07771424` — same.) The rigorous bounds sit 1.45x and 1.58x above
the true values: over-estimated as interval arithmetic must be, **not by orders of magnitude**. Split:
float `A_II = 0.0023695` vs rigorous `0.0034338`; float `B_[1e-6,1e-3] = 3.7e-5` vs rigorous
`B_I = 0.0067476` (the analytic region-I route is the loose part, 180x, but only 5.5% of `B`).
Side checks that land: `||chi R||_1` ungauged `= 0.284759` (earlier checker `0.28476`);
`max|F| = 0.001971 <= A`; `max|xi F| = 0.051885 <= B`; `min (p+F)/p = 0.80823 at xi = 27.253`
(report `0.8082 at 27.27`); no negative `p+F` on `[1e-3,2000]`.

## 6. `h4` end-to-end through (13g) — **CORRECT**, `0.0035088`

`h4 = (d^2-1/4)(1-(x/delta)^2)^4`, `hhat_4 = -(xi^2+1/4)phihat`,
`phihat = delta sqrt(pi) Gamma(5)(2/(delta xi))^{4.5}J_{4.5}(delta xi)`; `F(xi) = 2 int_0^{d0} chi R_g
cos(xi t)dt` from **my** float grid. `||h4||^2 = 301750.4469` in x-space vs `301750.4469` by Parseval.
`(1/2pi) int (p+F)|hhat_4|^2 / ||h4||^2` = **0.0035088** at `XMAX = 2000, 6000, 20000`, and identical
gauged vs ungauged to all printed digits — the gauge is invisible on a genuine moment-null test, as
Lemma 1 requires. Matches the ratified scalar floor.

## 7. Overall

**RESULT CODE `GAUGE_SOURCE_POSITIVE_EXTENSION_CERTIFIED` is justified**, conditionally on (13). The two
scalar inequalities are certified in ball arithmetic; they do imply `p + FT(chi R_g) >= 0` on all of `R`;
every constant feeding them that I could re-derive is valid and conservative. The three defects above do
not touch the outcome. Only (a) is a real hole in the *argument*: fix it by putting the true series tail
(`|z|^{2N}/((2N)!(2N+1)^2)`, `N=70`) into the radius instead of a fictitious `2^-900`.

**What is proved.** `F(h) >= 0` for every `h` in `H_00` **supported in `I`**, where `H_00` is the *closed
L^2 subspace* `{h in L^2(I): int h e^{x/2} = int h e^{-x/2} = 0}` — not smooth tests only. The verdict
states (13) "for every supported L2 test, followed by the moment restriction", and the right-hand side
`(2pi)^{-1} int (p + FT(chi R_g))|hhat|^2` converges for every `h in L^2(I)` (`p` locally integrable and
`O(1/|xi|)`, `hhat` bounded and square-integrable). Genuinely class-level.

**Dependences.** On `delta` and on `a = log 2` (Euler factor `p = 2`) essentially: `beta_j = 2pi 2^j`,
`c = cosh(a/2)-1`, `d0 = a/4`, the resonance combinatorics and the flat region `2delta` of `chi` all enter
`A`,`B`. On `chi` and `alpha`: **no hidden dependence**. (13) holds for *any* even `C^2` cutoff that is
`1` on `I-I` and supported in `(-d0,d0)`, and (13g) for *any* real `alpha`; one valid pair suffices and
the conclusion carries neither. "One valid choice suffices" is correct as stated. My float sweep confirms
`A` is minimised near `alpha = 0.519` and stays under `c_*/(4pi)` for `alpha` roughly in `[0.49,0.55]`
(float; the report's rigorous `[0.505,0.535]` I did not certify).

**First step asserted rather than derived.** Inside the report: the §4 constants (`5.91/b`,
`4.76/(b|t|)+25.4/(bt^2)`, `B1,B2,B3`, `1.83350`, `32.89735`) are called "all re-derived, all
conservative" with no derivation shown — I confirmed every one numerically, so the assertion is true, but
it is an assertion. Upstream and load-bearing: identity (13) itself, i.e. verdict §2.2's word *"Thus"*
(the convolution step giving `K_{ell,J} = (I_J(t)+I_J(-t))/(2pi)`) and §2.3's undisplayed collection
`1 - r/2 - sqrt2/2 = -c`. The report labels this PAPER-not-kernel (§7.1) correctly; I re-derived the
coefficient, the `2pi`/orientation step remains asserted, as the earlier checker recorded.

**Not proved.** I agree with §8(a)–(d) as written: nothing outside `H_00`, no other window, no other
Euler factor, nothing about RH.
