# Source-exact evaluator of the angle density d_S(xi) — report

Scope: verdict (1)-(18), 2.4, (16)-(17); cutoff lambda = 1; S = {inf} and S = {inf, 2}.
Grid xi = 0(0.25)600 (2401 points, identical to the diagnostic array's grid). d_S is even in xi
(verified to machine zero), so every full-line integral below is twice the half-line one.
Working dir `/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2/`; scripts and closed forms in `README.md`.

## 0. Dictionary check (verdict 2.2) — PASSES

`V g(u) = u^{-1/2} g(log u)` turns `U_c g(x)=g(x-c)` into `U_c f(u) = e^{-c/2} f(u e^{-c})`, so
`U_a f = p^{-1/2} f(u/p)` and `U_{-ja} f = p^{j/2} f(p^j u)`. Feeding `2cos(2 pi u v)` through (8):
`U_{-ja}F_inf` has kernel `p^{j/2} 2cos(2 pi p^j u v)` with coefficient `(1-r^2) r^j p^{j/2} = 1-1/p`,
`U_a F_inf` has kernel `r 2cos(2 pi u v/p)` with coefficient `-r^2 = -1/p`. Exactly
`beta_{-1}=2pi/p, c_{-1}=-1/p; beta_j=2pi p^j, c_j=1-1/p`. The Jacobian cancels the `r^j`.

## 1. Scalars I, J and Lemma 3 — PASS

`I` from the incomplete gamma closed form vs. the exact power series (dps = 0.435 beta + 60):
agreement **1e-42** at (beta,xi) = (0,1000), (3,2), (25,10), (200,30), (1000,50), (100,100),
(2 pi 2^8, 60); same for `J = -dI/ds`. Observed constants in (11):

| regime | observed |
|---|---|
| beta <= T/2 | `\|I\| T` = 1.063 / 1.031 / 0.569 at T = 50/200/800; `\|J\| T^2` = 1.203 / 1.175 / 0.770 |
| beta > T/2 | `\|I\| sqrt(beta)` -> **1.2533 = sqrt(pi/2)** (1.198, 1.261, 1.2534 at beta/T = 4, 64, 4096) |
| beta > T/2 | `\|J\| sqrt(beta)/(1+log(2 beta/T))` -> 1.041 |

Decay exponents -1 (I, low), -2 (J, low), -1/2 (I, high), -1/2 with one log (J, high): all confirmed,
with constants <= 1.3. `t_S` summed to `J_u = 55`; the (13) tail bound is **3.5e-8** (asked: 1e-6).

`|gamma_S| = 1` to 1e-12 and `(gamma_S'/gamma_S)/i = q_S` to 5e-11 (central differences), both places.
The diagnostic array's `q_inf/2pi` column reproduces ours to **2.2e-16**.

## 2. S1 — the operator, and the validation of A_inf

Nystrom (symmetrized GL) eigenvalues of `A_inf` (N-converged from 200 to 3200):
`+0.99997137627, -0.97948473467, +0.52408589623, -0.05897658918, +0.00273232874, -0.00007629136`.
**These square to the quoted Slepian numbers** 0.99994275335 / 0.95939034545 / 0.27466602663 /
0.0034782381 to 4e-12. So the quoted list is `spec(A_inf^2)` — the prolate concentration eigenvalues
at c = 2 pi — and `spec(A_inf)` is `+-sqrt` of them with alternating signs. **Validation passes**
under that reading. `alpha_inf = 0.9999713762674`, hence `1/(1-alpha^2) = 17466`.

An independent Legendre-Galerkin compression (closed-form `S_mn(beta)` and closed-form
`<phi_m,f_xi>`, see README) reproduces the same six eigenvalues and reproduces `d_inf` to
**8 significant digits** at xi = 0, 1, 5, 16, 40, 80, 120. d_inf is therefore verified by two
disjoint discretizations.

For `S={inf,2}` the operator is truncated at `j <= J`; there is no rescaling and no clipping
anywhere in the production runs (a first pass that clipped |lambda| at 0.999 was wrong by a factor
5 at xi=16 and was discarded). Runs: J = 6 (N=1610), 7 (N=3220), 8 (N=6440), `beta_J` = 402 / 804 / 1608.

## 3. d_inf — complete

| xi | d_inf(xi) | d_inf * xi^2 | q_inf/2pi | k_inf = q/2pi + d |
|---|---|---|---|---|
| 0 | +8.55009552e-01 | 0 | -0.855010 | +0.000000 |
| 0.5 | +5.30305009e-01 | +0.133 | -0.530305 | +0.000000 |
| 1 | +3.22312044e-01 | +0.322 | -0.322312 | +0.000000 |
| 2 | +1.84867663e-01 | +0.740 | -0.184868 | +0.000000 |
| 5 | +3.66339795e-02 | +0.916 | -0.036624 | +0.000010 |
| 10 | -7.14664889e-02 | -7.147 | +0.073894 | +0.002428 |
| 16 | -5.06998026e-02 | -12.979 | +0.148738 | +0.098038 |
| 20 | -2.07566572e-02 | -8.303 | +0.184262 | +0.163505 |
| 30 | -9.62254109e-03 | -8.660 | +0.248803 | +0.239180 |
| 40 | -3.33694283e-03 | -5.339 | +0.294592 | +0.291255 |
| 60 | -2.67350788e-03 | -9.625 | +0.359126 | +0.356453 |
| 80 | -9.16916288e-04 | -5.868 | +0.404913 | +0.403996 |
| 120 | -5.82128741e-04 | -8.383 | +0.469445 | +0.468863 |
| 200 | -1.90355909e-04 | -7.614 | +0.550746 | +0.550556 |
| 400 | -3.85378068e-05 | -6.166 | +0.661064 | +0.661025 |
| 600 | -2.03799227e-05 | -7.337 | +0.725596 | +0.725575 |

* **(i) O(xi^-2)**: log-log slope of `|d_inf|` on [60,600] = **-2.0043**; running-max envelope **-2.0920**.
* **(i) Tr D_inf = 0**: `int_0^X d_inf` = 0.073322 / 0.036608 / 0.024415 / 0.018308 / 0.014646 / 0.012205
  at X = 100..600. That is **7.32/X to three digits at every X**, i.e. `int_0^inf d_inf = 0` with the
  tail dictated by `d_inf xi^2 -> -7.3`. Confirmed.
* Structural by-product: `k_inf(xi) = 0` to 1e-16 for xi <= 2 — `d_inf = -q_inf/2pi` exactly there.
* **(ii) carrier**: `k_inf - k_arch` on [16,120] has max 1.28e-4, rms 4.7e-5 — an order better than the
  carrier's advertised 1e-3. Outside its validity the residual grows as the verdict's order-of-limits
  warning (2.4) requires: max 1.0e-2 on [120,300], **1.33e-1** on [300,600].

## 4. d_2 — values, and the amplification obstruction

| xi | d_2 (J=8) | J=7 | J=6 | 2Re(gamma_2 t_2) |
|---|---|---|---|---|
| 0 | +1.5690e+00 | +1.6345e+00 | +1.7218e+00 | +2.7421e+00 |
| 2 | +1.7495e-01 | +1.6920e-01 | +1.6902e-01 | +2.1048e-01 |
| 5 | -4.4951e-02 | -4.1479e-02 | -4.7152e-02 | -1.6346e-02 |
| 16 | -6.7173e-02 | -6.4121e-02 | -5.9185e-02 | -3.2854e-02 |
| 30 | +8.3093e-03 | +7.4385e-03 | +7.8310e-03 | +1.4939e-02 |
| 60 | -1.1268e-02 | -1.1897e-02 | -1.0859e-02 | -7.5179e-03 |
| 120 | -1.1800e-03 | -1.9339e-03 | -1.6120e-03 | +1.2429e-03 |
| 200 | -5.6971e-02 | -5.4442e-02 | -5.2383e-02 | -5.1359e-02 |
| 400 | +1.2936e-02 | +1.3819e-02 | +1.4308e-02 | +1.4334e-02 |
| 600 | -6.6835e-03 | -6.2786e-03 | -6.1022e-03 | -6.0991e-03 |

Pointwise J-spread (operator truncation): rms `|d_2^(8)-d_2^(7)|` = 1.15e-2 / 4.2e-3 / 2.4e-3 /
1.3e-3 / 5.7e-4 on [0,16] / [16,60] / [60,120] / [120,300] / [300,600]. **Pointwise d_2 below
xi ~ 16 is not converged**; above 120 it is good to ~1e-3 absolute.

**Why.** (6) carries `1/(1-lambda_n^2)`, and its finiteness rests on the exact cancellation
`Re{gamma conj(c_n)^2} - lambda_n |c_n|^2 = O(1-lambda_n^2)`, which holds only for the true operator.
An operator error eta enters d_S as `eta/(1-lambda^2)`. Already `A_inf` has `1-lambda_0^2 = 5.7e-5`.
The attainable eta is the multiplier tail `sup|m^(J)-m| = (1+r)r^{J+1}` (verified to be exactly that on
2e5 points): 0.151 / 0.107 / **0.0754** at J = 6/7/8, with `beta_J = 2 pi 2^J` and Nystrom cost `~4 beta_J`.
Top Nystrom eigenvalues of `A_2^(J)`, no rescaling:

| J | eta | lam_0 | lam_1 | lam_2 | lam_3 | lam_4 | lam_5 | lam_6 | lam_7 |
|---|---|---|---|---|---|---|---|---|---|
| 4 | 0.302 | -0.991119 | +0.830044 | +0.540982 | -0.467131 | +0.406266 | +0.321354 | -0.311612 | -0.242097 |
| 5 | 0.213 | -1.003920 | +0.892847 | +0.571009 | -0.504334 | +0.411279 | +0.361125 | -0.352029 | -0.284782 |
| 6 | 0.151 | -1.006413 | +0.933722 | +0.590533 | -0.527322 | +0.415601 | +0.384597 | -0.377653 | -0.311974 |
| 7 | 0.107 | -1.004706 | +0.959656 | +0.602670 | -0.541276 | +0.420941 | +0.397212 | -0.393533 | -0.328941 |
| 8 | 0.0754 | -1.001834 | +0.975791 | +0.610007 | -0.549601 | +0.426063 | +0.403687 | -0.403184 | -0.339331 |

`lam_0 -> -1` and `lam_1 -> +1` (increments ratio 0.622, geometric limit 1.0024); `lam_2 -> 0.6212`,
`lam_3 -> 0.5619`. So **the semilocal pair carries two near-unit angles where the archimedean place
carries one**, and `1-alpha_2` is below the resolution of any truncation we can afford: with
`1-lambda^2 ~ 5e-5` as at the archimedean place, `eta/(1-lambda^2) ~ 1.5e3`. **Pointwise d_2 at small
xi is not computable at precision better than O(1) by this route.** This is a property of the
semilocal pair, not of the code. The truncation's `sup|m^(J)| > 1` also produces exactly one
spurious eigenvalue with |lambda| > 1 per run; those modes are dropped, never rescaled (see §6).

**What is nevertheless computable.** The near-unit modes are dormant for xi >~ 16: their share of
`|b_n|^2` falls from 1.0e-4 at xi=16 to 2.1e-6 at 120 and 7.3e-8 at 600, and the J-spread of the
*integrated* quantities is two orders smaller than the pointwise one (§5).

**(iv) Theorem 4 exponent.** Running-max envelope slope of `|d_2|`: **-0.482 / -0.483 / -0.494** on
[60,600] / [100,600] / [200,600] (raw slopes -0.54 / -0.54 / -0.60, biased by the spikes). `-1/2` confirmed.

**(v) First cosine coefficient of `k_2 - k_inf` over complete periods 2pi/a = 9.064720** (target `-a r/pi = -0.156013`):

| window | periods | c1 | s1 |
|---|---|---|---|
| [50, 294.75] | 27 | -0.147939 | -0.000004 |
| [50, 593.88] | 60 | -0.150496 | +0.000002 |
| [100, 598.56] | 55 | -0.151330 | -0.000050 |
| [200, 598.85] | 44 | **-0.152054** | +0.000002 |

Converging to -0.1560 at the advertised `O(X^{-1/2})` rate; the sine coefficient vanishes. Confirmed.

**Structure found while checking this**: `|t_2(xi)|` peaks exactly at `xi = 0 mod 2pi/log 2` (checked at
408, 417, 426, 435, 444.25, 453.25), with peak height `1/(1-r) = 3.41` times the mean and width ~0.4,
because `t_2 = (1/pi) sum_j c_j J(beta_j,-xi)` has phases `-xi(log 2pi + j log 2)` — an arithmetic
progression, i.e. a Poisson kernel in `xi log 2`. This is what makes d_2 spiky.

## 5. S5 — the sign for the frozen h

`W_h = (1-cos(a xi))|hhat|^2/H`, `H = 1.6434228127646e8`, `|hhat|^2` from the diagnostic array.
Grid mass `int W_h = 5.826705` against Lemma 5's exact `2 pi = 6.283185`: **7.27% of the phase
marginal sits beyond xi = 600**; that deficit is used below as an exact tail-mass constraint.
W_h quantiles: 10/25/50/75/90% at xi = 58.5 / 122 / 203 / 297 / 429 — the integral lives at large xi.

```
m(h) = -int W_h d_2 :   J=6 +0.012007   J=7 +0.013246   J=8 +0.013424
increments +0.00124, +0.00018 (ratio 0.144) -> geometric limit +0.013453
decomposition at J=8:  from 2Re(gamma t_2)  +0.001943
                       from 2Re(gamma <u,AZ ubar>) +0.000076
                       from -2<u,Zu>        +0.011405   (>= 0 for every h)
int W_h d_inf = -0.004736  =>  A(h) = +0.004736 ;  w = a/sqrt2 = +0.490129
int W_h (d_2 - d_inf) = -0.008687  =>  B(h) = w + that = +0.481442
```

Error budget for `m(h)` restricted to |xi| <= 600:

| addend | size |
|---|---|
| (a) operator truncation J | +-2e-4 (J=8 vs geometric limit; J-increments 1.24e-3 -> 1.8e-4) |
| (b) scalar series tail J_u=55 | 3.5e-8 |
| (c) quadrature / Nystrom | <= 1e-4 (trapz at step 0.25/0.5/1.0 give +0.013424/+0.013308/+0.013211; Simpson agrees) |
| (d) inverse | exact — direct eigen-decomposition, no Neumann truncation |
| (e) one dropped spurious mode | one-signed, **adds** to m(h) (see below) |
| (f) |xi| > 600 | est. +3e-4 (last four 50-blocks give 2.3e-4, 9.8e-5, 6.8e-5, 6.8e-5); crude bound +-0.0456 |

**Result: `m(h) = +0.0134` (|xi| <= 600), with a resolved error of +-3e-4.**

Two facts make the positive sign robust upward. Writing `c_n = <psi_n, f_xi>`, each eigen-mode
contributes to `d_2` the amount `(2/(1-lambda_n^2)) lambda_n^2 [lambda_n Re{gamma conj(c_n)^2} - |c_n|^2]`
on top of `2Re{gamma t_2}`; since `|Re{gamma conj(c_n)^2}| <= |c_n|^2` and `|lambda_n| <= sup|m_2| = 1`,
**every such term is <= 0**. Hence pointwise `d_2(xi) <= 2Re{gamma_2(xi) t_2(xi)}`, so
`m(h) >= -int W_h 2Re{gamma_2 t_2} = +0.001943` using only the exactly evaluated scalar,
and the mode we had to drop (and any unresolved near-unit angle) can only push `m(h)` further up:
forcing `|lambda_0| = 1-1e-2` or `1-1e-3` adds +0.00196 or +0.0195 respectively.

**Comparison with the diagnostic.** Feeding the same integrator the carrier's own rows gives
`A = +0.093609`, `B = +0.224999`, `m = w + A - B = +0.358740` — i.e. the pipeline **reproduces the
diagnostic +0.34 / +0.36**. The source-exact value is 27x smaller. The gap is the carrier's error,
not a disagreement about the definition: `k_semi - k_2` has rms 1.08e-2 on [16,120], 9.0e-2 on
[120,300], 1.67e-1 on [300,600], and 74% of W_h's mass lies above 120. Even the purely archimedean
piece is affected: our fully verified `A(h) = +0.004736` against the carrier's `+0.093609`.

## 6. Three sentences

**Is d_2 one-signed on the relevant frequency range?** No — on [16,600] `d_2` is negative at 57% of
the grid points (61.6% on [16,120], 54.5% on [300,600]), with mean +0.00098, max +0.384 and min -0.107;
what is one-signed is only the reservoir part `-2<u,Z u> <= 0`, and that is what carries the sign of `m(h)`.

**Does m(h) come out positive with certified error?** It comes out `+0.0134` with a resolved error of
+-3e-4 over |xi| <= 600 and with a rigorous one-sided floor `m(h) >= +0.00194` there from the exact
scalar alone; it is **not** certified overall, because the 7.27% of phase-marginal mass beyond xi = 600
is only bounded crudely (+-0.046) — extending `|hhat|^2` past 600 would close this, and nothing else would.

**Anything strange?** Three things: `k_inf` is exactly 0 (1e-16) for xi <= 2 and `k_2` goes **negative**,
min -0.0141 at xi = 8.25 (-0.0151 at J=7, -0.0177 at J=6 — the trend is toward zero but the sign is
stable across J); the semilocal `A_2` appears to have **two** angles running to +-1 while the archimedean
place has one, which is exactly what makes (6) ill-conditioned at small xi; and `|t_2|` is a Poisson
kernel in `xi log 2` peaking at `xi = 0 mod 9.0647`, so `d_2` is spiky (99th percentile 0.097 against a
median 0.003 on [400,600]) — the peaks are the fixed Euler harmonics, resolved but only barely by a 0.25 grid.
