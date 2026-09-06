# Sign table for S = {infinity, 2} — implementation B

All numbers below were computed in this directory (scripts + rerun instructions in `README.md`).
Nothing is quoted from memory. Where a number is uncertain, the uncertainty is given.

**Conventions.** log model `x = log u`, `f(u) = u^{-1/2} v(log u)` (unitary),
`(F_inf f)(u) = 2 int_0^inf f(t) cos(2 pi u t) dt`, `theta(k)` = convolution by `v` in `x`,
`f = k * k^*`, `f(1) = ||v||^2`, `ell = log(TW) = 2 log lambda`,
`c_A = gamma + log(8 pi) + pi/2 = 5.372183419225665`.
`L_S(f) = D(v) - c_A ||v||^2 - 2 sum_{j>=1} (log2 / 2^{j/2}) C_v(j log 2)` (eq. (14), `S_f = {2}`);
`Q(v) = D(v) - c_A||v||^2 + P_02(v) - 2 sum_{n>=2} Lambda(n) n^{-1/2} C_v(log n)`;
`N_S = Tr(theta_f S_S) = ||theta(k) S_S||_HS^2`; `E_S = Tr(theta_f D_S) - ell f(1)`.
**E is computed directly from the block trace (7) and N directly from the Sonin projector; neither
is obtained from the other, so the identity check `L_S = N_S - E_S` is not tautological.**

---

## 0. The model, and one structural obstruction that must be stated first

The carrier is the **physical** variable: `u_i = i*delta`, `i = 0..N`, `delta = 1/sqrt(2N)`,
`U_max = N*delta = sqrt(N/2)`, trapezoid weights. On this grid the Nystrom form of `F_inf` is
exactly the orthogonal DCT-I matrix `sqrt(2/N) sqrt(k_i k_j) cos(pi i j / N)`, hence **exactly**
symmetric and **exactly** involutive. `P_lambda F_inf P_lambda` restricted to `ran P` is then
literally the finite cosine transform on `(0,lambda)`, so `alpha_n^2 = lambda_n(c)` with
`c = 2 pi lambda^2` (even sector) — that is the prolate cross-check of S1.

Two earlier designs were built and **rejected**; both failures are informative:

* *log grid + exact unimodular FFT multiplier* `chi(tau) = 2 (2pi)^{-1/2+i tau} Gamma(1/2 - i tau)
  cos(pi(1/2 - i tau)/2)`. It passed every algebraic test (`| |chi| - 1 | <= 2.2e-16`,
  `F = F^T` to `1.4e-16`, `F^2 = I` to `6.3e-15`, and the analytic fixed point
  `f(u)=e^{-pi u^2}` reproduced to `1.3e-8`) but its compression to `{x <= 0}` had eigenvalues
  `1.000000000000` instead of the prolate `0.99994, 0.9594, 0.2747, 3.48e-3, ...`. Reason: a cell
  at log-position `x` has physical width `e^x delta`, so its cosine transform reaches log-position
  `-x - log(2 pi Delta)`; for `x` deep negative that is outside the carrier and the periodic model
  aliases it back into `ran P`, manufacturing a spurious `+1` eigenspace.
* *physical grid with* `J_S^{-1} = I - (index doubling)`. Doubling the argument **doubles the
  bandwidth**, which aliases on a Nyquist-critical grid: `||F_S - F_S^T|| = 0.27`,
  `||F_S^2 - I|| = 1.9`, `alpha_max = 1.52` — a direct contradiction of Lemma 2 (`|alpha_n| < 1`),
  i.e. a detectable model failure, not a small error.

The design actually used builds the Euler intertwiner from **halving only**:
`B_S = I - (1/2) H` with `(H f)(u) = f(u/2)`, realised exactly as `H = E_half F_inf` (halving
lowers frequency, so it never aliases; `H` is exact on Gaussians to `1e-15` and `||H|| = 1.4142136
= sqrt 2`, the continuum value). `F_S = B_S F_inf B_S^{-1}` is then an **exact involution**.
The pair is built from **subspaces**: `ran Q = F_S(ran P)`, orthonormalised, so `P` and `Q` are
honest orthogonal projections and the Halmos algebra (6) is exact.

**The obstruction.** In the log variable `F_S = M_{chi_S} o R` with
`chi_S(tau) = chi(tau) (1 - 2^{-1/2} e^{-i tau log2}) / (1 - 2^{-1/2} e^{i tau log2})`. The extra
phase expands into multiplicative shifts by `2^m` with weights `2^{-|m|/2}`: reaching `1e-3`
needs about 20 octaves. A Nyquist-critical *physical* grid spanning 20 octaves needs `N ~ 2^40`;
a *log* grid carries the octaves but cannot carry `F_inf` (first rejected design). **No single
finite carrier holds the semilocal cutoff pair at high accuracy.** The residue of this is visible
as `|| W^T W - I ||_max = 0.249` for `W = F_S|_{ran P}` (it is `<= 6e-15` for the archimedean
pair). This is why the archimedean control table is reported alongside: that pair is exact.

---
## 1. S1 — model validation

| check | value | comment |
|---|---|---|
| `\|\|F_inf - F_inf^T\|\|_max` | `0.000e+00` | exact by construction (DCT-I) |
| `\|\|F_inf^2 - I\|\|_max` | `5.8e-14` (N=1024), `1.2e-13` (N=2048), `2.3e-13` (N=4096), `4.5e-13` (N=8192) | roundoff only |
| fixed point `f(u)=e^{-pi u^2}` | `\|\|Fc-c\|\|/\|\|c\|\| = 1.2e-15` | analytic self-dual function |
| Hermite-2 (eigenvalue `-1`) | `\|\|Fc+c\|\|/\|\|c\|\| = 2.4e-15` | second analytic eigenfunction |
| halving operator `H` | exact on Gaussians to `1.9e-15`; `\|\|H\|\| = 1.41421356 = sqrt2` | continuum value |

**Prolate cross-check** (independent computation: Gauss–Legendre Nystrom, 500 nodes, of the sinc
kernel `sin(c(x-y))/(pi(x-y))` on `[-1,1]`, even eigenfunctions), `alpha_n^2` vs `lambda_n(c)`,
`c = 2 pi lambda^2`. Grid `N = 4096` (`delta = 0.011049`):

| lambda | n | `alpha_n` (this model) | `alpha_n^2` | `lambda_n(c)` (independent) | rel. diff |
|--:|--:|--:|--:|--:|--:|
| 1 (c=6.283185) | 0 | `+0.999971421530` | `9.999428438758e-01` | `9.999427533541e-01` | `9.1e-08` |
| | 1 | `-0.979469260753` | `9.593600327597e-01` | `9.593903454479e-01` | `3.2e-05` |
| | 2 | `+0.523706396571` | `2.742683898091e-01` | `2.746660266254e-01` | `1.5e-03` |
| | 3 | `-0.058810051984` | `3.458622214318e-03` | `3.478238071586e-03` | `5.6e-03` |
| | 4 | `+0.002715074408` | `7.371629041460e-06` | `7.465620360493e-06` | `1.3e-02` |
| sqrt2 (c=12.566371) | 0 | `+0.999999999881` | `9.999999997615e-01` | `9.999999997054e-01` | `5.6e-11` |
| | 2 | `+0.999748425094` | `9.994969134776e-01` | `9.994100757304e-01` | `8.7e-05` |
| | 4 | `+0.567854266214` | `3.224584676571e-01` | `2.993750136389e-01` | `7.7e-02` |
| 2 (c=25.132741) | 0 | `+1.000000000000` | `1.000000000000e+00` | `1.000000000000e+00` | `2.0e-14` |
| | 5 | `-0.999992290100` | `9.999845802599e-01` | `9.999809214498e-01` | `3.7e-06` |
| | 6 | `+0.999180909819` | `9.983624905468e-01` | `9.980328548887e-01` | `3.3e-04` |

Signs alternate `+,-,+,-` as required (`mu_{2k} = (-1)^k |mu_{2k}|`). Accuracy degrades on the
transition eigenvalues (`lambda_n ~ 0.3`) like `delta^2`; that is the leading discretisation term.

## 2. S2 — semilocal Fourier

`B_S = I - 2^{-1/2} U_{log2}` realised as `I - (1/2) H`. Singular values of `B_S`:

| N | min sing.val | max sing.val |
|--:|--:|--:|
| 1024 | 0.322379 | 1.687927 |
| 2048 | 0.319578 | 1.691172 |
| 4096 | 0.317168 | 1.693656 |
| 8192 | 0.315078 | 1.695601 |

to be compared with `a_S = 1 - 2^{-1/2} = 0.292893` and `b_S = 1 + 2^{-1/2} = 1.707107`. The
model values sit strictly inside the theoretical interval and creep towards it as `U_max` grows —
the extremes are attained only on the untruncated line, so this is the expected behaviour.

`F_S^2 = I` to `2.3e-13` at N=4096 (exact by algebra).
`||F_S - F_S^T||_max` = `3.12e-02` (N=2048), `2.33e-02` (N=4096), `1.73e-02` (N=8192): the model
defect of section 0, shrinking only like `delta^{~0.6}`, i.e. very slowly, as predicted by the
20-octave argument.

## 3. S3 — projections, angles, Sonin projector

| model | lambda | dim ran P | # blocks with `\|alpha_n\|>1e-6` | `Tr S_S` (= dim of the common kernel) | `\|\|S^2-S\|\|_max` | `\|\|S P\|\|` |
|---|--:|--:|--:|--:|--:|--:|
| S={inf} | 1 | 91 | 7 | 3915 = 4097-2*91 | `6.15e-10` | `6.15e-10` |
| S={inf} | sqrt2 | 129 | 9 | 3839 = 4097-2*129 | `2.38e-08` | `2.38e-08` |
| S={inf} | 2 | 182 | 14 | 3733 = 4097-2*182 | `1.33e-01` (DEGENERATE) | `1.52e-08` |
| S={inf,2} | 1 | 91 | 54 | 3915 = 4097-2*91 | `1.19e-08` | `1.19e-08` |
| S={inf,2} | sqrt2 | 129 | 74 | 3839 = 4097-2*129 | `1.76e-08` | `1.76e-08` |
| S={inf,2} | 2 | 182 | 102 | 3733 = 4097-2*182 | `6.21e-08` | `9.67e-09` |

(N = 4096. The `lambda = 2` archimedean row is degenerate: `alpha_0 = 1 - O(1e-16)`, so
`s = sqrt(1-alpha^2)` is below double precision and the block decomposition there is not
resolvable in double precision. Flagged, not used as a headline. The semilocal pair does not have
this problem at `lambda = 2` because the prime-2 phase spreads the angles.)

`Tr S_S` comes out exactly `n - 2 dim(ran P)` in every non-degenerate row, i.e. the two ranges
intersect in `{0}` and the pair has no zero-angle overlap on the carrier — the numerical form of
Lemma 2(1). The common kernel is therefore the whole rest of the carrier: 3915 of 4097 dimensions
at `lambda = 1`, which is the finite-carrier image of "the semilocal Sonin space is
infinite-dimensional".

Independent confirmation via the SVD route asked for in S3 (N=1024, `lambda=1`, `dim ran P = 46`):
`rank[P | Q] = 92 = 2 dim(ran P)` at tolerance `1e-8`; the spectrum of
`S_S = (ran P v ran Q)^perp` is contained in `[-2.05e-08, 1.0000000000000036]` with exactly
933 eigenvalues above 1/2 and `Tr S_S = 933.0 = 1025 - 92`.

`zeta_n` diagnostics (all N, all non-degenerate lambda): `| ||zeta_n|| - 1 | <= 3.3e-15`,
`|<xi_n, zeta_n>| = 0` exactly, `||P zeta_n|| = 0` exactly (`zeta` is built as
`(I-P) Q xi / ||.|| * sign(alpha)`, which avoids the cancellation in `(Q xi - alpha^2 xi)/(alpha s)`).


**Angle spectra** (N = 2048, tolerance `1e-8`; `|alpha|_max < 1` strictly for `lambda = 1, sqrt2`,
which is the numerical form of Lemma 2):

| model | lambda | `|alpha|_max` | alpha_0 .. alpha_7 |
|---|--:|--:|---|
| S={inf} | 1 | `0.999976481839` | `+0.99997648, -0.98220704, +0.54787945, -0.06477050, +0.00308651, -0.00008808, +1.689e-06, -2.326e-08` |
| S={inf} | sqrt2 | `0.999999999857` | `+1.00000000, -0.99999941, +0.99970711, -0.96781132, +0.54641108, -0.08999923, +0.00740786, -0.00041638` |
| S={inf} | 2 | `1.000000000000` | `-1.0, +1.0, +1.0, -1.0, +0.99999997, -0.99999309, +0.99925272, -0.96417596` |
| S={inf,2} | 1 | `0.999966351179` | `+0.99996635, -0.99406169, +0.65536587, -0.57985357, +0.47673433, -0.44626961, +0.42693442, -0.39083506` |
| S={inf,2} | sqrt2 | `0.999983514285` | `+0.99998351, -0.99996707, +0.99967303, -0.98404436, +0.84055911, -0.66391330, +0.63348378, -0.54152509` |
| S={inf,2} | 2 | `0.999999999974` | `+1.0, +1.0, -1.0, -1.0, -0.99997354, +0.99988297, +0.99953176, -0.98381888` |

A structural difference worth recording: at `lambda = 1` the archimedean pair has only **7** angles
above `1e-6`, falling off super-exponentially (prolate decay), while the semilocal pair has **41**,
decaying slowly (`0.655, 0.580, 0.477, 0.446, 0.427, 0.391, 0.385, 0.353, ...`). The prime-2
intertwiner spreads the angle spectrum; the "few significant angles" picture of the archimedean
pair does not survive the semilocal step.

**Halmos plant, verdict eq. (10)** — done in exact rational arithmetic (`halmos.py`):
with `alpha = 3/5`, `s = 4/5`, `I - P - Q = [[-9/25, -12/25], [-12/25, +9/25]]`, and for
`v = (2,1)/sqrt5`: `<v, (I-P-Q) v> = -3/5` exactly, `D_S` block eigenvalues `+-3/5 = +-|alpha|`,
and `S v = (I-P-Q+D_S) v = 0` exactly. All three agree with the verdict.

## 4. Quadrature path (independent of every operator)

| check | value |
|---|---|
| `c_A` | `5.372183419225665` (mpmath, 30 dps; `= gamma + log(8 pi) + pi/2`) |
| `A = \|\|Phi\|\|_2` | `0.5654660130897` vs paper `0.565466013092` (11 digits) |
| `int Phi` | `0.497120778185` vs `Xi(0) = xi(1/2) = 0.497120778188` (11 digits) |
| `int f_0` | `0.8791346724250` vs paper `0.8791346724` |
| `A_pm(f_0)` | `0.884224` `= 1/(2A)` exactly |
| `P_02` vs `2\|C\|^2 - 2\|S\|^2` | agree to `<= 3.6e-14` on every test in the family |
| `Q(v_R)` (smoothstep cutoff) | `+8.09e-10` (R=0.5), `-7.77e-14` (R=1) |
| `Q(v_R)` (explicit quintic cutoff) | `+3.79e-10` (R=1), `-7.51e-14` (R=2) |

The last two rows are the strongest available check of the whole quadrature path: `f_0` lies in
the radical of the Weil form, and the computed `Q(v_R)` reaches machine zero.
Precision of the quadrature quantities: `||v||^2`, `C_v(t)`, `A_pm` are trapezoidal on a
`dx = 1e-4` (or `2e-4`) grid for a `C^inf` compactly supported integrand (spectral accuracy);
`D(v)` is 300-node Gauss-Legendre on 10 panels over `[0, L]` plus the exact tail series
`2||v||^2 sum_k e^{-(2k+1/2)L}/(2k+1/2)`. Estimated accuracy `1e-10` or better, consistent with
`Q(v_R) = -7.8e-14`.

---
## 5. S5 — the sign table

### 5.1 REFERENCE: S = {infinity, 2}, lambda = 1 (T = W = 1, ell = 0), N = 8192

| test | \|v\|^2 | D(v) | prime sum | L_S | P_02 | Q(v) | N_S | E_S (direct) | N_S-E_S | abs.res | rel.res | E_impl = N_S-L_S | sign(E) | Q-N_S |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|
| h_b b=0.05 | 0.088623 | 0.48780 | +0.000000 | +0.011700 | +0.031436 | +4.314e-02 | +0.035892 | +0.200196 | -0.164305 | 1.76e-01 | 1.5e+01 | +0.024191 | **POS** | +7.244e-03 |
| h_b b=0.1 | 0.177245 | 0.84503 | -0.000001 | -0.107166 | +0.125978 | +1.881e-02 | +0.013772 | +0.264161 | -0.250389 | 1.43e-01 | 1.3e+00 | +0.120938 | **POS** | +5.040e-03 |
| h_b b=0.2 | 0.354232 | 1.42252 | -0.011858 | -0.492335 | +0.492524 | +1.895e-04 | +0.000801 | +0.545689 | -0.544889 | 5.26e-02 | 1.1e-01 | +0.493135 | **POS** | -6.110e-04 |
| h_b b=0.3 | 0.519020 | 1.93525 | -0.068750 | -0.921770 | +0.923431 | +1.660e-03 | +0.003093 | +0.887832 | -0.884740 | 3.70e-02 | 4.0e-02 | +0.924863 | **POS** | -1.433e-03 |
| h_b b=0.5 | 0.731363 | 2.66215 | -0.169615 | -1.436483 | +1.448622 | +1.214e-02 | +0.015646 | +1.311779 | -1.296133 | 1.40e-01 | 9.8e-02 | +1.452130 | **POS** | -3.508e-03 |
| h_b shift +log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.035917 | +0.019599 | +0.016318 | 4.58e-03 | 3.9e-01 | +0.024177 | **POS** | +7.234e-03 |
| h_b shift -log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.035884 | +0.022917 | +0.012966 | 1.23e-03 | 1.0e-01 | +0.024144 | **POS** | +7.267e-03 |
| two-bump (+) b=0.05 | 0.177245 | 0.94584 | -0.086873 | -0.093228 | +0.129453 | +3.623e-02 | +0.045443 | +0.117636 | -0.072194 | 2.10e-02 | 2.3e-01 | +0.138671 | **POS** | -9.218e-03 |
| two-bump (-) b=0.05 | 0.177245 | 1.00551 | +0.086873 | +0.140187 | -0.003811 | +1.364e-01 | +0.098158 | -0.032605 | +0.130763 | 9.42e-03 | 6.7e-02 | -0.042029 | **NEG** | +3.822e-02 |
| h_b shift +log2/2 b=0.1 | 0.174822 | 0.85824 | -0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.019539 | +0.082904 | -0.063365 | 1.76e-02 | 2.2e-01 | +0.100473 | **POS** | +7.294e-03 |
| h_b shift -log2/2 b=0.1 | 0.174822 | 0.85824 | +0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.019473 | +0.090543 | -0.071070 | 9.86e-03 | 1.2e-01 | +0.100406 | **POS** | +7.361e-03 |
| two-bump (+) b=0.1 | 0.349644 | 1.61268 | -0.171371 | -0.437044 | +0.444141 | +7.098e-03 | +0.020809 | +0.386089 | -0.365280 | 7.18e-02 | 1.6e-01 | +0.457852 | **POS** | -1.371e-02 |
| two-bump (-) b=0.1 | 0.349644 | 1.82029 | +0.171371 | +0.113309 | -0.013074 | +1.002e-01 | +0.057215 | -0.039195 | +0.096410 | 1.69e-02 | 1.5e-01 | -0.056095 | **NEG** | +4.302e-02 |
| h_b e^(i2x) b=0.2 | 0.354232 | 1.48061 | -0.002175 | -0.424563 | +0.425115 | +5.519e-04 | +0.001377 | +0.493311 | -0.491934 | 6.74e-02 | 1.6e-01 | +0.425939 | **POS** | -8.249e-04 |
| h_b e^(i5x) b=0.2 | 0.354232 | 1.70909 | +0.011240 | -0.182675 | +0.191367 | +8.692e-03 | +0.008656 | +0.310898 | -0.302242 | 1.20e-01 | 6.5e-01 | +0.191331 | **POS** | +3.544e-05 |
| h_b e^(i10x) b=0.2 | 0.354232 | 2.03679 | -0.009452 | +0.124341 | +0.007376 | +1.317e-01 | +0.087411 | +0.132727 | -0.045316 | 1.70e-01 | 1.4e+00 | -0.036930 | **?** | +4.431e-02 |
| v_R = chi_R f_0  R=0.5 | 1.000000 | 3.88372 | -0.074018 | -1.562478 | +1.563592 | +8.092e-10 | +0.001445 | +1.622423 | -1.620977 | 5.85e-02 | 3.7e-02 | +1.563924 | **POS** | -1.445e-03 |
| v_R = chi_R f_0  R=1.0 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.770e-14 | +0.001445 | +1.622541 | -1.621096 | 5.85e-02 | 3.7e-02 | +1.564026 | **POS** | -1.445e-03 |
| pole-null v_+ | 1.000000 | 8.80929 | -0.490129 | +2.946977 | +0.000000 | +2.947e+00 | +2.968850 | +0.088894 | +2.879956 | 6.70e-02 | 2.3e-02 | +0.021873 | **POS** | -2.187e-02 |
| pole-null v_- | 1.000000 | 8.80929 | +0.490129 | +3.927236 | +0.000000 | +3.927e+00 | +3.587681 | +0.031883 | +3.555797 | 3.71e-01 | 9.5e-02 | -0.339556 | **?** | +3.396e-01 |
| pole-null v_i | 1.000000 | 8.80929 | -0.000000 | +3.437107 | -0.000000 | +3.437e+00 | +3.278265 | +0.060389 | +3.217877 | 2.19e-01 | 6.4e-02 | -0.158841 | **?** | +1.588e-01 |
| wide cos bump b=3 [OUTSIDE window] | 1.000000 | 1.43327 | -1.952910 | -5.891821 | +14.716673 | +7.101e-06 | +0.002247 | +4.221699 | -4.219452 | 1.67e+00 | 2.8e-01 | +5.894068 | **POS** | -2.240e-03 |
| wide cos bump b=4 [OUTSIDE window] | 1.000000 | 1.06874 | -2.301207 | -6.604655 | +26.702646 | +1.004e-05 | +0.002429 | +4.288019 | -4.285590 | 2.32e+00 | 3.5e-01 | +6.607083 | **POS** | -2.419e-03 |
| wide cos bump b=6 [OUTSIDE window] | 1.000000 | 0.64572 | -2.711791 | -7.438254 | +91.228591 | +3.087e-06 | +0.002521 | +4.107630 | -4.105109 | 3.33e+00 | 4.5e-01 | +7.440774 | **POS** | -2.518e-03 |
| v_R quintic chi_R f_0 R=1 | 1.000000 | 3.88367 | -0.074064 | -1.562579 | +1.563710 | +3.787e-10 | +0.001445 | +1.622540 | -1.621095 | 5.85e-02 | 3.7e-02 | +1.564024 | **POS** | -1.445e-03 |
| v_R quintic chi_R f_0 R=2 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.509e-14 | +0.001445 | +1.622541 | -1.621096 | 5.85e-02 | 3.7e-02 | +1.564026 | **POS** | -1.445e-03 |


### 5.2 Archimedean control S = {infinity}, lambda = 1, N = 8192
(here L = D(v) - c_A ||v||^2; no prime term. This pair is EXACT in the model.)

| test | \|v\|^2 | D(v) | prime sum | L_S | P_02 | Q(v) | N_S | E_S (direct) | N_S-E_S | abs.res | rel.res | E_impl = N_S-L_S | sign(E) | Q-N_S |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|
| h_b b=0.05 | 0.088623 | 0.48780 | +0.000000 | +0.011700 | +0.031436 | +4.314e-02 | +0.029701 | +0.062500 | -0.032799 | 4.45e-02 | 3.8e+00 | +0.018001 | **POS** | +1.343e-02 |
| h_b b=0.1 | 0.177245 | 0.84503 | +0.000000 | -0.107165 | +0.125978 | +1.881e-02 | +0.006971 | +0.151750 | -0.144779 | 3.76e-02 | 3.5e-01 | +0.114136 | **POS** | +1.184e-02 |
| h_b b=0.2 | 0.354232 | 1.42252 | +0.000000 | -0.480477 | +0.492524 | +1.895e-04 | +0.000189 | +0.504808 | -0.504619 | 2.41e-02 | 5.0e-02 | +0.480665 | **POS** | +9.036e-07 |
| h_b b=0.3 | 0.519020 | 1.93525 | +0.000000 | -0.853020 | +0.923431 | +1.660e-03 | +0.002255 | +0.868322 | -0.866067 | 1.30e-02 | 1.5e-02 | +0.855275 | **POS** | -5.947e-04 |
| h_b b=0.5 | 0.731363 | 2.66215 | +0.000000 | -1.266868 | +1.448622 | +1.214e-02 | +0.012667 | +1.280497 | -1.267831 | 9.62e-04 | 7.6e-04 | +1.279535 | **POS** | -5.281e-04 |
| h_b shift +log2/2 b=0.05 | 0.088623 | 0.48784 | +0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.029705 | +0.018076 | +0.011630 | 1.10e-04 | 9.4e-03 | +0.017966 | **POS** | +1.344e-02 |
| h_b shift -log2/2 b=0.05 | 0.088623 | 0.48784 | +0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.029705 | +0.019042 | +0.010664 | 1.08e-03 | 9.2e-02 | +0.017966 | **POS** | +1.344e-02 |
| two-bump (+) b=0.05 | 0.177245 | 0.94584 | +0.000000 | -0.006355 | +0.129453 | +3.623e-02 | +0.061799 | +0.067166 | -0.005367 | 9.88e-04 | 1.6e-01 | +0.068153 | **POS** | -2.557e-02 |
| two-bump (-) b=0.05 | 0.177245 | 1.00551 | +0.000000 | +0.053314 | -0.003811 | +1.364e-01 | +0.057023 | +0.007069 | +0.049954 | 3.36e-03 | 6.3e-02 | +0.003709 | **POS** | +7.935e-02 |
| h_b shift +log2/2 b=0.1 | 0.174822 | 0.85824 | +0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.010683 | +0.091368 | -0.080685 | 2.48e-04 | 3.1e-03 | +0.091616 | **POS** | +1.615e-02 |
| h_b shift -log2/2 b=0.1 | 0.174822 | 0.85824 | +0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.010683 | +0.092987 | -0.082305 | 1.37e-03 | 1.7e-02 | +0.091616 | **POS** | +1.615e-02 |
| two-bump (+) b=0.1 | 0.349644 | 1.61268 | +0.000000 | -0.265673 | +0.444141 | +7.098e-03 | +0.021964 | +0.284116 | -0.262152 | 3.52e-03 | 1.3e-02 | +0.287637 | **POS** | -1.487e-02 |
| two-bump (-) b=0.1 | 0.349644 | 1.82029 | +0.000000 | -0.058061 | -0.013074 | +1.002e-01 | +0.020767 | +0.084595 | -0.063827 | 5.77e-03 | 9.9e-02 | +0.078829 | **POS** | +7.947e-02 |
| h_b e^(i2x) b=0.2 | 0.354232 | 1.48061 | +0.000000 | -0.422387 | +0.425115 | +5.519e-04 | +0.000373 | +0.449048 | -0.448675 | 2.63e-02 | 6.2e-02 | +0.422760 | **POS** | +1.788e-04 |
| h_b e^(i5x) b=0.2 | 0.354232 | 1.70909 | +0.000000 | -0.193915 | +0.191367 | +8.692e-03 | +0.002585 | +0.230408 | -0.227823 | 3.39e-02 | 1.7e-01 | +0.196500 | **POS** | +6.107e-03 |
| h_b e^(i10x) b=0.2 | 0.354232 | 2.03679 | +0.000000 | +0.133793 | +0.007376 | +1.317e-01 | +0.036178 | -0.055588 | +0.091767 | 4.20e-02 | 3.1e-01 | -0.097614 | **NEG** | +9.554e-02 |
| v_R = chi_R f_0  R=0.5 | 1.000000 | 3.88372 | +0.000000 | -1.488461 | +1.563592 | +8.092e-10 | +0.000114 | +1.539290 | -1.539176 | 5.07e-02 | 3.4e-02 | +1.488575 | **POS** | -1.140e-04 |
| v_R = chi_R f_0  R=1.0 | 1.000000 | 3.88367 | +0.000000 | -1.488516 | +1.563713 | -7.770e-14 | +0.000114 | +1.539354 | -1.539240 | 5.07e-02 | 3.4e-02 | +1.488630 | **POS** | -1.140e-04 |
| pole-null v_+ | 1.000000 | 8.80929 | +0.000000 | +3.437106 | +0.000000 | +2.947e+00 | +3.307738 | +0.031878 | +3.275860 | 1.61e-01 | 4.7e-02 | -0.129368 | **?** | -3.608e-01 |
| pole-null v_- | 1.000000 | 8.80929 | +0.000000 | +3.437107 | +0.000000 | +3.927e+00 | +3.307569 | +0.012257 | +3.295312 | 1.42e-01 | 4.1e-02 | -0.129538 | **?** | +6.197e-01 |
| pole-null v_i | 1.000000 | 8.80929 | +0.000000 | +3.437107 | -0.000000 | +3.437e+00 | +3.307654 | +0.022068 | +3.285586 | 1.52e-01 | 4.4e-02 | -0.129453 | **?** | +1.295e-01 |
| wide cos bump b=3 [OUTSIDE window] | 1.000000 | 1.43327 | +0.000000 | -3.938912 | +14.716673 | +7.101e-06 | +0.000007 | +3.736515 | -3.736508 | 2.02e-01 | 5.1e-02 | +3.938919 | **POS** | +5.347e-08 |
| wide cos bump b=4 [OUTSIDE window] | 1.000000 | 1.06874 | +0.000000 | -4.303448 | +26.702646 | +1.004e-05 | +0.000002 | +3.921215 | -3.921214 | 3.82e-01 | 8.9e-02 | +4.303449 | **POS** | +8.341e-06 |
| wide cos bump b=6 [OUTSIDE window] | 1.000000 | 0.64572 | +0.000000 | -4.726463 | +91.228591 | +3.087e-06 | +0.000000 | +3.857972 | -3.857972 | 8.68e-01 | 1.8e-01 | +4.726463 | **POS** | +2.931e-06 |
| v_R quintic chi_R f_0 R=1 | 1.000000 | 3.88367 | +0.000000 | -1.488515 | +1.563710 | +3.787e-10 | +0.000114 | +1.539353 | -1.539239 | 5.07e-02 | 3.4e-02 | +1.488629 | **POS** | -1.140e-04 |
| v_R quintic chi_R f_0 R=2 | 1.000000 | 3.88367 | +0.000000 | -1.488516 | +1.563713 | -7.509e-14 | +0.000114 | +1.539354 | -1.539240 | 5.07e-02 | 3.4e-02 | +1.488630 | **POS** | -1.140e-04 |


### 5.3 S = {infinity, 2} at lambda = sqrt2 and lambda = 2, N = 8192

| test | \|v\|^2 | D(v) | prime sum | L_S | P_02 | Q(v) | N_S | E_S (direct) | N_S-E_S | abs.res | rel.res | E_impl = N_S-L_S | sign(E) | Q-N_S |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|
| h_b b=0.05 | 0.088623 | 0.48780 | +0.000000 | +0.011700 | +0.031436 | +4.314e-02 | +0.006978 | +0.196666 | -0.189688 | 2.01e-01 | 1.7e+01 | -0.004723 | **?** | +3.616e-02 |
| h_b b=0.1 | 0.177245 | 0.84503 | -0.000001 | -0.107166 | +0.125978 | +1.881e-02 | +0.000275 | +0.270836 | -0.270561 | 1.63e-01 | 1.5e+00 | +0.107442 | **POS** | +1.854e-02 |
| h_b b=0.2 | 0.354232 | 1.42252 | -0.011858 | -0.492335 | +0.492524 | +1.895e-04 | +0.000030 | +0.549195 | -0.549165 | 5.68e-02 | 1.2e-01 | +0.492365 | **POS** | +1.594e-04 |
| h_b b=0.3 | 0.519020 | 1.93525 | -0.068750 | -0.921770 | +0.923431 | +1.660e-03 | +0.000770 | +0.872743 | -0.871973 | 4.98e-02 | 5.4e-02 | +0.922541 | **POS** | +8.898e-04 |
| h_b b=0.5 | 0.731363 | 2.66215 | -0.169615 | -1.436483 | +1.448622 | +1.214e-02 | +0.004161 | +1.267182 | -1.263020 | 1.73e-01 | 1.2e-01 | +1.440645 | **POS** | +7.977e-03 |
| h_b shift +log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.006973 | -0.010275 | +0.017249 | 5.51e-03 | 4.7e-01 | -0.004767 | **NEG** | +3.618e-02 |
| h_b shift -log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.006973 | -0.007290 | +0.014263 | 2.52e-03 | 2.1e-01 | -0.004767 | **NEG** | +3.618e-02 |
| two-bump (+) b=0.05 | 0.177245 | 0.94584 | -0.086873 | -0.093228 | +0.129453 | +3.623e-02 | +0.008094 | +0.074955 | -0.066860 | 2.64e-02 | 2.8e-01 | +0.101322 | **POS** | +2.813e-02 |
| two-bump (-) b=0.05 | 0.177245 | 1.00551 | +0.086873 | +0.140187 | -0.003811 | +1.364e-01 | +0.019798 | -0.110086 | +0.129883 | 1.03e-02 | 7.3e-02 | -0.120389 | **NEG** | +1.166e-01 |
| h_b shift +log2/2 b=0.1 | 0.174822 | 0.85824 | -0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.001049 | +0.060865 | -0.059815 | 2.11e-02 | 2.6e-01 | +0.081983 | **POS** | +2.578e-02 |
| h_b shift -log2/2 b=0.1 | 0.174822 | 0.85824 | +0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.001048 | +0.067806 | -0.066758 | 1.42e-02 | 1.8e-01 | +0.081982 | **POS** | +2.578e-02 |
| two-bump (+) b=0.1 | 0.349644 | 1.61268 | -0.171371 | -0.437044 | +0.444141 | +7.098e-03 | +0.001366 | +0.349247 | -0.347881 | 8.92e-02 | 2.0e-01 | +0.438410 | **POS** | +5.732e-03 |
| two-bump (-) b=0.1 | 0.349644 | 1.82029 | +0.171371 | +0.113309 | -0.013074 | +1.002e-01 | +0.002829 | -0.091906 | +0.094735 | 1.86e-02 | 1.6e-01 | -0.110480 | **NEG** | +9.741e-02 |
| h_b e^(i2x) b=0.2 | 0.354232 | 1.48061 | -0.002175 | -0.424563 | +0.425115 | +5.519e-04 | +0.000030 | +0.498862 | -0.498832 | 7.43e-02 | 1.7e-01 | +0.424593 | **POS** | +5.219e-04 |
| h_b e^(i5x) b=0.2 | 0.354232 | 1.70909 | +0.011240 | -0.182675 | +0.191367 | +8.692e-03 | +0.000050 | +0.318305 | -0.318256 | 1.36e-01 | 7.4e-01 | +0.182725 | **POS** | +8.642e-03 |
| h_b e^(i10x) b=0.2 | 0.354232 | 2.03679 | -0.009452 | +0.124341 | +0.007376 | +1.317e-01 | +0.000429 | +0.069867 | -0.069438 | 1.94e-01 | 1.6e+00 | -0.123912 | **?** | +1.313e-01 |
| v_R = chi_R f_0  R=0.5 | 1.000000 | 3.88372 | -0.074018 | -1.562478 | +1.563592 | +8.092e-10 | +0.000010 | +1.618038 | -1.618028 | 5.56e-02 | 3.6e-02 | +1.562488 | **POS** | -9.629e-06 |
| v_R = chi_R f_0  R=1.0 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.770e-14 | +0.000010 | +1.618154 | -1.618144 | 5.56e-02 | 3.6e-02 | +1.562590 | **POS** | -9.630e-06 |
| pole-null v_+ | 1.000000 | 8.80929 | -0.490129 | +2.946977 | +0.000000 | +2.947e+00 | +2.285876 | -0.569638 | +2.855514 | 9.15e-02 | 3.1e-02 | -0.661101 | **NEG** | +6.611e-01 |
| pole-null v_- | 1.000000 | 8.80929 | +0.490129 | +3.927236 | +0.000000 | +3.927e+00 | +3.019861 | -0.661908 | +3.681769 | 2.45e-01 | 6.3e-02 | -0.907375 | **NEG** | +9.074e-01 |
| pole-null v_i | 1.000000 | 8.80929 | -0.000000 | +3.437107 | -0.000000 | +3.437e+00 | +2.652869 | -0.615773 | +3.268641 | 1.68e-01 | 4.9e-02 | -0.784238 | **NEG** | +7.842e-01 |
| wide cos bump b=3 [OUTSIDE window] | 1.000000 | 1.43327 | -1.952910 | -5.891821 | +14.716673 | +7.101e-06 | +0.000032 | +3.935718 | -3.935686 | 1.96e+00 | 3.3e-01 | +5.891854 | **POS** | -2.510e-05 |
| wide cos bump b=4 [OUTSIDE window] | 1.000000 | 1.06874 | -2.301207 | -6.604655 | +26.702646 | +1.004e-05 | +0.000034 | +3.963389 | -3.963355 | 2.64e+00 | 4.0e-01 | +6.604689 | **POS** | -2.399e-05 |
| wide cos bump b=6 [OUTSIDE window] | 1.000000 | 0.64572 | -2.711791 | -7.438254 | +91.228591 | +3.087e-06 | +0.000035 | +3.756714 | -3.756679 | 3.68e+00 | 4.9e-01 | +7.438288 | **POS** | -3.158e-05 |
| v_R quintic chi_R f_0 R=1 | 1.000000 | 3.88367 | -0.074064 | -1.562579 | +1.563710 | +3.787e-10 | +0.000010 | +1.618153 | -1.618143 | 5.56e-02 | 3.6e-02 | +1.562588 | **POS** | -9.630e-06 |
| v_R quintic chi_R f_0 R=2 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.509e-14 | +0.000010 | +1.618154 | -1.618144 | 5.56e-02 | 3.6e-02 | +1.562590 | **POS** | -9.630e-06 |


| test | \|v\|^2 | D(v) | prime sum | L_S | P_02 | Q(v) | N_S | E_S (direct) | N_S-E_S | abs.res | rel.res | E_impl = N_S-L_S | sign(E) | Q-N_S |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|
| h_b b=0.05 | 0.088623 | 0.48780 | +0.000000 | +0.011700 | +0.031436 | +4.314e-02 | +0.000094 | +0.202236 | -0.202142 | 2.14e-01 | 1.8e+01 | -0.011606 | **?** | +4.304e-02 |
| h_b b=0.1 | 0.177245 | 0.84503 | -0.000001 | -0.107166 | +0.125978 | +1.881e-02 | +0.000000 | +0.277313 | -0.277313 | 1.70e-01 | 1.6e+00 | +0.107166 | **POS** | +1.881e-02 |
| h_b b=0.2 | 0.354232 | 1.42252 | -0.011858 | -0.492335 | +0.492524 | +1.895e-04 | +0.000004 | +0.538319 | -0.538315 | 4.60e-02 | 9.3e-02 | +0.492338 | **POS** | +1.857e-04 |
| h_b b=0.3 | 0.519020 | 1.93525 | -0.068750 | -0.921770 | +0.923431 | +1.660e-03 | +0.000101 | +0.842513 | -0.842412 | 7.94e-02 | 8.6e-02 | +0.921871 | **POS** | +1.560e-03 |
| h_b b=0.5 | 0.731363 | 2.66215 | -0.169615 | -1.436483 | +1.448622 | +1.214e-02 | +0.000539 | +1.212295 | -1.211757 | 2.25e-01 | 1.6e-01 | +1.437022 | **POS** | +1.160e-02 |
| h_b shift +log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.000095 | -0.018543 | +0.018637 | 6.90e-03 | 5.9e-01 | -0.011645 | **NEG** | +4.306e-02 |
| h_b shift -log2/2 b=0.05 | 0.088623 | 0.48784 | -0.000000 | +0.011740 | +0.031411 | +4.315e-02 | +0.000095 | -0.014620 | +0.014715 | 2.97e-03 | 2.5e-01 | -0.011645 | **NEG** | +4.306e-02 |
| two-bump (+) b=0.05 | 0.177245 | 0.94584 | -0.086873 | -0.093228 | +0.129453 | +3.623e-02 | +0.000100 | +0.062198 | -0.062098 | 3.11e-02 | 3.3e-01 | +0.093328 | **POS** | +3.613e-02 |
| two-bump (-) b=0.05 | 0.177245 | 1.00551 | +0.086873 | +0.140187 | -0.003811 | +1.364e-01 | +0.000278 | -0.128524 | +0.128802 | 1.14e-02 | 8.1e-02 | -0.139909 | **NEG** | +1.361e-01 |
| h_b shift +log2/2 b=0.1 | 0.174822 | 0.85824 | -0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.000316 | +0.055241 | -0.054925 | 2.60e-02 | 3.2e-01 | +0.081250 | **POS** | +2.652e-02 |
| h_b shift -log2/2 b=0.1 | 0.174822 | 0.85824 | +0.000000 | -0.080934 | +0.107767 | +2.683e-02 | +0.000316 | +0.064348 | -0.064032 | 1.69e-02 | 2.1e-01 | +0.081250 | **POS** | +2.652e-02 |
| two-bump (+) b=0.1 | 0.349644 | 1.61268 | -0.171371 | -0.437044 | +0.444141 | +7.098e-03 | +0.000401 | +0.331808 | -0.331407 | 1.06e-01 | 2.4e-01 | +0.437444 | **POS** | +6.697e-03 |
| two-bump (-) b=0.1 | 0.349644 | 1.82029 | +0.171371 | +0.113309 | -0.013074 | +1.002e-01 | +0.000864 | -0.092630 | +0.093494 | 1.98e-02 | 1.7e-01 | -0.112446 | **NEG** | +9.937e-02 |
| h_b e^(i2x) b=0.2 | 0.354232 | 1.48061 | -0.002175 | -0.424563 | +0.425115 | +5.519e-04 | +0.000004 | +0.490855 | -0.490851 | 6.63e-02 | 1.6e-01 | +0.424566 | **POS** | +5.482e-04 |
| h_b e^(i5x) b=0.2 | 0.354232 | 1.70909 | +0.011240 | -0.182675 | +0.191367 | +8.692e-03 | +0.000004 | +0.320481 | -0.320477 | 1.38e-01 | 7.5e-01 | +0.182679 | **POS** | +8.688e-03 |
| h_b e^(i10x) b=0.2 | 0.354232 | 2.03679 | -0.009452 | +0.124341 | +0.007376 | +1.317e-01 | +0.000005 | +0.081531 | -0.081527 | 2.06e-01 | 1.7e+00 | -0.124336 | **?** | +1.317e-01 |
| v_R = chi_R f_0  R=0.5 | 1.000000 | 3.88372 | -0.074018 | -1.562478 | +1.563592 | +8.092e-10 | +0.000000 | +1.576485 | -1.576485 | 1.40e-02 | 9.0e-03 | +1.562478 | **POS** | +7.169e-10 |
| v_R = chi_R f_0  R=1.0 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.770e-14 | +0.000000 | +1.576599 | -1.576599 | 1.40e-02 | 9.0e-03 | +1.562581 | **POS** | -9.135e-11 |
| pole-null v_+ | 1.000000 | 8.80929 | -0.490129 | +2.946977 | +0.000000 | +2.947e+00 | +1.596994 | -1.207995 | +2.804989 | 1.42e-01 | 4.8e-02 | -1.349983 | **NEG** | +1.350e+00 |
| pole-null v_- | 1.000000 | 8.80929 | +0.490129 | +3.927236 | +0.000000 | +3.927e+00 | +2.353115 | -1.389256 | +3.742371 | 1.85e-01 | 4.7e-02 | -1.574121 | **NEG** | +1.574e+00 |
| pole-null v_i | 1.000000 | 8.80929 | -0.000000 | +3.437107 | -0.000000 | +3.437e+00 | +1.975055 | -1.298626 | +3.273680 | 1.63e-01 | 4.8e-02 | -1.462052 | **NEG** | +1.462e+00 |
| wide cos bump b=3 [OUTSIDE window] | 1.000000 | 1.43327 | -1.952910 | -5.891821 | +14.716673 | +7.101e-06 | +0.000000 | +3.638895 | -3.638895 | 2.25e+00 | 3.8e-01 | +5.891821 | **POS** | +6.977e-06 |
| wide cos bump b=4 [OUTSIDE window] | 1.000000 | 1.06874 | -2.301207 | -6.604655 | +26.702646 | +1.004e-05 | +0.000000 | +3.642416 | -3.642416 | 2.96e+00 | 4.5e-01 | +6.604655 | **POS** | +1.001e-05 |
| wide cos bump b=6 [OUTSIDE window] | 1.000000 | 0.64572 | -2.711791 | -7.438254 | +91.228591 | +3.087e-06 | +0.000000 | +3.407743 | -3.407743 | 4.03e+00 | 5.4e-01 | +7.438254 | **?** | +3.074e-06 |
| v_R quintic chi_R f_0 R=1 | 1.000000 | 3.88367 | -0.074064 | -1.562579 | +1.563710 | +3.787e-10 | +0.000000 | +1.576599 | -1.576599 | 1.40e-02 | 9.0e-03 | +1.562579 | **POS** | +7.847e-11 |
| v_R quintic chi_R f_0 R=2 | 1.000000 | 3.88367 | -0.074065 | -1.562581 | +1.563713 | -7.509e-14 | +0.000000 | +1.576599 | -1.576599 | 1.40e-02 | 9.0e-03 | +1.562581 | **POS** | -9.135e-11 |


## 6. THEOREM_CONTROL_CC20

Class fixed by the coordinator from Connes–Consani 2006.13771 Thm 1 (= Thm 6.11): `S = {infinity}`,
`lambda = 1`, `supp v subset [-(log2)/2, +(log2)/2]`, and the three linear conditions
`int v dx = 0`, `A_+(v) = 0`, `A_-(v) = 0`. On this class the theorem forces `E_inf <= 0`,
equivalently `Q(v) = L_inf(k*k^*) >= N_inf(k)`.

Construction used: `w_d = d_x (d_x^2 - 1/4) eta_d` with `eta` the standard `exp(-1/(1-s^2))` bump.
`int w = 0` because `w` is a total derivative; `A_pm(w) = int eta_d * (-d_x)(d_x^2 - 1/4) e^{+-x/2}
= 0` because `(d_x^2 - 1/4) e^{+-x/2} = 0`. Translates preserve all three conditions.
Numerically verified on all eight tests: `||v||^2 = 1.00000000` and
`|int v|, |A_+|, |A_-| <= 2.1e-17`. The third derivative of `eta` was checked against finite
differences (agreement `8.85e-08` at `h = 1e-5`, converging like `h^2`).
Since the support diameter is `<= log 2`, `C_v(log 2) = 0` and `P_02 = 0`, so `Q(v) = L_inf` exactly.

**Result (N = 8192).** `E_inf` computed *directly* from the block trace is `+0.031 .. +0.104` on all
eight tests, i.e. the wrong sign for the theorem — but on every one of them it is **smaller than the
identity residual**, and the value implied by the identity, `E_impl = N_inf - L_inf`, is **negative
on all eight** (`-0.024 .. -0.470`). So the theorem is **not violated beyond this model's error**,
and the test does what it was designed to do: it shows that **the direct block-trace `E` carries a
systematic positive bias of the order of the identity residual**. Every sign statement about `E`
below is therefore reported with both estimators (`E` direct and `E_impl = N - L`) and is called
resolved only when they agree and `|E| > |residual|`.

| test | \|v\|^2 | D(v) | L_inf = Q(v) | N_inf | E_inf (direct) | E_inf/N_inf | abs.res | E_impl = N_inf - L_inf | theorem (E<=0) |
|---|--:|--:|--:|--:|--:|--:|--:|--:|:--:|
| THM w_d d=0.05 | 1.000000 | 9.8351 | +4.462930 | +3.992484 | +0.031150 | +0.0078 | 5.02e-01 | -0.470446 | consistent |
| THM w_d d=0.1 | 1.000000 | 9.1420 | +3.769769 | +3.653560 | +0.059357 | +0.0162 | 1.76e-01 | -0.116209 | consistent |
| THM w_d d=0.2 | 1.000000 | 8.4487 | +3.076566 | +3.052154 | +0.054623 | +0.0179 | 7.90e-02 | -0.024412 | consistent |
| THM w_d d=0.3 | 1.000000 | 8.0432 | +2.671008 | +2.646340 | +0.034479 | +0.0130 | 5.91e-02 | -0.024668 | consistent |
| THM two-bump(+) d=0.08 a=0.25 | 1.000000 | 9.3651 | +3.992919 | +3.752618 | +0.082573 | +0.0220 | 3.23e-01 | -0.240301 | consistent |
| THM two-bump(-) d=0.08 a=0.25 | 1.000000 | 9.3651 | +3.992919 | +3.752648 | +0.083303 | +0.0222 | 3.24e-01 | -0.240271 | consistent |
| THM two-bump(i) d=0.08 a=0.25 | 1.000000 | 9.3651 | +3.992919 | +3.752633 | +0.082938 | +0.0221 | 3.23e-01 | -0.240286 | consistent |
| THM w_d d=0.1 shifted +0.2 | 1.000000 | 9.1420 | +3.769769 | +3.668926 | +0.103686 | +0.0283 | 2.05e-01 | -0.100842 | consistent |

(N-dependence)

| test | E_inf(N=4096) | E_inf(N=8192) |
|---|--:|--:|
| THM w_d d=0.05 | +0.031382 | +0.031150 |
| THM w_d d=0.1 | +0.070351 | +0.059357 |
| THM w_d d=0.2 | +0.074312 | +0.054623 |
| THM w_d d=0.3 | +0.051064 | +0.034479 |
| THM two-bump(+) d=0.08 a=0.25 | +0.100804 | +0.082573 |
| THM two-bump(-) d=0.08 a=0.25 | +0.101321 | +0.083303 |
| THM two-bump(i) d=0.08 a=0.25 | +0.101062 | +0.082938 |
| THM w_d d=0.1 shifted +0.2 | +0.132428 | +0.103686 |


## 7. Convergence of the identity residual |N_S - E_S - L_S|

Semilocal (S = {infinity, 2}), lambda = 1:

| test | N=2048 (delta=0.01562) | N=4096 (delta=0.01105) | N=8192 (delta=0.00781) | ratio |
|---|--:|--:|--:|--:|
| h_b b=0.05 | 2.151e-01 | 2.007e-01 | 1.760e-01 | 0.88 |
| h_b b=0.1 | 1.723e-01 | 1.623e-01 | 1.432e-01 | 0.88 |
| h_b b=0.2 | 4.989e-02 | 5.482e-02 | 5.255e-02 | 0.96 |
| h_b b=0.3 | 7.402e-02 | 5.268e-02 | 3.703e-02 | 0.70 |
| h_b b=0.5 | 2.176e-01 | 1.775e-01 | 1.404e-01 | 0.79 |
| h_b shift +log2/2 b=0.05 | 5.963e-03 | 6.022e-03 | 4.578e-03 | 0.76 |
| h_b shift -log2/2 b=0.05 | 1.976e-03 | 2.999e-03 | 1.227e-03 | 0.41 |
| two-bump (+) b=0.05 | 2.947e-02 | 2.743e-02 | 2.103e-02 | 0.77 |
| two-bump (-) b=0.05 | 1.359e-02 | 9.393e-03 | 9.424e-03 | 1.00 |
| h_b shift +log2/2 b=0.1 | 2.418e-02 | 2.211e-02 | 1.757e-02 | 0.79 |
| h_b shift -log2/2 b=0.1 | 1.495e-02 | 1.510e-02 | 9.863e-03 | 0.65 |
| two-bump (+) b=0.1 | 1.025e-01 | 9.122e-02 | 7.176e-02 | 0.79 |
| two-bump (-) b=0.1 | 2.426e-02 | 1.681e-02 | 1.690e-02 | 1.01 |
| h_b e^(i2x) b=0.2 | 7.027e-02 | 7.225e-02 | 6.737e-02 | 0.93 |
| h_b e^(i5x) b=0.2 | 1.420e-01 | 1.335e-01 | 1.196e-01 | 0.90 |
| h_b e^(i10x) b=0.2 | 2.101e-01 | 1.916e-01 | 1.697e-01 | 0.89 |
| v_R = chi_R f_0  R=0.5 | 2.473e-02 | 4.992e-02 | 5.850e-02 | 1.17 |
| v_R = chi_R f_0  R=1.0 | 2.474e-02 | 4.993e-02 | 5.852e-02 | 1.17 |
| pole-null v_+ | 2.317e-01 | 1.251e-01 | 6.702e-02 | 0.54 |
| pole-null v_- | 8.256e-01 | 5.802e-01 | 3.714e-01 | 0.64 |
| pole-null v_i | 5.286e-01 | 3.527e-01 | 2.192e-01 | 0.62 |
| wide cos bump b=3 [OUTSIDE window] | 2.251e+00 | 1.962e+00 | 1.672e+00 | 0.85 |
| wide cos bump b=4 [OUTSIDE window] | 2.961e+00 | 2.647e+00 | 2.319e+00 | 0.88 |
| wide cos bump b=6 [OUTSIDE window] | 4.029e+00 | 3.687e+00 | 3.333e+00 | 0.90 |
| v_R quintic chi_R f_0 R=1 | 2.474e-02 | 4.993e-02 | 5.852e-02 | 1.17 |
| v_R quintic chi_R f_0 R=2 | 2.474e-02 | 4.993e-02 | 5.852e-02 | 1.17 |


Archimedean control (S = {infinity}), lambda = 1 — the EXACT pair:

| test | N=2048 (delta=0.01562) | N=4096 (delta=0.01105) | N=8192 (delta=0.00781) | ratio |
|---|--:|--:|--:|--:|
| h_b b=0.05 | 8.856e-02 | 6.151e-02 | 4.450e-02 | 0.72 |
| h_b b=0.1 | 7.515e-02 | 5.091e-02 | 3.761e-02 | 0.74 |
| h_b b=0.2 | 4.830e-02 | 3.001e-02 | 2.414e-02 | 0.80 |
| h_b b=0.3 | 2.611e-02 | 1.256e-02 | 1.305e-02 | 1.04 |
| h_b b=0.5 | 1.927e-03 | 6.819e-03 | 9.623e-04 | 0.14 |
| h_b shift +log2/2 b=0.05 | 2.046e-04 | 8.392e-04 | 1.100e-04 | 0.13 |
| h_b shift -log2/2 b=0.05 | 2.110e-03 | 5.136e-04 | 1.076e-03 | 2.10 |
| two-bump (+) b=0.05 | 1.994e-03 | 3.374e-03 | 9.876e-04 | 0.29 |
| two-bump (-) b=0.05 | 6.622e-03 | 2.723e-03 | 3.360e-03 | 1.23 |
| h_b shift +log2/2 b=0.1 | 6.168e-04 | 2.331e-03 | 2.485e-04 | 0.11 |
| h_b shift -log2/2 b=0.1 | 2.681e-03 | 3.938e-05 | 1.371e-03 | 34.82 |
| two-bump (+) b=0.1 | 7.380e-03 | 8.940e-03 | 3.521e-03 | 0.39 |
| two-bump (-) b=0.1 | 1.151e-02 | 4.199e-03 | 5.766e-03 | 1.37 |
| h_b e^(i2x) b=0.2 | 5.259e-02 | 3.303e-02 | 2.629e-02 | 0.80 |
| h_b e^(i5x) b=0.2 | 6.782e-02 | 4.374e-02 | 3.391e-02 | 0.78 |
| h_b e^(i10x) b=0.2 | 8.403e-02 | 5.516e-02 | 4.203e-02 | 0.76 |
| v_R = chi_R f_0  R=0.5 | 1.015e-01 | 6.018e-02 | 5.072e-02 | 0.84 |
| v_R = chi_R f_0  R=1.0 | 1.015e-01 | 6.019e-02 | 5.072e-02 | 0.84 |
| pole-null v_+ | 4.502e-01 | 2.814e-01 | 1.612e-01 | 0.57 |
| pole-null v_- | 4.309e-01 | 2.628e-01 | 1.418e-01 | 0.54 |
| pole-null v_i | 4.405e-01 | 2.721e-01 | 1.515e-01 | 0.56 |
| wide cos bump b=3 [OUTSIDE window] | 3.910e-01 | 2.923e-01 | 2.024e-01 | 0.69 |
| wide cos bump b=4 [OUTSIDE window] | 6.879e-01 | 5.238e-01 | 3.822e-01 | 0.73 |
| wide cos bump b=6 [OUTSIDE window] | 1.322e+00 | 1.087e+00 | 8.685e-01 | 0.80 |
| v_R quintic chi_R f_0 R=1 | 1.015e-01 | 6.019e-02 | 5.072e-02 | 0.84 |
| v_R quintic chi_R f_0 R=2 | 1.015e-01 | 6.019e-02 | 5.072e-02 | 0.84 |


Read this pair of tables together: the archimedean residual falls by a factor ~0.62 per
doubling of N (i.e. like delta^{1.4}, delta = 1/sqrt(2N)), so the identity
L = N - E is confirmed as a converging numerical statement for the exact pair.
The semilocal residual falls only by ~0.85 and on several tests not at all: it is
approaching a nonzero floor set by the 20-octave model defect of section 0.

## 8. Discretisation budget

| source | size | how it was measured |
|---|---|---|
| `F_inf` involution / self-adjointness | `<= 4.5e-13` / exact `0` | direct |
| prolate eigenvalues `alpha_n` | `9e-08` (n=0) to `1e-02` (n=4) at N=4096 | independent GL-sinc solve |
| quadrature path (`D`, `C_v`, `A_pm`, primes) | `<= 1e-10` | `Q(v_R) = -7.8e-14` |
| Halmos block algebra | exact (rational) | `halmos.py` |
| `S_S` idempotency | `6e-10 .. 6e-08` | `\|\|S^2-S\|\|_max` |
| **semilocal model defect** (20-octave tail of `B_S`) | `\|\|W^T W - I\|\| = 0.249`, `\|\|F_S-F_S^T\|\| = 1.7e-2` | direct; does NOT shrink usefully with N |
| **identity residual** `\|N_S - E_S - L_S\|` | see the convergence table | scales like `delta ~ N^{-1/2}` |
| **translation defect of `E_S`** | `E_S` differs by 8-15% between `+log2/2` and `-log2/2` shifts of the same bump, while `N_S` agrees to `0.1%` | direct; localises the error in the `D_S` blocks |

The last row is the sharpest internal diagnostic: `f = v*v^*` is exactly translation invariant, so
`N_S` and `E_S` must be identical for the two shifted tests. `N_S` is (to `1e-3`); `E_S` is not
(to `1e-1`). The error therefore sits in the block trace (7), i.e. in `zeta_n`, whose tail decays
only like `1/u` and is cut at `U_max`. Any statement about `E_S` below the ~10% level is not
resolved by this implementation.

## 9. S6 — first pass (SUPERSEDED by section 10 — kept for the record)

> **Warning.** The paragraphs in this section were written from the `E_S (direct)` column before
> the CC20 theorem control was run. That control showed the direct `E` is biased upward by
> `0.02-0.5`. **Section 10 supersedes this section**; two of the verdicts below (`pole-null v_-`
> and `v_i`) are reversed there. Kept unedited so the correction is visible.

### the three sentences (first pass)

**(a) Does `E_S <= 0` hold on the support-matched tests?**
**No — and the failure is resolved, not an artefact.** At `lambda = 1`, `S = {infinity, 2}`,
`N = 8192`, both estimators (`E` direct from the block trace, and `E_impl = N_S - L_S`) agree on a
strictly positive `E_S`, by a margin far larger than the identity residual, on every single-bump
test, on both shifted bumps, on `two-bump(+)`, on the two low-frequency complex tests, and on the
canonical cutoffs `v_R` (`E_S = +1.62`, `E_impl = +1.56`, residual `0.06`). The only tests where
both estimators give `E_S < 0` are the two **antisymmetric** two-bump tests:
`E_S = -0.0326 / E_impl = -0.0420` (`b = 0.05`) and `E_S = -0.0392 / E_impl = -0.0561` (`b = 0.1`),
both stable across `N = 2048, 4096, 8192`. So the verdict's inequality (24), `E_S(k*k^*) <= 0` on
all compact tests, is **false in this model** — as the verdict's own Lemma 6 plant predicts. The
control where the sign is a theorem behaves correctly: on the wide positive bumps outside the
window, `E_S ~ +4.1..+4.3` and `N_S ~ +0.0025`, i.e. `E > N > 0`.

**(b) Where is it tightest?**
On the exactly pole-null two-bump tests and on the antisymmetric two-bump tests. For `v_+` the two
estimators give `E_S/N_S = +0.0299` and `+0.0074` — both inside `(0, 1/4)`, which **confirms the
registered prediction** for that test, but only by a factor of a few over the residual. For `v_-`
and `v_i` the two estimators disagree in sign (`+0.032` vs `-0.340`, `+0.060` vs `-0.159`), so those
are **not resolved**. The same holds for `h_b e^{i10x}` (`+0.133` vs `-0.037`). The margin
`Q - N_S` is negative — the verdict's kill inequality (21) — on `h_b b >= 0.2`, on `two-bump(+)`,
on the low-frequency complex tests, on the wide controls, and most cleanly on the canonical cutoffs
(`Q = -7.8e-14` against `N_S = +1.445e-03`, i.e. `Q - N_S = -1.445e-03 < 0`); it is positive on the
narrow bumps and on the pole-null tests. So the bare fixed-`S` Sonin trace is neither a minorant nor
a majorant of `Q` — exactly the scoped refutation the verdict states.

**(c) Anything strange?**
Four things. (i) The direct block-trace `E` is biased positive by about the identity residual; this
was invisible until the CC20 theorem control was run, and it is the reason (b) is stated with two
estimators. (ii) The angle spectrum of the semilocal pair does not decay like the archimedean
(prolate) one: at `lambda = 1` there are 41 angles above `1e-6` versus 7, with a slow
`0.655, 0.580, 0.477, 0.446, ...` tail; the `D_S` sum is not dominated by a few blocks in the
semilocal case, which is a real obstacle to any "few-block" estimate of `E_S`. (iii) `N_S` is
exactly translation invariant in exact arithmetic and is reproduced to `~1e-3` by the model, while
`E_S` is only reproduced to `~1e-1` on the same pair of shifted tests — the whole discretisation
error sits in the `D_S` blocks, i.e. in the `zeta_n` whose `1/u` tails are cut at `U_max`. (iv) The
semilocal Fourier operator cannot be carried faithfully by any finite carrier of feasible size
(section 0): the identity residual converges like `delta` for `S = {infinity}` but stalls at a floor
for `S = {infinity, 2}`. Nothing here contradicts the verdict; what it does contradict is any hope
of settling the *sign* of `E_S` on the tight tests with a carrier of this size.

---

## 10. Correction after the THEOREM_CONTROL_CC20 result: sign verdicts from `Q - N_S` only

**The theorem control PASSES for the pair `(Q, N_inf)` and FAILS for the direct `E` column.**
On all eight tests of the CC20 class the model gives `Q = L_inf >= N_inf` with margin
`0.024 .. 0.470` — exactly what Connes–Consani Thm 1 (= Thm 6.11) requires. The same theorem
therefore forces `E_inf = N_inf - L_inf <= -0.024 .. -0.470`, whereas the value computed
*directly* from the block trace (7) is `+0.031 .. +0.104`. The direct `E` is wrong by
`0.02 .. 0.47` on this class, while `N_inf` (Hilbert–Schmidt norm of `theta S_S`) and `L`
(pure quadrature) are jointly consistent with the theorem. **All sign verdicts below are
therefore recomputed from `Q` and `N_S` only; the `E_S (direct)` column of section 5 is retained
for the record but must not be used for a sign.**

**Diagnosis of the `E` defect.** `E` is `Tr(theta_f D_S) - ell f(1)`, and `D_S` lives on the
2-dimensional blocks `(xi_n, zeta_n)`. `xi_n` is a prolate-type function supported in `(0,lambda)`
and is represented very well; `zeta_n` is the normalised `(I-P) Q xi_n`, whose physical tail is
`F_inf xi_n(u) ~ sin(2 pi lambda u) xi_n(lambda)/(pi u)`, i.e. it decays only like `1/u` and is
**cut at `U_max`**. Its `theta_f`-expectation `<zeta_n, theta_f zeta_n>` is therefore
systematically too small, and since `zeta` enters `D_S` with coefficient `-alpha^2`, the block
trace is biased **upward**. Two independent signatures confirm this: (i) the residual
`N_S - E_S - L_S` is **negative on every test** of the theorem class and on almost every test of
the main family; (ii) `E_S` differs by 8–15 % between the `+log2/2` and `-log2/2` translates of the
same bump — a quantity that is exactly translation invariant in exact arithmetic — whereas `N_S`
differs by only 0.1–0.3 % on the same pair.

**Error bar on `N_S`.** Two independent contributions, the larger of which is taken:
(a) *translation defect*: `N_S` on the `+log2/2` and `-log2/2` translates of the same bump differs
by `9.2e-04` (relative) at `b = 0.05` and `3.4e-03` at `b = 0.1` (N = 8192); we use `3.4e-03` as
the floor.
(b) *semilocal model asymmetry*: `N_S` recomputed with the **symmetrised** `F_S`
(`(F_S + F_S^T)/2`, i.e. propagating `||F_S - F_S^T|| = 1.7e-02` directly into the Sonin
subspace) — the raw and symmetrised values and their difference are in `bar_N4096.json` /
`bar_N8192.json`. The relative difference is `8e-05 .. 1e-03` on the pole-null triple (where `N_S`
is O(3)), `3.5e-02 .. 1.7e-01` on the ordinary bumps, and `2.9e-01 .. 5.0e-01` on the tests whose
`N_S` is at the `1e-3` level (`h_b b=0.2`, `v_R`, wide bumps). Where an `N = 8192` value exists it
is used; otherwise the `N = 4096` relative figure is applied to the `N = 8192` `N_S`.

Note the exact algebraic relation used below: for a support-matched test the far-prime sum in (15)
vanishes, so `Q = L_S + P_02` and hence `Q - N_S = P_02 - E_S`; for the non-support-matched tests
(`v_R`, wide bumps) `L_S` from the quadrature is used directly. In both cases the estimator is
`E_true = N_S - L_S`, with `L_S` exact to `~1e-10` and the whole uncertainty carried by `N_S`.

### 10.1 Sign table recomputed from `Q` and `N_S` (S = {infinity, 2}, lambda = 1, N = 8192)

| test | Q(v) | N_S | bar(N_S) | Q - N_S | L_S | E_true = N_S - L_S | sign(E_true) | Q >= N_S ? |
|---|--:|--:|--:|--:|--:|--:|:--:|:--:|
| h_b b=0.05 | +4.313596e-02 | +0.035892 | 1.76e-03 | +7.2444e-03 | +0.011700 | +0.024191 | **POS** | YES |
| h_b b=0.1 | +1.881153e-02 | +0.013772 | 1.63e-03 | +5.0397e-03 | -0.107166 | +0.120938 | **POS** | YES |
| h_b b=0.2 | +1.895412e-04 | +0.000801 | 2.33e-04 | -6.1105e-04 | -0.492335 | +0.493135 | **POS** | **NO** |
| h_b b=0.3 | +1.660200e-03 | +0.003093 | 3.03e-04 | -1.4327e-03 | -0.921770 | +0.924863 | **POS** | **NO** |
| h_b b=0.5 | +1.213853e-02 | +0.015646 | 8.43e-04 | -3.5079e-03 | -1.436483 | +1.452130 | **POS** | **NO** |
| h_b shift +log2/2 b=0.05 | +4.315038e-02 | +0.035917 | 1.74e-03 | +7.2336e-03 | +0.011740 | +0.024177 | **POS** | YES |
| h_b shift -log2/2 b=0.05 | +4.315038e-02 | +0.035884 | 1.78e-03 | +7.2665e-03 | +0.011740 | +0.024144 | **POS** | YES |
| two-bump (+) b=0.05 | +3.622514e-02 | +0.045443 | 1.62e-03 | -9.2177e-03 | -0.093228 | +0.138671 | **POS** | **NO** |
| two-bump (-) b=0.05 | +1.363764e-01 | +0.098158 | 5.41e-03 | +3.8218e-02 | +0.140187 | -0.042029 | **NEG** | YES |
| h_b shift +log2/2 b=0.1 | +2.683319e-02 | +0.019539 | 2.11e-03 | +7.2940e-03 | -0.080934 | +0.100473 | **POS** | YES |
| h_b shift -log2/2 b=0.1 | +2.683319e-02 | +0.019473 | 2.18e-03 | +7.3607e-03 | -0.080934 | +0.100406 | **POS** | YES |
| two-bump (+) b=0.1 | +7.097566e-03 | +0.020809 | 1.97e-03 | -1.3711e-02 | -0.437044 | +0.457852 | **POS** | **NO** |
| two-bump (-) b=0.1 | +1.002352e-01 | +0.057215 | 9.25e-03 | +4.3020e-02 | +0.113309 | -0.056095 | **NEG** | YES |
| h_b e^(i2x) b=0.2 | +5.519483e-04 | +0.001377 | 3.06e-04 | -8.2485e-04 | -0.424563 | +0.425939 | **POS** | **NO** |
| h_b e^(i5x) b=0.2 | +8.691911e-03 | +0.008656 | 1.48e-03 | +3.5443e-05 | -0.182675 | +0.191331 | **POS** | ? |
| h_b e^(i10x) b=0.2 | +1.317164e-01 | +0.087411 | 1.11e-02 | +4.4305e-02 | +0.124341 | -0.036930 | **NEG** | YES |
| v_R = chi_R f_0  R=0.5 | +8.091916e-10 | +0.001445 | 4.96e-04 | -1.4454e-03 | -1.562478 | +1.563924 | **POS** | **NO** |
| v_R = chi_R f_0  R=1.0 | -7.770173e-14 | +0.001445 | 4.96e-04 | -1.4453e-03 | -1.562581 | +1.564026 | **POS** | **NO** |
| pole-null v_+ | +2.946977e+00 | +2.968850 | 1.01e-02 | -2.1873e-02 | +2.946977 | +0.021873 | **POS** | **NO** |
| pole-null v_- | +3.927236e+00 | +3.587681 | 1.22e-02 | +3.3956e-01 | +3.927236 | -0.339556 | **NEG** | YES |
| pole-null v_i | +3.437107e+00 | +3.278265 | 1.11e-02 | +1.5884e-01 | +3.437107 | -0.158841 | **NEG** | YES |
| wide cos bump b=3 [OUTSIDE window] | +7.100884e-06 | +0.002247 | 1.12e-03 | -2.2399e-03 | -5.891821 | +5.894068 | **POS** | **NO** |
| wide cos bump b=4 [OUTSIDE window] | +1.004341e-05 | +0.002429 | 1.26e-03 | -2.4187e-03 | -6.604655 | +6.607083 | **POS** | **NO** |
| wide cos bump b=6 [OUTSIDE window] | +3.087228e-06 | +0.002521 | 1.28e-03 | -2.5177e-03 | -7.438254 | +7.440774 | **POS** | **NO** |
| v_R quintic chi_R f_0 R=1 | +3.787275e-10 | +0.001445 | 4.40e-04 | -1.4453e-03 | -1.562579 | +1.564024 | **POS** | **NO** |
| v_R quintic chi_R f_0 R=2 | -7.509271e-14 | +0.001445 | 4.40e-04 | -1.4453e-03 | -1.562581 | +1.564026 | **POS** | **NO** |

* `E_true > 0` beyond the bar: 21 tests -> ['h_b b=0.05', 'h_b b=0.1', 'h_b b=0.2', 'h_b b=0.3', 'h_b b=0.5', 'h_b shift +log2/2 b=0.05', 'h_b shift -log2/2 b=0.05', 'two-bump (+) b=0.05', 'h_b shift +log2/2 b=0.1', 'h_b shift -log2/2 b=0.1', 'two-bump (+) b=0.1', 'h_b e^(i2x) b=0.2', 'h_b e^(i5x) b=0.2', 'v_R = chi_R f_0  R=0.5', 'v_R = chi_R f_0  R=1.0', 'pole-null v_+', 'wide cos bump b=3 [OUTSIDE window]', 'wide cos bump b=4 [OUTSIDE window]', 'wide cos bump b=6 [OUTSIDE window]', 'v_R quintic chi_R f_0 R=1', 'v_R quintic chi_R f_0 R=2']
* `E_true < 0` beyond the bar: 5 tests -> ['two-bump (-) b=0.05', 'two-bump (-) b=0.1', 'h_b e^(i10x) b=0.2', 'pole-null v_-', 'pole-null v_i']
* unresolved: 0 tests -> []

### 10.2 The three sentences, rewritten in terms of `Q - N_S`

**(a) Does `E_S <= 0` hold on the support-matched tests?**
**No, and it is now resolved on every one of them — no test is left undetermined.** With
`E_true = N_S - L_S` and the `N_S` bar above, **21 of the 26 tests have `E_true > 0` beyond the
bar** and **5 have `E_true < 0` beyond the bar**. The negative ones are exactly the
*antisymmetric / high-frequency* directions: `two-bump(-) b=0.05` (`E = -0.0420`, bar `5.4e-03`),
`two-bump(-) b=0.1` (`-0.0561`, bar `9.3e-03`), `h_b e^{i10x} b=0.2` (`-0.0369`, bar `1.1e-02`),
`pole-null v_-` (`-0.3396`, bar `1.2e-02`) and `pole-null v_i` (`-0.1588`, bar `1.1e-02`).
So the verdict's (24), `E_S(k*k^*) <= 0` on all compact tests, is **false** — it fails on 21 of 26
tests, including every single narrow bump and both canonical cutoffs (`E_true = +1.564`), while it
*holds* on five antisymmetric directions. The wide-bump control behaves as the exact theorem
requires: `E_true = +5.89, +6.61, +7.44` against `N_S = +0.0022, +0.0024, +0.0025`, i.e.
`E > N > 0`.

**(b) Where is it tightest, and does `N_S` minorise `Q`?**
The minorant `Q >= N_S` — the inequality the verdict kills in (21) — **fails on 14 of the 26 tests**,
holds on 11 and is marginal on 1, so `N_S` is neither a minorant nor a majorant of `Q`. It fails most
cleanly on the canonical cutoffs, where `Q` is machine zero and `N_S` is not:
`Q - N_S = -1.4453e-03` against a bar of `4.4e-04` for `v_R` with the explicit quintic cutoff at
`R = 2` (`Q = -7.5e-14`), which is the numerical form of (21). It also fails on `h_b b >= 0.2`, on
`two-bump(+)`, on `h_b e^{i2x}`, on all three wide controls, and — most interestingly — on the
pole-null `v_+` (`Q - N_S = -2.19e-02`, bar `1.0e-02`). The tightest case is `h_b e^{i5x}`
(`Q - N_S = +3.5e-05` against a bar of `1.5e-03` — **the one test where the minorant question is
not decided**); next tightest is `pole-null v_+`. For the pole-null triple, where `P_02 = 0` exactly so that
`E_true = -(Q - N_S)` with no extra term, the classification is sharp because `N_S ~ 3` and its bar
is only `~1e-02`:

| test | `Q` | `N_S` | bar | `Q - N_S` | `E_true` | `E_true/N_S` | classification |
|---|--:|--:|--:|--:|--:|--:|:--|
| `v_+` | `+2.946977` | `+2.968850` | `1.01e-02` | `-2.1873e-02` | `+0.021873` | `+0.00737` | `E_true > 0`, and `0 < E/N < 1/4` — **the registered prediction is confirmed** |
| `v_-` | `+3.927236` | `+3.587681` | `1.22e-02` | `+3.3956e-01` | `-0.339556` | `-0.09465` | `E_true < 0`, resolved |
| `v_i` | `+3.437107` | `+3.278265` | `1.11e-02` | `+1.5884e-01` | `-0.158841` | `-0.04843` | `E_true < 0`, resolved |

**(c) Anything strange?**
Five things, in decreasing order of importance. (i) The direct block-trace `E` is biased upward by
`0.02–0.5`; the CC20 theorem control is what exposed it, and without that control the section-5
`E_S` column would have produced two wrong sign verdicts (`pole-null v_-` and `v_i`, where the
direct `E` says `+0.032` and `+0.060` and the reliable estimator says `-0.340` and `-0.159`).
(ii) The three pole-null tests, built from the *same* `w` and differing only in the phase
(`+`, `-`, `i`) with `||v|| = 1` and identical `D(v) = 9.365102`, split cleanly in the sign of
`E_true`: `+` gives `E > 0`, `-` and `i` give `E < 0`. The sign of `E_S` is not a property of the
support or of the energy; it is a property of the relative phase across the `log 2` separation.
(iii) The angle spectrum of the semilocal pair does not decay like the archimedean (prolate) one:
41 angles above `1e-6` at `lambda = 1` versus 7, with a slow `0.655, 0.580, 0.477, 0.446, ...`
tail; and symmetrising `F_S` changes that count from 54 to 76 (N=4096) / 73 to 105 (N=8192), which
is a direct measure of how badly the semilocal pair is pinned down on a finite carrier.
(iv) `N_S` is far better conditioned than `E_S` — 0.1–0.3 % translation defect versus 8–15 % —
because it is a Hilbert–Schmidt norm over the common kernel and does not involve the `zeta_n`
tails. (v) The semilocal Fourier operator cannot be carried faithfully by any finite carrier of
feasible size (section 0), and this shows up as an identity residual that falls like `delta^{1.4}`
for `S = {infinity}` (median ratio 0.63 then 0.77 per doubling of `N`) but only like `delta^{0.3}`
for `S = {infinity, 2}` (median ratio 0.92 then 0.88), i.e. approaching a nonzero floor.
