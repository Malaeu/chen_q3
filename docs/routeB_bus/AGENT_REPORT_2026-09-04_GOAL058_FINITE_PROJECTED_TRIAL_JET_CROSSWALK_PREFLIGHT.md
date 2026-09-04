# AGENT REPORT — GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT

**Basis line (convention card rule).** Everything below is in the FULL mode basis
`c_n, n in [-N,N]` of `docs/routeB_bus/CONVENTION_CARD_GOAL058.md`, i.e. the row that
`portable_k_channel_v1.py` writes into `portable_k_coeffs_lambda_sq_<m>_N_<N>.json`
and that Lean calls `c_n i h hLp hNonzero`. No `v`/`y` even coordinates, no `sqrt 2`.
Curvature is the anchored second jet `kappa(F) = -F''(0)/(2 F(0))`.

- MODE: PAPER_AND_SOURCE READ_ONLY. No Lean edit, no commit, no route promotion.
- TASK_ID: `GOAL058_FINITE_PROJECTED_TRIAL_JET_CROSSWALK_PREFLIGHT`
- Verdict answered: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_TRIAL_SECOND_JET_EXACT_AND_GROUND_TRIAL_JET_GAP_2026-09-04.md`
- **CODE: `P59_FINITE_PROJECTED_TRIAL_JET_RATE_CROSSWALK` (SUCCESS).**
- **FALSIFIER NOT TRIGGERED.** Neither correction carries a `lambda^-2` term, neither
  touches `1/(16 pi)`, and both are super-polynomially small through the second jet.
- `PX_RH_CLAIM: NOT_MADE`. `RH_CLAIM: false`. All numbers are DIAGNOSTIC, never a proof.

---

## 0. One-line answer

On the production law `N = lambda^2 = m`, `L = log m`:

| correction | exact size | vs `lambda^-4 = m^-2` |
|---|---|---|
| finite Fourier projection tail `kappa(P_{lambda,N})` | `exp(-pi^2 m / (2 log m))` up to `poly` | `1.5e-9` at `m=13`, `4.7e-37` at `m=83` |
| lower multiplicative window tail `kappa(B_lambda)` | `exp(-pi m)` up to `poly` | `3.1e-16` at `m=13`, `3.9e-110` at `m=83` |

Both are `o(lambda^-K)` for every `K`. The projection tail dominates the window tail for
every `m > e^{pi/2} = 4.81`, and the gap widens with `m`. `E_{lambda,N}` is the one that
is only *geometrically* small; `B_lambda` is the one that is *exponentially* small in `m`
itself. Neither is polynomially small: the requested `O(lambda^-4)` target is not merely
true, it is enormously conservative.

---

## 1. The exact objects, in the project's own conventions

Locators (all verified on disk, this session):

| object | file | line-level anchor |
|---|---|---|
| `lambda_m = sqrt m`, `L_m = log m`, `dStar = du/u`, `I_m = [lambda^-1, lambda]` | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean` | `def lambda_m`, `def dStar`, `def I_m` |
| `V_{n,m}(u) = L^{-1/2} exp(2 pi i n log(lambda u)/L)` | same file | `def V_n_m` |
| `E_star(h)(u) = sqrt u * sum_{n>=1} h(n u)` | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean` | `def E_star` |
| `kTrial_{m,N}` = normalized orthogonal projection, `||kTrial|| = 1` | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean` | `def kTrial_m_N`, `theorem norm_kTrial_m_N` |
| `F_{q,N}(z) = int_{I_m} kTrial(u) u^{-i z} d*u = ` raw P59 transform of the row | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean` | `selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate` |
| `F(0) = sqrt L * v_0`; `F''(0) = -(L^2 sqrt L)(v_0/12 + (1/(2 pi^2)) sum_{k != 0} v_k/k^2)` | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean` | `proposition59RawTransform_at_zero_eq_sqrt`, `proposition59RawTransform_secondDerivative_zero` |
| numeric builder: window split at `x = log(m/j)`, `u = e^x/lambda`, `t = j e^x / m` | `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/true_precision_packet_gate_v1.py` | `split_intervals`, `integrate_coefficients` |
| `g04` = zero-integral combination of prolate `psi_0, psi_4`; `pN_norm` = `||P_N f||` | same file / `portable_k_channel_v1.py` | `build_prolate_model`, `build_coeff_cache` |

Set

```
lambda = sqrt m,   L = log m = 2 log lambda,
x = log(lambda u) in [0, L],   s = x - L/2 = log u,
h_lambda(y) = g04(y/lambda)  supported in |y| <= lambda,
k_lambda(u) = E_star(h_lambda)(u) = sqrt u * sum_{n>=1} h_lambda(n u),
f_lambda(x) = k_lambda(e^x / lambda),
Phi_lambda(s) = k_lambda(e^s)                       (the same function, centred)
c_n = <V_n, k_lambda> = L^{-1/2} int_0^L f_lambda(x) e^{-2 pi i n x / L} dx.
```

The builder's `raw_norm_g04` is `||f_lambda||_{L^2[0,L]}` and its `pN_norm_g04` is
`||P_N f_lambda||_2` — the exact normalization of (2.2). **Two exact structural facts of
the source construction that everything below rests on:**

- `int_{-lambda}^{lambda} h_lambda = 0` **exactly**, by the cross-product construction
  `g04_c = normalize_real_combo([integrals[4], -integrals[0]])`. Hence `hhat_lambda(0) = 0`.
- `h_lambda` is supported in `[-lambda, lambda]` **exactly**, so `k_lambda(u) = 0` for
  `u > lambda`: the **upper** window tail is identically zero, not merely small.

### 1.1 The exact sampling identity (the key to the whole ledger)

Directly from the definitions, for **every** integer `n`:

```
c_n = (-1)^n L^{-1/2} H_lambda(2 pi n / L),        H_lambda(z) = int_{lambda^-1}^{lambda} k_lambda(u) u^{-i z} d*u.
```

*Proof.* `H_lambda(z) = int_0^L f_lambda(x) e^{-i z (x - L/2)} dx`; at `z = 2 pi n/L` the phase
`e^{i z L/2}` is `e^{i pi n} = (-1)^n`. QED.

So **the project's coefficient row is the windowed Mellin transform sampled on the lattice
`z = 2 pi n / L`, with an alternating sign.** The `(-1)^n` in the convention card's
`f_k(x_n) = (-1)^n x_n` is exactly this phase. Everything the judge calls "the finite
Fourier projection" is therefore *aliasing of a sampled Mellin transform*, and its second-jet
cost is computable in closed form (Section 3).

---

## 2. Required output (1) — `B_lambda` and `E_{lambda,N}` with all constants

**Lower multiplicative window tail.**

```
B_lambda(z) = int_0^{lambda^-1} E_star(h_lambda)(u) u^{-i z} d*u
            = int_{-inf}^{-L/2} Phi_lambda(s) e^{-i z s} ds,
H_lambda(z) = A_lambda(z) - B_lambda(z),     A_lambda(z) = zeta(w) M_lambda(w),  w = 1/2 - i z.
```

No upper tail term: `k_lambda` vanishes identically above `u = lambda` by support.

**Finite Fourier projection tail.**

```
E_{lambda,N}(z) = e^{i z L/2} int_0^L ((I - P_N) f_lambda)(x) e^{-i z x} dx
                = sum_{|n| > N} (-1)^n L^{-1/2} H_lambda(2 pi n / L) * kernelHat_n(z),
```

where `kernelHat_n(z) = e^{izL/2} int_0^L U_n(x) e^{-izx} dx = 2 L^{-1/2} sin(zL/2)/(z - 2 pi n/L)`
is precisely `proposition59PoleKernel L n z` up to the `L^{-1/2}` factor kept in
`proposition59RawTransform`. The exact repair is the judge's (2.2):

```
F_{q,N}(z) = ||P_N f_lambda||_2^{-1} (H_lambda(z) - E_{lambda,N}(z)).
```

---

## 3. Required output (2) — values and second derivatives at `z = 0`

### 3.1 `E_{lambda,N}(0) = 0` — **exactly, not approximately**

`E_{lambda,N}(0) = int_0^L ((I - P_N) f_lambda)(x) dx = sqrt L * <U_0, (I - P_N) f_lambda> = 0`
because `U_0` lies in the range of `P_N`. This is pure orthogonality; it is Lean-ready with no
analysis at all, and it kills the `E(0)` term of the judge's (2.8) and (3.3) identically.

### 3.2 `E''_{lambda,N}(0)` in closed form

`E(z) = int_{-L/2}^{L/2} r(s + L/2) e^{-izs} ds` with `r = (I - P_N) f_lambda`, so
`E''(0) = - int_0^L (x - L/2)^2 r(x) dx = - <(I - P_N) P_2 , f_lambda>` with `P_2(x) = (x - L/2)^2`.
The Fourier coefficients of `P_2` are `p_n = <U_n, P_2> = L^{5/2}/(2 pi^2 n^2)` for `n != 0`
(`p_0 = L^{5/2}/12`). Hence, exactly:

```
E_{lambda,N}(0)   = 0
E_{lambda,N}''(0) = - (L^{5/2} / (2 pi^2)) * sum_{|n| > N} c_n / n^2
                  = - (L^{5/2} / pi^2)   * sum_{n > N}  c_n / n^2      (even row).
```

Note `p_n = L^{5/2} * proposition59SecondJetCoefficient n` — the same rational kernel already
kernel-checked in `Proposition59EntireTransform.lean`. This is bookkeeping, not new analysis.

### 3.3 `B_lambda(0)`, `B_lambda''(0)`

```
B_lambda(0)   =   int_{-inf}^{-L/2} Phi_lambda(s) ds
B_lambda''(0) = - int_{-inf}^{-L/2} s^2 Phi_lambda(s) ds.
```

On the whole range of integration `Phi_lambda` is given by the **exact** Poisson/Voronoi form
(legal because `hhat_lambda(0) = int h_lambda = 0`):

```
Phi_lambda(s) = e^{-s/2} sum_{k>=1} hhat_lambda(k e^{-s})  -  e^{s/2} h_lambda(0) / 2,
```

and `s <= -L/2` means every argument `k e^{-s} >= lambda` is **out of the prolate band**
(`hhat_lambda(xi) = lambda * g04hat(lambda xi)`, and `g04hat` is band-concentrated on
`|nu| <= m` because `c = 2 pi m` in `build_prolate_model`). Therefore

```
|B_lambda(0)|   <= C  ( sup_{xi >= lambda} |hhat_lambda(xi)| * lambda^{1/2} + lambda^{-1/2} |g04(0)| )
|B_lambda''(0)| <= C (1 + L^2) ( same two quantities ).
```

---

## 4. Required output (3) — the induced curvature correction, exact algebra then bound

The judge's quotient algebra (3.3), re-derived here and confirmed:
for `F = H - E`, `kappa(F) - kappa(H) = [H(0)E''(0) - H''(0)E(0)] / (2 H(0)(H(0) - E(0)))`.

### 4.1 Projection part — closed form, no inequality needed

With `E(0) = 0` and `H(0) = sqrt L c_0` this collapses to

```
kappa(P_{lambda,N}) := kappa(F_{q,N}) - kappa(H_lambda)
                     = E''_{lambda,N}(0) / (2 H_lambda(0))
                     = - (L^2 / (2 pi^2)) * sum_{n > N} (c_n / c_0) / n^2 .        (*)
```

This is an **identity**, not an estimate. It is the exact tail of the same series that gives
the project's curvature

```
kappa(F_{q,N}) = L^2/24 + (L^2/(2 pi^2)) * sum_{k=1}^{N} (c_k/c_0)/k^2 ,
```

which is what `proposition59RawTransform_secondDerivative_zero` computes and what makes the
judge's (4.1) a difference of two such sums. Both derivations were carried out independently
here and agree; the numeric check is in Section 6, row `m=13`.

### 4.2 Window part

```
kappa(B_lambda) := kappa(H_lambda) - kappa(A_lambda)
                 = [A(0) B''(0) - A''(0) B(0)] / (2 A(0)(A(0) - B(0))) ,
```
so with `|B(0)| << |A(0)|`

```
|kappa(B_lambda)| <= ( |B''(0)| / |A(0)| + 2 |kappa(A)| |B(0)| / |A(0)| ) * (1 + O(|B(0)/A(0)|)) .
```

`A(0) = zeta(1/2) M_lambda(1/2)` is the anchor; it is `O(1)` relative to `||f_lambda||` and
bounded away from zero on every registered cell (`c_0` is the dominant coefficient in all
caches). Combining with Section 3.3:

```
|kappa(B_lambda)| <= C (1 + L^2) ( lambda^{1/2} sup_{xi>=lambda} |hhat_lambda| + lambda^{-1/2}|g04(0)| ) / |A(0)| .
```

### 4.3 Total, on `N = lambda^2 = m`

```
| kappa(B_lambda + P_{lambda,N}) |
      <= (L^2/(2 pi^2)) sum_{n>m} |c_n/c_0| / n^2
       + C (1 + L^2) ( lambda^{1/2} sup_{xi>=lambda}|hhat_lambda| + lambda^{-1/2}|g04(0)| ) / |A(0)| .
```

The first term is bounded in Section 5.3, the second in Section 5.2.

---

## 5. Required output (4) — endpoints, jumps, and the true decay law

### 5.1 `f_lambda` has NO endpoint jump: the two mechanisms, named separately

The naive expectation is wrong and it is worth stating why, because it is the whole content
of the crosswalk. `f_lambda` is built by a sum whose number of terms **drops by one** at each
breakpoint `x_j = log(m/j)`, `j = 1..m` (this is literally `split_intervals()`), and the drop
at `x_j` has size `(lambda/j)^{1/2} g04(1)`. If `g04(1)` were `O(1)`, `f_lambda` would carry
`m` interior jumps plus a wrap-around jump, the coefficients would decay like `1/n`, the
projection tail on `N = m` would be `O(L^2/m^2 * 1/m)` — the same order as the target effect
`1/(16 pi m)` divided by `m`, i.e. exactly at the falsifier's `O(lambda^-4)` boundary. It is
not, for two independent reasons:

- **Right endpoint (`x = L`, `u = lambda`) — support + prolate concentration.**
  `f_lambda(L) = lambda^{1/2} g04(1)`. Rescaling the prolate operator by `x = lambda t` gives
  exactly the judge's (2.9), `PW_lambda = lambda^2(-d_x^2 + 4 pi^2 x^2) + d_x(x^2 d_x)`, so the
  packet is a perturbed harmonic-oscillator eigenfunction with Gaussian envelope `e^{-pi x^2}`
  on `|x| <= lambda`. Its endpoint value is `e^{-pi lambda^2} = e^{-pi m} = e^{-c/2}`, `c = 2 pi m`.
  This is the classical PSWF endpoint decay. The builder measures it and records it as
  `g04_endpoint_t_eq_1` / `k_edge`. **This is the exponentially small one.**
- **Left endpoint (`x = 0`, `u = lambda^-1`) — Fourier self-duality of the `h_0/h_4` line.**
  `psi_0` and `psi_4` are eigenfunctions of the finite Fourier transform `F_c` with eigenvalues
  `mu_0, mu_4` of the *same* phase `i^0 = i^4 = 1`. Setting `t = 0` in `F_c psi_n = mu_n psi_n`
  gives `int psi_n = mu_n psi_n(0)`. Hence for `g = a psi_0 + b psi_4` the source's zero-integral
  condition `a mu_0 psi_0(0) + b mu_4 psi_4(0) = 0` forces

  ```
  g04(0) = b psi_4(0) ( 1 - mu_4/mu_0 ) .
  ```

  So on this line **zero integral is the same condition as vanishing at the origin, up to the
  relative prolate finite-Fourier eigenvalue defect**, which is again exponentially small in `c`.
  Combined with the exact Poisson form of Section 3.3, `f_lambda(0) = -lambda^{-1/2} g04(0)/2 +
  (out-of-band terms)` is exponentially small too.

Consequence: the periodized `f_lambda` is `C^infinity` up to `O(e^{-pi m})`, and it is not a
"function that happens to vanish at the ends" — it is a **fixed-width bump sitting at the centre
of a window that grows**, `f_lambda(x) = Phi(x - L/2)` with `Phi` essentially `lambda`-independent
and doubly-exponentially decaying (`Phi(s) ~ e^{s/2} e^{-pi e^{2s}}` as `s -> +inf`, and by the
self-duality `Phi(-s) = Phi(s)` in the limit). Measured: at `m = 43`, `|f| = 3.9e-12` already one
`log 2` inside the right end and `4.1e-24` at the end; at `m = 83`, `4.2e-26` and `3.3e-36`.

### 5.2 The first nonzero endpoint/jump term (the answer the judge asked for)

The circle jump of the periodized `f_lambda` is, exactly,

```
D_lambda = f_lambda(0^+) - f_lambda(L^-)
         = lambda^{1/2} ( sum_{k>=1} hhat_lambda(k lambda) - g04(1) )  -  lambda^{-1/2} g04(0)/2 ,
```

giving the first non-super-algebraic Fourier term

```
c_n^{jump} = ( sqrt L / (2 pi i n) ) D_lambda + O(n^{-2}) .
```

**It is not zero, but every one of its three pieces is a prolate exponential:**
`sum_k hhat_lambda(k lambda)` is out-of-band mass, `g04(1)` is the endpoint value, `g04(0)` is
the eigenvalue defect. All are `e^{-pi m + O(log m)}`. Cache evidence:

| `m` | measured `|g04(1)|` (dps 110) | `e^{-pi m}` | note |
|---|---|---|---|
| 13 | `8.94e-30` | `1.83e-18` | below the model; run is precision-floored |
| 43 | `8.82e-23` | `2.15e-59` | precision floor of that run, not the true value |
| 83 | `2.34e-110` | `5.71e-114` | clean; model times a `4.1e3` polynomial prefactor |

**Honest limit of the evidence:** the `m = 13` and `m = 43` caches cannot resolve `g04(1)`,
`g04(0)` or `B_lambda` below their own eigensolve floor — the observed `|c_n|` plateaus in
those two caches (`~1e-30` at `m=13`, `~1e-23` at `m=43`) sit exactly at their measured
`|g04(1)|`, which is the signature of this floor. The `m = 83` cache does not plateau at all
inside `|n| <= 83` (Section 6.2). So `B_lambda`'s size is established **structurally**
(support + Poisson + prolate concentration), and is *consistent with*, not *measured by*, the
caches.

### 5.3 The true decay law — and it is a classical statement about `Xi`

By the sampling identity of Section 1.1 and the judge's (2.5)-(2.6),

```
c_n / c_0 = (-1)^n * [ Xi(t_n) / Xi(0) ] * Phi_lambda^arch(t_n) * (1 + B-corrections),
            t_n = 2 pi n / L,     Xi(t) = xi(1/2 + i t).
```

**So the decay of the project's Fourier row is exactly the decay of the Riemann `Xi` function
on the real axis**, `|Xi(t)| ~ C t^{7/4} e^{-pi t/4}` (from `Gamma(1/4 + it/2)`). In `n`:

```
|c_n / c_0| ~ C (2 pi n/L)^{7/4} exp( - pi^2 n / (2 L) ) * Phi_lambda^arch(2 pi n/L),
```

i.e. geometric with ratio `exp(-pi^2/(2 log m))`. The analyticity half-width `pi/4` of the
profile `Phi` in `Im s` is the same `pi/4` as the `Gamma`-factor decay: `Phi(s) = e^{s/2}
sum_n h(n e^s)` converges only while `Re(e^{2s}) > 0`, i.e. `|Im s| < pi/4`.

The `Phi^arch` factor grows like `exp(z^2/(16 pi m))` (empirical resummation of the judge's
(2.10), fits the caches to 3 digits out to `t = 73`), so the tail exponent is
`- pi^2 n/(2L) + pi n^2/(4 m L^2)`; the two terms only cross at `n = 2 pi m L`, which on
`N = m` is a factor `2 pi L` beyond the projection cut. No interference.

---

## 6. Numbers (all DIAGNOSTIC; caches are exact, mpmath at dps 60)

Sources: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_*_N_*.json`.

### 6.1 Exact projection-tail curvature correction — formula (*), measured

| `m` | `N` -> `N_big` | `kappa(F_{q,N}) - kappa(F_{q,N_big})` | `|corr| / lambda^-4` |
|---|---|---|---|
| 13 | 13 -> 120 | `+4.0906739e-11` | `6.91e-9` |
| 13 | 26 -> 120 | `-7.512186e-20` | `1.27e-17` |
| 13 | 90 -> 120 | `+7.8826071e-36` | `1.33e-33` |
| 43 | 43 -> 86 | `-5.0100455e-24` | `9.26e-21` |
| 83 | 83 -> — | (no larger-`N` cache) | — |

The `m = 13` row reproduces the observer's fact (b) exactly: `kappa(q_{13,13}) =
0.021542919243621` and `kappa(q_{13,120}) = 0.021542919202714`, difference `4.09e-11`. The
`(43,43)` vs `(43,86)` row requested for the verdict intake is `-5.01e-24`. Note the **sign
alternation** — it is `(-1)^{N+1}` from the sampling phase, exactly as (*) predicts.

### 6.2 `L^2` projection tail mass beyond the cut (`raw^2 - pN^2`, exact from the caches)

| `m` | `N` | `|| (I-P_N) f ||^2` | relative |
|---|---|---|---|
| 13 | 13 | `1.139e-16` | `5.17e-16` |
| 13 | 26 | `1.788e-33` | `8.12e-33` |
| 13 | 90 | `2.236e-60` | `1.02e-59` |
| 23 | 23 | `1.915e-27` | `8.71e-27` |
| 43 | 43 | `2.156e-41` | `9.82e-41` |
| 43 | 86 | `5.241e-46` | `2.39e-45` |
| 83 | 83 | `0.0` (below dps 110) | `0.0` |

Mass beyond `|n| > m` on `N = m`: `5.2e-16`, `8.7e-27`, `9.8e-41`, `< 1e-108`.

### 6.3 Mathematical tail bound from the `Xi` model (independent of the caches)

`|kappa(P)| <= (L^2/(2 pi^2)) sum_{n>N} |Xi(t_n)/Xi(0)| / n^2` on `N = m`:

| `m` | `L` | tail bound | `lambda^-4` | ratio | `exp(-pi^2 N/(2L))` | `exp(-pi m)` |
|---|---|---|---|---|---|---|
| 13 | 2.5649 | `8.91e-12` | `5.92e-3` | `1.51e-9` | `1.37e-11` | `1.83e-18` |
| 23 | 3.1355 | `2.22e-17` | `1.89e-3` | `1.17e-14` | `1.90e-16` | `4.16e-32` |
| 43 | 3.7612 | `5.11e-25` | `5.41e-4` | `9.45e-22` | `3.15e-25` | `2.15e-59` |
| 83 | 4.4188 | `6.85e-41` | `1.45e-4` | `4.72e-37` | `5.55e-41` | `5.71e-114` |
| 313 | 5.7462 | `5.58e-117` | `1.02e-5` | `5.47e-112` | `1.82e-117` | `8.9e-428` |

(The `m=13` model value `8.9e-12` is `4.6x` below the measured `4.09e-11` because
`Phi^arch(t_13) = 4.9` there; on `m >= 43` model and measurement agree to a factor `2`.)

### 6.4 The continuum ledger, re-derived here from the caches

`kappa_X` by two independent channels: Taylor of `Xi` gives `0.023104993115419`; the P59
sampling formula `L^2/24 + (L^2/2 pi^2) sum (-1)^k (Xi(t_k)/Xi(0))/k^2` gives
`0.0231049931154` and is `L`-independent across all four cells. Agreement to 12 digits.

| `m` | `kappa(q_m)` | `a_m = m(kappa_X - kappa(q_m))` | `1/(16 pi) + 13/(256 pi^2 m)` | residual | `m^2 *` residual |
|---|---|---|---|---|---|
| 13 | `0.0215429192436` | `0.02030696033` | `0.020290154` | `1.681e-5` | `2.840e-3` |
| 23 | `0.0222300667110` | `0.0201233073` | `0.020118073` | `5.234e-6` | `2.769e-3` |
| 43 | `0.0226395163852` | `0.0200154994` | `0.020014024` | `1.475e-6` | `2.728e-3` |
| 83 | `0.0228645503298` | `0.0199567512` | `0.019956358` | `3.928e-7` | `2.706e-3` |

This reproduces the observer's `a_m = 0.020307, 0.020123, 0.020016, 0.019957` exactly, and it
**identifies the residual**: it is `c_3/m^2` with `c_3` converging (Richardson on `m=43,83`
gives `2.68e-3`), i.e. the `O(m^-3)` term of `[z^2]Phi^arch` — **not** a tail. Compare
`7/(256 pi^2) = 2.771e-3` as a candidate closed form; the extrapolation is not sharp enough to
confirm it and it is recorded here as a guess, not a claim.

### 6.5 Direct confirmation of the judge's repaired (2.10)

`ratio_n := (c_n/c_0) / ((-1)^n Xi(t_n)/Xi(0))` should be `Phi_lambda^arch(t_n)`:

| `m` | `n` | `t_n` | measured `ratio` | `1 + t^2/(16 pi m)` | `+ (13 t^2/(256 pi^2) + t^4/(512 pi^2))/m^2` | residual |
|---|---|---|---|---|---|---|
| 83 | 1 | 1.4219 | `1.000486251` | `1.000484613` | `1.000486241` | `1.0e-8` |
| 83 | 2 | 2.8438 | `1.001946424` | `1.001938452` | `1.001946371` | `5.3e-8` |
| 83 | 4 | 5.6876 | `1.007808471` | `1.007753809` | `1.007808031` | `4.4e-7` |
| 43 | 2 | 3.3411 | `1.005209488` | `1.005164503` | `1.005208901` | `5.9e-7` |
| 13 | 1 | 2.4496 | `1.009417804` | `1.009183092` | `1.009407948` | `9.9e-6` |

Both the `1/(16 pi)` first-order coefficient and the `13/(256 pi^2)`, `1/(512 pi^2)`
second-order coefficients of (2.10) are confirmed to the next order in `1/m`, from a channel
(mpmath `zeta`/`Gamma`) completely disjoint from the prolate eigensolve that produced `c_n`.

---

## 7. Required output (5) — proof targets

### 7.1 Minimal target that already clears `O(lambda^-4)` (cheap, no strips)

> **`P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL` (algebraic form).**
> There are constants `C_1, C_2, C_3` independent of `lambda` such that the centred profile
> `Phi_lambda(s) = k_lambda(e^s)` satisfies `|| d^j Phi_lambda / ds^j ||_{L^1(R)} <= C_j` for
> `j = 1,2,3`, and its boundary data at `s = +- L/2` is `O(e^{-pi m})`. Then, by three
> integrations by parts in the sampling identity of Section 1.1,
> `|c_n / c_0| <= C (L/(2 pi n))^3` uniformly in `lambda`, hence by (*)
> `|kappa(P_{lambda,N})| <= C' L^5 N^{-4}`, which on `N = m` is `O(m^{-4} (log m)^5) = O(lambda^{-8} (log lambda)^5)`.

**`k = 3` already gives `lambda^-8`.** The requested `O(lambda^-4)` needs only `k = 1`
(one derivative in `L^1`, plus the `O(e^{-pi m})` boundary terms), giving `O(m^{-2} L^3) =
O(lambda^{-4} (log lambda)^3)`; `k = 2` clears it outright. This is the honest cheapest target
and it needs **no** analyticity strip, **no** `Xi` growth theory, and **no** sharp PSWF asymptotics
— only uniform-in-`lambda` `L^1` bounds on derivatives of a `lambda`-independent profile.

### 7.2 `P59_LOWER_WINDOW_MELLIN_TWO_JET_TAIL`

> There is `C` with `|B_lambda(0)| + |B_lambda''(0)| <= C (1 + L^2)( lambda^{1/2}
> sup_{xi >= lambda} |hhat_lambda(xi)| + lambda^{-1/2} |g04(0)| )`, and both bracketed
> quantities are `O(e^{-pi m + O(log m)})` by (i) the exact support of `h_lambda`, (ii) the
> exact `int h_lambda = 0` making the Poisson form legal, (iii) classical PSWF concentration
> `psi_n(+-1) = O(e^{-c/2} poly(c))` and `1 - mu_4/mu_0 = O(e^{-c/2} poly(c))` at `c = 2 pi m`.
> Hence `kappa(B_lambda) = O(L^2 e^{-pi m}/|A_lambda(0)|)`.

The rigorous ingredient that is genuinely new here is only (iii) — a quantitative,
uniform-in-`c` PSWF endpoint/eigenvalue-defect bound on the fixed indices `0` and `4`. That is
classical literature (Slepian/Fuchs asymptotics), not new mathematics; it must nevertheless be
*cited or proved*, because the anchoring of `g04(0)` to `1 - mu_4/mu_0` is the only thing
standing between "the left endpoint is exponentially small" and "the left endpoint is `O(1)`".

### 7.3 Sharp target (optional, matches the numerics)

> For every `theta < pi/4` there is `C(theta)` with `|H_lambda(t)| <= C(theta) ||f_lambda||_2
> e^{-theta|t|}` for `|t| >= 1`, uniformly in `lambda`. Then
> `|kappa(P_{lambda,N})| <= C L^3 N^{-2} e^{-2 pi theta N/L}`, which on `N = m` is
> `exp(-pi^2 m/(2 log m) + O(log m))`.

This is the statement the caches actually exhibit, and its `pi/4` is the `Gamma`-factor
half-width of `Xi`. It is strictly stronger than needed for the crosswalk.

### 7.4 Is `O(lambda^-4)` false? No — and here is the certified reason it is not

The falsifier asks for a nonzero `lambda^-2` coefficient in either correction. Formula (*) is an
identity, and its right-hand side is a sum over `n > N` of a row that is a sampled Mellin
transform of a fixed-width, exponentially-decaying profile. A nonzero `lambda^-2` (or any
polynomial) coefficient would require `|c_n/c_0|` to be polynomially large at `n ~ m`; the caches
put it at `5.9e-8` (`m=13`), `7.8e-12` (`m=23`), `9.2e-21` (`m=43`), `3.9e-35` (`m=83`) —
monotonically collapsing, matched to `Xi(2 pi m/L)/Xi(0)` times the `Phi^arch` factor at every
one of those points. There is no mechanism left that could reinstate a power of `lambda`.

---

## 8. What is verified, by which channel, and what is not

| claim | channel | status |
|---|---|---|
| `kappa(F) = L^2/24 + (L^2/2 pi^2) sum (v_k/v_0)/k^2` | re-derived here from the sinc kernel **and** read off `proposition59RawTransform_secondDerivative_zero` (Lean, kernel-checked) | two channels agree |
| `E_{lambda,N}(0) = 0` | pure orthogonality, `U_0 in range P_N` | exact, no numerics |
| `E''_{lambda,N}(0)` closed form | Fourier coefficients of `(x-L/2)^2`; matches `proposition59SecondJetCoefficient` | exact |
| formula (*) | derived twice (quotient algebra (3.3), and truncation of the `kappa` series); numerically equal to the measured `kappa` difference at `m=13` to all shown digits | verified |
| `c_n/c_0 = (-1)^n (Xi/Xi(0)) Phi^arch` | mpmath `zeta`/`Gamma` vs the prolate eigensolve caches — **fully disjoint inputs** | verified, Section 6.5 |
| `kappa_X = 0.023104993115419` | Taylor of `Xi` vs P59 sampling formula | two channels, 12 digits |
| observer's `a_m` (0.020307 ... 0.019957) | recomputed here from the caches | reproduced exactly |
| judge's repaired (2.10) incl. the `-13/(256 pi^2 m^2)` curvature sign | Section 6.5 residuals | confirmed to next order |
| `g04(0) = b psi_4(0)(1 - mu_4/mu_0)` | algebra from `F_c psi_n = mu_n psi_n` at `t=0` plus the builder's zero-integral construction | derived, **not** numerically resolved (see 5.2) |
| `|g04(+-1)|, |g04(0)| = O(e^{-pi m} poly)` | structural (harmonic-oscillator rescaling (2.9) + PSWF concentration); `m=83` cache consistent to a `4.1e3` prefactor | **not independently verified**; `m=13`/`m=43` caches are precision-floored |
| `B_lambda` size | structural only | **not measured**; the caches cannot resolve it |
| `c_3 ~= 2.68e-3` third-order `a_m` coefficient | Richardson on `m=43,83` | numerical guess, no closed form claimed |
| `Phi^arch(z) ~ exp(z^2/(16 pi m))` resummation | empirical fit over `t <= 73` | heuristic, used only to show the tail exponents do not cross |

---

## 9. CLOSES / OPENS

**CLOSES**
- `P_FINITE_PROJECTION_SECOND_JET_TAIL_LOWER_ORDER` (registered at `0.55`): **CONFIRMED**, and
  by a much wider margin than the prediction supposed.
- `CURRENT_SMALLEST_GAP: P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL` — reduced from
  "unknown order" to an explicit identity (*) plus a `k <= 3` integration-by-parts lemma.
- The worry that the finite projection "changes the `1/(16 pi)` constant": dead. The measured
  `a_m` on `N = m` already *is* the continuum two-term law to `4e-7` at `m = 83`, and the exact
  projection correction at that cell is bounded by `6.85e-41`.
- The judge's `NEW_ANALYTIC` item `P59_FINITE_FOURIER_PROJECTION_SECOND_JET_TAIL` is downgraded
  from "new analytic mathematics" to "uniform `L^1` derivative bounds on a fixed profile".

**OPENS**
- One genuinely external citation obligation: quantitative PSWF endpoint and eigenvalue-defect
  asymptotics at fixed index and large `c` (Section 7.2 item (iii)). Nothing else here needs a
  supplier. Recommended first move: `./ask.sh prolate` / `./ask.sh Slepian` before any new file.

**No new script and no new tool is proposed.** The three checks in this report were run in the
scratchpad against existing caches and mpmath, and nothing about them needs to persist.

---

## 10. Next

The crosswalk is no longer the front. Both corrections in the judge's FINAL PROPOSAL ledger
`G_{q,N} = X Phi^arch + B_lambda + P_{lambda,N}` are super-polynomially small on `N = lambda^2`,
so the continuum trial jet `kappa(k_lambda) = kappa_X - 1/(16 pi m) - 13/(256 pi^2 m^2) + O(m^-3)`
transfers to the actual project row `q_{lambda,N}` once the two bounded targets of Section 7 are
proved — neither of which needs an eigensolve. The remaining rate obligation is unchanged and
sits where the judge put it: `|delta_m| = O(T_m) <=> |alpha_{G,m}| = O(T_m)`, with
`R1_GROUND_TRIAL_CURVATURE_SUBLEVEL_ENVELOPE` as the ranked-1 supplier. The cheapest next
decisive test is therefore the Rank-1 envelope's own falsifier — an exact finite witness in the
low-Rayleigh admissible set with macroscopic `J_{q,m}` — not any further work on the projection.

Lean-ready bookkeeping this report makes available immediately, with no new hypothesis:
`E_{lambda,N}(0) = 0`, the closed form for `E''_{lambda,N}(0)`, and identity (*). All three are
statements about `proposition59RawTransform` and `Finset.Icc` only.
