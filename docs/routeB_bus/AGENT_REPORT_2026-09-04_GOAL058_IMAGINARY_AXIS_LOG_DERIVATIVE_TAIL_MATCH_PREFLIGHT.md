# Claude-agent report — Goal 058: imaginary-axis log-derivative tail-match preflight

Date: 2026-09-04
Task: judge's `CHEAPEST_NEXT_ACTION` = `GOAL058_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT`
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RATE_L2_OVER_M_AND_FAR_ZERO_DEFICIT_2026-09-04.md`
(§Q1 `EXACT_IDENTITY`, §Q2 zero ledger + `kappa_X` guard, `CANDIDATE_REPRESENTATIONS` R1,
`FINAL PROPOSAL`, `STRONGEST ATTACK`, `CODEX DIRECTIVE` items 1–5)
Mode: `PAPER_AND_SOURCE_READ_ONLY`
Executor: Linux-Claude agent, branch `rh_clean`, no commit, no push, no `.lean` touched

```yaml
TASK_ID: GOAL058_P59_IMAGINARY_AXIS_LOG_DERIVATIVE_TAIL_MATCH_PREFLIGHT
RESULT: P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE
RESULT_SCOPE: ABSTRACT
REGISTERED_PREDICTION: P_LOG_DERIVATIVE_EXPOSES_SOURCE_TAIL_BEFORE_GAP (0.35) -> REFUTED
FIRST_UNCONTROLLED_TERM: >-
  sum_{rho in R+_m} 1/(rho^2 + y^2), the numerator-root reciprocal-square moment at scale y,
  weighed against the unconditional quartet-grouped Xi moment sum_j 1/(z_j^2 + y^2).
  For every y below the spectral gap 14.1347 this bracket equals Def_m up to
  y^2*(kappa4(G_m)+kappa4(X)); it is Def_m in new coordinates, not an omitted tail.
FALSIFIER_SELF_CHECK:
  first_quantitative_step_assumes_RH: false
  substitutes_sum_one_over_gamma_squared_for_kappa_X: false
  invokes_full_or_reduced_resolvent_norm: false
  assumes_abs_alpha_le_C_T_under_another_name: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
EIGENSOLVE_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
DIAGNOSTIC_NEVER_A_PROOF: true
```

## 0. Scope, sources, and what "no numerical run" means here

Read only:

- `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RATE_L2_OVER_M_AND_FAR_ZERO_DEFICIT_2026-09-04.md`
- `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md`
- `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`
- `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean`
- `q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean`
- `docs/routeB_bus/litreview/pdfs/2511.22755.pdf` (CCM), Prop. 5.9 eq. (5.25) and Thm 5.10 (i)–(iii)
- `docs/Progress_Log.md`, entries of 2026-09-04, and the earlier
  `PROSHKA_VERDICT_REQ_2026_08_28_R1A_CORRECTION_16_GLOBAL_GAUGE_KILL_AND_LOG_DERIVATIVE_RERANK_2026-08-28.md`
  (so that the killed generic-global-gauge class is not reopened)

Every number quoted below is either (a) already published on the bus, (b) a classical
constant with a name, or (c) a symbolic expansion carried out by hand. No transform was
evaluated, no eigensolve was run, no script was executed. The internal consistency check in
§1.3 is a hand series expansion checked against a Lean statement, not a computation.

**Notation.** `L = L_m = log m`, `N = N_m = m`, `x_k = 2*pi*k/L` (`proposition59Pole`),
`v = v_m` the even real ground row (`v_0 != 0`), `S = Icc(-N, N)`,

```
F(z) = L^{-1/2} * sum_{k in S} v_k * 2*sin(z*L/2)/(z - x_k)      (CCM (5.25) = proposition59RawTransform)
G(z) = F(z)/F(0),   X(z) = centeredXi(z)/centeredXi(0),   S_f(y) = -f'(i*y)/(2*i*y*f(i*y)).
```

`R+_m` is the positive-root multiset of the finite Cauchy numerator (`positiveRootMultiset`),
`S_m = sum_{rho in R+_m} rho^{-2}`, `T_m = (L^2/4pi^2) * sum_{k>N} k^{-2}`,
`kappa(G_m) = S_m + T_m` (`proposition59Curvature_eq_root_sum_add_tail`),
`kappa_X = -X''(0)/2 = 0.0231049931`, `Def_m = kappa_X - S_m`, `alpha_m = T_m - Def_m`.

---

## 1. Item (1) — exact formula for `S_G(y)` in source objects, and its `y`-expansion

### 1.1 Divisor form

Under the source hypothesis that `F` has only real zeros — CCM Theorem 5.10(iii) supplies
exactly this from the *simple, even bottom eigenvector*, and the project's Lean statements
carry it as the hypothesis `ZerosRealOn Set.univ (proposition59RawTransform ...)` — the
explicit product of `proposition59_normalized_euler_tail_product` gives

```
G(z) = prod_{rho in R+_m} (1 - z^2/rho^2) * prod_{k>N} (1 - z^2/x_k^2).
```

Taking `d/dz log`, `G'/G(z) = -2z * [ sum_rho 1/(rho^2 - z^2) + sum_{k>N} 1/(x_k^2 - z^2) ]`,
and substituting `z = i*y` (so `z^2 = -y^2`):

```
                                          1                        1
   S_G(y)  =  sum_{rho in R+_m}  ----------------  +  sum_{k>N} ----------------          (1.1)
                                    rho^2 + y^2                   x_k^2 + y^2
```

a positive Stieltjes sum, `S_G(0) = S_m + T_m = kappa(G_m)`. The forced lattice block is
elementary in closed form. With `beta := L*y/(2*pi)`, so that `x_k^2 + y^2 = (4pi^2/L^2)(k^2+beta^2)`,

```
   A_G(y) := sum_{k>N} 1/(x_k^2+y^2)
           = (L^2/4pi^2) * [ (pi/(2*beta)) * coth(pi*beta) - 1/(2*beta^2)
                             - sum_{k=1}^{N} 1/(k^2+beta^2) ]                              (1.2)
```

At `y = 0` this is exactly `(L^2/4pi^2) * proposition59TailZetaTwo N = T_m`, i.e. `A_G(0) = T_m`.

### 1.2 Root-free form (the genuinely new source object)

`S_G` does **not** require knowing `R+_m`. Write `F(z) = 2*L^{-1/2} * sin(z*L/2) * R(z)` with
`R(z) = sum_{k in S} v_k/(z - x_k)`. Pairing `k` with `-k` (the row is even, `x_{-k} = -x_k`) gives
`R(i*y) = -i * Rc(y)` with the real function

```
   Rc(y) := v_0/y + 2*y * sum_{k=1}^{N} v_k/(x_k^2 + y^2).                                 (1.3)
```

Since `cot(i*y*L/2) = -i*coth(y*L/2)`, the same substitution gives

```
                1     [  L                         Rc'(y)  ]
   S_G(y)  =  -----   [ --- * coth(y*L/2)   +     -------  ]                               (1.4)
               2*y    [  2                          Rc(y)  ]
```

**(1.4) is a finite, elementary, explicit function of the ground row `v_m` alone.** No root
location, no real-rootedness, no spectral measure, no resolvent. This is stronger than the
form R1 asked for and is the one usable new object this preflight produced.

### 1.3 Internal consistency check against Lean (hand expansion, no run)

Expand (1.4) at `y -> 0`. From (1.3), `Rc'(y)/Rc(y) = -1/y + (4*y/v_0)*sum_{k>=1} v_k/x_k^2 + O(y^3)`
and `(L/2)*coth(y*L/2) = 1/y + y*L^2/12 + O(y^3)`. The `1/y` poles cancel and

```
   S_G(0) = L^2/24 + (2/v_0) * sum_{k>=1} v_k / x_k^2
          = L^2/24 + (L^2/(2*pi^2*v_0)) * sum_{k>=1} v_k/k^2
          = (L^2/2) * [ 1/12 + (1/(2*pi^2*v_0)) * sum_{k != 0} v_k/k^2 ],
```

which is verbatim `proposition59_curvature_closed_form`. The two representations agree. `[LEAN]`

### 1.4 `y`-expansion

With `kappa_{2j}(G) := sum_{rho} rho^{-2j} + sum_{k>N} x_k^{-2j}` (`kappa_2 = kappa(G_m)`),

```
   S_G(y) = kappa(G_m) - y^2 * kappa_4(G_m) + y^4 * kappa_6(G_m) - ...                     (1.5)
```

convergent for `|y| < rho_min(G_m) := min |divisor point|`. Two free unconditional bounds:

- `kappa_4(G) <= kappa(G)/rho_min^2` and `rho_min^2 >= 1/kappa(G)`, hence
  **`kappa_4(G_m) <= kappa(G_m)^2`** — and `kappa(G_m)` is explicit in `v_m` by §1.3.
  With the published `kappa(G_m) ~ 0.0252` this is `kappa_4(G_m) <= 6.4e-4`.
- The same for the target: `kappa_4(X) <= (sum_j |z_j|^{-2})^2`, an unconditional finite constant.

---

## 2. Item (2) — exact formula for `S_X(y)` **without RH**, and the zero-free segment

### 2.1 The zero-free segment is the whole real `y`-axis, not `[0, 1/2)`

`centeredXi(z) = riemannXi(1/2 + i*z)` (`ClassicalXiInterface.lean`), so

```
   X(i*y) = riemannXi(1/2 - y) / riemannXi(1/2) = xi(1/2 - y)/xi(1/2).
```

The imaginary `z`-axis is exactly the **real `s`-axis**. Unconditionally `xi(s) > 0` for every
real `s`:

- `s > 1`: `zeta(s) > 1`, `s(s-1) > 0`, `Gamma(s/2) > 0`, `pi^{-s/2} > 0`.
- `0 < s < 1`: `zeta(s) = eta(s)/(1 - 2^{1-s}) < 0` (Dirichlet eta positive, denominator
  negative), while `(1/2)s(s-1) < 0`; the product is positive.
- `s = 0, 1`: `riemannXi_zero` and `riemannXi_one` in Lean give `xi(0) = xi(1) = 1/2`. The pole
  of `zeta` at `s = 1` and the trivial zero at `s = 0` are both removed by the `s(s-1)` /
  `Gammaℝ` structure — the question raised in the directive is settled here, in Lean. `[LEAN]`
- `s < 0`: `xi(s) = xi(1-s)` with `1-s > 1`, already covered.

Consequently `S_X(y)` is defined, finite and real for **every** real `y`, with a removable
singularity at `y = 0` (`xi(1/2 - y)` is even in `y` by the functional equation, so
`(xi'/xi)(1/2 - y)` is odd and vanishes at `y = 0`). No RH, no zero-free-region input, no
segment restriction. This is a correction, in the strengthening direction, of the
directive's tentative "`0 <= y < 1/2`?".

### 2.2 Closed form in source objects

`X'(i*y)/X(i*y) = i*(xi'/xi)(1/2-y)` and `(xi'/xi)(1/2-y) = -(xi'/xi)(1/2+y)`, so

```
                 1
   S_X(y)  =  ------- * (xi'/xi)(1/2 + y)                                                  (2.1)
                2*y
```

and with `log xi = log(1/2) + log s + log(s-1) - (s/2)log pi + log Gamma(s/2) + log zeta(s)`
at `s = 1/2 + y`:

```
                 1          1        [ 1                1                       ]
   S_X(y) = ----------  +  ----- * [ - * psi(1/4 + y/2)  -  - * log(pi) + (zeta'/zeta)(1/2+y) ]
             y^2 - 1/4      2*y      [ 2                2                       ]           (2.2)
```

(the elementary pieces `1/(1/2+y) + 1/(y-1/2)` collapse to `2y/(y^2-1/4)`; the pole of
`zeta'/zeta` at `s = 1` cancels the pole of `1/(y^2-1/4)` at `y = 1/2` exactly). For `y > 1/2`,

```
   (zeta'/zeta)(1/2+y) = - sum_{n>=2} Lambda(n) * n^{-1/2-y}                                (2.3)
```

converges absolutely: **archimedean digamma term plus a convergent prime-power sum, no zeros.**
(2.2)+(2.3) is the Guinand–Weil dictionary in log-derivative form — the object the leakage
verdict classified `exact_zero_sum_dictionary: GREEN_PAPER`.

### 2.3 Hadamard / quartet form, real without RH

`X` is entire of order 1, even, `X(0) = 1`, and its zero set is the centered nontrivial-zero
set, closed under `z -> -z` (functional equation) and `z -> conj z` (real coefficients:
`conj X(conj z) = X(z)`). Because `sum_j |z_j|^{-2} < infinity` classically, the pair product
converges absolutely with no exponential factors:

```
   X(z) = prod_j (1 - z^2/z_j^2),      S_X(y) = sum_j 1/(z_j^2 + y^2)                       (2.4)
```

where `j` runs over one representative of each `{z, -z}` pair, equivalently over each
`{rho, 1-rho}` pair, i.e. over zeros with `t_j := Re z_j = Im rho_j > 0`. In centered
coordinates `z_j = t_j + i*delta_j` with `delta_j = 1/2 - Re rho_j`, `|delta_j| < 1/2`.

Reality without RH: an off-line zero contributes its whole quartet, and the two
representatives with `t > 0` are conjugates, so

```
   1/(z_0^2+y^2) + 1/(conj z_0^2 + y^2) = 2 * Re[1/(z_0^2+y^2)]
                                        = 2 * (t^2 - delta^2 + y^2) / |z_0^2 + y^2|^2.       (2.5)
```

`S_X(y)` is therefore real for every real `y` **unconditionally**. Two further honest remarks:

- For `y >= 1/2` every quartet term in (2.5) is **positive with no input at all**, since
  `y^2 >= 1/4 > delta^2`.
- For `0 <= y < 1/2` positivity of each term needs `t_j^2 + y^2 > delta_j^2`, which follows
  from `|t_j| > 1/2` — classical and rigorous (lowest ordinate `14.1347...`, certified by a
  finite argument-principle verification), but it is a **cited finite certificate**, not a
  one-line consequence of the functional equation. Flagged, not hidden.

`S_X(0) = kappa_X = sum_j 1/z_j^2` is the judge's `canonical_product_object`. The forbidden
substitution `kappa_X = sum_{gamma>0} gamma^{-2}` is **never used below**; it is exactly the
RH-only specialization of (2.4).

### 2.4 Two exact unconditional target constants (`CLOSES` material)

From (2.1)–(2.2) and `(xi'/xi)(1/2) = 0`:

```
   kappa_X = (1/2) * (xi'/xi)'(1/2)
           = (1/2) * [ -8 + (1/4)*psi'(1/4) + (zeta'/zeta)'(1/2) ],    psi'(1/4) = pi^2 + 8*G  (2.6)
```

(`G` = Catalan). And at `y = 1/2`, `z_j^2 + 1/4 = rho_j*(1-rho_j)`, so

```
   S_X(1/2) = sum over {rho,1-rho} pairs of 1/(rho*(1-rho)) = sum_rho 1/rho
            = 1 + gamma_E/2 - (1/2)*log(4*pi) = 0.0230957...                                 (2.7)
```

Both are **unconditional closed forms for target curvature-type scalars that never mention a
zero location**. (2.7) is consistent with the bus value `kappa_X = 0.0231049931` in the right
direction and magnitude (`S_X` is decreasing in `y`, and the gap `9.3e-6` is the expected
`(1/4)*kappa_4(X)`-size correction). This is the one place where the log-derivative
representation genuinely buys something: it removes `kappa_X` from the "unknown zero sum"
column and puts it in the "named classical constant" column, **without RH**.

---

## 3. Item (3) — a legal `y_m -> 0` regularization budget, and the three-piece ledger

### 3.1 The budget is legal, explicit, and quantitatively harmless

Write `D(y) := S_G(y) - S_X(y)`, so `D(0) = alpha_m`. From (1.5) and its target analogue,

```
   |D(y) - alpha_m| <= y^2 * ( kappa_4(G_m) + kappa_4(X) ) + O(y^4)                          (3.1)
```

with both fourth moments bounded unconditionally by §1.4 (`kappa_4(G_m) <= kappa(G_m)^2`,
`kappa(G_m)` explicit in `v_m`). Numerically `kappa_4(G_m) + kappa_4(X) <= c_4 ~ 1.1e-3` on the
production cells (and the tracked value is nearer `8e-5`). A legal schedule is therefore any

```
   y_m = o( sqrt(T_m / c_4) ) = o( L_m / sqrt(m) ),                                          (3.2)
```

for instance `y_m = 1/(L_m * sqrt(m))`. Under (3.2) the regularization error is `o(T_m)`, so a
bound `|D(y_m)| <= C*T_m` is *equivalent* to `|alpha_m| <= (C+o(1))*T_m`.

**That equivalence is the whole finding.** The budget is legal, but what it buys is nothing:
by (3.1) the map `y -> D(y)` is, for every `y` below the spectral gap, a bounded invertible
perturbation of the single scalar `alpha_m`.

### 3.2 The requested split at a height `R`

```
   S_G(y) - S_X(y) =
        [ sum_{rho <= R} 1/(rho^2+y^2)  -  sum_{|z_j| <= R} 1/(z_j^2+y^2) ]     (A)
      + [ sum_{k>N} 1/(x_k^2+y^2) ]                                              (B)
      + [ sum_{rho > R} 1/(rho^2+y^2) ]                                          (C)
      - [ sum_{|z_j| > R} 1/(z_j^2+y^2) ]                                        (D)                (3.3)
```

- **(B) is source-explicit**: the forced P59 lattice tail, closed form (1.2), `= T_m` at `y=0`.
- **(D) is the target's tail and is unconditional**: `|z_j^2+y^2| >= t_j^2 - 1/4`, and
  Riemann–von Mangoldt `N(T) = (T/2pi)log(T/(2*pi*e)) + O(log T)` counts **all** nontrivial
  zeros regardless of location, so by Stieltjes integration
  `|(D)| <= (1/2pi)*(log(R/2pi) + 1)/R * (1 + o(1))`. To fit an `O(T_m) = O(L^2/m)` budget it
  suffices to take `R >~ m/(2*pi*L) = x_N/(4*pi^2)` — comfortably inside the window. So (D) is
  affordable and needs no hypothesis. `[ABSTRACT][PAPER]`
- **(A) and (C) are the open pieces.** (A) is the inside-height mismatch; (C) is the ground
  numerator-root mass beyond `R`, which the judge's own plant
  `P_N(z) = prod_{j=1}^{N}(1 - z^2/(R+j)^2)` shows cannot be located by evenness, degree and
  real-rootedness. This is `REALROOT_DEGREE_TO_WINDOW_COUNT`, unchanged by the `y`-weight.

So the log-derivative reproduces the *same* three-piece ledger as the curvature, with the
`y`-dependence entering only as the factor `1 + O(y^2/R^2)` inside each term.

---

## 4. Item (4) — the first term remaining after source subtraction, and why the `y`-weight
does not suppress the far zeros

### 4.1 Which way the `y`-weight actually points

The hoped-for mechanism was that `1/(rho^2+y^2)` suppresses far zeros so that only a
controllable near part survives. **It points the other way.** For `rho >> y` the weight is
`1/rho^2 * (1 + O(y^2/rho^2))` — identical to the curvature weight. For `rho << y` it is
`~ 1/y^2 << 1/rho^2` — suppressed. So the `y`-weight suppresses the **near** zeros, and only
once `y` exceeds the spectral gap. The far tail is discounted by `1/rho^2` in `kappa` already;
`S(y)` adds nothing there. This is the precise reason the representation cannot convert
`Def_m` (which the judge established is *not* only an inside-window mismatch) into an
omitted tail.

### 4.2 The gap dichotomy

The entire divisor of both objects sits at modulus `>= 14.1347` on the target side and, by
the same tracking, at `~14` on the ground side (unconditionally `rho_min(G_m) >= kappa(G_m)^{-1/2} ~ 6.3`).
Hence:

- **`y` below the gap (`y <~ 6`).** `S(y) = kappa - y^2*kappa_4 + ...`, so by (3.1)
  `D(y) = alpha_m + O(y^2 * c_4)`. The bracket left after subtracting the two explicit
  archimedean/lattice blocks is
  ```
     sum_{rho in R+_m} 1/(rho^2 + y^2)   versus   sum_j 1/(z_j^2 + y^2) - (archimedean part)
  ```
  which is `Def_m` up to `O(y^2*c_4)`. **Rename.** The prime-series representation (2.3) is
  available on `1/2 < y`, i.e. entirely inside this regime, so the "explicit prime side" and
  the "`alpha_m` side" are the *same* number — there is no cancellation to exploit, only two
  independently explicit quantities whose difference is by definition `alpha_m`.

- **`y` above the gap (`y >~ 14`).** `S(y) ~ #{divisor points of modulus <~ y}/y^2 + tail`, a
  smoothed **zero count**. Here `D(y)` is genuinely a new functional — and it is exactly the
  count comparison the judge killed twice over in this same verdict (wrong direction,
  no location theorem). Worse, control here does not descend: at `y = Y`,
  ```
     alpha_m - D(Y) = Y^2 * [ sum_rho 1/(rho^2(rho^2+Y^2)) - sum_j 1/(z_j^2(z_j^2+Y^2)) ],
  ```
  of size `O(Y^2 * c_4)`, which at `Y = 20` is `~0.2 >> alpha_m ~ 1e-3`. Extracting `alpha_m`
  from `D(Y)` needs a fourth-moment comparison — a fresh instance of the same problem, and
  the same at every even order. Infinite regress.

### 4.3 What an honest "boundary functional" looks like, and why it is the reverse implication

The exact boundary form does exist, by Cauchy, for any `r < 14`:

```
   alpha_m = -(1/(2*pi*i)) * contour_{|z|=r} log(G_m(z)/X(z)) * dz/z^3,
   |alpha_m| <= r^{-2} * sup_{|z|=r} |log(G_m/X)|.                                            (4.1)
```

Unconditional, exact, no RH. But its budget is a **sup-norm relative approximation rate on a
fixed compact**, which controls `alpha_m` *and everything else* — by the judge's own Q4 table
that is a strictly stronger object than the one we are trying to bound. (4.1) is the correct
statement of "boundary functional" for this problem; it is not progress, it is the converse
implication.

---

## 5. The large-`y` question: is `S_G(x_N)` dominated by the explicit lattice tail?

**No — the two blocks are comparable, and the comparison at large `y` is free for a reason
that carries no information.**

At `y = x_N = 2*pi*m/L`:

- lattice tail, from (1.2) with `beta = N`: `A_G(x_N) = (L^2/4pi^2)*(1/N)*int_1^inf du/(1+u^2)*(1+o(1))
  = L^2/(16*pi*m)*(1+o(1)) = (pi/4)*T_m*(1+o(1))`. **Explicit.**
- root block: the numerator has degree `2N` with `N` positive roots, so **unconditionally**
  ```
     sum_{rho in R+_m} 1/(rho^2 + x_N^2)  <=  N / x_N^2  =  L^2/(4*pi^2*m)  =  T_m           (5.1)
  ```
  — the degree bound and `T_m` coincide *exactly*. No location theorem is used.
- target: by (2.2)–(2.3) at `y = x_N`, `S_X(x_N) = psi(1/4 + x_N/2)/(4*x_N) + O(2^{-x_N})
  = log(x_N/2)/(4*x_N)*(1+o(1)) = (pi/2)*T_m*(1+o(1))`. **Explicit, unconditional, and every
  term positive** by §2.3 since `x_N >> 1/2`.

Hence `|D(x_N)| <= S_G(x_N) + S_X(x_N) = O(T_m)` unconditionally and for free. The judge's
guess is confirmed **and is the trap**: the bound is a triangle inequality on two quantities
that are each individually `O(T_m)` at that scale. Nothing cancels; the statement has zero
information content about `y = 0`. Also, contrary to the sub-question's phrasing, the lattice
tail does **not** dominate: root block `<= T_m` against lattice tail `~0.785*T_m` — same scale.

### 5.1 The interpolation in `y`: two independent obstructions

**(i) The Stieltjes property of `S_X` is equivalent to RH.** In the variable `w = y^2`,
`S_G(w) = sum_j 1/(rho_j^2 + w)` is a Stieltjes transform of the positive measure
`sum_j delta_{rho_j^2}` — unconditional given CCM Thm 5.10(iii) (simple, even bottom
eigenvector). For the target, `S_X(w) = sum_j 1/(z_j^2 + w)` has poles at `w = -z_j^2`. A
Stieltjes transform of a positive measure on `[0, infinity)` has all poles on `(-infinity, 0]`.
So

```
   S_X is a Stieltjes transform of a positive measure
     <=>  every z_j^2 is real and >= 0
     <=>  every z_j is real (purely imaginary z_j is excluded by xi > 0 on R, §2.1)
     <=>  RH.
```

Therefore any argument whose first quantitative step invokes complete monotonicity,
Herglotz/Nevanlinna interpolation, Loewner monotonicity or a Schur/Pick-type bound **for
`S_X`** assumes RH and is killed by the judge's falsifier. This is the exact obstruction the
directive asked to be named, and it is an equivalence, not a difficulty. It also retires the
`R2 Loewner/Schur` follow-up in its `S_X`-side form.

**(ii) Even with the Stieltjes property on both sides, large-`y` control never descends.**
Suppose both measures existed. Then `D(w) = int d(mu_G - mu_X)(u)/(u+w)` for a signed measure.
Take `mu_G - mu_X = eps*(delta_{u_0} - delta_{u_1})` with `0 < u_0 < u_1` both small. Then
`D(w) = eps*(u_1-u_0)/((u_0+w)(u_1+w)) = O(eps*(u_1-u_0)/w^2)` at large `w`, arbitrarily small,
while `D(0) = eps*(1/u_0 - 1/u_1)` is arbitrarily large. Positivity and monotonicity of the
two sides constrain nothing about the *difference* at small `y` given the difference at large
`y`. So even the RH-conditional version of the interpolation is worthless — the obstruction is
not only RH, it is structural.

A Hadamard three-lines / harmonic-measure descent from a small-`|D|` region to `y = 0` is the
only remaining formal possibility; with an a-priori bound `M` on a neighbourhood it yields
`|D(0)| <= M^{1-theta} * eps^theta`, i.e. a rate `m^{-theta}` with `theta < 1` strictly, never
`O(T_m)`. Recorded as a fact, not proposed as a route.

---

## 6. Item (5) — code, and the honest ledger

```
RESULT: P59_LOG_DERIVATIVE_ONLY_RENAMES_CURVATURE
```

Reason, in one line: for every `y` below the spectral gap — which includes the entire range
`1/2 < y` where the target has a convergent prime-power representation — `D(y) = alpha_m + O(y^2*c_4)`
with `c_4` an explicit constant, so a bound on `D(y_m)` under any legal `y_m -> 0` budget *is* a
bound on `alpha_m`; and for `y` above the gap `D(y)` becomes a smoothed zero-count difference
that is both already killed as a supplier and provably decoupled from `alpha_m` at order `y^2`.
The difference never becomes an omitted tail smaller than `alpha_m` itself.

### What this preflight nevertheless produced (usable, none of it a rate supplier)

1. **Root-free explicit `S_G(y)`**, formula (1.4), a finite elementary function of the ground
   row; verified by hand against `proposition59_curvature_closed_form` at `y = 0` (§1.3).
   `LEAN_READY` as a definition plus the `y -> 0` expansion.
2. **`xi > 0` on the whole real `s`-axis**, hence `S_X(y)` defined for every real `y`, not only
   `|y| < 1/2`. Two of the four cases are already in Lean (`riemannXi_zero`, `riemannXi_one`).
   `LEAN_READY`.
3. **`kappa_X = (1/2)*(xi'/xi)'(1/2) = (1/2)*[-8 + (1/4)*psi'(1/4) + (zeta'/zeta)'(1/2)]`** and
   **`S_X(1/2) = sum_rho 1/rho = 1 + gamma_E/2 - (1/2)log(4pi)`**, both unconditional closed
   forms that never mention a zero location. This moves the target curvature scalar out of the
   "unknown zero sum" column — a genuine `CLOSES` against the `kappa_X` guard of §Q2.
4. **`sum_{rho} 1/(rho^2+y^2) <= N/y^2`, with `N/x_N^2 = T_m` exactly** (5.1) — a free
   unconditional bound from degree alone.
5. **`S_X` Stieltjes `<=>` RH** (§5.1(i)) — an exact equivalence, so the whole
   Herglotz/Loewner/Schur family is off the table on the target side, unconditionally.
6. **The signed-measure counterexample** (§5.1(ii)) — large-`y` control never descends, even
   under RH.

### The gap, restated as sharply as this representation permits

Both sides of `alpha_m` are now source-explicit scalars: `kappa(G_m)` by
`proposition59_curvature_closed_form` (a *linear* functional of the ground row `v_m`), and
`kappa_X` by (2.6) (a named classical constant). Neither zeros of `zeta` nor roots of `P_N`
appear anywhere. The remaining question is therefore, in full:

```
   Does  (L^2/2) * [ 1/12 + (1/(2*pi^2*v_0)) * sum_{k != 0} v_k/k^2 ]  ->  (1/2)*(xi'/xi)'(1/2)
   at rate  O(L^2/m),  where v_m is the bottom eigenvector of the m-truncated Weil matrix?
```

That is a statement about the CCM bottom eigenvector and nothing else. Every `y`-evaluation of
the log-derivative is a bounded, invertible reparametrization of that one scalar. The
representation improved the *statement* of the gap; it did not supply a source for it.

### `CLOSES` / `OPENS`

```
CLOSES:
  - IMAGINARY_AXIS_LOG_DERIVATIVE_AS_AN_OMITTED_TAIL_SUPPLIER
  - HERGLOTZ_LOEWNER_SCHUR_MONOTONICITY_ON_THE_TARGET_SIDE (equivalent to RH)
  - LARGE_Y_TO_SMALL_Y_INTERPOLATION_UNDER_STIELTJES_STRUCTURE (counterexample)
  - KAPPA_X_AS_AN_UNKNOWN_ZERO_SUM (closed form (2.6), unconditional)
  - S_X_RESTRICTED_TO_A_SHORT_ZERO_FREE_SEGMENT (whole real y-axis, §2.1)
OPENS: []
```

No Lean file was edited. No numerical run was started. No route promotion and no RH claim was
made. `PX_RH_CLAIM: NOT_MADE`.
