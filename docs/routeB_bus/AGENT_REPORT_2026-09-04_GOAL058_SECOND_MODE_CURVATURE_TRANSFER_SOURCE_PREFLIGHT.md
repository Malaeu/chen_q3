# Claude-agent report — Goal 058: second-mode curvature-transfer source preflight

Date: 2026-09-04
Task: judge's `CHEAPEST_NEXT_ACTION` = `GOAL058_SECOND_MODE_CURVATURE_TRANSFER_SOURCE_PREFLIGHT`
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_OF_THE_XI_ROW_2026-09-04.md`
(§Q2 `EXACT_TRANSFER_IDENTITY`, `SAME_PARAMETER_SUFFICIENT_CONDITIONS`, `CONTINUUM_Q2`,
`EULER_MACLAURIN`; §Q3; `CANDIDATE_REPRESENTATIONS` R1–R3; `FINAL PROPOSAL`; `STRONGEST ATTACK`)
Mode: `PAPER_AND_EXISTING_DATA_READ_ONLY`
Executor: Linux-Claude agent, branch `rh_clean`, no commit, no push, no `.lean` touched

```yaml
TASK_ID: GOAL058_SECOND_MODE_CURVATURE_TRANSFER_SOURCE_PREFLIGHT
RESULT: P59_SECOND_MODE_CURVATURE_TRANSFER_REMAINDER_LOWER_ORDER
RESULT_SCOPE: FINITE_CELL          # the code is earned on the five registered cells only
COFINAL_STATUS: NOT_PROVED
FIRST_UNCONTROLLED_TERM: >-
  Def_m = kappa_Xi - sum_{rho} 1/rho^2, the second inverse-power moment deficit of the
  ground transform's own root divisor (equivalently: the one-sided zero count
  N_G(t) >= N_Xi(t) up to t ~ 1.5*x_N). Everything else in alpha_m is explicit and classical.
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false     # see section 0 for what "arithmetic on published scalars" means
EIGENSOLVE_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
DIAGNOSTIC_NEVER_A_PROOF: true
```

## 0. What was and was not done

Read only: the OVERLAP verdict, the parent verdicts, `CONVENTION_CARD_GOAL058.md`,
`PRECOMMIT_2026-09-03_edge_ledger_probes.md` (ADDENDUM 20), `docs/Progress_Log.md`
(2026-09-04 entries: deep night, ONESHAPE + probe 17, the two morning entries, probe 18),
`docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_P59_ALTERNATING_LATTICE_CURVATURE_LEAN.md`,
`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean`,
`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`
(definition of `proposition59Curvature`), `docs/routeB_bus/phase5_codex/out/xi_row_zeros.md`,
`docs/routeB_bus/phase5_codex/lattice_equation.py:19`.

**One arithmetic pass** was run on scalars that are already published in the log
(`kappa(G_m)` from probe 18, `L_m = ln m` from `lattice_equation.py:19`, `N_m = m`):
tail of `zeta(2)`, the two derived columns `Ttail` and `Def`, and the classical constant
`(2 + gamma_E - ln 4*pi)/2`. No eigensolve, no transform evaluation, no new data — every
input is a number already on the bus. Script kept in scratchpad, not in the repo.

No `.lean` file was read for editing and none was written; the Codex/agent transaction on
`Proposition59AnchoredSecondModeOverlap.lean` was not touched.

## 1. Q(1) — what `E = Tr_m(B F_2)` actually is

### 1.1 The fourth-jet form of `B`

With `G(0) = X(0) = 1` write the ratio `q = G/X = 1 + a_2 z^2 + a_4 z^4 + ...`. Since
`kappa(f) = -f''(0)/2`, `kappa(G) - kappa(X) = -a_2`, i.e. **`a_2 = -alpha`**. Hence

```
B = G - X + alpha z^2 X = X * (q - 1 + alpha z^2) = X * ( a_4 z^4 + a_6 z^6 + ... ),
```

so `B(0) = B''(0) = 0` and `B = O(z^4)` near `0`, as the judge states. Writing
`kappa_4(f) = f''''(0)/4!` and using Leibniz on `G = X q` with `X''(0) = -2 kappa_Xi`:

```
24 kappa_4(G) = 24 kappa_4(X) + 12 X''(0) a_2 + 24 a_4
             = 24 kappa_4(X) + 24 kappa_Xi alpha + 24 a_4,
```

hence the exact fourth-jet difference asked for:

```
    a_4 = kappa_4(G) - kappa_4(X) - alpha * kappa_Xi ,
    E   = Tr_m(B F_2) = a_4 * Tr_m(z^4 X F_2)  +  sum_{k>=3} a_{2k} * Tr_m(z^{2k} X F_2).
```

The `- alpha * kappa_Xi` term is the "(terms)" of the request: the fourth jet of the ratio is
*not* the fourth jet difference of the functions; the quadratic jet feeds back through `X''(0)`.

### 1.2 Does `E/(alpha M) -> 0` follow from a jet hierarchy?

**Numerically the hierarchy is coherent.** From the m = 43 degree-4 profile fit
`q_1 = 0.9027 - 2.448e-3 x^2 + 2.7e-6 x^4`, normalised: `a_2 = -2.712e-3` (matching the
independently computed `alpha = 2.74e-3` to 1 %), `a_4 = +2.99e-6`, so `|a_4/a_2| ~ 1.1e-3`.
The measured `E/(alpha M) = 0.066` at m = 43 then forces
`Tr_m(z^4 X F_2)/M ~ 60`, i.e. an effective `<z^2>` of about `60` (`z_rms ~ 7.8`) for the
`X F_2` pairing — which is exactly where `psi_2` peaks (`max 0.76 at x = 6.9`, probe 17).
Three independent numbers close a triangle. That is real support, and it is the reason the
discriminator holds on the registered cells.

**As a proof it does not follow. An independent input is required.** Four reasons, in
increasing order of severity:

1. `a_4` is available only from a least-squares fit, at one cell. The judge's own rule
   ("a least-squares quadratic is not a source object and cannot be a premise") forbids it as
   a premise, and m-stability of `a_4/alpha` has never been measured.
2. No source theorem bounds `a_{2k}`. The obvious candidate function class — the ladder
   `X * {1, x^2, x^4, ...}` — was **falsified as a trial family** on 2026-09-04
   (`mu_1/lambda_1 = 1.7e6, 1e16, 3e36`; defect `p` *growing*; `c_1/c_0 * L^2` closer to
   `1/L^4` than to `1/L^2`). The bottom profile is a band-limited correction to `X*p` that
   explicit polynomials do not capture at the `lambda_1` scale. So the very hierarchy one
   would like to invoke is the object already shown not to be a controlled family.
3. The expansion is a jet at `0` while the pairing weight sits at `z ~ 7`. The moments grow
   like `<z^2>^k ~ 60^k`, so a hierarchy proof must show `a_{2k}` decays faster than `60^{-k}`.
   The single measured ratio `1.1e-3 << 1/60` is consistent with that, and is not a bound.
4. **Decisive.** `E` is not an independent object. Expanding the definition and using the
   judge's own (D) and (E),

   ```
   E = Tr_m((G-X) F_2) + alpha Tr_m(z^2 X F_2)
     = [ Tr_m(G F_2) - Tr_m(X F_2) ] + alpha M
     = [ 0 - 2*pi*d_2/ell_1 ] + alpha M
     = alpha M - 2*pi*d_2/ell_1 .
   ```

   So identity (F) is a **rearrangement of the definition of `B` plus linearity of `Tr_m`** —
   the observed residual `<= 3e-15` (probe 18) tests floating-point arithmetic and the two
   sampling lemmas, not mathematics. Consequently "prove `E = o(L^-2)`" is *logically
   equivalent* to "prove `d_2 = (ell_1 M / 2*pi) alpha + o(L^-2)`", which is the
   same-parameter conclusion itself. `E` becomes a genuinely smaller object **only** through a
   source representation of the ratio `G/X` that does not mention `d_2` — i.e. exactly the
   judge's `P59_QUADRATIC_PROFILE_REMAINDER_PAIRING_O_L_MINUS_2`, which is new analysis.

**Answer to (1):** `E/(alpha M) -> 0` does **not** follow from a jet hierarchy; it requires an
independent input (a source profile theorem for `G/X`). What the transfer identity *does* buy
is not nothing — see §1.3.

### 1.3 What the transfer identity does buy (why this is not "only renames")

The renaming is not empty, and this is why the success code is earned rather than the failure
code:

* it **removes `u_2` from the rate atom**. `d_2 = <y, u_2>` needs coherent second-mode
  selection, simplicity of `lambda_2`, `u_2[0] != 0`, and `psi_2 -> psi`. After (F) the rate
  question is carried entirely by `alpha_m = kappa(G_m) - kappa_Xi`, a scalar built from the
  **ground row alone**, with an exact finite closed formula (Lean, 2026-09-03) and a classical
  constant `kappa_Xi`. The second-mode machinery survives only in the *representation*
  statement, not in the *rate* statement.
* `M` is stable and one-signed and `d_2/alpha = -13.8` to 2 % across a factor 4 in `L^2`, so a
  dominant term is identified, which is precisely what the `STRONGEST ATTACK` says would be
  missing in the failure case.

## 2. Q(2) — is `M = Tr_m(z^2 X F_2)` a source-computable limit?

**At finite m, `M` needs no limit at all.** By the judge's (C) and the exact P59 removable-node
sampling, `M = 2*pi * <w, u_2>` where `w` is the row whose transform matches `z^2 X` at the
lattice nodes. It is a finite explicit inner product, not an approximation.

**The continuum limit `M -> integral z^2 X(z)^2 q_2(z) dz` needs three adapters. Two are safe:**

1. *Trapezoid to whole-line integral.* Step `h = 2*pi/L`, so Poisson puts the defect at
   frequencies `2*pi/h = L` and its multiples. `Xi_hat = 2*pi*Phi` with
   `Phi(u) ~ exp(-pi e^{2u})` (doubly exponential), and the integrand carries `X^2`, whose
   transform is a `Phi*Phi` convolution with the same class of decay. The alias at frequency
   `L` is therefore of order `exp(-pi e^{2L})`. **Superalgebraic, hence `o(L^-2)` with an
   absurd margin.** This is the judge's `EULER_MACLAURIN.surviving_role`, and it confirms the
   kill of the pure-Nyquist mechanism from the other side.
2. *Finite window.* The sum stops at `x_N = 2*pi*m/L = 31.9, 46.1, 71.8, 118.0, 201.1`. `X^2`
   there is `~exp(-pi x_N/2)`, i.e. `e^{-50}` already at m = 13. Harmless.

   **Independent confirmation from the existing data**: the morning probe computed
   `I_11 = integral X^2 q_1^2 = 6.283, 6.283` and `I_22 = 6.18, 6.22` against `2*pi = 6.2832`.
   Since `||u_j|| = 1` forces `Tr_m(F_j^2) = 2*pi` exactly, this is a direct 0.1 %/1 % check
   that the crosswalk *and* the amplitude normalisation are right. The 1 % gap is attributable
   to the degree-4 profile fit, not to the quadrature.

**The first uncontrolled term is the third adapter: the profile limit of `F_{2,m}` itself.**
`F_{2,m} -> X q_2` locally uniformly with a fixed amplitude is `P59_SECOND_MODE_PROFILE_LIMIT`
+ `P59_SECOND_MODE_SELECTION_COHERENCE`; nothing on the shelf supplies it. The finite data
support boundedness but not convergence, and the *residual drift is the same size as the
effect being measured*:

| object | m = 43 | m = 83 | drift |
|---|---|---|---|
| `q_2` constant `c_0` | 0.6387 | 0.6421 | +0.5 % |
| `q_2` curvature `c_2/c_0` | −0.1103 | −0.1073 | −2.7 % |
| `M` | −102.22 | −101.74 | −0.5 % |
| `E/(alpha M)` | 0.066 | 0.052 | −21 % |

So at these cells one cannot separate "`M` has a limit" from "`M` drifts slowly"; what the data
*do* establish is the judge's weaker discriminator — `M` keeps one sign and varies by 1.3 %
across all five cells, so it "does not lose a nonzero stable scale". That half of the falsifier
is untriggered.

## 3. Q(3) — the load-bearing question: can `alpha_m = O(L^-2)` be sourced without a gap?

### 3.1 `alpha_m` as an explicit functional of the row — three exact forms

`L_m = ln m` (`docs/routeB_bus/phase5_codex/lattice_equation.py:19`), `N_m = m`,
`x_n = 2*pi*n/L`, `v` = raw **FULL** mode coefficients of `u_1`.

**(i) Closed form (the addendum-20 formula).**

```
kappa(G_m) = (L^2/2) [ 1/12 + (1/(2 pi^2 v_0)) * sum_{0<|n|<=N} v_n/n^2 ].
```

*Convention catch (report it before reuse):* this is consistent only with `v` = FULL
coefficients. In EVEN orthonormal coordinates (`v_n = sqrt2 c_n`, convention card) the sum
acquires a stray `sqrt2` and the formula fails its own sanity check — the constant row
`G == 1` must give `kappa = 0`, which needs `1/12 + (1/pi^2) sum_{n>=1} (-1)^n/n^2 = 0`,
i.e. `eta(2) = pi^2/12`, exactly.

**(ii) Alternating node form (Lean, kernel-green:
`proposition59_alternating_curvature_identity`).**

```
kappa(G_m) = (L^2/(2 pi^2)) * sum_{n=1}^{N} (-1)^n (G(x_n) - 1)/n^2
             - (L^2/(2 pi^2)) * TailAlt(N),      TailAlt(N) = sum_{n>N} (-1)^n/n^2.
```

**(iii) Zero-divisor form (Lean, this is the *definition* in
`Proposition59ExplicitProductCurvatureBridge.lean:922`).**

```
kappa(L,N,v) = sum_{rho > 0, roots of the Cauchy numerator} 1/rho^2
             + (L^2/(4 pi^2)) * sum_{k>N} 1/k^2 .
```

The second term is exactly the contribution of the transform's *lattice* zeros
`x_k = 2*pi*k/L`, `|k| > N`, each contributing `1/x_k^2`. So the project's own `kappa` is
literally the second inverse-power moment of the full zero divisor. Independently,
`kappa_Xi = -Xi''(0)/(2 Xi(0)) = sum_{gamma>0} 1/gamma^2`; the classical constant
`(2 + gamma_E - ln 4*pi)/2 = 0.023095709` plus the `(1/4) sum 1/(gamma^2(gamma^2+1/4))`
correction `~9e-6` reproduces the published `kappa_Xi = 0.0231049931` to six digits. The
curvature atom is therefore a **zero-divisor statement**, which merges this front with ZEROPIN
("the atom is the full zero divisor") and WINDLOCK ("the full fence remains the minimal
counting lock").

Subtracting the Ξ-row version of (ii) gives the requested explicit functional:

```
    alpha_m = (L^2/(2 pi^2)) * sum_{n=1}^{N} (-1)^n Delta_n / n^2
              + [ kappa(y-row_m) - kappa_Xi ] ,        Delta_n = G(x_n) - X(x_n).
```

The `TailAlt(N)` terms cancel identically between the two rows.

### 3.2 Option (c) — Nyquist aliasing of the Ξ-row's own curvature

**Answer: yes, that difference is already far below `O(1/L^2)` — and that is bad news.**

Exactly:

```
kappa(y-row_m) - kappa_Xi = -(L^2/(2 pi^2)) sum_{n>N} (-1)^n X(x_n)/n^2
                            + (1/h) sum_k phi_hat((2k+1)*pi/h),   phi = (X-1)/z^2.
```

The first term is bounded by the Ξ tail beyond the window (`X(x_N) ~ e^{-pi x_N/4} <= e^{-25}`
already at m = 13, times `L^2/(2 pi^2 N^2)`), the second by `Phi`'s doubly exponential decay at
frequency `L/2`, i.e. `~exp(-pi e^{L})`. Both are superexponentially small. Sanity check of
the algebra: for the smooth part `Delta_n ~ -alpha x_n^2 X(x_n)` the same Poisson step gives
`sum_{n>=1} (-1)^n X(x_n) = -1/2 + (aliases)`, which returns `alpha = alpha` identically.

Consequence: the split `alpha = [kappa(G) - kappa(y-row)] + [kappa(y-row) - kappa_Xi]` is
legitimate and the second piece is classical — but it explains **0 %** of `alpha`. All of
`alpha` sits in the alternating-weighted node deviation
`(L^2/2 pi^2) sum (-1)^n Delta_n/n^2`.

**First uncontrolled term for (c): the *signed* alternating sum.** This is the sharpest form of
the wall. The already-green Lean chain
(`proposition59_weighted_curvature_inequality` + `proposition59_projective_node_inequality`)
bounds only `W = sum |Delta_n|/n^2`, giving

```
alpha <= (L^2/(2 sqrt45)) * sqrt(p)/|v_0|.
```

Estimating `sqrt(p)/|v_0|` from the measured profile (`Delta_n ~ -alpha x_n^2 X(x_n)`) gives
roughly `~60 alpha` at m = 163, so the bound overshoots by two orders of magnitude, and the
overshoot **grows like `L^{2.5}`** while `alpha` falls. The absolute-value step destroys
precisely the alternation that carries the entire effect: `alpha` is the Nyquist-frequency
content of `Delta`, filtered by `1/n^2`, not its size. Any route through `|Delta_n|` is dead
for this target.

### 3.3 Option (b) — the leakage picture

`lambda_1 = min sum_z F_v(z)^2 / ||v||^2` is the leakage past the window, and it is
**`~10^{-1.9 m}`** (`lambda_1(163) = 2.40e-294`). The corrected probe-12/S9 datum is
`F_ground(gamma_j) = C_j(m) * lambda_1` with `C_1 * L -> ~205`, so the zero shift is
`~lambda_1/|F'|`, and the root list confirms it: ground roots match `gamma_j` to
`2e-8 / 8e-18 / 2e-36` at m = 13/23/43 (`out/xi_row_zeros.md`, ADDENDUM 14 block).

**Answer: no — the second moment of the row does not see the leakage at order `1/L^2`; it sees
it at `10^{-1.9m}`.** The pinned (in-window) part of the zero divisor contributes
`O(lambda_1) = 10^{-294}` to `alpha` at m = 163, against `alpha = 1.4e-3`. The leakage picture
therefore explains why the *inside* contributes nothing, and says nothing at all about
`alpha`, which is entirely a far-field object. First uncontrolled term for (b): the far zeros
— `sum_z` in the leakage identity runs over zeta zeros, not over the transform's own roots
above the window, so the functional is silent exactly where `alpha` lives.

### 3.4 Option (a) — the exact identity `K = sum_z E(z)E(z)^T` paired with the curvature functional

Pairing the evaluation-range identity with form (iii) gives a complete and *explicit*
decomposition. Write

```
Ttail(m) = (L^2/(4 pi^2)) * sum_{k>m} 1/k^2        (lattice zeros beyond the window; explicit,
                                                   row-independent, classical)
Def(m)   = kappa_Xi - sum_{rho>0} 1/rho^2          (deficit of the finite root divisor)

                     alpha_m = Ttail(m) - Def(m).
```

Arithmetic on the published `kappa(G_m)` with `L = ln m`, `N = m`:

| m | L | x_N | `alpha` | `alpha*L^2` | `Ttail` | `Def` | `alpha/Ttail` | `alpha*m/L^2` |
|---|---|---|---|---|---|---|---|---|
| 13 | 2.5649 | 31.85 | 2.791e-3 | 0.0184 | 1.2339e-2 | 9.548e-3 | 0.2262 | 5.515e-3 |
| 23 | 3.1355 | 46.09 | 3.158e-3 | 0.0310 | 1.0595e-2 | 7.437e-3 | 0.2981 | 7.388e-3 |
| 43 | 3.7612 | 71.83 | 2.738e-3 | 0.0387 | 8.2372e-3 | 5.499e-3 | 0.3324 | 8.322e-3 |
| 83 | 4.4188 | 118.02 | 2.063e-3 | 0.0403 | 5.9232e-3 | 3.860e-3 | 0.3483 | 8.769e-3 |
| 163 | 5.0938 | 201.06 | 1.415e-3 | 0.0367 | 4.0196e-3 | 2.605e-3 | 0.3520 | 8.889e-3 |

**This is the report's main structural finding, and it is uncomfortable for the registered
reading of the front.**

* `alpha * L^2 = 0.018, 0.031, 0.039, 0.040, 0.037` is **not monotone**: it rises by a factor
  2.2 and then *turns over* at m = 163. It has been read as "converging to ~0.04". It is at
  least as consistent with a maximum followed by decay.
* `alpha/Ttail = 0.226, 0.298, 0.332, 0.348, 0.352` is **monotone with geometrically shrinking
  increments** (0.072, 0.034, 0.016, 0.004; increment ratios 0.48, 0.46, 0.23), extrapolating
  to `~0.354`.
* `alpha*m/L^2 = 5.5, 7.4, 8.3, 8.8, 8.9` (e-3) is monotone convergent to `~8.9e-3`, and
  `alpha` compared with the smooth Ξ zero tail above the window edge,
  `sum_{gamma > x_N} 1/gamma^2`, gives `0.213, 0.306, 0.360, 0.389, 0.400` — again monotone
  convergent.

Since `L = ln m`, `Ttail ~ L^2/(4 pi^2 m) = L^2 e^{-L}/(4 pi^2)`. **The data prefer
`alpha ~ 0.354 * L^2/(4 pi^2 m)` — exponentially small in `L` — over `alpha ~ c/L^2`.** The two
readings differ only by the factor `L^4/m`, which moves by a factor 3 across the five cells, so
the cells cannot *decide*; but one parameterisation converges monotonically and the other turns
over, and the converging one has a mechanism attached.

If this reading is right the consequences are all favourable and all deflationary:

* `alpha = O(L^2/m)` implies `alpha = o(L^-2)` with an enormous margin, so `d_2 = O(L^-2)`
  holds *a fortiori* and the consumer's requirement is met;
* the "`1/L^2` law" is then a mis-parameterisation, and hunting a `1/L^2` perturbation theory
  (degenerate perturbation inside the collapsed subspace, `a(m) L^2 -> 0.6`, etc.) is hunting
  the wrong exponent;
* the supplier is not spectral at all — it is a **zero-count**.

**First uncontrolled term for (a): `Def(m)`, i.e. the pinning depth.** Back-solving `Def(m)`
against the smooth Ξ zero density gives an effective capture height `T ~ 1.5 x_N` and a capture
count `J(m)/m ~ 0.71, 0.76, 0.78, 0.81, 0.81` of the `m` available root pairs. Nothing in the
source proves (i) how deep the pinning goes, or (ii) that no unpinned root is anomalously
small — a single small root inflates `sum 1/rho^2` and flips the sign of `alpha`.

### 3.5 The non-circular residue: what would actually supply the bound

Pinning at full strength (the ground roots *are* the zeta zeros) is the identification theorem,
so deriving `alpha = O(...)` from it is circular — this is the judge's own kill of the
zero-sum mechanism (verdict `99927f01`: the sum over off-line zeros is indefinite without RH).
But the decomposition of §3.4 needs **less than pinning**. All terms `1/rho^2` are positive
when the ground roots are real, so by Abel summation
`sum_{rho<=T} 1/rho^2 = N_G(T)/T^2 + 2 integral_0^T N_G(t)/t^3 dt`, and the same for `Xi`.
Hence:

```
IF   N_G(t) >= N_Xi(t)  for all t <= T*   (a ONE-SIDED COUNT, no location)
THEN Def(m) <= sum_{|rho_Xi| > T*} 1/|rho_Xi|^2 = O(log T*/T*)   [unconditional, Riemann-von Mangoldt]
AND  alpha_m <= Ttail(m) + O(log T*/T*) = O(L^2/m).
```

The upper bound on the Ξ tail is unconditional: `N_Xi(T)` is the classical zero count and
`|sum_{|rho|>T} 1/rho^2| <= sum_{|rho|>T} 1/|rho|^2` needs no information about where the
zeros are. The two-sided bound (`alpha` bounded below as well) needs `N_G(t) <= N_Xi(t)` too,
i.e. the **full fence** — which is exactly the object the WINDLOCK verdict already named as
"the minimal counting lock". This closes rather than opens: no new tool is requested, the
counting front already exists.

`CLOSES`: names one supplier for the curvature atom that is a count, not a location, and not a
gap. `OPENS`: nothing new — it re-uses the WINDLOCK counting object.

Caveat, stated plainly: the Abel step needs the ground roots real (see §5.2), and the
inequality direction has been checked on paper here, not in Lean.

## 4. Falsifier for this code

The code is `P59_SECOND_MODE_CURVATURE_TRANSFER_REMAINDER_LOWER_ORDER` at `FINITE_CELL` scope.
It flips to `..._ONLY_RENAMES_CANCELLATION` on any of:

**F1 — exact fourth jet (cheapest, no eigensolve; kills or confirms §1.2).** Compute `a_4`
*exactly* from the fourth-jet lattice formula (not from a fit) on all five cells, and compare
`a_4 * Tr_m(z^4 X F_2)` with `E`. Prediction if the code is right: agreement within 30 % and
`a_4/alpha` m-stable to a factor 2, hovering near `1.1e-3`.
Falsifier: `E` is not dominated by the fourth jet, or `a_4/alpha` moves by more than a factor 3
across the cells — then `E` has no jet representation and the "lower order" is a coincidence of
these cells.

**F2 — parity probe on the root divisor (cheap, decisive about §3.4).** All five registered
cells have **odd** m, hence `N+1` even, hence `TailAlt(N) > 0` in every cell — a same-sign
artifact across the whole registered family. Run one **even** cell (m = 14 next to m = 13, or
m = 84 next to m = 83) and check that `alpha` and the `Ttail/Def` split move smoothly. A visible
odd/even zigzag would mean the alternating tail is not being handled as the identity says.

**F3 — one more decade in `m` (decides the parameterisation).** m = 313 or m = 523
(`L = 5.75, 6.26`). `alpha * L^2` predicted by the two readings:
`L^-2` law → 0.037…0.040 (flat); `L^2/m` law → `0.354 * L^4/(4 pi^2 m)` = 0.0098 (m = 313),
0.0064 (m = 523). These differ by a factor 4–6 — the cheapest decisive test in the whole
report. `alpha/Ttail` should meanwhile sit at 0.354 ± 0.01.

**F4 — the judge's own falsifier.** `M` changes sign or drifts by more than ×1.5, or
`E/(alpha M)` rises back above 0.1 at larger m.

**F5 — reality of the root divisor.** `ZerosRealOn` for the ground row is verified only at
m = 13, 23, 43 (`out/xi_row_zeros.md`: `NONREAL=0`). If a complex ground root appears at
m = 83 or 163, form (iii) and the whole §3.4/§3.5 argument lose their hypothesis at exactly
the two cells that carry the trend.

## 5. Q(5) — Lean-ready versus new analytic

### 5.1 Already green, reusable now

Three of the judge's five "Lean-ready bookkeeping" items have a green ancestor in the repo:

| judge's item | status | where |
|---|---|---|
| `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY` (F) | rearrangement of (C)+(D)+(E)+linearity | new file |
| curvature closed form / alternating identity | **kernel-green** | `proposition59_alternating_curvature_identity` |
| `eta(2) = pi^2/12` | **kernel-green** (derived; Mathlib has no `eta(2)`) | `hasSum_alternating_eta_two_zero` |
| alternating tail bound `|TailAlt| <= 1/(N+1)^2` | **kernel-green** | `proposition59_alternating_tail_abs_le` |
| `kappa` = zero-divisor second moment | **definitional** | `proposition59Curvature` |

Additional finite items that this preflight shows are worth stating, all still rate-free:

* `P59_CURVATURE_TRANSFER_IS_REARRANGEMENT`: `E = alpha M - 2 pi d_2/ell_1` as an identity, so
  that no later text can present the `3e-15` residual as evidence for a mechanism.
* `P59_FOURTH_JET_RATIO_IDENTITY`: `a_4 = kappa_4(G) - kappa_4(X) - alpha kappa_Xi`.
* `P59_CURVATURE_ROW_DIFFERENCE`: `alpha = (L^2/2pi^2) sum (-1)^n Delta_n/n^2 + [kappa(y-row) - kappa_Xi]`,
  with the `TailAlt` cancellation explicit.
* `P59_ROOT_DIVISOR_SPLIT`: `alpha = Ttail - Def` with `Ttail = (L^2/4pi^2) sum_{k>N} 1/k^2`.
* `P59_COUNT_TO_MOMENT_ABEL`: `N_G >= N_Xi` on `[0,T]` implies domination of the truncated
  inverse-square sums (Abel summation; the analytic half of §3.5).

### 5.2 Two hypothesis catches to record before anything is built on them

1. **`ZerosRealOn` is false for the Ξ-sample row.** `out/xi_row_zeros.md`: `NONREAL = 16/26,
   28/46, 50/86` at m = 13, 23, 43. Hence any α-split that goes through the *zero-sum*
   definition (iii) for the Ξ row is invalid; the split must go through the *closed form* (ii),
   which needs no reality. For the ground row `NONREAL = 0`, but only at m = 13, 23, 43 (F5).
2. **FULL versus EVEN coordinates in the κ formula** (§3.1). The formula as written in
   ADDENDUM 20 is correct only for FULL coefficients; the EVEN-coordinate version needs a
   `1/sqrt2` on the sum. Any report that reuses it must name its basis (convention-card rule).

### 5.3 New analytic — unchanged from the judge's list, with one addition and one deletion

Unchanged: second-mode selection coherence; second-mode profile limit; `d_2 = O(L^-2)`;
combined interpolation + higher-mode tail; uniform Poisson/trapezoid crosswalk; the
`Tr_m(B F_2) = o(L^-2)` estimate.

**Add:** `P59_GROUND_ROOT_COUNT_LOWER_BOUND` — `N_G(t) >= N_Xi(t)` for `t <= T* ~ 1.5 x_N`
(one-sided, location-free), which by §3.5 delivers `alpha = O(L^2/m)` and hence the atom, with
no spectral gap and no pinning.

**Delete (or at least demote):** the search for a `1/L^2` perturbation-theoretic mechanism for
`alpha`. §3.4 gives reasons to believe `L^2/m` is the true scale and that the `1/L^2` reading
is an artifact of a five-cell window in which `L` moves only from 2.56 to 5.09.

## 6. Strange things recorded before they are explained

Per `CLAUDE.md` ("everything strange is written down before it is explained"), four entries,
each with both readings and the distinguishing outcome:

1. **`alpha * L^2` turns over at m = 163** (0.0184, 0.0310, 0.0387, 0.0403, 0.0367).
   *A*: noise/finite-size on a genuine `1/L^2` plateau. *B*: `alpha` decays faster than `L^-2`
   and the plateau is a maximum. Distinguisher: F3 (m = 313).
2. **Two decompositions of the same few percent disagree.** The continuum profile
   decomposition (morning entry) attributes `-6 %/-5 %` to the `x^4` jet and `-13 %/-10 %` to
   the band-limit orthogonality residue `I_12`, total ~`-19 %` of `d_2/d_1`; the exact lattice
   ledger attributes `+6.6 %/+5.2 %` to `E`. Same order, wrong sign, factor 3.
   *A*: different references (continuum integrals with fitted profiles vs exact lattice traces;
   `d_2/d_1` vs `d_2/alpha`). *B*: one of the two decompositions has a sign or normalisation
   error. Distinguisher: F1 — the exact fourth jet is common to both.
   The exact ledger is authoritative; the fits are not source objects.
3. **`E/(alpha M)` is not monotone** (0.048 at m = 13, rising to 0.070 at m = 23, then falling).
   The registered prediction `P_E_OVER_ALPHA_M_DECREASES` was REFUTED as worded for exactly
   this reason. *A*: m = 13 is below the asymptotic regime (`Def/Ttail` also moves most between
   13 and 23). *B*: two competing terms of opposite sign inside `E`. Distinguisher: F1.
4. **All five registered cells have odd m**, so the alternating tail carries the same sign in
   every one of them. Never noticed, never controlled. Distinguisher: F2.

## 7. Для владельца — крыша, опоры, канаты

Крыша прежняя. По опоре G6 сегодня натянут один канат и обнаружены два.

Натянут: тождество переноса кривизны судьи проверено **как тождество** — оно есть
перестановка определения `B` и линейности следа, поэтому невязка `3e-15` проверяет
арифметику, а не механизм. Остаток `E` при этом действительно мал (4–7 % и убывает),
`M` устойчив (1.3 % по всем пяти ячейкам), `d₂ = −13.8·α` с точностью 2 %. Код судьи —
**успех**: механизм назван, а не переименован. Главный выигрыш: из вопроса о ТЕМПЕ ушёл
второй собственный вектор; остался один скаляр от строки дна.

Найдено первое: кривизна в этом проекте по определению (Lean,
`Proposition59ExplicitProductCurvatureBridge.lean:922`) есть **вторая обратная степень
нулевого дивизора** — `κ = Σ 1/ρ² + (L²/4π²)Σ_{k>N}1/k²`. Значит «стена кривизны» и «атом
= полный нулевой дивизор» из ZEROPIN — одна и та же вещь. И `κ_Ξ = Σ 1/γ²` подтверждается
классической константой `(2+γ_E−ln4π)/2` до шести знаков.

Найдено второе, и оно неприятное: `α = Ttail − Def`, где `Ttail` — явное классическое число.
Отношение `α/Ttail = 0.226, 0.298, 0.332, 0.348, 0.352` монотонно сходится к `0.354`,
а `α·L² = 0.018, 0.031, 0.039, 0.040, 0.037` **разворачивается**. Похоже, закон не `1/L²`,
а `L²/m` — то есть `α` падает экспоненциально по `L`, а не полиномиально. Для маршрута это
хорошо (нужное `d₂ = O(L⁻²)` тогда выполнено с колоссальным запасом), но это значит, что
мы полгода целимся не в тот показатель. Различающий зонд дешёвый: одна ячейка `m = 313`.
Два прочтения расходятся в 4–6 раз.

Поставщик, который из этого следует, — **счёт нулей, а не их положение**: если нулей у дна
не меньше, чем у Ξ, до высоты `~1.5 x_N`, то `α = O(L²/m)` без всякой щели и без
запрещённого судьёй «нули дна = нули дзеты». Считающий объект уже открыт — это «полный
забор» WINDLOCK.

---

**Read-only preflight.** No `.lean` file touched, no eigensolve, no probe, no commit, no push.
Every number in §3.4 is arithmetic on scalars already published on the bus.
`DIAGNOSTIC_NEVER_A_PROOF`.
