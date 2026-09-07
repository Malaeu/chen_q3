# Parity-complete Legendre packet — certified floors on both parity blocks

**RESULT CODE: `CLASSFLOOR_PARITY_COMPLETE_PACKET_PSD_CERTIFIED_COMPLEMENT_UNSIGNED`** — the second success condition of the CLASSFLOOR CODEX DIRECTIVE §8 (the verdicts define no code for it). **No negative direction exists on this packet**, so neither `CLASSFLOOR_SCALAR_NEGATIVE_DIRECTION_NOT_FULL_MARGIN` nor `CLASSFLOOR_UNSIGNED_COMPLEMENT_ZERO_STRADDLE` fires; `CLASSFLOOR_INTERVAL_SERIALIZATION_GAP` is closed by §3(d).

```
packet  h_j = (d^2/dx^2 - 1/4)[ (1-z^2)^4 P_j(z) ],  z = x/delta,  j = 0..7,  N = 1, zero extension
rank 8 = 4 (even) + 4 (odd), symbolic over Q(u);  the 32 cross-parity entries vanish exactly
EVEN {L0,L2,L4,L6}:  F >= 0 CERTIFIED   0.00100526773010578 <= lambda_min <= 0.00105181125036325
ODD  {L1,L3,L5,L7}:  F >= 0 CERTIFIED   0.00087028981368640 <= lambda_min <= 0.00096434783699806
=> for EVERY complex c on the 8-dim packet span:  m(h) >= F(h) = c*Fc/c*Hc >= 870289813/10^12
   both blocks >= 1/2000; the even block also >= 1/1000; the odd block is NOT >= 1/1000 -- its float
   lambda_min is 0.00092318, so no X reaches 1/1000 there: a property of the packet, not of X.
```

Every interval below is a numerical certificate (python-flint 0.8 / arb, ball arithmetic), CONDITIONAL on the paper theorems of §9. Anything that is not such an interval is **DIAGNOSTIC_NEVER_A_PROOF**.

## 1. The packet, its rank, its parity split

Predeclared in CLASSFLOOR §5.6 and fixed here before any entry of **F** existed (all scripts written and the run launched before the first assembly). `a = log 2`, `delta = (log3-log2)/8 = 0.050683138513520547747`, support `[-delta,delta]`, `eta_j = (1-z^2)^4 P_j(z)`, `h_j(x) = p_j(z) = delta^{-2} eta_j'' - eta_j/4`, `deg_z p_j = 8+j`.

* **Rank 8 = 4 + 4**, symbolic over `Q(u)`, `u = delta^{-2}`: `eta -> eta''-eta/4` is injective on polynomials and `p -> (1-z^2)^4 p` is injective. No exact dependence (unlike the 2026-09-07 packet, rank 3). `P_j` has the parity of `j`, hence so does `h_j`.
* **Vanishing order exactly `m = 2` for every test**: `P_j(±1) = ±1 ≠ 0`, so `p_j(±1) = p_j'(±1) = 0` and `p_j''(±1) = ±384u ≠ 0` — exact rational identities in `u`, all eight tests, both endpoints. The analytic tail is the `xi^{-3}` one everywhere and `C_a = 2|p''(1)|delta^{-2} = 116387735.517` is the **same** for all eight (it equals `B_3` of the h4 report).
* **Cross-parity entries vanish exactly**: `b = (1-cos a xi) ell_2` is real and even (`ell_2(-xi) = 2Re(conj(gamma_2 t_2)) = ell_2(xi)`) and `g_j` has the parity of `j` (§5 V4), so the cross-parity integrand is odd. **These 32 entries were not computed.**
* **`h_0 = h_4` exactly** (`P_0 = 1`) — used as a cross-run check (§5 V2). **Span identity**: `span{L0,L2,L4,L6} = eta_4·span{1,z^2,z^4,z^6} = span{h4,h5,h6,h7}`, the earlier packet's *span4* (rank identity over `Q`: 4, 4, union 4) — see §8.
* **Pole-nullity**: `int h e^{±x/2}dx = 0` algebraically (two parts; `eta, eta'` vanish at `z = ±1`); arb confirmation `<= 5.1e-114`, all eight tests, both signs.

## 2. Conventions, objects, transform evaluator

Identical to the h4 and packet reports §2 (nonunitary `hhat`, `gamma_2` = RESONANCE (2), `t_2` = RESONANCE (10) with `p = 2`, `ell_2 = 2Re(gamma_2 t_2)`), reusing `h4arb.py`, `evalf.py`, `cert.py`, `budget.py` unchanged. With `w_a = 1-cos(a xi)`: `F_ij = -int w_a conj(hhat_i)hhat_j ell_2`, `M_ij` the same with `d_2`, `H_ij = <h_i,h_j>`; `M - F >= 0` (v1 (8)) and `m(sum c_j h_j) = c*Mc/c*Hc` (v2 Cor. 1 (6)).

For an **odd** test `hhat_j = -i v_j` with `v_j` real and odd, so inside a parity block `conj(hhat_i)hhat_j = g_i g_j` with `g = hhat` (even) or `g = i·hhat = v` (odd) — real and even in `xi` either way. Each block of `F` is real symmetric, so a certified `F >= 0` covers **all complex** coefficient vectors (CLASSFLOOR §2.4). The continuation used for the quadrature bound is `conj(hhat_i(zbar))hhat_j(z) = G_i(z)G_j(z)`, entire, `|G_i(z)| <= ||h_i||_1 e^{delta|Im z|}` — CLASSFLOOR §2.2, never a continuation of `Re` or `| |^2`.

`hhat_j(xi) = delta int_{-1}^1 p_j(z)e^{-i delta xi z}dz` is assembled from `E_n(c) = int_0^1 z^n e^{icz}dz`, `n = 0..15`, once per node: for `|c| <= 48` the entire power series with a geometric tail enclosure, for `|c| > 48` the exact integration-by-parts recursion `E_0 = (e^{ic}-1)/(ic)`, `E_n = e^{ic}/(ic) - (n/(ic))E_{n-1}`, whose error amplification `n/|c| <= 15/48` is contracting. The branches agree to `1e-120` at `c = 48.1, 202.7, 304.1` against a 4000-bit reference. This is a *different* algorithm from the packet's cosine-moment series, which is what makes §5 V2 a real cross-check.

## 3. What is computed rigorously, per entry

    F_ij = [-int_{|xi|<=X} w_a g_i g_j ell_2^{[J0]}] + R_euler^{ij} + R_freq^{ij},   X = 6000, J0 = 90

**(a) Euler tail.** `|ell_2 - ell_2^{[J0]}| <= 2 eps_{J0}` uniformly, CLASSFLOOR (12) with **C = 256 kept** (the newly proved 120 is deliberately unused, so nothing here depends on it). Cauchy-Schwarz plus the exact identity `int w_a|hhat|^2 = 2 pi H` (Parseval; the `cos(a xi)` part drops since the autocorrelation of `h` lives in `[-2delta,2delta]`, `2delta = 0.1014 < a = 0.6931`) give `|R_euler^{ij}| <= 4 pi eps_{J0} sqrt(H_ii H_jj)` — normalized cost `9.4726921e-10` for every entry.

**(b) Frequency tail: two rigorous branches, minimum taken.** Analytic `2 T0 nu_X^{ij}` from `|hhat_j| <= C_a/|xi|^3 + C_b/|xi|^4`, `T0 = 13.9371046604`; mass-deficit `2 T0 sqrt(D_i D_j)`, `D_i = 2 pi H_ii - int_{|xi|<=X}w_a|hhat_i|^2` (CLASSFLOOR (6)), the compact mass taken on the same nodes with its own Bernstein enclosure. **The mass branch wins on all 20 entries**, by 4.8x (L0,L0) up to 718000x (L7,L7): `C_b` carries the 4th derivative of `p_j` and explodes with the Legendre index, while the true tail amplitude is set by `h_j''(±delta) = 384 delta^{-4}`, the *same* for all eight. So `D_i` is nearly test-independent: `3.4554e-4 .. 3.6970e-4` at `X = 6000` (`2.6464e-3 .. 3.0468e-3` at `X = 4000`, matching the closed form `4K^2/(5X^5)`, `K = 384 delta^{-4}`, to four digits).

**(c) Quadrature.** Composite Clenshaw-Curtis, `w = 0.5`, `n = 36`, doubled by evenness. The rule does not depend on `rho`, so the ATAP Thm 8.2 bound is re-derived post hoc with `rho` optimized and the semi-**minor** axis `R_min = (w/4)(rho-1/rho)` used for every factor measuring distance to `Im xi = ±1/2`. Sweep over the 12000 panels: `3.0 -> 7.34e-7`, `3.4 -> 4.54e-8`, `3.6 -> 1.61e-8`, `3.8 -> 9.20e-9`, **`3.9 -> 9.0066303e-9` (best)**, `4.0 -> 1.20e-8`. `E_quad^{ij} = ||h_i||_1||h_j||_1·Ebase`; since `||h_i||_1||h_j||_1/sqrt(H_iiH_jj) = 2delta`, the normalized cost is `9.130e-10` for all 20 entries.

**(d) Serialization — NOTES.md items 2 and 3, mandatory this run.** `Ebase` and `Ebasem` are emitted as full balls *and* as certified upward-rounded decimals, each verified by ball comparison `arb(s) > x`: `Ebase = 9.00663030119015950e-09` (ball `[9.0066303011901505502e-9 +/- 4.82e-29]`), `Ebasem = 1.87229186662733177e-17` (ball `[1.8722918666273299783e-17 +/- 4.13e-38]`). No radius-free decimal is relied on anywhere. `abs_lower` is **never** used as a signed lower endpoint: every directed endpoint below comes from `legser.dec_lower / dec_upper / rat_lower`, which emit a decimal (or rational) and then *verify* `arb(s) < x` / `arb(s) > x`; the helper is sign-agnostic and self-tested on negative and zero-straddling balls. The float transports in `cert.pack` / `read_mr` are radius-padded (`2^-50|m|`, `2^-48|m|`, 1.0001 inflation) — protected, and stated, not silent.

## 4. The matrices and the full ledger

**H** (Gram, exact rational in `delta`; radii `<= 4e-10` are pure evaluation width). The 32 cross-parity entries are **exactly zero** (`arb.is_zero()`), so `H` is block diagonal in the parity basis.

```
EVEN       L0            L2            L4            L6      ODD        L1            L3            L5            L7
 L0  301750.44686 -201163.44624  178480.99298 -118952.22040   L1  100578.97888 -145937.37469  145988.67050 -100266.52353
 L2 -201163.44624  183409.53145 -227105.08655  211897.72761   L3 -145937.37469  256270.59445 -327575.87075  298834.94582
 L4  178480.99298 -227105.08655  379576.72025 -473201.31308   L5  145988.67050 -327575.87075  550725.93889 -668998.65117
 L6 -118952.22040  211897.72761 -473201.31308  780229.60112   L7 -100266.52353  298834.94582 -668998.65117 1078008.24147
```

**F** (interval: midpoint = rule value, radius = `E_quad + E_euler + E_freq` + rule ball).

```
EVEN      L0              L2              L4              L6     ODD      L1              L3              L5              L7
 L0 1058.8 ±0.0334  -642.8 ±0.0390   533.9 ±0.0496  -353.9 ±0.0589  L1  265.0 ±0.0571  -366.6 ±0.0156   355.1 ±0.0271  -245.7 ±0.0526
 L2 -642.8 ±0.0390   492.7 ±0.0436  -540.4 ±0.0561   475.6 ±0.0586  L3 -366.6 ±0.0156   582.7 ±0.0107  -682.9 ±0.0569   592.1 ±0.0432
 L4  533.9 ±0.0496  -540.4 ±0.0561   777.2 ±0.0197  -883.2 ±0.0471  L5  355.1 ±0.0271  -682.9 ±0.0569  1008.0 ±0.0343 -1120.0 ±0.0166
 L6 -353.9 ±0.0589   475.6 ±0.0586  -883.2 ±0.0471  1283.2 ±0.0352  L7 -245.7 ±0.0526   592.1 ±0.0432 -1120.0 ±0.0166  1602.5 ±0.0211
```

| entry | I_compact (rule value) | E_quad | E_euler | E_freq | (nu branch) |
|---|---|---|---|---|---|
| L0,L0 | `1058.7767974996 ± 2.36e-11` | 2.755e-4 | 2.858e-4 | **9.632e-3** | 4.667e-2 |
| L0,L2 | `-642.8289052932 ± 4.56e-11` | 2.148e-4 | 2.228e-4 | 9.637e-3 | 7.503e-2 |
| L0,L4 | `533.9392310715 ± 4.70e-11` | 3.090e-4 | 3.206e-4 | 9.675e-3 | 4.662e-1 |
| L0,L6 | `-353.9481164264 ± 3.03e-11` | 4.430e-4 | 4.596e-4 | 9.811e-3 | 5.381 |
| L2,L2 | `492.6664026944 ± 4.47e-11` | 1.674e-4 | 1.737e-4 | 9.642e-3 | 1.210e-1 |
| L2,L4 | `-540.3541517049 ± 5.61e-11` | 2.409e-4 | 2.499e-4 | 9.680e-3 | 7.557e-1 |
| L2,L6 | `475.5519330673 ± 3.35e-11` | 3.454e-4 | 3.583e-4 | 9.816e-3 | 8.729 |
| L4,L4 | `777.2091905612 ± 6.27e-11` | 3.465e-4 | 3.596e-4 | 9.718e-3 | 4.748 |
| L4,L6 | `-883.1637869991 ± 8.87e-11` | 4.968e-4 | 5.155e-4 | 9.854e-3 | 5.490e+1 |
| L6,L6 | `1283.2237042256 ± 9.26e-11` | 7.123e-4 | 7.391e-4 | 9.993e-3 | 6.350e+2 |
| L1,L1 | `264.9529122705 ± 5.41e-11` | 9.183e-5 | 9.528e-5 | 9.779e-3 | 5.796e-2 |
| L1,L3 | `-366.60548513975 ± 9.43e-12` | 1.466e-4 | 1.521e-4 | 9.788e-3 | 1.770e-1 |
| L1,L5 | `355.0831910767 ± 9.07e-12` | 2.149e-4 | 2.229e-4 | 9.849e-3 | 1.743 |
| L1,L7 | `-245.65810843425 ± 7.84e-12` | 3.006e-4 | 3.119e-4 | 1.004e-2 | 2.052e+1 |
| L3,L3 | `582.6996014619 ± 2.85e-11` | 2.340e-4 | 2.428e-4 | 9.797e-3 | 5.450e-1 |
| L3,L5 | `-682.8536836706 ± 4.15e-11` | 3.430e-4 | 3.559e-4 | 9.858e-3 | 5.387 |
| L3,L7 | `592.0678473212 ± 2.32e-11` | 4.799e-4 | 4.979e-4 | 1.005e-2 | 6.346e+1 |
| L5,L5 | `1007.9766944082 ± 9.11e-11` | 5.028e-4 | 5.217e-4 | 9.920e-3 | 5.333e+1 |
| L5,L7 | `-1119.994995486 ± 4.35e-10` | 7.035e-4 | 7.299e-4 | 1.011e-2 | 6.284e+2 |
| L7,L7 | `1602.4912829550 ± 5.10e-11` | 9.842e-4 | 1.021e-3 | 1.031e-2 | 7.405e+3 |

**Diagonal normalized floors `F_ii/H_ii`** (certified directed endpoints): L0 `[3.50874906507669e-3, 3.50881666236092e-3]`; L1 `[2.63417811584076e-3, 2.63437631292618e-3]`; L2 `[2.68610041166539e-3, 2.68620929273312e-3]`; L3 `[2.27372683002613e-3, 2.27380702199298e-3]`; L4 `[2.04754064543521e-3, 2.04759558982915e-3]`; L5 `[1.83024926809594e-3, 1.83028902756633e-3]`; L6 `[1.64465979469241e-3, 1.64468914044847e-3]`; L7 `[1.48651828749279e-3, 1.48654114127567e-3]`. All eight `> 1/1000`; L0..L4 also `> 1/500`; L5, L6, L7 are not.

## 5. Verification

* **V1 — mass, load-bearing.** `int_{|xi|<=X}w_a|hhat_i|^2 = 2 pi H_ii - D_i`; at `X = 6000` every `D_i` is enclosed in `[3.4554e-4, 3.6970e-4]` and lies in `[0, nu_ii]`. This row *is* the frequency tail.
* **V2 — `h_0 = h_4`, two independent evaluators.** Over `[0,4000]`, `I_compact[L0,L0]` equals the ratified packet's `I_compact[h4,h4]` — both `[1058.7767974790 ± 1.68e-11]`, `|diff| <= 3.4e-11`; `MASS[L0]` vs `MASS[h4]` both `[1895953.9715004 ± 1.04e-8]`, `|diff| <= 2.1e-8`. `F_00/H_00` is **contained** in the packet h4 diagonal `[0.0035085369, 0.0035090288]` and in the scalar certificate `[0.0034393623, 0.0035782034]`.
* **V3 — second quadrature, different node set.** Band `[0,1000]` under `w = 0.5, n = 36` vs `w = 0.4, n = 28, rho = 2.8` (2500 panels, 72500 nodes, 483.9 s): **all 20 entries overlap** to every printed digit (`|diff| <= 1.4e-10` on values up to 1.6e3).
* **V4 — cross-parity vanishing, measured.** `|ell_2(xi)-ell_2(-xi)| <= 2.5e-43, 2.9e-62, 6.0e-54, 3.1e-88` at `xi = 3.7, 41.3, 377.9, 1913.1`; the L0,L1 integrand at `+xi` plus at `-xi` is `<= 2.6e-45` at each. Parity of all eight profiles confirmed to `1e-100`.
* **V5 — structure.** Rank and vanishing identities (§1) are exact rational statements, not numerics. Max panel ball radius `1.24e-26` on `[0,4000]`, `2.10e-64` on `[4000,6000]`.

## 6. Positivity certificates

Split `F = F0 + Delta`, `F0` the thin midpoint matrix, `|Delta| <= R` entrywise; Weyl gives `lambda_min(F) >= lambda_min(F0) - ||R||_2`, `||R||_2 <= min(||R||_F, ||R||_inf)`, and `lambda_min(F0) > s` is certified by an interval Cholesky of `F0 - sI`. Success proves **every** symmetric matrix in the hull positive definite, the exact `F` included.

| matrix | ok | `\|\|R\|\|_2 <=` | shifted pivots |
|---|---|---|---|
| H even | **True** | 3.19e-107 | 3.0175e5, 49302.9, 36904.2, 36451.2 |
| H odd | **True** | 2.06e-106 | 1.00579e5, 44519.4, 37875.8, 38926.3 |
| **F even** | **True** | 0.0418627 | 1058.73, 102.320, 51.2189, **37.7789** |
| **F odd** | **True** | 0.0430204 | 264.910, 75.3158, 45.2810, **34.8841** |

At `X = 4000` both blocks already certified (`||R||_2 <= 0.3034` / `0.3144` against `lambda_min(F0) = 1.2916` / `0.62713`); the band `[4000,6000]` was run only to tighten the pencil floor, and it shrinks the radius 7.3x. Plain interval Cholesky without the split succeeds at `X = 6000` for both blocks but fails for the odd block at `X = 4000`, so the split is kept.

## 7. Certified pencil floors, weakest directions, growth

    EVEN   0.00100526773010578 <= lambda_min(H^-1/2 F H^-1/2) <= 0.00105181125036325
           rational lower endpoint 1005267730/10^12      >= 1/1000 : TRUE
    ODD    0.00087028981368640 <= lambda_min(H^-1/2 F H^-1/2) <= 0.00096434783699806
           rational lower endpoint  870289813/10^12      >= 1/2000 : TRUE,  >= 1/1000 : FALSE

Lower endpoints: bisection on `lam` with the §6 certificate applied to `F - lam H` (midpoint `F0 - lam H0`, radius `R_F + lam R_H`), then rounded down and verified by ball comparison. Upper endpoints: the interval Rayleigh quotient of the float minimizing vector treated as its exact binary rational. Brackets 4.6 % and 10.8 % wide, the width entirely the `E_freq` row.

**Signed value on the declared weakest direction** (exact rational rounding of the float minimizer, ball arithmetic): even `c*Fc` in `[2.96402372914955, 3.08043955191163]`, `c*Hc = 2928.69996113`; odd `c*Fc` in `[1.44015494958495, 1.57458488797768]`, `c*Hc = 1632.79766201`. Both **strictly positive** — no zero-straddle, no strictly negative upper endpoint. The judge's discriminator returns no negative witness here.

**Weakest combinations (float, DIAGNOSTIC_NEVER_A_PROOF).** Even pencil eigenvalues `0.00103194, 0.00134439, 0.00202696, 0.00385199`, weakest `L0:+0.28506 L2:+1.00000 L4:+0.81752 L6:+0.27572`. Odd `0.00092318, 0.00117998, 0.00168182, 0.00280116`, weakest `L1:+0.67386 L3:+1.00000 L5:+0.66416 L7:+0.19865`. Both are all-positive and peaked on the *second* member, not on the most oscillatory test.

**Growth with the block** (nested `k = 1..4`, certified lower endpoint / float `lambda_min`): even `3.508749083299e-3 / 3.508782865e-3`, `1.977726533743e-3 / 1.978196937e-3`, `1.340125676218e-3 / 1.344348466e-3`, `1.005267730105e-3 / 1.031936245e-3`; odd `2.634178126337e-3 / 2.634277214e-3`, `1.648305006355e-3 / 1.649411538e-3`, `1.169073412685e-3 / 1.177537829e-3`, `8.702898136864e-4 / 9.23182311e-4`. The floor decreases monotonically with every added dimension in both blocks, at a decelerating rate — consistent with, and no evidence against, `inf Spec T <= 0` on the class (CLASSFLOOR §5.1).

## 8. What this settles about the earlier packet

`span{L0,L2,L4,L6} = span{h4,h5,h6,h7}` exactly (§1), and the pencil eigenvalues here reproduce the earlier report's *span4* floats `0.00103194, 0.00134439, 0.00202696, 0.00385199` digit for digit — an independent confirmation of both runs. That span was reported **NOT CERTIFIED at X = 4000**, needing `X ≈ 5900` and three further core-hours. In the Legendre basis the same span certifies at `X = 4000`. The earlier failure was a **basis conditioning artefact**: `lambda_min(F)` is basis-dependent (`F -> L*FL`) and the `(1-z^2)^k` basis made it `0.0146` where the Legendre basis makes it `1.2916`, an 89x difference; the pencil floor — the basis-invariant quantity — is one and the same object.

## 9. What remains unproved — CONDITIONALs

(1) RESONANCE Lemma 2 (6) and the source identity for `ell_2`; (2) SCALARFLOOR Theorem 1 (5)-(6); (3) SCALARFLOOR Thm 4 (31) / CLASSFLOOR Thm 1 (12) with **`C = 256`**, used twice (Euler tail, uniform `T0`) and not re-derived here — the alternative constant 120 is deliberately unused, so nothing here depends on it; (4) Trefethen ATAP Thm 8.2 (re-derived in CLASSFLOOR §2.2); (5) RESONANCE (2)/(10) as the correct source objects at cutoff `lambda = 1`; (6) v1 §2 (8) / v2 Cor. 1 (6), i.e. `M - F >= 0` and `m = c*Mc/c*Hc`; **(7) CLASSFLOOR §4** — the tested trace identity and Mellin density at cutoff one, which is what makes `ell_2` the source object at all, together with its §4.6 regularity extension, which licenses these zero-extended polynomial tests as members of the smooth moment-null class. (7) is a PAPER proof awaiting independent review and was not re-derived here.

**Not certified here**: `T >= 0` on the class, on any infinite-dimensional subclass, or on the complement of this packet; the signed Schur complement (33); the frame contraction (28); the frozen PHASEPROOF bump; anything about the operator part of `d_2`. Per CLASSFLOOR §5.5 a positive finite compression plus *any* unsigned complement bound cannot certify whole-class positivity — an exact theorem-shape obstruction this report does not attempt to evade. No `epsilon_{N,X}` of (29) was computed, so no proximity claim to `T` is made.

## 10. Honest gaps in *this* work

* A packet floor is evidence about one 8-dimensional span; the floor fell at every enlargement (§7) and the trend cannot be extrapolated. The odd block cannot reach `1/1000` at any `X`; the exported joint threshold is `1/2000`.
* `E_freq` dominates every entry (`~1e-2` against `~3e-4` for the other rows) and is set by the single physical quantity `h''(±delta) = 384 delta^{-4}` common to all eight tests. Only a larger `X` or a sharper tail argument moves it; the analytic `nu` branch is useless for the high Legendre modes.
* `P_CF_FIRST_ODD_PACKET_HAS_NO_CERTIFIED_NEGATIVE_DIRECTION` (p = 0.60) is **CONFIRMED**. No independent static re-audit of *this* run has happened; a second body committed these scripts mid-run (§11).
* The scripts are not registered in `docs/cartographer/TOOLS.yaml`; by the project's registry rule they "do not exist" until that entry is made.

## 11. Runtime, files, reproduction

`X = 6000`, `w = 0.5`, `n = 36`, `J0 = 90`, 22 processes, `systemd-run --user --unit=leg_main`: band `[0,4000]` 8000 panels / 296000 nodes / 2999188 J-series calls / **4378.7 s**; band `[4000,6000]` 4000 panels / 148000 nodes / 1776000 calls / **8694.9 s**; cross-check `[0,1000]` at `w = 0.4, n = 28`, 2500 panels / 72500 nodes / **483.9 s**. Total **13557.5 s wall ≈ 3.77 h**, about 83 core-hours; `rho` sweep, assembly and verification take seconds each. `ell_2` is evaluated once per node and reused for all 20 pairs and the eight profiles share one 16-moment cache, so a parity-complete 20-entry packet costs what one scalar cost.

Scripts (this run committed nothing): `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/h4_cert/legendre/` — `legarb.py` (exact coefficients, rank, Gram, tails, moment evaluator, identities), `legbudget.py` (`eps_J`, `T0`, `nu_X`), `legcert.py` (panel loop, masses, full-ball output), `legequad.py` (post-hoc `rho`-optimized Bernstein bound), `legser.py` (certified directed serialization), `legassemble.py` (ledger, positivity, pencil floors, signed witness), `legverify.py`, `run.sh`. Raw outputs in `.../legendre/out/` (`profiles.txt`, `budget.txt`, `equad.txt`, `main_0_4000.txt`, `main_4000_6000.txt`, `xcheck.txt`, `assemble.txt`, `verify.txt`); job logs in `/home/chirurgie/.claude/jobs/4b35770d/tmp/h4_legendre/`. **Note:** a parallel body committed a mid-run snapshot of these scripts as `2ed5751d` at 09:52 while this run was executing; the two later working-tree edits (`legarb.span_identity_report`; the node-precision fix in `legverify` V4) are from this run and are **not** committed.
