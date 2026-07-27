# SOFT_L2 projection measurements — edge profile and `(13,120)` lag ledger

Status: `MEASURED / DIAGNOSTIC_ONLY / NOT_RH`

The measurements implement the exact definitions in the round-9/round-10
verdicts. They do not assert smallness and do not infer support from a grid.

## 1. Two-edge profile `e_L(delta)`

The measured quantity is exactly the round-10 norm-scale

```text
e_L(delta)
  = (integral_{L/2-delta<|u|<=L/2} |q_L(u)|^2 du)^(1/2),
0<delta<=L/2.
```

Each interval mass is integrated analytically from the Fourier coefficients;
the profile is not a sampled-density Riemann sum. All available coefficient
cells were retained, with source roles kept separate:

| series | role | fitted inward slope `d log(e_L)/d delta` | `R^2` on `0.05<=delta/L<=0.20` | `e_L(0.01L)` | `e_L(0.10L)` |
|---|---|---:|---:|---:|---:|
| `(12,120)` | portable `k1` | 57.6429 | 0.9683 | `5.254e-22` | `1.224e-9` |
| `(13,90)` | portable `k1` | 60.9838 | 0.9675 | `5.870e-24` | `2.396e-10` |
| `(13,120)` | portable `k1` | 60.9838 | 0.9675 | `5.870e-24` | `2.396e-10` |
| `(14,120)` | portable `k1` | 64.2522 | 0.9667 | `6.606e-26` | `4.803e-11` |
| `(53,120)` | float64 `k1` diagnostic | 4.5942 | 0.4008 | `7.466e-16` | `3.011e-15` |
| `(101,120)` | float64 `k1` diagnostic | 1.0437 | 0.9276 | `6.006e-16` | `1.951e-15` |
| `(13,120)` | finite ground `xi1` | 61.1021 | 0.9673 | `4.763e-24` | `2.347e-10` |

Registered prediction readback:

- On the high-precision `N=120` cells `m=12,13,14`, the curves are close to
  exponential on the registered outer-depth band and the fitted exponent is
  strictly increasing: `57.64 < 60.98 < 64.25`.
- The independent `(13,120)` ground vector tracks the portable `k1` profile
  closely (`61.10` versus `60.98`), which is a useful consistency check.
- The `m=53,101` inputs are float64-only and hit an approximately `1e-15`
  cancellation floor near the edge. They cannot decide the large-`m`
  exponent. Therefore the all-cell monotonicity prediction is **supported on
  the high-precision cells and unresolved, not falsified, on the two
  large-`m` float64 cells**.

This is not `UniformRadialExponentialLocalization`: it is a finite family of
all-depth numerical profiles.

## 2. Exact-functional lag ledger at `(13,120)`

Inputs:

```text
L=log(13)=2.5649493574615367...
mu=3.4839881993313208538820384112812237e-59
A(t)=<U_t q,q>
LHS(t)=W02(t)-WR(t)-Wp(t)
residual(t)=LHS(t)-mu*A(t).
```

The lag grid is `t/L=k/6`, `k=-6,...,6`. Symmetry agrees to the displayed
precision, so the compact table shows the nonnegative half:

| `t/L` | `LHS` | `mu A(t)` | residual | window `E_win` from `D_(a,L)` | aggregate remainder |
|---:|---:|---:|---:|---:|---:|
| 0 | `5.7315e-36` raw | `3.4840e-59` | `5.7315e-36` raw | `0` | `5.7315e-36` raw |
| 1/6 | `1.9457900e-2` | `1.2615e-59` | `1.9457900e-2` | `-6.0041e-7` | `1.9458501e-2` |
| 1/3 | `1.1115106e-3` | `4.3659e-61` | `1.1115106e-3` | `-2.5837261e-2` | `2.6948772e-2` |
| 1/2 | `1.5177378e-6` | `4.7435e-64` | `1.5177378e-6` | `-7.6469112e-1` | `7.6469264e-1` |
| 2/3 | `4.9090237e-12` | `1.3539e-69` | `4.9090237e-12` | `-1.7389334` | `1.7389334` |
| 5/6 | `8.1831189e-23` | `2.0963e-80` | `8.1831189e-23` | `-2.1961298` | `2.1961298` |
| 1 | `7.1887167e-37` | `-6.6688e-140` | `7.1887167e-37` | `-2.7237980` | `2.7237980` |

The isolated window row is computed as required:

```text
E_win(t)=-sum_k Lambda(k)/sqrt(k)
  [D_(log k,L)(t)+D_(-log k,L)(t)].
```

The reported remainder is

```text
residual-E_win
 = Galerkin + sector + Arch-window + pole/midpoint correction.
```

It is deliberately **not** labelled pure Galerkin: the saved finite matrix
does not supply the ambient vector `T_full q`, and D0.3 forbids promoting the
form compression to `P A_m P`. Numerically, however, the non-window aggregate
is plainly not small: it ranges from `1.95e-2` to `2.72` on the nonzero lag
grid and remains `2.72` at `|t|=L`. It cancels the window row almost exactly
at large lags. This supports Proshka's warning that the omitted
Galerkin/correction ledger cannot be treated as a small compactly supported
edge source. A finite grid does not prove noncompact support.

### `t=0` cancellation anchor

Direct `W02-WR-Wp` quadrature is cancellation-limited at `t=0`: it returns
`5.7315e-36`, far above the `1e-59` eigenvalue. The saved high-precision
finite-matrix eigenpair supplies the exact anchor instead:

```text
LHS(0)=mu*A(0)=mu,
residual(0)=0,
E_win(0)=0.
```

The raw value is kept in the CSV/JSON rather than silently replaced; the
matrix anchor and its interpretation are recorded separately.

## 3. Artifacts and scope

- `SOFT_L2_EDGE_MASS_PROFILE.csv/.json`: all depth/cell values and fits;
- `SOFT_L2_EDGE_MASS_PROFILE_LOG.png`: requested log-scale plot;
- `SOFT_L2_LAG_LEDGER_13_120.csv/.json`: all 13 lag rows, individual
  `W02`, `WR`, `Wp`, `LHS`, `muA`, window, and remainder fields;
- `soft_l2_projection_measurements.py`: deterministic runner.

Closeout: diagnostic measurement complete, `NOT_RH`; Bus 010 was not
created.
