# Track B S5.1: Negative-Mass Ledger

Status: REFUTED(Route A small-negative-ledger for the current smoothed lift)
plus OPEN(Route C direct PSD lift).  This is a numerical diagnostic audit only:
no Lean proof, no Q3.Main change, no route mutation, and no RH-conditional
input.

## Established Input

S3 remains a closure identity / bookkeeping regression:

```text
S3 = B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC
```

S4 remains fatal only for the current smoothed receiver lift:

```text
L = Mplus * F_v
S4 = B2B_S4_FATAL_NOT_PSD_ELIGIBLE_FOR_CURRENT_LIFT
```

Scope:

```text
fatal for current lift only
not fatal for all B2b
not a reason to reopen B2a
```

## Universal Replacement Requirements

Any replacement lift `L` must satisfy all four requirements.

| id | requirement | meaning |
| --- | --- | --- |
| R1 | edge-control | `L` must control the edge defect one-sidedly or through an explicit `mu`-ledger-compatible inequality. |
| R2 | PSD eligibility | The zero-side object must have a PSD / nonnegative-hat / Hermitian-square certificate. |
| R3 | cone transport | `ker Q` and cone structure must be preserved; no supnorm-only shortcut. |
| R4 | budget | Every correction, projection, or signed-negative part must fit the `mu`-book. |

## S5.0 Failure Atlas Entry

```text
DO_NOT_USE:
  L = Mplus * F_v as zero-side PSD lift

Reason:
  S4 planted detector valid;
  hat(L) has large negative values;
  L is not PSD eligible.

Scope:
  kills current lift only, not all B2b.
```

Important correction for Route B:

```text
hat(L_proj) = max(hat(L), 0)
```

does repair Fourier-side PSD if the projected object is regular enough.  The
danger is not "clipping kills Hermitian-square".  The danger is that clipping
may destroy physical edge-control and create a projection-loss ledger larger
than the `mu`-budget.

## S5.1 Command

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvnegmass \
  --K 2 3 3.5 --schedule stable --grid-delta 0.5 --k-spline 5 \
  --p0-na 401 --receiver-delta 1 --directions opnorm \
  --quad-na 4001 --fourier-u-max 2 --fourier-nu 1001 \
  --top-modes 8 --q3-weight one_plus_u2 --budget-fraction-threshold 0.05
```

D2 convention:

```text
raw a = r log p
xi = a / (2*pi)
hat(f)(u) = int f(a) exp(-2*pi*i*u*a) da after even extension
q3_weight = 1 + u^2 diagnostic spectral proxy
```

The exact `mu`-book numerical threshold is not present in the local Track B
docs.  Therefore this audit does not report a proof-grade `mu_budget_ratio`.
It reports the available scale test: the negative part is approximately half of
the sampled spectral L1 mass, far beyond the `5%` small-ledger threshold.

## Summary Table

`L` denotes the failed S4 lift `Mplus*F_v`.  `E` denotes the correction
`(Mplus-1_edge)*F_v`.

| K | object | min hat | neg mass | neg/L1 | q3-neg mass | q3-neg/L1 | neg width / `[0,2]` | regions | verdict |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 2 | `L` | `-1.68036` | `0.370328` | `0.499632` | `0.652242` | `0.499667` | `0.978 / 2` | 8 | `S5_NEGMASS_BUDGET_SIZED` |
| 2 | `E` | `-0.412284` | `0.205267` | `0.508842` | `0.444670` | `0.522080` | `1.014 / 2` | 8 | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | `L` | `-2.67972` | `0.401929` | `0.500130` | `0.597761` | `0.500830` | `0.974 / 2` | 13 | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | `E` | `-0.449693` | `0.209726` | `0.494477` | `0.410513` | `0.486656` | `0.958 / 2` | 13 | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | `L` | `-2.44648` | `0.399101` | `0.500021` | `0.763298` | `0.500286` | `0.986 / 2` | 14 | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | `E` | `-0.459538` | `0.193493` | `0.506019` | `0.457622` | `0.513305` | `0.988 / 2` | 14 | `S5_NEGMASS_BUDGET_SIZED` |

## Top Negative Modes

For the current lift `L=Mplus*F_v`:

| K | top negative sampled modes `(u, hat L(u))` |
| --- | --- |
| 2 | `(0.650,-1.68036)`, `(0.630,-1.40220)`, `(0.850,-1.34227)`, `(0.670,-1.33341)` |
| 3 | `(0.504,-2.67972)`, `(0.640,-1.79001)`, `(0.484,-1.69688)`, `(0.524,-1.55077)` |
| 3.5 | `(0.924,-2.44648)`, `(0.802,-2.01534)`, `(1.050,-1.57673)`, `(0.944,-1.34059)` |

For the correction `E=(Mplus-1_edge)*F_v`:

| K | top negative sampled modes `(u, hat E(u))` |
| --- | --- |
| 2 | `(0.638,-0.412284)`, `(0.892,-0.408276)`, `(0.912,-0.365826)`, `(0.658,-0.362860)` |
| 3 | `(0.508,-0.449693)`, `(0.338,-0.440602)`, `(0.170,-0.434606)`, `(0.000,-0.432968)` |
| 3.5 | `(0.932,-0.459538)`, `(1.078,-0.433489)`, `(0.788,-0.425690)`, `(1.224,-0.386300)` |

## Direction Sensitivity

The main table uses the opnorm direction matched to S4.  A sensitivity run with
`--directions all` gives the same broad-negative verdict for lower, upper, and
opnorm directions.

| K | direction | object | neg/L1 | q3-neg/L1 | min hat | verdict |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 2 | lower | `L` | `0.499775` | `0.500210` | `-1.81273` | `S5_NEGMASS_BUDGET_SIZED` |
| 2 | lower | `E` | `0.488840` | `0.477182` | `-0.433136` | `S5_NEGMASS_BUDGET_SIZED` |
| 2 | upper/opnorm | `L` | `0.499632` | `0.499667` | `-1.68036` | `S5_NEGMASS_BUDGET_SIZED` |
| 2 | upper/opnorm | `E` | `0.508842` | `0.522080` | `-0.412284` | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | lower/opnorm | `L` | `0.500130` | `0.500830` | `-2.67972` | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | lower/opnorm | `E` | `0.494477` | `0.486656` | `-0.449693` | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | upper | `L` | `0.499834` | `0.499783` | `-2.46316` | `S5_NEGMASS_BUDGET_SIZED` |
| 3 | upper | `E` | `0.505421` | `0.514166` | `-0.454911` | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | lower | `L` | `0.499967` | `0.500148` | `-2.42571` | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | lower | `E` | `0.493965` | `0.487449` | `-0.452640` | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | upper/opnorm | `L` | `0.500021` | `0.500286` | `-2.44648` | `S5_NEGMASS_BUDGET_SIZED` |
| 3.5 | upper/opnorm | `E` | `0.506019` | `0.513305` | `-0.459538` | `S5_NEGMASS_BUDGET_SIZED` |

## Interpretation

The negative spectrum is not a tiny local blemish.  It occupies roughly half of
the sampled spectral L1 mass and roughly half of the `1+u^2` weighted spectral
mass on every tested K.

Therefore:

```text
S5_NEGMASS_BUDGET_SIZED
```

Consequence:

```text
Route A = signed PSD ledger for this current family is REFUTED.
```

The only way Route A could be revived would be an explicit `mu`-book allowance
for order-one signed spectral losses, which is opposite to the current Track B
contract `epsilon_K = o(1/B_K)` / `epsilon_K <= C*K^(-c)`.

## Route Status After S5.1

| route | status | reason |
| --- | --- | --- |
| A signed PSD ledger | `REFUTED_FOR_CURRENT_FAMILY` | Negative spectral mass is broad and budget-sized. |
| B spectral clipping | `DEFERRED_BY_S5_NEGMASS_BUDGET_SIZED` | Clipping repairs PSD, but broad negative mass predicts large projection-loss / edge-control damage. Not run before an explicit route decision. |
| C structure-first PSD lift | `MAIN_OPEN_ROUTE` | Needs C0 uncertainty-tax preflight before constructing objects. |
| D finite ledger fallback | `PARKED_LAST_ROUTE` | Only after A dies, C fails/borderlines, and B projection loss is explicitly unacceptable. |

## S5C Preflight Input Gap

C0 requires:

```text
actual Fourier slack B_K
explicit mu-budget target for the relevant K range
edge-control inequality shape required from a PSD lift
```

The local docs record the qualitative target `epsilon_K = o(1/B_K)` and
`epsilon_K <= C*K^(-c)`, but do not expose a single proof-grade numerical
`mu_budget(K)` for this S5 run.  Therefore S5.1 stops at the route decision:
Route A is killed for the current family; Route C is the next serious Track B
path, with C0 uncertainty-tax as its first gate.

## Status Dictionary

```text
PROVED: none
SKETCH: sampled Fourier negative-mass ledger
OPEN: Route C direct PSD lift after C0 uncertainty-tax preflight
REFUTED: current lift L=Mplus*F_v as PSD object; Route A small-negative-ledger for this family
ZERO_CONSISTENT: S3 closure identity remains green; S4 detector remains valid
GAP: exact mu-budget ratio absent from local S5 inputs
```
