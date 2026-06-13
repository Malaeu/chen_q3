# Track B S5C0: PSD-First Tax Preflight

Status: SKETCH_DIAGNOSTIC(surcharge confirmed) plus GAP(exact `mu_budget(K)`
absent).  This is a finite numerical tax instrument only: no Lean proof, no
Q3.Main change, no route mutation, and no RH-conditional input.

## Accepted Prior State

```text
S3:
  closure identity is GREEN as bookkeeping/regression only.

S4:
  current lift L=Mplus*F_v is not zero-side PSD eligible.

S5.1:
  negative spectral mass is budget-sized, about half of spectral L1.
  Route A signed-small-negative ledger is refuted for this family.

Route B correction:
  spectral clipping repairs PSD; the danger is edge-control/projection-loss,
  not Hermitian-square failure.
```

## C0 Question

Route C wants a PSD-first lift:

```text
hat(L) >= 0
supp hat(L) subset [-B_K, B_K]
L controls the hard edge [2K,4K]
```

The preflight asks whether this object pays only the ordinary hard-edge tax
`1/B_K`, or whether PSD/nonnegative-hat adds a sign-uncertainty surcharge.

## C0.0 Planted Instrument

The finite LP tax checker is required to distinguish hard-edge from smooth-edge
targets before the surcharge number is used.

Finite LP surrogate:

```text
L(a) = c0 + 2 * sum_j c_j cos(2*pi*u_j*a)
c_j >= 0
u_j in [0,B_K]
sampled L(a_i) >= target(a_i) on [0,max_a]
```

This enforces sampled Fourier-side PSD by nonnegative spectral masses.  It is a
diagnostic finite LP, not a continuous extremal theorem.

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvtaxpreflight \
  --K 2 3 3.5 --bandlimit 1 \
  --tax-na 801 --freq-nu 121 --a-margin 4 \
  --planted-tol 0.05 --surcharge-tol 0.05
```

C0.0 result:

| K | hard PSD tax | smooth PSD tax | hard/smooth | instrument |
| --- | ---: | ---: | ---: | --- |
| 2 | `2.93072` | `1.77598` | `1.65020` | `S5C0_TAX_INSTRUMENT_VALID` |
| 3 | `3.50596` | `2.41236` | `1.45333` | `S5C0_TAX_INSTRUMENT_VALID` |
| 3.5 | `3.96288` | `2.84375` | `1.39354` | `S5C0_TAX_INSTRUMENT_VALID` |

The detector sees the hard edge as strictly more expensive than the smoothed
edge at the same sampled PSD/bandlimit constraints.

## C0.1 Ordinary Tax Baseline

The ordinary Selberg/Vaaler hard-edge reference from the local CLV pair docs is:

```text
ordinary_tax = 1/B_K
```

For this run:

```text
B_K = 1
ordinary_tax = 1
```

This is the B2a scalar-mask tax.  It does not include the extra PSD/nonnegative
Fourier-side constraint.

## C0.2 Sign-Uncertainty Surcharge

The PSD-first finite LP tax is larger than the ordinary `1/B_K` baseline.

| K | ordinary tax `1/B_K` | PSD hard-edge tax | additive surcharge | surcharge ratio |
| --- | ---: | ---: | ---: | ---: |
| 2 | `1.00000` | `2.93072` | `1.93072` | `2.93072` |
| 3 | `1.00000` | `3.50596` | `2.50596` | `3.50596` |
| 3.5 | `1.00000` | `3.96288` | `2.96288` | `3.96288` |

Verdict:

```text
S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN
```

Interpretation:

```text
tax_PSD(K,B_K) > 1/B_K
```

on the finite LP instrument.  This matches the v8 sign-uncertainty warning:
PSD-first is not "ordinary Selberg tax for free"; nonnegative-hat is an
additional constraint.

## C0.3 Ratio To Budget

No proof-grade numerical `mu_budget(K)` is exposed in the current local Track B
docs.  Therefore this audit does not claim:

```text
S5C0_FATAL_UNCERTAINTY_TAX
```

as a theorem-grade final verdict.

What it does establish diagnostically:

```text
PSD-first hard-edge tax is order 3-4 at B_K=1 in this finite LP surrogate.
The local Track B target is qualitative decay: epsilon_K=o(1/B_K) or
epsilon_K<=C*K^(-c).
Without an additional normalization or named cancellation, this scale is
incompatible with the intended shrinking mu-ledger.
```

If a future route supplies explicit `mu_budget(K)`, rerun:

```bash
... clvtaxpreflight --mu-budget <value>
```

and compare `psd_hard_edge_tax / mu_budget`.

## C0.4 Atlas Links

Hard-edge tax:

```text
docs/trackB/b2_uncertainty_tax_preflight.md
docs/trackB/clv_pair.md
docs/RH_TRICK_ATLAS.md#9-selberg-extremal-functions
```

Sign-uncertainty surcharge:

```text
docs/RH_TRICK_ATLAS.md#11-sign-uncertainty-surcharge
```

The v8 correction is now explicit: Route C inherits the hard-edge tax and adds
a PSD/sign-uncertainty surcharge.  It is not just "B2a with PSD pasted on".

## Route Status After C0

| route | status | reason |
| --- | --- | --- |
| A signed PSD ledger | `REFUTED_FOR_CURRENT_FAMILY` | S5.1 negative spectral mass is broad. |
| B spectral clipping | `DEFERRED` | PSD repair is possible, but projection-loss / edge-control is endangered. |
| C PSD-first lift | `SURCHARGE_CONFIRMED_MU_RATIO_OPEN` | PSD-first finite tax is `2.93x` to `3.96x` the ordinary `1/B_K` baseline. |
| D finite ledger | `PARKED_LAST_ROUTE` | Still the last fallback before global negative Track B closure. |

## Status Dictionary

```text
PROVED: none
SKETCH: finite sampled PSD-majorant LP tax instrument
OPEN: explicit mu-budget ratio; possible Route D finite ledger fallback
REFUTED: assumption that PSD-first edge control pays only ordinary 1/B_K tax
ZERO_CONSISTENT: S3 closure green; S4 current lift fatal; S5.1 Route A killed
GAP: continuous extremal theorem and exact mu_budget(K)
```
