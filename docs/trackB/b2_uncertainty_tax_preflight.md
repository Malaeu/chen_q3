# Track B B2-0: Uncertainty-Tax Preflight

Status: PROVED preflight obstruction for naive B2a; OPEN for B2b.  This is
strategy documentation only: no Lean proof, no Q3.Main change, no route
mutation, and no RH/RH-conditional input.

## Purpose

Before spending time on B2, separate two very different routes:

```text
B2a naive scalar mask:
  Selberg/CLV majorant of 1_[2K,4K] times ||g||_infty

B2b structured route:
  explicit formula on a Hermitian-square test,
  zero-side PSD / boundary / cap bookkeeping preserved
```

The preflight kills only the first route when the mu-ledger asks for a bound
better than the available Fourier slack can pay.

## D2

Raw logarithmic coordinate:

```text
x = log n
I_K = [2K, 4K]
|I_K| = 2K
```

Q3 node coordinate:

```text
xi = x/(2*pi)
```

Let `B_K` be the actual Fourier radius/slack available inside the cone
receiver in raw `x` coordinates.  If the analysis is done in `xi`, convert the
radius before comparing to `delta`.

## Allowed Inputs

1. `UNCONDITIONAL`: Selberg-Beurling/Vaaler interval majorant-minorant theorem.
   Source already recorded in `docs/trackB/clv_pair.md`: Vaaler, "Some
   extremal functions in Fourier analysis", Bull. Amer. Math. Soc. 12 (1985),
   183-216.

2. `UNCONDITIONAL`: explicit interval pair with Fourier support
   `supp(hat M) subset [-delta,delta]` and one-sided `L1` error `1/delta`.
   Source already recorded in `docs/trackB/clv_pair.md`: Le--Vaaler, "Sums of
   products of fractional parts", Section 3.

3. `UNCONDITIONAL`: CLV Gaussian subordination framework as background for
   Beurling-Selberg extremal functions.  Source already recorded in
   `docs/trackB/clv_pair.md`: Carneiro--Littmann--Vaaler, "Gaussian
   subordination for the Beurling-Selberg extremal problem", Trans. AMS 365
   (2013), 3493-3534.

Forbidden inputs remain RH/GRH, Fourier-quasicrystal transfer, de Branges
positivity as an RH certificate, and RH-conditional prime-gap conclusions.

## Lower Tax

For every majorant

```text
M^+ >= 1_I
supp(hat M^+) subset [-delta,delta]
```

the Selberg/Vaaler extremal theorem gives the sharp one-sided excess

```text
int_R (M^+ - 1_I) dx >= 1/delta.
```

For every minorant

```text
M^- <= 1_I
supp(hat M^-) subset [-delta,delta]
```

it gives

```text
int_R (1_I - M^-) dx >= 1/delta.
```

Therefore any hard-edge majorant/minorant pair pays an uncertainty tax

```text
tau_CLV >= 1/delta.
```

If the cone receiver only allows

```text
delta <= B_K,
```

then

```text
tau_CLV >= 1/B_K.
```

This is not a removable numerical constant.  It is the cost of the hard edge
under the bandlimit.

## Window-Normalized Tax

Relative to the raw Lebesgue length of the window:

```text
tau_CLV / |I_K| >= 1/(2 K B_K).
```

If `B_K ~ K`, the Lebesgue-relative tax is at least `K^-2`.  This is the
friendliest normalization and is not the relevant prime-comb obstruction.

## Prime-Weighted Tax

The prime side in raw log coordinates has the rough density

```text
dmu_P(x) ~ e^(x/2) dx
```

on the edge window.  On `I_K=[2K,4K]`, the mass is dominated by the upper edge:

```text
int_[2K,4K] e^(x/2) dx ~ e^(2K).
```

A hard-edge smoothing layer of width `~1/delta` at the upper edge costs, in
prime weight,

```text
>= c * e^(2K) / delta
```

for an absolute model constant `c` depending only on the chosen edge-side
normalization.  After normalizing by the prime mass of the window, the naive
scalar-mask route pays

```text
normalized_CLV_tax >= c / delta >= c / B_K.
```

Thus if `B_K ~ K`, the best expected scale for the naive hard-edge CLV mask is

```text
epsilon_K^naive >= c / K.
```

## Gate

Before starting B2a, record the active `B_K` and the mu-ledger target.

```text
if mu_budget requires epsilon_K = o(1/B_K):
  B2a naive scalar majorant route is FATAL.

continue B2a only if:
  1. the mu-budget is compatible with >= c/B_K, or
  2. there is a named extra decay/cancellation theorem for the cone factor,
     not just ||g||_infty.

otherwise:
  skip B2a and continue with B2b or a structured non-scalar replacement.
```

The registered expectation `C*exp(-a*delta*K)/delta` is not a free consequence
of a hard interval Selberg/CLV majorant.  It requires additional named
structure such as analytic decay of the cone factor, explicit-formula
cancellation, genuine PSD zero-side control, or a smoothed edge that changes
the object.

## Route Verdicts

```text
PROVED:
  hard Selberg/Vaaler majorant/minorant of [2K,4K] pays >= 1/B_K after
  bandlimit delta <= B_K.

FATAL:
  B2a in the form "majorant times ||g||_infty" when the mu-ledger asks for
  epsilon_K = o(1/B_K).

OPEN:
  B2b explicit-formula / Hermitian-square route.  This preflight does not
  kill it because B2b preserves sign/cone/zero-side structure instead of
  replacing the defect by a scalar absolute-value mask.
```

## Impact On Current Track B

This preflight agrees with the S3 verdict in `docs/trackB/VERDICT_B2B.md`:
the live obstruction is not an arithmetic decomposition error.  The serious
route is B2b, and its current failure point is the zero-side PSD eligibility
slot for the smoothed receiver.

Next useful B2b question:

```text
Can we replace the naive smoothed zero-side proxy by a structure-preserving
object: signed PD decomposition, corrected cone projection, admissible lift,
or a receiver whose zero-side term is actually PSD on the Hermitian-square
cone?
```
