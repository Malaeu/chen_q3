# Track B Selberg Route B Repair

Status: REFUTED(Route B not undied by Selberg alone) plus SKETCH(edge constant
made exact).  This is strategy/diagnostic documentation only: no Lean proof, no
Q3.Main change, no route mutation, and no RH-conditional input.

Atlas source:

```text
009 Selberg extremal functions
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/009-selberg-extremals.md
```

Unconditional input: Beurling-Selberg / Selberg extremal majorants and
minorants are UNCONDITIONAL classical Fourier analysis.

## Current Route B Status

From the price table:

```text
Route B:
  Clip spectrum: hat(L_proj)=max(hat(L),0).
  PSD is repaired, but edge-control/projection-loss likely budget-sized.
  Do not run unless exact projection-loss budget is supplied.
```

The key correction from S5.1 remains important:

```text
clipping does repair Fourier-side PSD if the projected object is regular enough
```

The failure is not "clipping cannot be PSD."  The failure is that the clipped
object no longer has proved physical edge control inside the `mu` budget.

## Selberg Sign Direction

The edge defect to control is a positive prime-weighted sum over the hard edge:

```text
prime_edge(g) = sum_{log n in [2K,4K]} Lambda(n)/sqrt(n) * g(log n).
```

For an upper control with positive prime weights, the scalar Selberg direction
is:

```text
M^+ >= 1_[2K,4K]
```

The minorant `M^- <= 1_[2K,4K]` has the wrong direction for an upper defect
bound.  It can lower-bound the edge but cannot certify the E5p upper budget.

This sign is checked against the explicit-formula bookkeeping by S3:

```text
prime_edge = arch - zero_PSD + boundary
```

with closure errors at sampled K:

| K | S3 max relative closure error |
| --- | ---: |
| 2 | `9.93e-17` |
| 3 | `3.47e-16` |

So the Selberg majorant direction is the scalar direction compatible with the
prime slot.  It is not, by itself, a cone-preserving operator inequality.

## Sharp Edge Constant

For bandwidth `B_K`, the Selberg hard-edge surplus is:

```text
int (M^+ - 1_[2K,4K]) dx = 1 / B_K.
```

In the current C0 run:

```text
B_K = 1
ordinary Selberg tax = 1
```

The PSD-first finite LP tax from S5C0 is larger:

| K | ordinary Selberg tax | PSD hard-edge tax | recovered scalar margin vs PSD tax |
| --- | ---: | ---: | ---: |
| 2 | `1.00000` | `2.93072` | `1.93072` |
| 3 | `1.00000` | `3.50596` | `2.50596` |
| 3.5 | `1.00000` | `3.96288` | `2.96288` |

Interpretation:

```text
Selberg repairs the edge constant.
Selberg does not repair the PSD/cone transport.
```

The recovered scalar margin is real, but it is gained by using the ordinary
majorant rather than a PSD-first admissible lift.

## Symmetry Caveat

Card 009 warns that Selberg extremals can drop symmetry/sign structure.  In
Track B that danger has already appeared numerically:

| object | K=2 min hat | K=3 min hat | K=3.5 min hat | source |
| --- | ---: | ---: | ---: | --- |
| `L=Mplus*F_v` | `-1.68036` | `-2.67972` | `-2.44648` | S4 eligibility |
| `E=(Mplus-1_edge)*F_v` | `-0.412284` | `-0.449693` | `-0.459538` | S4 eligibility |

Those are order-one sampled Fourier negatives.  They are not rounding noise and
they are not small signed ledgers: S5.1 measured negative/L1 around `0.5`.

Therefore Selberg's exact hard-edge constant is not enough to undie Route B.
The route still needs one of:

```text
1. a PSD-preserving Selberg-compatible lift,
2. an LP dual witness that absorbs the Selberg edge constant,
3. a proof-grade projection-loss budget after clipping.
```

None of those is supplied by card 009 alone.

## Verdict

```text
SELBERG_REPAIR_NO_UNDIE_ROUTE_B
```

Evidence:

```text
sign direction: majorant M^+ is correct for upper prime-edge control
edge constant: exact ordinary surplus 1/B_K, equal to 1 in current run
failure: PSD/cone eligibility remains broken for the current lifted family
```

Route B should stay deferred/negative in the price table.  Selberg remains
useful as an exact scalar ingredient inside the LP dual route, not as a
standalone resurrection of spectral clipping.

## Status Dictionary

```text
PROVED: none
SKETCH: Selberg sign direction and exact scalar edge constant
OPEN: PSD-preserving Selberg-compatible lift or projection-loss budget
REFUTED: claim that ordinary Selberg majorant alone undies Route B
ZERO_CONSISTENT: S3 closure still supports the prime-slot sign convention
GAP: operator/cone transport from scalar majorant to Hermitian-square cone
```
