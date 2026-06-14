# Track B Mollifier S5.1 Revival Check

Status: GAP(no inverse expansion found in current Track B inputs).  This is
strategy/diagnostic documentation only: no Lean proof, no Q3.Main change, no
route mutation, and no RH-conditional input.

Atlas source:

```text
028 Conrey-Ghosh mollifier
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/028-conrey-ghosh-mollifier.md
```

Unconditional input: the mollifier method is UNCONDITIONAL only when the
required inverse expansion and first/second moment asymptotics are available.
Those moment inputs are the real cost.  This document checks whether Track B
currently has them.

## Why S5.1 Died

S5.1 tried to rescue the failed lift by treating the negative Fourier part as a
small signed ledger.  The measured negative mass was not small:

| K | object | negative/L1 | q3-weighted negative/L1 |
| --- | --- | ---: | ---: |
| 2 | `L=Mplus*F_v` | `0.499632` | `0.499667` |
| 3 | `L=Mplus*F_v` | `0.500130` | `0.500830` |
| 3.5 | `L=Mplus*F_v` | `0.500021` | `0.500286` |
| 2 | `E=(Mplus-1_edge)*F_v` | `0.508842` | `0.522080` |
| 3 | `E=(Mplus-1_edge)*F_v` | `0.494477` | `0.486656` |
| 3.5 | `E=(Mplus-1_edge)*F_v` | `0.506019` | `0.513305` |

This kills the "small negative part" route for the current family:

```text
S5_NEGMASS_BUDGET_SIZED
```

The Cauchy-Schwarz ratio collapses because roughly half the sampled spectral
L1 mass is on the wrong side.

## Candidate K-Mollifier

The Conrey-Ghosh style move would no longer ask for a uniform per-cell repair.
Instead, choose a finite K-mollifier:

```text
M_K(a) = 1 + sum_{m in W_K} c_m I_{K,m}(a)
```

where:

```text
I_{K,m}(a) = 1_[2K,4K](a - log m) - beta_{K,m}
W_K       = finite edge-shift set from the current prime-power / packet grid
c_m       = coefficients optimized against an inverse expansion of the margin
beta      = centering term so the family average is normalized
```

The desired averaged quantity would be:

```text
Margin_K(a) * |M_K(a)|^2.
```

This deliberately changes the deliverable:

```text
old target: Gate(K) uniformly for every K-cell
new target: Gate(K) for a positive-proportion K-family, ideally density -> 1
```

That shift is mathematically meaningful but it is also a route mutation in
strength.  It can only be accepted by the route owner if the second-moment
input is real.

## Required Second Moment

The mollifier card requires:

```text
family measure dK
explicit inverse expansion of 1 / Margin_K in K-cell coefficients
first moment asymptotic for Margin_K * |M_K|^2
second moment asymptotic with off-diagonal control
bounded ratio:
  E[Margin_K * |M_K|^2]^2 / E[|Margin_K * |M_K|^2|^2] > c > 0
```

If this holds, Cauchy-Schwarz gives a positive proportion of K-cells where the
E5p budget remains open.

## Feasibility Check

Local evidence search:

```bash
rg -n "inverse Dirichlet|Dirichlet expansion|mollifier|second moment|second-moment|edge-defect indicator|mu_budget|LP-gap|LP gap" \
  docs/trackB q3.lean.aristotle scripts docs/RH_TRICK_ATLAS.md
```

Result:

```text
No Track B inverse Dirichlet expansion of the margin was found.
No Track B first/second moment formula for K-cell margins was found.
Existing hits are:
  - S5/S5C0 price and mu-budget diagnostics,
  - generic historical/literature uses of "mollifier" and "second moment",
  - the handoff file requesting this check.
```

Therefore the current repository inputs do not satisfy card 028's
`must_survive` condition.

## Verdict

```text
MOLLIFIER_S51_REVIVAL_GAP_NO_INVERSE_EXPANSION
```

Meaning:

```text
The finite M_K ansatz can be written down.
The required inverse expansion and off-diagonal second moment are absent.
So the mollifier currently collapses to an uncontrolled noise rescale.
```

This does not refute all future mollifier ideas.  It refutes using the
Conrey-Ghosh card as a present Track B rescue without first building the missing
K-family moment theory.

## Status Dictionary

```text
PROVED: none
SKETCH: finite K-mollifier ansatz
OPEN: K-family measure, inverse expansion, first/second moment asymptotics
REFUTED: immediate S5.1 revival from current local inputs
ZERO_CONSISTENT: S5.1 negative-mass measurement remains the reason for death
GAP: off-diagonal second-moment control for the Track B margin family
```
