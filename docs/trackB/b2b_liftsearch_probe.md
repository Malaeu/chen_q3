# Track B B2b: Finite Lift-Search Probe

Status: B2 numerical probe.  This is not a proof certificate and does not close
E5'.  It tests the admissible-lift lemma from
`docs/trackB/b2b_admissible_lift_audit.md` in the projected Step13 `G`
normalization.

## Question

Can a small positive-definite lift family operator-majorize the raw edge prime
matrix?

Finite target at `K=2`:

```text
N^T(P_lift - P_edge)N + eta * N^T G N >= 0.
```

If `eta <= 0`, the candidate family gives finite operator dominance.  If
`eta > 0`, the lift still needs extra slack.  This is only the prime-side
dominance test; a real B2b proof also needs the arch/continuum budget.

## D2 Normalization

Raw variable:

```text
a = r * log p,
edge = [4,8] = [2K,4K] at K=2.
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

The script reports raw-log coordinates and uses the same Step13 packet
parameters as the current edge sanity check:

```text
ell = 0.35,
grid delta = 0.5,
k_spline = 5.
```

## Candidate Family

The probe uses two-point Gaussian autocorrelation lifts:

```text
L_{c,s}(a)
  = 2*G_s(a) + G_s(a-c) + G_s(a+c),
G_s(a) = exp(-pi*(a/s)^2).
```

This is `UNCONDITIONAL` positive-definite as an autocorrelation of two equal
Gaussian packets separated by `c`.  It is a finite scalar proxy for an
admissible convolution-square lift; it is not yet a theorem-level Q3 Weil test.

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py liftsearch \
  --K 2 \
  --num-centers 9 \
  --widths 0.35 0.5 0.75 1.0 1.5 2.0 3.0 4.0 \
  --coeff-budget 10 \
  --coeff-bound 10 \
  --tol 1e-7 \
  --p0-na 1001
```

The script uses the compact B-spline support to replace the requested
`max_a=16` by the effective cutoff `max_a=8.200000000001`, because larger
prime-power shifts do not interact with the packet matrix.  This preserves the
D2 operator and removes zero matrix work.

## Results

Baseline edge-defect proxy:

```text
opnorm_G(Pnu_edge^circ) = 0.4416718760986585.
```

Dense lift dictionary:

```text
centers = 4.0, 4.5, ..., 8.0
widths  = 0.35, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0
basis_count = 72
prime_power_shifts_total = 547 after effective support cutoff
```

Tradeoff:

```text
coeff_budget=2:
  eta = 0.39980474606046074
  eig(P_lift-P_edge,G)_min = -0.3998059680059875
  opnorm_G(P0_lift-P0_edge) = 2.034795081100215

coeff_budget=5:
  eta = 0.10467630884157803
  eig(P_lift-P_edge,G)_min = -0.10470647147320755
  opnorm_G(P0_lift-P0_edge) = 4.183032849892227

coeff_budget=10:
  eta = 0.007718167761385715
  eig(P_lift-P_edge,G)_min = -0.007718217924791366
  opnorm_G(P0_lift-P0_edge) = 5.267566976647217
```

At budget `10`, the LP nearly majorizes the finite edge operator.  The dominant
coefficients are narrow lifts centered near the upper half of the edge:

```text
c=7.5, width=0.35, coeff=1.457760473825666
c=7.0, width=0.35, coeff=1.3753060600846854
c=6.5, width=0.35, coeff=1.3486697579264713
c=6.0, width=0.35, coeff=1.3389181787342161
```

## Joint Cost Optimization

The next check adds the continuum/arch proxy directly to the LP.  The script
introduces a second slack variable `gamma`:

```text
N^T(P_lift - P_edge)N + eta * N^T G N >= 0,
N^T(P0_lift - P0_edge)N <= gamma * N^T G N.
```

Here `gamma` is the one-sided upper arch/continuum cost.  This is closer to the
B2b admissible-lift theorem than the post-hoc opnorm report above.

Commands:

```bash
# Penalize cost in the objective:
.venv/bin/python scripts/trackb_edge_operator_probe.py liftsearch \
  --K 2 --num-centers 9 \
  --widths 0.35 0.5 0.75 1.0 1.5 2.0 3.0 4.0 \
  --coeff-budget 10 --coeff-bound 10 \
  --cost-weight 0.5 --tol 1e-5 --max-iter 80 --p0-na 1001

# Hard cap cost near the measured edge proxy:
.venv/bin/python scripts/trackb_edge_operator_probe.py liftsearch \
  --K 2 --num-centers 9 \
  --widths 0.35 0.5 0.75 1.0 1.5 2.0 3.0 4.0 \
  --coeff-budget 10 --coeff-bound 10 \
  --gamma-upper 0.4416718761 --tol 1e-5 --max-iter 80 --p0-na 1001
```

Joint tradeoff:

```text
unconstrained cost:
  eta   = 0.007718167761385715
  gamma = 5.267566976647217

cost_weight=0.5:
  eta   = 0.6424766217601645
  gamma = 0.9034628054063174

cost_weight=1.0:
  eta   = 0.6895262826836916
  gamma = 0.832622682317381

gamma <= 2.0:
  eta   = 0.3874752228956056
  gamma = 2.000000545056545

gamma <= 0.4416718761:
  eta   = 1.7101952677636467
  gamma = 0.44167531440670377
```

So this simple lift family cannot make both `eta` and `gamma` small in the
current `K=2` packet model.  It either nearly dominates the edge prime matrix
but pays a large arch cost, or it keeps the arch cost near the measured
edge-defect scale and loses prime dominance by order `1`.

## Interpretation

This is good news and bad news.

Good:

- The finite operator-dominance part of B2b is not obviously impossible.
- A structured positive-definite autocorrelation dictionary can drive `eta`
  down from order `1` to about `7.7e-3`.
- This is much sharper than the naive Gaussian pointwise majorant, which was
  violently indefinite.

Bad:

- The continuum/arch proxy cost grows to about `5.27` in `G`-opnorm.
- That is far larger than the measured edge fluctuation scale
  `0.4416718760986585`.
- So this lift family does not yet give an E5' bound.  It solves the wrong half
  of B2b unless the arch budget can be compressed.
- Joint optimization confirms the problem is structural for this simple
  scalar positive-definite lift dictionary: cost control and prime dominance
  pull in opposite directions.

## Current B2b Verdict

`FATAL(two-point Gaussian autocorrelation lift family)`.

Not fatal for Track B.  The route-level status remains:

```text
B2-GAP(cost-controlled admissible lift)
```

The wall has moved:

```text
old wall: find any cone-preserving operator lift.
new wall: find a lift with small arch/continuum cost.
```

Surviving next moves:

1. Try signed but still convolution-square eligible multi-packet lifts.  Scalar
   nonnegative coefficients are too expensive because self-correlation at
   zero creates large continuum cost.
2. Move to a direct `FINITE-OP` certificate for `P_edge-P0_edge`, using CLV only
   for tail/continuum control.
3. Ask Proshka for a cost-controlled admissible-lift theorem shape that avoids
   the zero self-correlation tax.

## Proshka Update

Claim:
A positive-definite two-point Gaussian autocorrelation dictionary can nearly
operator-majorize the `K=2` edge prime matrix, but the associated continuum
proxy cost is too large for the E5' ledger.  Joint cost optimization confirms
this is not just a post-hoc artifact.

Point of blockage:
Prime-side dominance wants many narrow autocorrelation peaks across the edge.
Those peaks carry self-correlation mass near zero, which inflates
`P0_lift-P0_edge`.

What was tried:
- Added `liftsearch` mode to `scripts/trackb_edge_operator_probe.py`.
- Used centers `4.0..8.0` and widths `0.35..4.0`.
- Solved the projected Loewner problem by a cutting-plane LP over worst
  eigenvectors.
- Scanned coefficient budgets `2`, `5`, and `10`.
- Added `gamma` constraints/objective for the one-sided continuum cost.

Minimal example:
`K=2`, raw edge `[4,8]`, Step13 packet parameters `ell=0.35`,
grid `delta=0.5`, `k_spline=5`, two-point Gaussian autocorrelation dictionary
with `72` basis functions.  Budget `10` gives `eta≈0.0077`, but
`gamma≈5.27`; forcing `gamma≈0.4417` raises `eta≈1.71`.
