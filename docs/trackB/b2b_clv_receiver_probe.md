# Track B B2b: Selberg-CLV Receiver Probe

Status: B2 diagnostic.  This is not a proof certificate and does not close
E5p.  It tests the next viable branch after the generic Hilbert spacing
barrier:

```text
replace hard edge 1_[2K,4K] by Selberg-Vaaler receivers M^+ / M^-
  -> apply explicit-formula-style prime/continuum comparison to the receiver
  -> check whether the smoothed residual is small enough for B3
  -> separately test whether the hard edge can be bridged to the receiver
     on the corrected cross-correlation cone.
```

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

The receiver in this probe is applied in raw `a = r log p` coordinates.  No
extra Q3 evenization factor is inserted into the raw Step13 prime weights.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler interval majorant/minorant from
  `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: Vaaler `H0,K0` construction, Le--Vaaler interval-function
  restatement, and CLV Gaussian subordination framework.
  Sources:
  - https://arxiv.org/abs/1309.1506
  - https://home.olemiss.edu/~leth/papers/fractional_parts.pdf
  - https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL / finite-dimensional linear algebra`: each fixed packet
  model gives generalized eigenvalue diagnostics on the projected `kerQ`
  subspace.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvrecv \
  --K 2 --ell 0.75 --grid-delta 0.5 \
  --receiver-delta 0.25 0.5 1.0 2.0 \
  --p0-na 801 --receiver-grid-nt 4001
```

The mode builds the raw Selberg receivers

```text
M^+_{I_K,delta}, M^-_{I_K,delta}
```

from the explicit B1 `H0,K0` formulas.  The implementation evaluates `H0`
through the equivalent trigamma form of Vaaler's defining series and fills the
removable values `H0(n)=sgn(n)` at integers.

For each receiver it reports:

```text
hard_edge_minus_continuum:
  P(1_I) - P0(1_I)

Mplus_minus_Mplus_continuum:
  P(M^+) - P0(M^+)

prime_Mplus_minus_edge:
  P(M^+) - P(1_I)

continuum_Mplus_minus_edge:
  P0(M^+) - P0(1_I)
```

All eigens are generalized against the projected Gram metric `G` on `kerQ`.

Important: `M^+ >= 1_I` is a scalar inequality.  It does **not** automatically
imply

```text
P(M^+) >= P(1_I)
```

on the cross-correlation cone.  The probe explicitly checks this missing
operator bridge instead of assuming it.

## Formula Sanity

For every run below, the sampled grid sanity check has

```text
min(M^+ - chi_I) >= 0,
min(chi_I - M^-) >= 0.
```

The finite grid integral approximates the exact one-sided `L1` error
`1/delta`.  The small deficit is truncation from integrating only a finite
margin around the edge interval.

Example for K=2, delta=1:

```text
expected L1 error = 1
grid trapz(M^+ - chi_I) ~= 0.9894
grid trapz(chi_I - M^-) ~= 0.9895
```

So the implementation is consistent with the B1 Selberg pair at the numerical
level needed for this diagnostic.

## Stable Packet Results

The packet choices are the stability-filtered candidates from
`docs/trackB/b2b_stability_schedule.md`.

### K=2, ell=0.75

```text
hard edge epsilon ~= 0.10143

delta=0.25: smooth M+ epsilon ~= 0.00798, prime bridge min ~= -4.1267
delta=0.50: smooth M+ epsilon ~= 0.00517, prime bridge min ~= -3.5211
delta=1.00: smooth M+ epsilon ~= 0.01026, prime bridge min ~= -2.3539
delta=2.00: smooth M+ epsilon ~= 0.08826, prime bridge min ~= -1.5087
```

### K=2.5, ell=1.375

```text
hard edge epsilon ~= 0.41938

delta=0.25: smooth M+ epsilon ~= 0.02425, prime bridge min ~= -6.1316
delta=0.50: smooth M+ epsilon ~= 0.01028, prime bridge min ~= -5.0016
delta=1.00: smooth M+ epsilon ~= 0.00197, prime bridge min ~= -3.4773
delta=2.00: smooth M+ epsilon ~= 0.05955, prime bridge min ~= -2.0203
```

### K=3, ell=0.75

```text
hard edge epsilon ~= 0.10964

delta=0.25: smooth M+ epsilon ~= 0.03781, prime bridge min ~= -13.8568
delta=0.50: smooth M+ epsilon ~= 0.00661, prime bridge min ~= -10.9901
delta=1.00: smooth M+ epsilon ~= 0.00951, prime bridge min ~= -7.5311
delta=2.00: smooth M+ epsilon ~= 0.09192, prime bridge min ~= -4.3891
```

### K=3.5, ell=1.375

```text
hard edge epsilon ~= 0.23849

delta=0.25: smooth M+ epsilon ~= 0.02622, prime bridge min ~= -20.3760
delta=0.50: smooth M+ epsilon ~= 0.00516, prime bridge min ~= -18.6559
delta=1.00: smooth M+ epsilon ~= 0.00101, prime bridge min ~= -12.5165
delta=2.00: smooth M+ epsilon ~= 0.06505, prime bridge min ~= -7.3347
```

## Interpretation

The good news:

```text
P(M^+) - P0(M^+)
```

is often far smaller than the hard edge residual.  At K=3.5, delta=1, the
smoothed receiver epsilon is about `0.00101` versus hard-edge epsilon
`0.23849`.

This means the CLV receiver is not a dead end.  It is doing the expected
Fourier-smoothing job.

The bad news:

```text
P(M^+) - P(1_I)
```

is not positive on the projected cross-correlation cone.  The most negative
generalized eigenvalue is large in magnitude and worsens with K in these
stable packets.  Thus the scalar majorant inequality

```text
M^+(a) >= 1_I(a)
```

does not provide the missing operator bridge.

This is exactly the B2 cone-transport trap in a sharper form:

```text
scalar majorant works pointwise on shifts
  but the shifted packet matrices are not ordered shift-by-shift
  on the corrected cross-correlation cone.
```

## Verdict

`PARTIAL(CLV receiver gives small smoothed residual)`.

`GAP(hard-edge-to-CLV-receiver operator bridge is missing)`.

This keeps B2b alive but changes the theorem target.  We should not try to
prove E5p by scalar majorization of the edge indicator.  The next theorem must
be one of:

1. A Hermitian-square explicit-formula identity where the hard edge is never
   separately majorized; the receiver is the test object from the start.
2. A structured operator bridge:

```text
P(1_I) <= P(M^+) + R_K * G
```

with `R_K <= C*K^(-c)`.

3. A signed receiver / correction term that cancels the negative bridge modes
   while preserving explicit-formula eligibility.

## Proshka Audit Block

Claim:
Selberg-CLV receivers dramatically reduce the smoothed prime-continuum
residual on the stable packet models, but scalar interval majorization does
not transport to Loewner dominance on the corrected cross-correlation cone.

Point of blockage:
`P(M^+) - P(1_I)` has large negative generalized eigenvalues.  Therefore
`M^+ >= 1_I` cannot be used as the B2 cone bridge.

What was tried:
- Implemented exact Selberg `M^+`/`M^-` receiver values from the B1 `H0,K0`
  formulas.
- Verified sampled grid inequalities `M^- <= chi_I <= M^+` and approximate
  `L1` errors.
- Ran stable packet probes for K=2, 2.5, 3, 3.5 and
  `delta in {0.25,0.5,1,2}`.

Minimal example:
At K=3.5, `ell=1.375`, `grid_delta=0.5`, `delta=1`:

```text
hard edge epsilon ~= 0.23849
smoothed M+ epsilon ~= 0.00101
min eig(P(M+) - P(edge)) ~= -12.5165
```

Question for Proshka:
Can the explicit-formula/Hermitian-square route use `M^+` as the primary test
object without needing `P(M^+) >= P(edge)`, or do we need a structured
operator bridge/correction term for the hard edge?
