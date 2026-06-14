# Track B B2: PSD Gaussian Majorant Probe

Status: FATAL for the naive Gaussian/PSD majorant.  Not fatal for Track B.

This note tests the simplest `PSD-CLV` idea after the ordinary Selberg pair
failed to transport through the Q3 cone.

## Candidate

Use the positive-definite Gaussian majorant

```text
W_K(x) = exp(4*pi) * exp(-pi * (x/(2K))^2).
```

For the raw-log edge strip `I_K=[2K,4K]`, and its reflection, this satisfies:

```text
W_K(x) >= 1       for 2K <= |x| <= 4K,
W_K(4K) = 1.
```

With the B1 Fourier convention

```text
hat(f)(u) = integral_R f(x) exp(-2*pi*i*u*x) dx,
```

the transform is

```text
hat(W_K)(u)
  = exp(4*pi) * (2K) * exp(-pi * (2K*u)^2) >= 0.
```

Source classification:

- `UNCONDITIONAL`: Gaussian self-duality under the Fourier transform.
- `UNCONDITIONAL`: positivity mechanism "nonnegative Fourier transform gives
  a positive-definite kernel"; this is the same structural condition used in
  Cohn--Elkies linear programming.
- Related local precedent: `D2g29e1` in
  `q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`
  uses `exp(4*pi) exp(-pi*t^2)` as a concrete positive-definite height
  majorant.

This is a PSD-friendly object, but the question is stricter: does it transport
the edge operator on the Q3 packet cone?

## D2 Normalization

Raw-log variable:

```text
a = r * log p
I_K = [2K,4K]
weight = log(p) / p^(r/2)
```

Q3 formal variable:

```text
xi_n = log n / (2*pi)
w_Q(n) = 2 * Lambda(n) / sqrt(n)
```

The Gaussian above is in raw-log coordinates.  In `xi` coordinates its scale is
divided by `2*pi`.

## Fourier Error Test

Let

```text
chi_sym = chi_[2K,4K] + chi_[-4K,-2K],
E_K = W_K - chi_sym.
```

For operator transport against arbitrary positive-definite/autocorrelation
tests, it is not enough that `W_K >= chi_sym` and `hat(W_K) >= 0`.  We would
need the error `E_K` to be positive definite, i.e. `hat(E_K) >= 0`, or some
weaker statement on the actual packet spectrum.

For `K=2`, numerical sampling gives:

```text
hat(E_K) first negative near u = 0.625089,
hat(E_K) minimum near u = 0.661348,
min hat(E_K) = -0.8462943231504024.
```

So the Gaussian majorant error is not Fourier-positive.

## Finite Packet Operator Test

The decisive D2 test is the actual Step13 packet operator order.

Define:

```text
P_W    = prime-shift matrix weighted by W_K(a),
P_edge = prime-shift matrix weighted by chi_[2K,4K](a),
E_P    = P_W - P_edge.
```

If the naive Gaussian route were valid on the finite packet, the projected
matrix

```text
N^T E_P N
```

would be positive semidefinite relative to the packet Gram matrix `G`.

Using the Step13 B-spline pilot (`ell=0.35`, grid `delta=0.5`,
`k_spline=5`) gives:

```text
K=1:
  total_shifts = 465
  edge_shifts  = 19
  max_a        = 8
  W_K(0)       = 2.867513131367e+05
  W_K(4K)      = 1
  eig_G(N^T(P_W-P_edge)N) min = -8.388894479312e+04
  eig_G(N^T(P_W-P_edge)N) max =  6.455596143406e+03

K=2:
  total_shifts = 595877
  edge_shifts  = 441
  max_a        = 16
  W_K(0)       = 2.867513131367e+05
  W_K(4K)      = 1
  eig_G(N^T(P_W-P_edge)N) min = -3.477462109260e+05
  eig_G(N^T(P_W-P_edge)N) max =  2.587302870166e+05
```

The projected error is violently indefinite.  Thus:

```text
W_K >= chi_edge and hat(W_K) >= 0
```

does not imply the needed finite packet operator inequality.

## Reason For Failure

The edge defect is not a scalar count against a pointwise nonnegative test.
It is a shifted autocorrelation operator:

```text
sum_a measure(a) * [r((d-a)/ell) + r((d+a)/ell)].
```

The shift kernel carries oscillatory Fourier factors `cos(2*pi*u*a)`.  A
positive scalar weight in `a` does not remove this oscillation.  Therefore
pointwise majorization in the shift variable does not imply Loewner
majorization of the packet matrix.

This is the same structural trap as the rejected positive/negative split: it
drops the Hermitian-square operator geometry.

## Verdict

`FATAL(naive Gaussian PSD majorant)`.

What is killed:

```text
pointwise edge majorant + positive Fourier transform of the majorant
```

What survives:

1. `PSD-CLV` with a stronger requirement:

   ```text
   hat(M - chi_edge) >= 0
   ```

   on the actual packet spectrum, not merely `hat(M)>=0`.

2. `FINITE-OP`: prove the projected operator inequality directly.

3. A genuine explicit-formula receiver in which the zero-side PSD appears
   before the prime-shift oscillation is converted into this finite matrix.

## Proshka Update

Claim:
The obvious positive-definite Gaussian majorant
`exp(4*pi) exp(-pi*(x/(2K))^2)` is not enough for E5p edge-defect transport.

Point of blockage:
It is pointwise above the edge and has positive Fourier transform, but
`W_K-chi_edge` is not positive definite, and the projected Step13 packet matrix
`N^T(P_W-P_edge)N` has large negative generalized eigenvalues.

What was tried:
- Checked the Fourier error for `K=2`; it becomes negative near `u=0.625089`.
- Built the Step13 projected packet matrix for `K=1` and `K=2`.
- Found `eig_G` minima `-8.39e4` and `-3.48e5`, respectively.

Minimal example:
`K=2`, raw edge `[4,8]`, `W_2(x)=exp(4*pi)exp(-pi*(x/4)^2)`,
Step13 packet parameters `ell=0.35`, grid `delta=0.5`, `k_spline=5`.
The candidate majorant is scalar-correct but operator-wrong.

Reproducibility:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py gaussian --K 1
.venv/bin/python scripts/trackb_edge_operator_probe.py gaussian --K 2
```

The `K=2` run enumerates prime-power shifts up to `max_a=16` and is much
heavier than `K=1`.  These runs are D2 numerical probes only; they do not
interval-certify matrix entries and do not close E5p.
