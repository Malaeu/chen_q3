# Track B B2b: Analytic Selberg Receiver Derivatives

Status: RP4/B2 diagnostic and proof-generator refinement.  This is not a
proof of E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_profile_derivative_enclosure.md`.  The
packet-profile derivatives were already made analytic.  This note removes the
next sampling layer: `clvsigncert` now computes the Selberg/Vaaler receiver
derivatives analytically from the `H0/K0` formulas.

## D2 Normalization

Raw variable:

```text
a = r * log p,
x = exp(a),
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

Smooth correction:

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a),
H_v(a) = E_delta(a) F_v(a),
phi_v(x) = x^(-1/2)H_v(log x).
```

On every smooth segment not crossing `2K` or `4K`, the indicator term is
constant, so:

```text
E_delta'  = (M^+)'
E_delta'' = (M^+)''
```

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler/Selberg sign-function construction as a standard
  Beurling--Selberg formula.
  Reference used for this audit:
  https://www.math.ntnu.no/emner/MA3001/2020v/2021v/class11_zeta_NTNU.pdf
- `UNCONDITIONAL`: polygamma functions are derivatives of the digamma/log
  gamma function.
  Reference: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary Stieltjes/BV bookkeeping.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Analytic Receiver Formulas

The probe already used:

```text
K0(z) = sinc(z)^2
H0(z) = A(z) B(z)
A(z) = (sin(pi z)/pi)^2
B(z) = psi1(1-z) - psi1(1+z) + 2/z
```

where `psi1` is trigamma.  The new derivative helpers use:

```text
A'(z)  = sin(2*pi*z)/pi
A''(z) = 2*cos(2*pi*z)

B'(z)  = -psi2(1-z) - psi2(1+z) - 2/z^2
B''(z) =  psi3(1-z) - psi3(1+z) + 4/z^3

H0'(z)  = A'(z)B(z) + A(z)B'(z)
H0''(z) = A''(z)B(z) + 2A'(z)B'(z) + A(z)B''(z)
```

`K0'` and `K0''` are computed directly from `sinc(z)^2`, with a small-`z`
series branch for stability.

For the interval majorant:

```text
M^+(a) = 1/2 H0(delta(a-2K))
       - 1/2 H0(delta(a-4K))
       + 1/2 K0(delta(a-2K))
       + 1/2 K0(delta(a-4K)).
```

The first derivative gains one factor `delta`; the second gains `delta^2`.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now emits:

```text
receiver_derivative_source = analytic_vaaler_polygamma_derivative
receiver_derivative_fd_max_abs_error
receiver_second_derivative_fd_max_abs_error
```

The finite-difference errors are sanity diagnostics only.  They are not used
as proof inputs.

## K=3.5 Worklist

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 1601 --cells 58 59 61
```

Results:

```text
cell 58:
  recommendation: smooth_sign_cert_candidate
  receiver derivative source: analytic_vaaler_polygamma_derivative
  sampled sign guard: ~0.067408
  receiver derivative FD error: ~2.31e-8
  receiver second-derivative FD error: ~7.25e-4

cell 59:
  recommendation: smooth_sign_cert_candidate
  receiver derivative source: analytic_vaaler_polygamma_derivative
  sampled sign guard: ~0.128763
  receiver derivative FD error: ~2.32e-8
  receiver second-derivative FD error: ~7.27e-4

cell 61:
  recommendation: smooth_sign_cert_plus_explicit_jump_cert
  smooth side guards: ~0.022024 and ~0.007154
  receiver derivative FD errors: ~9.22e-6 and ~1.23e-6
  receiver second-derivative FD errors: ~1.789 and ~0.198
```

Interpretation:

- The receiver derivative is now analytic, and the previous cell
  classification survives.
- The largest finite-difference disagreement appears exactly where expected:
  near the edge split close to Vaaler interpolation nodes.  This is a
  numerical sanity warning, not a proof failure.
- Cell `61` remains the tightest first target because the right smooth side
  guard is only about `0.007154`.

## K=3 Worklist

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 1601 --cells 35 36 39
```

Results:

```text
cell 35:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.058968
  receiver derivative FD error: ~4.90e-9
  receiver second-derivative FD error: ~1.18e-4

cell 36:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.048085
  receiver derivative FD error: ~4.92e-9
  receiver second-derivative FD error: ~1.18e-4

cell 39:
  recommendation: isolate_roots_then_sign_certify
  root bracket: [5.995196059570327, 5.995289794921890]
  receiver derivative FD error: ~8.15e-7
  receiver second-derivative FD error: ~0.108781
```

Interpretation:

- K=3 cells `35,36` stay smooth sign candidates.
- K=3 cell `39` still has one root bracket before the edge jump.  The root is
  stable after both packet and receiver derivative rewrites.

## Refined Generator Contract

The analytic formula stack is now:

```text
F_v, F_v', F_v'':
  centered B-spline formulas.

E_delta, E_delta', E_delta'':
  Vaaler H0/K0 + polygamma formulas on smooth pieces.

S(a), S'(a):
  product-rule combination.
```

The remaining proof-generator requirement is intervalization:

```text
1. split at 2K/4K and at Vaaler interpolation nodes near the segment;
2. enclose H0/H0'/H0'' and K0/K0'/K0'' on each smooth interval;
3. combine with packet polynomial/B-spline enclosures;
4. prove S keeps a sign, or isolate a root and split.
```

Preferred next experiment:

```text
Build an interval-node audit for K=3.5 cell 61, measuring distance to Vaaler
integer nodes and the local cancellation pressure for H0/H0'/H0''.
```

Follow-up:

- `docs/trackB/b2b_vaaler_node_audit.md` implements this experiment.  It
  splits the remaining interval work into a non-node branch (`K=3.5` cells
  `58,59`) and a node-local branch (`K=3.5` cell `61`, then `K=3` cell `39`).

## Verdict

`PARTIAL(receiver derivative sampling removed)`.

`GAP(interval enclosures near Vaaler interpolation nodes still missing)`.

`FATAL(treating analytic floating-point polygamma values as proof intervals)`.

Track B remains active.

## Proshka Audit Block

Claim:
The selected `V_J` worklist now uses analytic formulas for both packet
derivatives and Selberg/Vaaler receiver derivatives.  The remaining missing
object is interval enclosure near Vaaler interpolation nodes, especially for
the edge-adjacent smooth sides.

Point of blockage:
The analytic polygamma values are floating-point evaluations.  Near integer
Vaaler nodes, cancellation in `H0/H0'/H0''` makes finite-difference sanity
checks noisy, so a proof-grade interval enclosure must split and bound those
terms explicitly.

What was tried:
Added analytic `K0`, `K0'`, `K0''`, `H0`, `H0'`, `H0''`, and
`M^+`, `(M^+)'`, `(M^+)''` helpers; reran K=3 and K=3.5 worklists.

Minimal example:
At K=3.5 cell `61`, the right smooth side remains sign-stable with guard
`~0.007154`, but it is close to the Vaaler nodes at `z=0` and `z=-7`; this is
where the receiver interval enclosure must be tight first.

Question for Proshka:
Should the first interval proof split around every nearby Vaaler integer node
and use local Taylor/series bounds for `H0`, or should it use the polygamma
product formula directly with outward-rounded interval arithmetic?
