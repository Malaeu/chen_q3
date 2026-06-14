# Track B B2b: Non-Node Analytic Curvature Audit

Status: RP4/B2 diagnostic and proof-generator audit.  This is not a proof of
E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_nonnode_curvature_guard_audit.md`.  The
previous curvature guard still used a finite-difference sample for `S_v''`.
This audit replaces that layer by an analytic product-rule formula.

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

Receiver variables:

```text
z_left  = delta * (a - 2K),
z_right = delta * (a - 4K).
```

All intervals below are raw `a` intervals.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler's extremal-function construction.
  Source: https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/
- `UNCONDITIONAL`: polygamma functions and derivative identities.
  Source: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: elementary product rule and mean-value/Lipschitz transfer.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for Taylor/curvature/derivative-envelope certificates
again point to the same proof-generator style:

```text
grid values,
analytic derivative envelope,
mesh-cover lift.
```

External checks were limited to allowed sources: DLMF for polygamma
derivatives and standard mean-value/Lipschitz transfer.  No conditional
analytic number theory input was introduced.

## Analytic Formula Added

The smooth sign density is:

```text
S_v(a) = exp(-a/2) * (H_v'(a) - H_v(a)/2).
```

The first derivative was already analytic:

```text
S_v'(a) = exp(-a/2) * (H_v''(a) - H_v'(a) + H_v(a)/4).
```

The new analytic curvature formula is:

```text
S_v''(a) =
  exp(-a/2) *
    (H_v'''(a) - (3/2)H_v''(a) + (3/4)H_v'(a) - (1/8)H_v(a)).
```

For `H_v(a)=E_delta(a)F_v(a)`, the probe now computes:

```text
H_v''' =
  E_delta''' F_v
  + 3 E_delta'' F_v'
  + 3 E_delta' F_v''
  + E_delta F_v'''.
```

The packet profile third derivative uses the centered B-spline finite
difference identity:

```text
B_n'''(x) =
  B_{n-3}(x+3/2)
  - 3 B_{n-3}(x+1/2)
  + 3 B_{n-3}(x-1/2)
  - B_{n-3}(x-3/2).
```

The Vaaler receiver now has analytic third derivatives:

```text
K0'''(z) =
  -4*pi*sin(2*pi*z)/z^2
  -12*cos(2*pi*z)/z^3
  +18*sin(2*pi*z)/(pi*z^4)
  -12*(1-cos(2*pi*z))/(pi^2*z^5),
```

with a small-`z` Taylor fallback.

For `H0=A*B`, where

```text
A=(sin(pi*z)/pi)^2,
B=polygamma(1,1-z) - polygamma(1,1+z) + 2/z,
```

the third derivative uses:

```text
H0''' = A'''B + 3A''B' + 3A'B'' + AB'''.
```

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now reports:

```text
profile_third_derivative_source = analytic_centered_b_spline_third_derivative
receiver_derivative_source = analytic_vaaler_polygamma_derivative3
signed_density_curvature_source = analytic_product_rule
signed_density_curvature_fd_max_abs_error
profile_third_derivative_max_abs
receiver_third_derivative_max_abs
receiver_third_derivative_fd_max_abs_error
```

The finite-difference quantities are retained only as sanity diagnostics.

Micro sanity check away from Vaaler integer nodes:

```text
K0''' vs central-difference derivative of K0'': max error ~7.5e-9
H0''' vs central-difference derivative of H0'': max error ~4.2e-9
```

This is diagnostic only; it does not replace outward-rounded interval
enclosures.

## K=3.5 Analytic Curvature Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --interval-safety-factors 1 2 10 100 1000 2000 5000 10000 \
  --cells 58 59 61
```

Results:

```text
cell 58:
  non-node candidates: 1
  curvature source: analytic_product_rule
  signed_density_curvature_fd_max_abs_error: ~2.72e-6
  profile_third_derivative_max_abs: ~190.488
  receiver_third_derivative_max_abs: ~13.724
  curvature guard passes through factor 10000
  worst factor-10000 guard: ~0.067340

cell 59:
  non-node candidates: 1
  curvature source: analytic_product_rule
  signed_density_curvature_fd_max_abs_error: ~3.31e-6
  profile_third_derivative_max_abs: ~189.316
  receiver_third_derivative_max_abs: ~13.503
  curvature guard passes through factor 10000
  worst factor-10000 guard: ~0.128377

cell 61:
  non-node candidates: 0
  receiver_third_derivative_max_abs: ~2.2e5 on node-local sides
  signed_density_curvature_fd_max_abs_error: ~6.5e3
  remains node-local, not a non-node target.
```

Interpretation:

- The first non-node targets no longer depend on finite-difference curvature.
- Finite-difference sanity remains close for `S_v''` on cells `58,59`.
- The node-local cells show exactly why they must not be mixed into the
  non-node branch: third receiver derivatives and finite-difference errors
  explode near Vaaler integer nodes.

## K=3 Analytic Curvature Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 801 \
  --interval-safety-factors 1 2 10 100 1000 2000 5000 10000 \
  --cells 35 36 39
```

Results:

```text
cell 35:
  non-node candidates: 1
  signed_density_curvature_fd_max_abs_error: ~1.15e-6
  curvature guard passes through factor 10000

cell 36:
  non-node candidates: 1
  signed_density_curvature_fd_max_abs_error: ~1.22e-6
  curvature guard passes through factor 10000

cell 39:
  non-node candidates: 0
  receiver_third_derivative_max_abs: ~3.32e4
  remains root/node-local.
```

Interpretation:

- K=3 cells `35,36` remain easier non-node targets.
- K=3 cell `39` remains outside the non-node branch.

## Next Proof-Generator Contract

First theorem-producing target remains:

```text
K = 3.5,
cell = 58,
raw a interval = [6.645833333333817, 6.760416666667158],
worst pilot mesh interval =
  [6.645833333333817, 6.645976562500484].
```

The next generator no longer needs a finite-difference model for `S_v''`.
It should emit outward-rounded intervals for:

```text
E_delta, E_delta', E_delta'', E_delta'''
F_v, F_v', F_v'', F_v'''
S_v, S_v', S_v''
```

and prove the mesh guard:

```text
max_abs_S_prime_on_interval
  <= max(endpoint S_prime upper bounds)
     + upper_sup_abs_S_second_on_interval * mesh_width / 2

min(endpoint S lower bounds)
  > max_abs_S_prime_on_interval * mesh_width / 2.
```

## Verdict

`PARTIAL(analytic S_v'' product-rule route installed for non-node branch)`.

`GAP(outward-rounded intervals for receiver/profile derivatives still missing)`.

`FATAL(treating floating analytic product-rule values as interval enclosures)`.

Track B remains active.

Follow-up:

- `docs/trackB/b2b_nonnode_interval_atom_audit.md` fixes the first
  atom-level certificate scaffold for K=3.5 cell `58`, mesh interval `0`.
  It names the future interval atoms
  `E_delta^{(j)}`, `F_v^{(j)}`, `H_v^{(j)}`, and `S_v^{(j)}` and reproduces
  the factor-`10000` mesh guard.  It remains diagnostic because the current
  ranges are directed-rounded sampled ranges, not natural interval
  extensions of the formulas.

## Proshka Audit Block

Claim:
K=3.5 cell `58` now uses analytic product-rule `S_v''`, not finite-difference
curvature, and still passes curvature factors through `10000` with worst guard
about `0.067340`.

Point of blockage:
The analytic formulas are still evaluated in floating point.  We need
outward-rounded interval enclosures for the receiver/profile derivatives.

What was tried:
Added third derivative formulas for centered B-spline packet profiles,
Vaaler `K0`, Vaaler `H0`, and Selberg receiver `M^+`; reran K=3.5 and K=3
non-node/node-local probes.

Minimal example:
K=3.5 cell `58`, worst mesh interval
`[6.645833333333817, 6.645976562500484]`: analytic `S_v''` agrees with the
old finite-difference sanity check to about `2.72e-6` in max absolute error on
the segment; factor-10000 guard remains `~0.067340`.

Question for Proshka:
Should the first proof-producing interval generator enclose the analytic
third-derivative product formula directly, or split receiver/profile factors
into separately certified interval atoms first?
