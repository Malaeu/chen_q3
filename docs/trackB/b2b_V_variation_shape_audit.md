# Track B B2b: `V_J` Variation Shape Audit

Status: RP4/B2 diagnostic and proof-contract refinement.  This is not a proof
of E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_finite_U_staircase_audit.md`.  The `U_J`
side of the Stieltjes ledger now has a finite Chebyshev-staircase theorem
shape.  The remaining live object is:

```text
V_J >= integral_J exp(-a/2) |H_v'(a) - H_v(a)/2| da,
```

plus explicit jump terms at `a=2K` and `a=4K`.

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

In raw `a` coordinates:

```text
d phi_v / dx = x^(-3/2) * (H_v'(a) - H_v(a)/2),
dx = exp(a) da,
|d phi_v| contribution = exp(-a/2)|H_v'(a)-H_v(a)/2| da.
```

This is the `V_J` density used by `clvledger`.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: exact finite Chebyshev staircase for `U_J`, recorded in
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: standard bounded-variation / absolutely-continuous fact:
  for absolutely continuous `phi`, total variation is bounded by the integral
  of `|phi'|`.  This is a proof-engine input, not an RH input.
- `UNCONDITIONAL / finite-dimensional linear algebra`: packet eigenvectors
  and finite B-spline profiles in the Step13 model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for variation envelopes, derivative sign partitions,
and B-spline derivative certificates returned:

- `FloorCert.Lipschitz_2219`, i.e. grid plus Lipschitz/envelope pattern;
- PrimeCert and heat certificate notes that already use finite interval
  envelopes and theorem-producing generator plans;
- `prime_norm_leq_rho` monotonicity remarks, showing the repo already accepts
  derivative-sign arguments when they are made explicit.

External search only confirms standard BV/Riemann--Stieltjes facts:

- bounded variation is the right language for Stieltjes integration;
- for differentiable/absolutely continuous functions, variation is controlled
  by the integral of the absolute derivative.

No conditional number-theory input is added.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvledger` now reports, for each cell:

```text
continuous_variation_x
jump_variation_x
sampled_phi_derivative_min
sampled_phi_derivative_max
sampled_phi_derivative_max_abs
sampled_phi_derivative_peak_a
sampled_phi_derivative_sign_changes
```

and, for each direction:

```text
continuous_variation_x_sum
jump_variation_x_sum
sampled_phi_derivative_sign_changes_total
sampled_phi_derivative_sign_change_cell_count
top_cells_by_continuous_variation
top_cells_by_phi_derivative_sign_changes
```

`clvmesh` carries the direction-level variation fields to track mesh stability.

These fields are diagnostic.  Sign changes are sampled, not certified.  Their
purpose is to identify the finite subintervals where a future interval
arithmetic or closed-form monotonicity proof must work.

## K = 3 Result

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3 --ell 0.75 --schedule fixed \
  --receiver-delta 0.5 \
  --p0-na 201 --quad-na 4001 \
  --ledger-cells 80 --top-cells 5
```

Summary:

```text
finite-U global bound / |residual|      ~= 2.98465
continuous variation sum                ~= 0.127925
jump variation sum                      ~= 0.049769
sampled sign-change cells               = 16
sampled sign changes total              = 16
```

Top continuous-variation cells:

```text
cell 39: [5.850, 6.000], left_edge_jump
  continuous V ~= 0.040003
  sampled sign changes = 1

cell 35: [5.250, 5.400]
  continuous V ~= 0.009096
  sampled sign changes = 0

cell 36: [5.400, 5.550]
  continuous V ~= 0.007912
  sampled sign changes = 0
```

Mesh check:

```text
quad_na   continuous V   jump V      sign changes   finite-U/residual
2001      0.126036       0.049769    16             1.78680
4001      0.127925       0.049769    16             2.98465
8001      0.128868       0.049769    16             4.43210
```

Interpretation: the K=3 `V_J` work is sharply concentrated in the same
left-endpoint shoulder.  The sampled sign pattern is stable across mesh
refinement at this diagnostic level.

## K = 3.5 Result

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 \
  --p0-na 401 --quad-na 4001 \
  --ledger-cells 120 --top-cells 5
```

Summary:

```text
finite-U global bound / |residual|      ~= 4.81151
continuous variation sum                ~= 0.104734
jump variation sum                      ~= 0.030132
sampled sign-change cells               = 41
sampled sign changes total              = 46
```

Top continuous-variation cells:

```text
cell 61: [6.990, 7.104], left_edge_jump
  continuous V ~= 0.032039
  sampled sign changes = 2

cell 59: [6.760, 6.875]
  continuous V ~= 0.015511
  sampled sign changes = 0

cell 58: [6.646, 6.760]
  continuous V ~= 0.011678
  sampled sign changes = 0
```

Interpretation: K=3.5 is also endpoint-shoulder dominated, but has more
sampled sign-change cells.  The highest-priority cells remain `58,59,61`.

## Candidate `V_J` Certificate Shape

The next theorem-producing generator should emit, for every selected raw-`a`
cell:

```text
cell J=[alpha,beta],
finite U_J certificate,
subpartition alpha = t_0 < ... < t_m = beta,
sign certificate for H_v'(a)-H_v(a)/2 on each subinterval,
endpoint or interval bound for phi_v on each subinterval,
integral/variation bound V_J,
jump term if J contains 2K or 4K.
```

Two possible routes:

1. **Interval arithmetic route.**  Directly enclose
   `exp(-a/2)|H_v'(a)-H_v(a)/2|` on subcells and integrate the enclosure.
2. **Sign-partition route.**  Certify zeros/signs of
   `H_v'(a)-H_v(a)/2`; then total variation over sign-stable pieces is the
   finite endpoint variation of `exp(-a/2)H_v(a)`.

The sign-partition route is attractive because most large cells in K=3 have
zero sampled sign changes.

## Verdict

`PARTIAL(V_J worklist localized and sign-shape exposed)`.

`GAP(certified sign partition or interval enclosure for V_J missing)`.

`FATAL(treating sampled sign changes as certified signs)`.

Track B remains active.  The next implementation step is a theorem-producing
or at least interval-arithmetic prototype for the top cells:

```text
K=3:   cells 39,35,36
K=3.5: cells 61,59,58
```

## Proshka Audit Block

Claim:
The `V_J` blocker is localized to a small endpoint-shoulder worklist.  K=3 has
stable sampled sign structure across meshes, and the largest continuous
variation cell is the left-edge jump cell.

Point of blockage:
The sign-change data and variation integrals are sampled.  They are not yet
certificates for the sign of `H_v'-H_v/2` or for the integral of its absolute
value.

What was tried:
Extended `clvledger` and `clvmesh` with continuous/jump variation fields and
sampled sign-change diagnostics; ran K=3 and K=3.5 endpoint schedules.

Minimal example:
At K=3, cell 39 `[5.850,6.000]` contains the left-edge jump and has continuous
variation `~0.040003` with one sampled sign change.  Cells 35 and 36 have zero
sampled sign changes and much smaller continuous variation.

Question for Proshka:
Should we first build interval-arithmetic enclosures for
`exp(-a/2)|H_v'-H_v/2|`, or should we certify sign partitions of
`H_v'-H_v/2` and reduce `V_J` to endpoint variation on sign-stable pieces?
