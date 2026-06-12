# Track B B2b: Vaaler Node And Cancellation Audit

Status: RP4/B2 diagnostic and interval-generator planning.  This is not a
proof of E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_receiver_derivative_enclosure.md`.  The
receiver derivatives are now analytic floating-point evaluations.  The next
question is where a proof-grade interval generator must split the Vaaler
receiver around integer interpolation nodes.

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

Vaaler integer nodes are the integers in the `z_left` or `z_right`
coordinates.  For K=3.5 and `delta=1`, the edge jump at `a=7` is exactly
`z_left=0` and `z_right=-7`.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler/Selberg sign-function construction as a standard
  Beurling--Selberg formula.
  Reference used for this audit:
  https://www.math.ntnu.no/emner/MA3001/2020v/2021v/class11_zeta_NTNU.pdf
- `UNCONDITIONAL`: polygamma definitions/properties.
  Reference: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary Stieltjes/BV bookkeeping.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now emits
`receiver_node_audit` for every smooth segment:

```text
z_left/z_right ranges,
nearest integer and distance,
samples within 1e-2, 1e-3, 1e-4 of an integer,
whether local node treatment is needed,
H0/H0'/H0'' cancellation ratios.
```

Cell-level summaries were also added:

```text
receiver_node_treatment_segment_count
receiver_min_distance_to_vaaler_integer
receiver_H0_prime_max_cancellation_ratio
receiver_H0_second_max_cancellation_ratio
```

The cancellation ratios are diagnostic:

```text
ratio = sum(abs(product-rule terms)) / abs(final value).
```

They are not proof bounds.

## Local And External Search Synthesis

Local `q3_docs` searches for Vaaler integer nodes, removable singularities,
and interval/Lipschitz certificates returned:

- `NodeSpacing` files, confirming the repo already treats node proximity as a
  first-class finite certificate issue;
- `FloorCert.Grid_2219` / `Lipschitz_2219`, matching the intended
  grid-plus-envelope generator style;
- existing INSIGHTS entries that separate diagnostic numerical artifacts from
  theorem-producing packages.

External search added no conditional number-theory input.  It only confirms
the Vaaler/Selberg formulas and polygamma calculus already used by Track B.

## K=3.5 Node Audit

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 --cells 58 59 61
```

Cell-level summary:

```text
cell 58:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  min distance to Vaaler integer: ~0.239583
  max H0' cancellation ratio:  ~5.143e4
  max H0'' cancellation ratio: ~1.700e6

cell 59:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  min distance to Vaaler integer: ~0.125000
  max H0' cancellation ratio:  ~1.510e5
  max H0'' cancellation ratio: ~4.863e8

cell 61:
  recommendation: smooth_sign_cert_plus_explicit_jump_cert
  node-treatment segments: 2
  min distance to Vaaler integer: ~3.580729e-5
  max H0' cancellation ratio:  ~8.726e11
  max H0'' cancellation ratio: ~3.423e12
```

For cell `61`, the two smooth sides are:

```text
left smooth side:
  a in [6.989583333333842, 6.999964192708333]
  z_left  in [-0.0104167, -0.0000358073], nearest node 0
  z_right in [-7.0104167, -7.0000358073], nearest node -7

right smooth side:
  a in [7.000035807291667, 7.104166666667184]
  z_left  in [0.0000358073, 0.1041667], nearest node 0
  z_right in [-6.9999641927, -6.8958333], nearest node -7
```

Interpretation:

- Cells `58` and `59` are not near Vaaler integer nodes; their interval
  proof can start with the direct polygamma product formula.
- Cell `61` is the first node-local target.  Both smooth sides are within
  `~3.6e-5` of Vaaler nodes and have huge cancellation pressure, so a direct
  outward-rounded polygamma interval may be too wide unless it splits or uses
  local Taylor/series bounds.

## K=3 Node Audit

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 801 --cells 35 36 39
```

Cell-level summary:

```text
cell 35:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  min distance to Vaaler integer: ~0.300000
  max H0'' cancellation ratio: ~1.025e4

cell 36:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  min distance to Vaaler integer: ~0.225000
  max H0'' cancellation ratio: ~1.021e5

cell 39:
  recommendation: isolate_roots_then_sign_certify
  node-treatment segments: 1
  min distance to Vaaler integer: ~2.343750e-5
  max H0' cancellation ratio:  ~2.917e12
  max H0'' cancellation ratio: ~3.757e11
```

Interpretation:

- K=3 cells `35` and `36` can use the non-node interval route.
- K=3 cell `39` combines two hard features: one root bracket and a
  near-node receiver segment.  It should stay behind K=3.5 cell `61` in the
  theorem-producing order.

## Refined Interval Generator Contract

The interval generator should split the receiver proof into two branches:

```text
Non-node branch:
  distance to nearest Vaaler integer >= rho_node;
  use direct polygamma product intervals for H0/H0'/H0'' and K0/K0'/K0''.

Node-local branch:
  distance to nearest Vaaler integer < rho_node;
  split at the integer node;
  use local Taylor/series bounds for H0/H0'/H0'' and K0/K0'/K0'';
  combine with packet B-spline enclosures.
```

Recommended first theorem-producing order:

```text
1. K=3.5 cells 58 and 59: non-node direct interval route.
2. K=3.5 cell 61: node-local split at z_left=0 and z_right=-7.
3. K=3 cells 35 and 36: non-node direct interval route.
4. K=3 cell 39: node-local split plus root isolation.
```

## Verdict

`PARTIAL(node-local interval targets identified)`.

`GAP(Taylor/series or outward-rounded interval bounds near Vaaler nodes missing)`.

`FATAL(treating cancellation-heavy floating-point polygamma values as proof intervals)`.

Track B remains active.

## Proshka Audit Block

Claim:
The remaining receiver interval problem splits into a non-node branch and a
node-local branch.  K=3.5 cells `58,59` are non-node; K=3.5 cell `61` is the
first node-local target, with both smooth sides within `~3.6e-5` of Vaaler
integer nodes.

Point of blockage:
For node-local pieces, direct polygamma product intervals may be too wide
because cancellation ratios reach `~1e12`.  A proof-grade local Taylor/series
enclosure or carefully split outward-rounded interval evaluation is still
missing.

What was tried:
Added node proximity and cancellation diagnostics to `clvsigncert`; reran K=3
and K=3.5 worklists.

Minimal example:
At K=3.5 cell `61`, the right smooth side has
`z_left in [0.0000358073, 0.1041667]` and
`z_right in [-6.9999641927, -6.8958333]`; the nearest nodes are `0` and `-7`,
and the max `H0''` cancellation ratio is about `5.65e11` on that side and
`3.42e12` on the left side.

Question for Proshka:
Should the first node-local certificate use Taylor expansions around the
integer Vaaler nodes, or use outward-rounded polygamma intervals after
splitting off a small exclusion radius around each node?
