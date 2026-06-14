# Track B B2b: Sampled Sign-Partition Audit For `V_J`

Status: RP4/B2 diagnostic and generator-shape refinement.  This is not a
proof of E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_V_variation_shape_audit.md`.  The previous
audit found the live `V_J` worklist.  This audit asks whether the
sign-partition route is numerically plausible before we build a certificate
generator.

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

The raw-`a` variation density is:

```text
exp(-a/2) * |H_v'(a) - H_v(a)/2|.
```

If `H_v'(a)-H_v(a)/2` has certified constant sign on subintervals, then the
continuous part of `V_J` is reduced to endpoint variation of
`exp(-a/2)H_v(a)` on those subintervals.  Jump terms at `a=2K` and `a=4K`
must remain separate.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary bounded-variation / absolutely-continuous
  variation identity on sign-stable intervals.
- `UNCONDITIONAL / finite-dimensional linear algebra`: packet profiles and
  kerQ eigen-directions in the Step13 finite model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvledger` now emits sampled
sign-partition fields per cell:

```text
sampled_sign_partition_count
sampled_sign_partition_break_count
sampled_sign_partition_variation
sampled_sign_partition_variation_over_continuous
sampled_sign_partition_max_width
```

Direction-level summaries:

```text
sampled_sign_partition_variation_sum
sampled_sign_partition_variation_over_continuous_sum
sampled_sign_partition_break_count_sum
sampled_sign_partition_cells_with_breaks
top_cells_by_sign_partition_breaks
top_cells_by_sign_partition_variation
```

`clvmesh` carries the same partition summary fields across `quad_na`.

These are sampled diagnostics only.  They are not sign certificates.

## Local And External Search Synthesis

Local `q3_docs` search again points to the existing project pattern:

- `FloorCert.Lipschitz_2219` and `Grid_2219` for grid plus Lipschitz/envelope
  certificates;
- PrimeCert and finite-dictionary notes for theorem-producing finite
  interval packages;
- Stieltjes-related local files for the convention that the continuous and
  jump pieces must be accounted for separately.

External search added no new conditional number-theory input.  It only
confirms the already-used CLV/Beurling--Selberg source and standard
Riemann--Stieltjes/BV bookkeeping.

## K=3 Numbers

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --quad-na 4001 --ledger-cells 80 --top-cells 3
```

Result:

```text
finite-U / residual                     ~= 2.984654
continuous variation sum                ~= 0.127925
sampled sign-partition variation sum    ~= 0.140369
partition / continuous                  ~= 1.097276
sampled derivative sign-change cells    = 16
sampled sign-partition cells w/ breaks  = 16
sampled sign-partition break count      = 31
```

Mesh check:

```text
quad_na  continuous V   sampled partition V   ratio      breaks
2001     0.126036       0.138489              1.098805   30
4001     0.127925       0.140369              1.097276   31
```

Top partition-variation cells:

```text
cell 39: [5.850, 6.000]
  continuous V ~= 0.040003
  jump V       ~= 0.049769
  partition V  ~= 0.052446
  ratio         ~= 1.311049
  jump labels   = left_edge_jump

cell 35: [5.250, 5.400]
  continuous V ~= 0.009096
  partition V  ~= 0.009097
  ratio         ~= 1.000032
  sampled sign changes = 0

cell 36: [5.400, 5.550]
  continuous V ~= 0.007912
  partition V  ~= 0.007912
  ratio         ~= 1.000009
  sampled sign changes = 0
```

Interpretation: non-jump shoulder cells are almost endpoint-exact under the
sampled sign partition.  The left-edge jump cell is not clean: it mixes a
true jump term with a sampled derivative/sign partition artifact.  It must be
split into `jump + smooth-left/right` before theorem production.

## K=3.5 Numbers

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --quad-na 4001 --ledger-cells 120 --top-cells 3
```

Result:

```text
finite-U / residual                     ~= 4.811506
continuous variation sum                ~= 0.104734
sampled sign-partition variation sum    ~= 0.104928
partition / continuous                  ~= 1.001845
sampled derivative sign-change cells    = 41
sampled derivative sign changes total   = 46
sampled sign-partition cells w/ breaks  = 41
sampled sign-partition break count      = 85
```

Top partition-variation cells:

```text
cell 61: [6.990, 7.104]
  continuous V ~= 0.032039
  jump V       ~= 0.030132
  partition V  ~= 0.032226
  ratio         ~= 1.005820
  sampled sign changes = 2
  jump labels   = left_edge_jump

cell 59: [6.760, 6.875]
  continuous V ~= 0.015511
  partition V  ~= 0.015514
  ratio         ~= 1.000151
  sampled sign changes = 0

cell 58: [6.646, 6.760]
  continuous V ~= 0.011678
  partition V  ~= 0.011679
  ratio         ~= 1.000084
  sampled sign changes = 0
```

Interpretation: K=3.5 strongly supports the sign-partition route for smooth
cells.  The main proof-generator risk is now localized to the edge-jump cell
and to certifying the signs, not to discovering the right finite shape.

## Candidate Generator Contract

For each raw-`a` cell `J=[alpha,beta]`, emit:

```text
1. finite U_J certificate from the Chebyshev staircase;
2. split points containing all jumps of E_delta and all certified roots of
   H_v'(a)-H_v(a)/2;
3. sign certificate for H_v'(a)-H_v(a)/2 on each smooth subinterval;
4. endpoint enclosure for exp(-a/2)H_v(a);
5. jump certificate U(a0)exp(-a0/2)|Delta H_v(a0)| at a0=2K,4K;
6. final V_J and U_J*V_J bound.
```

Preferred next experiment:

```text
Build a prototype interval/sign generator for:
K=3:   cells 35,36,39
K=3.5: cells 58,59,61
```

Do not certify cell 39 or 61 as smooth.  Split the edge jump first.

Follow-up:

- `docs/trackB/b2b_signcert_prototype.md` adds the first smooth/jump split
  prototype.  It introduces `clvsigncert`, reports sampled sign guards and
  root brackets on selected worklist cells, and refines the next generator
  order: K=3.5 cells `58,59,61`, then K=3 cells `35,36`, then K=3 cell `39`
  with one root-isolation subproblem.

## Verdict

`PARTIAL(sign-partition route looks viable for smooth shoulder cells)`.

`GAP(certified derivative sign/zero isolation and jump split missing)`.

`FATAL(treating sampled partition endpoints as certified critical points)`.

Track B remains active.

## Proshka Audit Block

Claim:
The sign-partition route is the most efficient next generator shape for
`V_J`: smooth shoulder cells reduce numerically to endpoint variation, while
edge-jump cells must be split into explicit jump plus smooth pieces.

Point of blockage:
The sampled partition does not certify roots or signs of
`H_v'(a)-H_v(a)/2`.  It also sees edge discontinuities unless the jump cells
are split first.

What was tried:
Added sampled sign-partition endpoint-variation fields to `clvledger` and
`clvmesh`; ran K=3 and K=3.5 endpoint schedules.

Minimal example:
At K=3.5, cells 59 and 58 have zero sampled sign changes and
partition/continuous ratios `~1.000151` and `~1.000084`.  Cell 61 contains
`left_edge_jump`, has two sampled sign changes, and must be split before
certification.

Question for Proshka:
Should the first theorem-producing prototype isolate zeros of
`H_v'-H_v/2` by interval arithmetic directly, or should it use Bernstein/
B-spline derivative envelopes to prove sign stability on the sampled
subintervals?
