# Track B B2b: Smooth/Jump Sign-Certificate Prototype

Status: RP4/B2 diagnostic and proof-generator prototype.  This is not a
proof of E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_sign_partition_audit.md`.  The previous
audit said the next object should split edge jumps and certify signs of
`H_v'(a)-H_v(a)/2` on smooth pieces.  The new `clvsigncert` probe implements
that prototype.

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

The continuous variation density is:

```text
exp(-a/2) * |H_v'(a) - H_v(a)/2|.
```

The edge jumps at `a=2K` and `a=4K` are not smooth variation.  They are
separate terms:

```text
|psi(exp(a0))-exp(a0)| * exp(-a0/2) * |Delta H_v(a0)|.
```

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary Stieltjes integration-by-parts and
  bounded-variation bookkeeping.
  Reference used for the audit: Rudin advanced-calculus chapter notes,
  https://ani.stat.fsu.edu/~jfrade/HOMEWORKS/STA5446/Rudin-AdvCalc/ch7.pdf
- `UNCONDITIONAL / finite-dimensional linear algebra`: packet profiles and
  kerQ eigen-directions in the Step13 finite model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Probe Update

`scripts/trackb_edge_operator_probe.py` now has:

```text
clvsigncert
```

It emits, for selected raw-`a` cells:

```text
smooth_segments
jump_terms
sampled_sign_guard
sampled_root_brackets
smooth_endpoint_variation_x
smooth_partition_variation_x
finiteU_endpoint_plus_jump_candidate_bound
finiteU_partition_plus_jump_candidate_bound
recommendation
```

The `sampled_sign_guard` is a heuristic Lipschitz-style margin computed from
sampled first differences.  It is only a prototype for the future
theorem-producing interval/B-spline envelope generator.

## Local And External Search Synthesis

Local `q3_docs` searches for sign certificates, root isolation, jump splits,
and theorem-producing envelope generators again point to:

- `FloorCert.Grid_2219` and `FloorCert.Lipschitz_2219`;
- PrimeCert finite interval packages and closure notes;
- the existing project convention that finite numerical artifacts are
  reproducibility aids until converted into explicit theorem statements.

External search added no new conditional number-theory input.  The only
external analytic ingredients still used are the already-recorded
Selberg--Vaaler/CLV source and standard BV/Stieltjes facts.

## K=3 Worklist

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 1601 --cells 35 36 39
```

Results:

```text
cell 35 [5.250, 5.400]
  recommendation: smooth_sign_cert_candidate
  sign-stable segments: 1
  sampled sign guard: ~0.058968
  endpoint/continuous V: ~1.00000003
  finite U * endpoint V: ~0.091893

cell 36 [5.400, 5.550]
  recommendation: smooth_sign_cert_candidate
  sign-stable segments: 1
  sampled sign guard: ~0.048085
  endpoint/continuous V: ~1.00000001
  finite U * endpoint V: ~0.094775

cell 39 [5.850, 6.000]
  recommendation: isolate_roots_then_sign_certify
  jump: left_edge_jump at a=6
  jump variation: ~0.049769
  finite jump bound: ~0.019709
  smooth endpoint V: ~0.002773
  endpoint+jump candidate bound: ~0.040170
  sampled root bracket:
    [5.995196059570327, 5.995289794921890]
```

Interpretation:

- Cells `35` and `36` are ready for a first smooth sign certificate prototype.
- Cell `39` is no longer a giant variation cell after splitting the edge
  jump.  The remaining smooth obstruction is one isolated root just before
  `a=6`.

## K=3.5 Worklist

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 1601 --cells 58 59 61
```

Results:

```text
cell 58 [6.646, 6.760]
  recommendation: smooth_sign_cert_candidate
  sign-stable segments: 1
  sampled sign guard: ~0.067408
  endpoint/continuous V: ~1.00000004
  finite U * endpoint V: ~0.197654

cell 59 [6.760, 6.875]
  recommendation: smooth_sign_cert_candidate
  sign-stable segments: 1
  sampled sign guard: ~0.128763
  endpoint/continuous V: ~1.00000007
  finite U * endpoint V: ~0.201232

cell 61 [6.990, 7.104]
  recommendation: smooth_sign_cert_plus_explicit_jump_cert
  jump: left_edge_jump at a=7
  sign-stable smooth segments: 2
  sampled sign guards: ~0.022024 and ~0.007154
  smooth endpoint/continuous V: ~1.00000008
  finite jump bound: ~0.152588
  endpoint+jump candidate bound: ~0.187659
```

Interpretation:

- K=3.5 is the cleanest first target for theorem production: after the edge
  split, all selected smooth segments are sampled sign-stable with positive
  guard.
- Cell `61` gives the template for jump-cell certificates:
  `finite jump term + endpoint variation on each smooth side`.

## Generator Contract Refined

The next theorem-producing generator should emit:

```text
For each smooth segment:
  interval enclosure for H_v'(a)-H_v(a)/2,
  sign certificate on the segment,
  endpoint enclosure for exp(-a/2)H_v(a),
  endpoint variation bound.

For each edge jump:
  one-sided Delta H_v(a0),
  one-sided psi(exp(a0))-exp(a0),
  finite jump bound.

For cells with sampled root brackets:
  root isolation certificate,
  split at the isolated root,
  sign certificates on both sides.
```

Recommended order:

```text
1. K=3.5 cells 58,59,61: no root isolation needed after jump split.
2. K=3 cells 35,36: smooth sign-stable.
3. K=3 cell 39: one root-isolation subproblem near a=5.99524, then split.
```

## Verdict

`PARTIAL(smooth/jump proof-generator shape identified)`.

`GAP(interval or B-spline derivative enclosure still missing)`.

`FATAL(treating sampled sign guards as proof of sign stability)`.

Track B remains active.

## Proshka Audit Block

Claim:
After explicitly splitting edge jumps, the selected `V_J` worklist becomes a
finite smooth sign-certificate problem.  K=3.5 cells `58,59,61` and K=3 cells
`35,36` are sampled sign-stable; K=3 cell `39` has one root bracket before
the edge jump.

Point of blockage:
The current guard is sampled.  It must be replaced by an interval/B-spline
derivative enclosure or another certified sign method.

What was tried:
Added `clvsigncert`, split cells at `2K/4K`, computed jump terms separately,
and sampled sign guards/root brackets on smooth pieces.

Minimal example:
At K=3, cell `39=[5.850,6.000]` has `left_edge_jump` at `a=6`, finite jump
bound `~0.019709`, and one smooth root bracket
`[5.995196059570327, 5.995289794921890]`.

Question for Proshka:
For the first certificate generator, should we enclose
`H_v'(a)-H_v(a)/2` directly by interval arithmetic on the explicit sampled
packet formula, or should we first derive B-spline derivative envelopes and
use them as reusable sign guards?
