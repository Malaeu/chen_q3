# Track B B2b: Non-Node Curvature Guard Audit

Status: RP4/B2 diagnostic and proof-generator audit.  This is not a proof of
E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_nonnode_mesh_guard_audit.md`.  The mesh
guard still used sampled endpoint values of `|S_v'|` as if they were a
supremum on each mesh interval.  This card adds one diagnostic layer:

```text
sup_{[a_i,a_{i+1}]} |S_v'|
  <= max(|S_v'(a_i)|, |S_v'(a_{i+1})|)
     + factor * max_endpoint |S_v''| * (a_{i+1}-a_i)/2.
```

Here `S_v''` is currently sampled by finite differences of the analytic
`S_v'` grid.  The future proof generator must replace it by an
outward-rounded interval supremum or a Taylor-model remainder.

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

All intervals below are raw `a` intervals, not Q3 `xi` intervals.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler's extremal-function construction.
  Source: https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/
- `UNCONDITIONAL`: polygamma functions and derivative identities.
  Source: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: elementary mean-value/Lipschitz transfer:
  a bound on `|S_v''|` controls variation of `S_v'` on a mesh interval.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for:

```text
Taylor derivative envelope mesh interval certificate
curvature bound Lipschitz derivative mesh certificate
Taylor model certificate derivative bound interval proof
```

again point to the same finite-certificate pattern: isolate grid values,
provide an explicit derivative/Lipschitz envelope, then use the mesh cover to
lift pointwise certificates to intervals.  The most relevant local hits were
`FloorCert.Lipschitz_2219`, `A2_Lipschitz`, `Q_Lipschitz`, and prior
Step33 Taylor-model certificate notes.

External checks were limited to allowed sources: DLMF polygamma facts and the
standard mean-value/Lipschitz transfer principle.  No conditional analytic
number theory input was added.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now emits:

```text
signed_density_curvature_sampled_max_abs
```

and, inside each `non_node_interval_candidate`:

```text
mesh_curvature_guard:
  route = per_mesh_curvature_endpoint_guard
  mesh_interval_count
  max_mesh_width
  min_endpoint_abs_S
  max_endpoint_L_sample
  max_endpoint_curvature_sample
  stress_factors:
    curvature_factor
    min_mesh_guard
    passes_all_mesh_intervals
    worst_interval_index
    worst_a_lo
    worst_a_hi
    worst_endpoint_min_abs_S
    worst_endpoint_L_sample
    worst_endpoint_curvature_sample
    worst_derivative_envelope
    worst_mesh_width
  largest_passing_factor
  first_failing_factor
```

Cell-level summaries:

```text
non_node_mesh_curvature_common_passing_factors
non_node_mesh_curvature_largest_common_passing_factor
```

The curvature field is diagnostic only:

```text
sampled_gradient_only:
  replace sampled S_v'' by outward-rounded sup |S_v''| or an analytic Taylor
  remainder before proof use.
```

## K=3.5 Curvature Guard Run

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
  curvature guard passes all tested factors through 10000
  max sampled curvature on segment: ~6.23566
  worst factor-10000 interval:
    [6.645833333333817, 6.645976562500484]
    endpoint L_sample: ~0.760447
    endpoint curvature sample: ~0.788029
    derivative envelope: ~1.324791
    min mesh guard: ~0.067340

cell 59:
  non-node candidates: 1
  curvature guard passes all tested factors through 10000
  max sampled curvature on segment: ~7.57678
  worst factor-10000 interval:
    [6.8748567708338335, 6.8750000000005]
    endpoint L_sample: ~0.490710
    endpoint curvature sample: ~7.19213
    derivative envelope: ~5.64132
    min mesh guard: ~0.128377

cell 61:
  non-node candidates: 0
  remains node-local.  Its sampled curvature data is not routed through the
  non-node certificate.
```

Interpretation:

- For K=3.5 cell `58`, local variation of `S_v'` across a mesh interval is not
  the bottleneck.  Even an extreme sampled-curvature inflation factor `10000`
  leaves a large positive guard.
- The real proof bottleneck is now narrower: obtain outward-rounded endpoint
  enclosures for `S_v`, `S_v'`, and a verified local `sup |S_v''|` or Taylor
  remainder.

## K=3 Curvature Guard Run

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
  curvature guard passes all tested factors through 10000
  max sampled curvature on segment: ~1.01732

cell 36:
  non-node candidates: 1
  curvature guard passes all tested factors through 10000
  max sampled curvature on segment: ~0.836755

cell 39:
  non-node candidates: 0
  curvature guard fails already at factor 1 near the sampled root bracket;
  remains root/node-local.
```

Interpretation:

- K=3 non-node cells remain easier than the K=3.5 pilot.
- K=3 cell `39` is correctly rejected again.  The curvature layer does not
  hide the root obstruction.

## Next Proof-Generator Contract

First theorem-producing target remains:

```text
K = 3.5,
cell = 58,
raw a interval = [6.645833333333817, 6.760416666667158],
worst pilot mesh interval =
  [6.645833333333817, 6.645976562500484].
```

For each mesh interval `[a_i,a_{i+1}]`, emit:

```text
lower_abs_S_endpoint_i
lower_abs_S_endpoint_i_plus_1
upper_abs_S_prime_endpoint_i
upper_abs_S_prime_endpoint_i_plus_1
upper_sup_abs_S_second_on_interval
mesh_width
proof:
  max_abs_S_prime_on_interval
    <= max(endpoint S_prime upper bounds)
       + upper_sup_abs_S_second_on_interval * mesh_width / 2
  min(endpoint S lower bounds)
    > max_abs_S_prime_on_interval * mesh_width / 2
```

The sampled curvature audit says this route should have ample slack for cell
`58`.  If direct outward-rounded product-rule intervals for `S_v''` are too
wide, the fallback is a short Taylor model for `S_v'`.

## Verdict

`PARTIAL(sampled curvature-envelope route validated on non-node pilots)`.

`GAP(outward-rounded S_v, S_v', and sup |S_v''| enclosures still missing)`.

`FATAL(treating sampled finite-difference S_v'' as a proof bound)`.

Track B remains active.

## Proshka Audit Block

Claim:
For K=3.5 cell `58`, replacing endpoint-only `|S_v'|` by a curvature-envelope
candidate does not consume the margin.  The worst interval still has guard
`~0.067340` even with sampled curvature inflated by factor `10000`.

Point of blockage:
The curvature value is sampled by finite differences of `S_v'`.  A
proof-grade generator must produce outward-rounded enclosures for `S_v`,
`S_v'`, and `sup |S_v''|` or a Taylor remainder on each mesh interval.

What was tried:
Added `mesh_curvature_guard` diagnostics to `clvsigncert`; reran K=3.5 cells
`58,59,61` and K=3 cells `35,36,39`.

Minimal example:
K=3.5 cell `58`, mesh interval
`[6.645833333333817, 6.645976562500484]`: endpoint min `|S_v| ~ 0.067435`,
endpoint `|S_v'| ~ 0.760447`, sampled endpoint `|S_v''| ~ 0.788029`.
With curvature factor `10000`, the derivative envelope is `~1.324791` and
the sign guard remains `~0.067340`.

Question for Proshka:
Should the first proof-producing generator build direct outward-rounded
product-rule intervals for `S_v''`, or should it avoid a third derivative
formula by using a Taylor-model enclosure for `S_v'` on each mesh interval?
