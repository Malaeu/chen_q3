# Track B B2b: Non-Node Mesh Guard Audit

Status: RP4/B2 diagnostic and proof-generator audit.  This is not a proof of
E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_nonnode_interval_stress_audit.md`.  The
stress audit measured global derivative-inflation tolerance.  This card
refines that into the actual finite-certificate shape:

```text
for each mesh interval [a_i, a_{i+1}],
  lower(|S_v(a_i)|, |S_v(a_{i+1})|)
    > upper(|S_v'| on [a_i, a_{i+1}]) * (a_{i+1}-a_i)/2.
```

The current audit still uses sampled endpoint derivatives for the upper bound.
The next generator must replace those samples by outward-rounded interval
suprema.

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

All intervals below are raw `a` intervals.  Do not read the printed cell
coordinates as Q3 `xi` coordinates.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler's extremal-function construction.
  Source: https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/
- `UNCONDITIONAL`: polygamma functions and derivative identities.
  Source: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: elementary finite mesh/Lipschitz transfer:
  if every point in a mesh interval is within `h/2` of a certified endpoint
  and `|S'| <= L` on the interval, then `|S|` keeps sign when
  `lower(|S(endpoint)|) > L*h/2`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local Search Synthesis

Local `q3_docs` searches for:

```text
grid point lower bound derivative upper bound mesh interval sign certificate
FloorCert Grid Lipschitz lower bound mesh certificate
interval proof generator derivative envelope cell guard
PrimeCert interval closure grid Lipschitz margin
```

returned the existing finite-certificate pattern:

```text
Grid_2219: pointwise grid lower bounds;
Lipschitz_2219: derivative/Lipschitz envelope;
grid_cover: every point is close to a grid point;
PrimeCert closure notes: theorem-producing generator must emit envelopes, not
sampled numerics.
```

This Track B mesh guard mirrors that shape.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now emits, inside each
`non_node_interval_candidate`:

```text
mesh_interval_guard:
  route = per_mesh_endpoint_guard
  mesh_interval_count
  max_mesh_width
  min_endpoint_abs_S
  max_endpoint_L_sample
  stress_factors:
    factor
    min_mesh_guard
    passes_all_mesh_intervals
    worst_interval_index
    worst_a_lo
    worst_a_hi
    worst_endpoint_min_abs_S
    worst_endpoint_L_sample
    worst_mesh_width
  largest_passing_factor
  first_failing_factor
  derivative_bound_status
```

Cell-level summaries:

```text
non_node_mesh_guard_common_passing_safety_factors
non_node_mesh_guard_largest_common_passing_safety_factor
```

The field is still diagnostic:

```text
sampled_endpoint_only:
  replace endpoint derivative samples by outward-rounded sup |S_v'| on each
  mesh interval.
```

## K=3.5 Mesh Guard Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --interval-safety-factors 2 10 100 1000 2000 5000 10000 \
  --cells 58 59 61
```

Results:

```text
cell 58:
  non-node candidates: 1
  mesh intervals: 800
  mesh guard passes factors: 2, 10, 100, 1000
  first failing factor: 2000
  worst factor-1000 interval:
    [6.645833333333817, 6.645976562500484]
    min mesh guard: ~0.012976
    endpoint min |S_v|: ~0.067435
    endpoint L_sample: ~0.760447

cell 59:
  non-node candidates: 1
  mesh intervals: 800
  mesh guard passes factors: 2, 10, 100, 1000, 2000
  first failing factor: 5000
  worst factor-1000 interval:
    [6.8748567708338335, 6.8750000000005]
    min mesh guard: ~0.093639
    endpoint min |S_v|: ~0.128781
    endpoint L_sample: ~0.490710

cell 61:
  non-node candidates: 0
  remains node-local, not a non-node theorem target.
```

Interpretation:

- K=3.5 cell `58` is still the first target.  The worst mesh interval is the
  leftmost subinterval of the cell.
- K=3.5 cell `59` is also clean; its worst interval is the rightmost
  subinterval.
- Cell `61` stays on the node-local branch even though one smooth side has a
  sampled mesh guard.

## K=3 Mesh Guard Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 801 \
  --interval-safety-factors 2 10 100 1000 2000 5000 10000 \
  --cells 35 36 39
```

Results:

```text
cell 35:
  non-node candidates: 1
  mesh guard passes factors: 2, 10, 100, 1000, 2000, 5000
  first failing factor: 10000
  worst factor-5000 interval:
    [5.250000000000438, 5.250187500000438]
    min mesh guard: ~0.021742

cell 36:
  non-node candidates: 1
  mesh guard passes factors: 2, 10, 100, 1000, 2000, 5000
  first failing factor: 10000
  worst factor-5000 interval:
    [5.511750000000459, 5.511937500000459]
    min mesh guard: ~0.006643

cell 39:
  non-node candidates: 0
  remains root/node-local, not a non-node theorem target.
```

Interpretation:

- K=3 cells `35` and `36` remain easier than the K=3.5 pilot.
- K=3 cell `39` is correctly rejected.  Its worst mesh interval is near the
  sampled root bracket, so the non-node route must not absorb it.

## Next Generator Contract

First theorem-producing target:

```text
K = 3.5,
cell = 58,
raw a interval = [6.645833333333817, 6.760416666667158],
mesh intervals = 800,
worst pilot mesh interval =
  [6.645833333333817, 6.645976562500484].
```

For each mesh interval `[a_i, a_{i+1}]`, emit:

```text
lower_abs_S_endpoint_i
lower_abs_S_endpoint_i_plus_1
upper_sup_abs_S_prime_on_interval
mesh_width
proof:
  min(lower_abs_S_endpoint_i, lower_abs_S_endpoint_i_plus_1)
    > upper_sup_abs_S_prime_on_interval * mesh_width / 2
```

The current audit says the first cell tolerates the sampled derivative bound
inflated by `1000x`, so a direct interval product-rule enclosure is plausible.
If the direct interval enclosure is wider than this, the fallback is a local
Taylor model for `S_v'` on each mesh interval.

## Verdict

`PARTIAL(per-mesh non-node certificate shape extracted)`.

`GAP(outward-rounded sup |S_v'| on each mesh interval still missing)`.

`FATAL(treating endpoint derivative samples as interval suprema)`.

Track B remains active.

Follow-up:

- `docs/trackB/b2b_nonnode_curvature_guard_audit.md` adds a sampled
  curvature-envelope layer for `sup |S_v'|` on each mesh interval.  On K=3.5
  cell `58`, even curvature factor `10000` keeps the worst interval guard
  positive, so the next proof-producing generator should focus on
  outward-rounded endpoint values and certified `sup |S_v''|` or a Taylor
  remainder.

## Proshka Audit Block

Claim:
The non-node certificate can be driven by a finite mesh guard.  For K=3.5
cell `58`, all 800 mesh intervals pass the tested factor `1000`; the worst
interval is `[6.645833333333817, 6.645976562500484]` with guard
`~0.012976` at factor `1000`.

Point of blockage:
The current derivative bound is still sampled at interval endpoints.  The
proof-producing generator must replace it with an outward-rounded supremum of
`|S_v'|` over each mesh interval.

What was tried:
Added `mesh_interval_guard` diagnostics to `clvsigncert`; reran K=3.5 cells
`58,59,61` and K=3 cells `35,36,39` with safety factors through `10000`.

Minimal example:
K=3.5 cell `58`, interval `[6.645833333333817, 6.645976562500484]`,
endpoint min `|S_v| ~ 0.067435`, sampled endpoint `L ~ 0.760447`, width
`~1.43229e-4`; factor `1000` guard is `~0.012976`.

Question for Proshka:
Is it better to prove `sup |S_v'|` on each mesh interval by direct
outward-rounded product-rule intervals, or to derive a short Taylor enclosure
for `S_v'` using one more derivative layer?
