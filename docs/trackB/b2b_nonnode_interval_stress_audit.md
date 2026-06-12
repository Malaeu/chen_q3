# Track B B2b: Non-Node Interval Stress Audit

Status: RP4/B2 diagnostic and proof-generator audit.  This is not a proof of
E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_nonnode_interval_candidate.md`.  The
candidate card extracted the non-node sign certificate

```text
min |S_v| > L*h/2.
```

The remaining proof gap is to replace sampled `min |S_v|` and sampled
`L = sup |S_v'|` by outward-rounded interval bounds.  This audit measures how
wide the future derivative enclosure may be before the non-node sign guard
breaks.

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

All reported cell intervals are raw `a` intervals.  No Q3 `xi` interval is
used directly in this audit.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler's extremal-function construction.
  Source: https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/
- `UNCONDITIONAL`: polygamma functions and derivative identities.
  Source: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary grid/Lipschitz implication:
  if `|S(a_i)| >= m`, `|S'| <= L` on each mesh interval, and mesh width is
  at most `h`, then `|S|` has fixed sign when `m > L*h/2`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches:

```text
non-node interval sign certificate Lipschitz derivative envelope
FloorCert Grid Lipschitz positive guard interval certificate
outward rounded interval bounds derivative sampled guard
Vaaler polygamma receiver interval bounds non node
```

returned the same finite-certificate pattern as the earlier Track B notes:

```text
grid values + derivative envelope + positive guard.
```

The most relevant local hits were `FloorCert.Grid_2219`,
`FloorCert.Lipschitz_2219`, `NodeSpacing`, and earlier PrimeCert interval
closure notes.  External/source checks were limited to the already-allowed
Selberg--Vaaler/CLV and DLMF polygamma sources.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now accepts:

```text
--interval-safety-factors 2 10 100 1000 ...
```

For each non-node segment it emits:

```text
interval_safety_stress:
  route = sampled_derivative_inflation_stress
  stress_factors:
    factor
    inflated_guard = min_sample |S_v| - factor * L_sample * h / 2
    passes
  largest_passing_factor
  first_failing_factor
```

For each cell it also emits:

```text
non_node_interval_common_passing_safety_factors
non_node_interval_largest_common_passing_safety_factor
```

These fields are diagnostic only.  They answer:

```text
If the final outward-rounded bound for sup |S_v'| is N times wider than the
sampled L_sample, does this segment/cell still have a positive sign guard?
```

They do not replace the outward-rounded interval proof.

## K=3.5 Stress Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --interval-safety-factors 2 10 100 1000 2000 5000 \
  --cells 58 59 61
```

Results:

```text
cell 58:
  non-node candidates: 1
  min allowable L_S multiplier: ~1238.27
  common passing safety factors: 2, 10, 100, 1000
  largest tested passing factor: 1000
  factor 2000 fails

cell 59:
  non-node candidates: 1
  min allowable L_S multiplier: ~3664.59
  common passing safety factors: 2, 10, 100, 1000, 2000
  largest tested passing factor: 2000
  factor 5000 fails

cell 61:
  non-node candidates: 0
  receiver node-treatment segments: 2
  remains node-local, not a non-node theorem target
```

Interpretation:

- Cell `58` is the first non-node theorem target and has enough margin to
  tolerate a derivative envelope about `1000x` wider than the sampled
  derivative.
- Cell `59` is even more robust in this audit.
- Cell `61` must stay on the node-local branch even though one smooth side
  numerically passes some stress factors.

## K=3 Stress Run

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 801 \
  --interval-safety-factors 2 10 100 1000 2000 5000 \
  --cells 35 36 39
```

Results:

```text
cell 35:
  non-node candidates: 1
  min allowable L_S multiplier: ~7919.99
  common passing safety factors: 2, 10, 100, 1000, 2000, 5000
  largest tested passing factor: 5000

cell 36:
  non-node candidates: 1
  min allowable L_S multiplier: ~5245.40
  common passing safety factors: 2, 10, 100, 1000, 2000, 5000
  largest tested passing factor: 5000

cell 39:
  non-node candidates: 0
  receiver node-treatment segments: 1
  recommendation: isolate_roots_then_sign_certify
  remains root/node-local, not a non-node theorem target
```

Interpretation:

- K=3 cells `35` and `36` have very large non-node stress margins.
- K=3 cell `39` is correctly rejected by both the root detector and the
  node-local detector.

## Next Proof-Generator Gate

The next generator should target K=3.5 cell `58` first and emit:

```text
For each grid interval [a_i, a_{i+1}]:
  interval lower bound for |S_v(a_i)|;
  interval upper bound for |S_v'| on [a_i, a_{i+1}];
  proof of lower(|S_v(a_i)|) > upper(|S_v'|) * h / 2.
```

The stress audit says this has a large numerical buffer: the first target
survives the sampled derivative bound inflated by `1000x`.  Therefore the
direct product-rule enclosure for `S_v` and `S_v'` is worth trying before
falling back to a more symbolic Taylor model.

## Verdict

`PARTIAL(non-node interval stress margins measured)`.

`GAP(actual outward-rounded interval enclosures for S_v and S_v' still missing)`.

`FATAL(treating stress factors as proof-grade derivative bounds)`.

Track B remains active.

## Proshka Audit Block

Claim:
The first non-node theorem target, K=3.5 cell `58`, has enough margin to
tolerate a derivative envelope about `1000x` wider than the sampled
`sup |S_v'|`; K=3.5 cell `59` tolerates `2000x`, and K=3 cells `35,36`
tolerate at least `5000x` on the tested factors.

Point of blockage:
The audit still uses sampled `min |S_v|` and sampled `L_sample`.  We need an
outward-rounded interval backend for `S_v` and `S_v'`.

What was tried:
Added `--interval-safety-factors` to `clvsigncert` and reran K=3.5 cells
`58,59,61` plus K=3 cells `35,36,39`.

Minimal example:
At K=3.5 cell `58`, safety factor `1000` leaves inflated guard
`~0.012976 > 0`, while factor `2000` gives `~-0.041483`.  So a proof-grade
receiver/profile derivative enclosure can be roughly three orders of magnitude
looser than the sampled `L_sample`, but not arbitrary.

Question for Proshka:
For the first theorem-producing generator, should we enclose `S_v'` directly
by product-rule interval arithmetic over each mesh interval, or derive a
coarser symbolic supremum for receiver/profile derivatives and use the
`1000x` slack as the safety budget?
