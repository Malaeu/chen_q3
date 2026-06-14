# Track B B2b: Mesh Stability Audit

Status: RP4/B2 diagnostic and proof-contract correction.  This is not a proof
of E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_interval_envelope_audit.md`.  The previous
audit correctly identified the missing proof-grade object, but it compared
cell residuals against local variation budgets too aggressively.  That
comparison is a useful worklist heuristic, not a proof criterion: when the
global Stieltjes integration-by-parts identity is split into cells, internal
endpoint terms cancel before absolute values are taken.

The proof criterion is global:

```text
|integral phi_v d(psi-x)|
  <= endpoint terms + sum_J sup_J |psi(e^a)-e^a| * Var_J(phi_v).
```

Cell residuals only tell us where a future interval-envelope generator should
look first.

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

The only admissible mesh-stability test is the global Stieltjes budget in raw
`a` coordinates.  Local cell residual ratios are not proof certificates.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: exact finite Chebyshev staircase
  `psi(x)=sum_{n<=x} Lambda(n)` on the finite packet range.
- `UNCONDITIONAL`: Stieltjes integration by parts for bounded-variation
  functions.
- `UNCONDITIONAL`: Fiori--Kadiri--Swidinsky explicit comparison bound for
  `|psi(x)-x|`, used only as a coarse baseline.
  Source: https://arxiv.org/abs/2204.02588
- `UNCONDITIONAL / proof-engine style only`: validated numerics and interval
  arithmetic for future quadrature certificates.  This supplies a verification
  style, not a mathematical RH input.
  Example reference:
  https://old.maa.org/press/maa-reviews/validated-numerics-a-short-introduction-to-rigorous-computations

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local Search Synthesis

Local `q3_docs` searches for validated quadrature, FloorCert Lipschitz
certificates, and PrimeCert theorem-producing generators returned:

- `FloorCert.Grid_2219` and `FloorCert.Lipschitz_2219`, i.e. the existing
  `grid + Lipschitz` certificate pattern;
- PrimeCert closure notes with interval/numeric quadrature certificate plans;
- earlier instructions to keep certificate outputs as theorems, not new axioms.

So the Track B proof engine should look like:

```text
raw-a cells
  + certified U_J
  + certified V_J / quadrature remainder
  + jump terms
  -> theorem-producing data file
```

not like a hand-picked floating-point mesh.

## Probe Update

`scripts/trackb_edge_operator_probe.py` now has:

```bash
clvmesh
```

It wraps `clvledger` over several `quad_na` values and reports only the global
mesh-stability fields:

```text
ledger_total_residual
exact_total_with_endpoints
exact_bound_over_abs_residual
first_quad_na_covering_total_residual
last_mesh_residual_abs_delta
last_mesh_exact_total_abs_delta
```

It also carries this warning in JSON:

```text
cell residual ratios remain worklist heuristics because cell endpoint terms
cancel only before taking absolute values
```

## K = 3 Mesh Sweep

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvmesh \
  --K 3 --ell 0.75 --schedule fixed \
  --receiver-delta 0.5 \
  --p0-na 201 \
  --quad-na-values 2001 4001 8001 16001 \
  --ledger-cells 80 --top-cells 3
```

Output summary:

```text
quad_na   residual       exact_total    exact/residual
2001     -0.52122844     0.34220358     0.65653
4001     -0.31705963     0.31870330     1.00518
8001     -0.21520135     0.30658480     1.42464
16001    -0.16432851     0.30106324     1.83208
```

Mesh verdict:

```text
first_quad_na_covering_total_residual = 4001
last residual delta                   ~= 0.05087
last exact-total delta                ~= 0.00552
```

Interpretation: the earlier K=3 underbound at `quad_na=2001` was not a fatal
mathematical obstruction.  It was a mesh/continuum-convention warning.  By
`quad_na=4001`, the global Stieltjes budget already covers the direct residual;
by `16001`, the exact-total budget is stable near `0.30`, while the residual
continues moving because the diagnostic continuum integral is still trapezoid
mesh dependent.

## K = 3.5 Mesh Sweep

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvmesh \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 \
  --p0-na 401 \
  --quad-na-values 2001 4001 8001 \
  --ledger-cells 120 --top-cells 3
```

Output summary:

```text
quad_na   residual       exact_total    exact/residual
2001      0.35616692     0.68713098     1.92924
4001      0.31896772     0.75430745     2.36484
8001      0.29978030     0.79188448     2.64155
```

Mesh verdict:

```text
first_quad_na_covering_total_residual = 2001
last residual delta                   ~= 0.01919
last exact-total delta                ~= 0.03758
```

Interpretation: K=3.5 is mesh-stable enough for the current diagnostic level.
The next proof-grade work is not to chase cell residual ratios; it is to
replace the trapezoid continuum and sampled variation by certified interval
enclosures.

## Corrected Interpretation

The previous interval-envelope audit remains useful, but with this correction:

- `required_exact_multiplier_to_cover_cell_residual` is a priority score;
- it is not a local proof obligation;
- the real proof obligation is global Stieltjes coverage with certified
  `U_J`, `V_J`, and jumps;
- mesh stability must be checked before interpreting any cell worklist.

This reduces the immediate blocker.  K=3 no longer says the route is failing;
it says the proof engine must lock a single quadrature/interval convention.

## Verdict

`PARTIAL(mesh-stability gate added and K=3 false alarm downgraded)`.

`GAP(certified quadrature/variation envelope generator still missing)`.

`FATAL(treating cell residual ratios or low-resolution meshes as proof)`.

Track B remains active.  The next implementation step is to generate certified
interval enclosures for `V_J` on the K=3 shoulder cells, using the mesh-stable
global Stieltjes budget as the acceptance criterion.

Follow-up:

- `docs/trackB/b2b_finite_U_staircase_audit.md` removes the sampled dependency
  from the `U_J` side.  Since `psi(exp(a))-exp(a)` is strictly decreasing
  between prime-power jumps, each `U_J` is a finite max over endpoints and
  jump one-sided values.  The remaining proof-grade gap is therefore the
  `V_J` variation/quadrature envelope, not `U_J`.

## Proshka Audit Block

Claim:
K=3 is not a fatal obstruction to the CLV finite-ledger route.  The earlier
underbound at `quad_na=2001` disappears when the global Stieltjes budget is
tested on a finer mesh; `quad_na=4001` already covers the total residual.

Point of blockage:
The current mesh sweep is still diagnostic floating-point work.  The missing
proof object is a certified interval/quadrature enclosure for the global
Stieltjes budget, not a sampled mesh.

What was tried:
Added `clvmesh`, swept K=3 over `quad_na=2001,4001,8001,16001`, and swept
K=3.5 over `quad_na=2001,4001,8001`.

Minimal example:
At `K=3`, `ell=0.75`, `delta=0.5`, `quad_na=2001` gives
`exact/residual ~= 0.65653`; the same setup at `quad_na=4001` gives
`exact/residual ~= 1.00518`, and `quad_na=16001` gives `~1.83208`.

Question for Proshka:
Should the next theorem-producing generator certify the global Stieltjes
variation by interval arithmetic on `H_v`, or should we first derive a
closed-form variation envelope for `E_delta(a)F_v(a)` on the K=3 shoulder?
