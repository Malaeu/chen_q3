# Track B B2b: Interval Envelope Audit

Status: RP4/B2 proof-contract audit.  This is not a proof of E5p, not a proof
of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_finite_chebyshev_ledger_probe.md`.  The
finite Chebyshev ledger localized the smooth Selberg correction, but it also
exposed the precise danger: sampled derivatives can underbound the true
bounded-variation contribution.  This audit turns that danger into a finite
certificate contract.

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
phi_v(x) = x^(-1/2) H_v(log x).
```

The ledger residual is:

```text
sum Lambda(n)n^(-1/2)H_v(log n) - integral exp(a/2)H_v(a) da
  = integral phi_v d(psi-x).
```

Jumps at `a=2K` and `a=4K` are part of `d phi_v`; they are not derivative
terms and must be certified separately.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: exact finite Chebyshev staircase
  `psi(x)=sum_{n<=x} Lambda(n)` on the finite range touched by the packet.
- `UNCONDITIONAL`: Stieltjes integration by parts for bounded-variation
  functions.
- `UNCONDITIONAL`: Fiori--Kadiri--Swidinsky explicit comparison bound for
  `|psi(x)-x|`, used only as a coarse baseline.
  Source: https://arxiv.org/abs/2204.02588
- `UNCONDITIONAL / finite-dimensional linear algebra`: eigenvectors and
  packet profiles in the Step13 packet model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for interval derivative envelopes, prime bucket
certificates, and Stieltjes prime-sum certificates returned:

- `FloorCert` / Lipschitz certificate patterns;
- PrimeCert closure notes and theorem-producing generator plans;
- finite bucket and endpoint-envelope infrastructure;
- RKHS prime-cap and prime-term bridge material.

The useful repo pattern is therefore:

```text
finite cells + endpoint envelopes + theorem-producing generator
```

not another global PNT estimate.

External primary-source search confirms the same allowed inputs: CLV/Selberg
majorants, Fiori--Kadiri--Swidinsky `psi` bounds, and classical
Riemann--Stieltjes integration by parts.  No conditional theorem was added.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvledger` now reports, for each cell:

```text
abs_direct_residual
exact_bound_over_abs_cell_residual
required_exact_multiplier_to_cover_cell_residual
sampled_exact_cell_underbound
sampled_exact_cell_deficit
```

and, for each eigen-direction:

```text
sampled_exact_underbound_cell_count
sampled_exact_cell_deficit_sum
sampled_exact_cell_bound_over_sum_abs_residuals
required_uniform_exact_multiplier_to_cover_sum_abs_cells
top_cells_by_required_exact_multiplier
top_cells_by_sampled_exact_deficit
```

The ratio fields are diagnostics only.  A huge required multiplier in a cell
with tiny deficit is lower priority than a moderate multiplier in a cell with
large absolute deficit.

## Proof-Grade Cell Contract

For a cell `J=[alpha,beta]` with no jump, define:

```text
U_J >= sup_{a in J} |psi(exp(a)) - exp(a)|,
V_J >= integral_J exp(-a/2) |H_v'(a) - H_v(a)/2| da.
```

Then the continuous part satisfies:

```text
|integral_J phi_v d(psi-x)| <= U_J * V_J
```

up to the standard endpoint terms at the boundary of the whole support:

```text
U(alpha_0)|phi_v(alpha_0)| + U(beta_0)|phi_v(beta_0)|.
```

For a cell containing a jump at `a0`, add:

```text
U(a0) * exp(-a0/2) * |Delta H_v(a0)|.
```

Thus a proof-grade finite certificate must produce, for every live cell:

```text
cell J,
exact prime-power list for psi on J,
certified U_J,
certified V_J,
certified jump term if J contains 2K or 4K,
cell budget contribution.
```

The derivative envelope `V_J` is the missing object.  It should be generated
from the explicit Vaaler functions and the finite B-spline packet profile,
using interval arithmetic or a theorem-producing polynomial/rational envelope.

## K = 3 Audit

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3 --ell 0.75 --schedule fixed \
  --receiver-delta 0.5 \
  --p0-na 201 --quad-na 2001 \
  --ledger-cells 80 --top-cells 5
```

Summary:

```text
ledger residual                         ~= -0.5212284378
sum_abs_cell_residuals                  ~= 1.5208709492
exact_total_with_endpoints              ~= 0.3422035773
exact_total / |ledger residual|         ~= 0.65653

sampled exact underbound cells          = 52 / 80
sampled exact cell deficit sum          ~= 1.2162598291
required uniform exact multiplier       ~= 4.44435
```

Top deficit cells:

```text
cell 39: [5.850, 6.000], left_edge_jump
  abs residual ~= 0.44824
  sampled exact bound ~= 0.09982
  deficit ~= 0.34842
  required multiplier ~= 4.49

cell 36: [5.400, 5.550]
  abs residual ~= 0.36867
  sampled exact bound ~= 0.02712
  deficit ~= 0.34155
  required multiplier ~= 13.59

cell 38: [5.700, 5.850]
  abs residual ~= 0.18382
  sampled exact bound ~= 0.02697
  deficit ~= 0.15684
  required multiplier ~= 6.81
```

Interpretation: K=3 is not a harmless numerical wrinkle.  The proof-grade
envelope must strengthen the left-endpoint shoulder and nearby pre-edge cells.

## K = 3.5 Audit

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
ledger residual                         ~= 0.3189677222
sum_abs_cell_residuals                  ~= 0.7560455443
exact_total_with_endpoints              ~= 0.7543074488
exact_total / |ledger residual|         ~= 2.36484

sampled exact underbound cells          = 70 / 120
sampled exact cell deficit sum          ~= 0.1945438521
required uniform exact multiplier       ~= 1.00231
```

Top deficit cells:

```text
cell 56: [6.417, 6.531]
  abs residual ~= 0.10518
  sampled exact bound ~= 0.01475
  deficit ~= 0.09043
  required multiplier ~= 7.13

cell 58: [6.646, 6.760]
  abs residual ~= 0.10144
  sampled exact bound ~= 0.06480
  deficit ~= 0.03664
  required multiplier ~= 1.57

cell 64: [7.333, 7.448]
  abs residual ~= 0.02337
  sampled exact bound ~= 0.00755
  deficit ~= 0.01582
  required multiplier ~= 3.10
```

Interpretation: K=3.5 is much closer globally, but local underbounds remain.
The largest-ratio cells are mostly tiny-tail artifacts; the actual certificate
worklist should be sorted by deficit, not by ratio alone.

## Mesh-Stability Correction

Follow-up:

- `docs/trackB/b2b_mesh_stability_audit.md` adds `clvmesh` and corrects the
  interpretation of cell residual ratios.  A cell residual is not required to
  be bounded by the cell's local variation integral alone, because internal
  endpoint terms cancel only at the global Stieltjes level.  The ratio fields
  above are priority scores for a future interval-envelope generator, not local
  proof obligations.
- The K=3 underbound at `quad_na=2001` is downgraded from route-danger to
  mesh/continuum-convention warning.  A sweep over
  `quad_na=2001,4001,8001,16001` shows first global coverage at `quad_na=4001`.
- `docs/trackB/b2b_finite_U_staircase_audit.md` then removes the sampled
  dependency from `U_J`: the Chebyshev staircase side is a finite max over
  endpoints and prime-power jump one-sided values.  The remaining live proof
  object is the certified `V_J` variation/quadrature envelope.

## Verdict

`PARTIAL(interval-envelope contract isolated; mesh-stability correction added)`.

`GAP(certified quadrature/derivative/variation envelope generator missing)`.

`FATAL(using sampled required multipliers as proof certificates)`.

Track B remains active.  The next implementation step is a theorem-producing
cell-envelope generator that emits certified `U_J`, `V_J`, and jump terms for
the deficit-priority cells.  If that generator cannot keep the K=3 left
endpoint shoulder under budget, the correct escalation is Proshka with the
minimal K=3 cell examples above.

## Proshka Audit Block

Claim:
The finite Chebyshev ledger can be reduced to a finite interval-envelope
certificate: each cell needs a certified `U_J` for `|psi(e^a)-e^a|`, a
certified variation envelope `V_J` for `H_v`, and explicit jump terms.

Point of blockage:
The current probe remains sampled.  K=3 requires a uniform sampled-envelope
multiplier of about `4.44` over the sum of absolute cell residuals, and its
largest deficits sit near the left endpoint shoulder `[5.4,6.0]`.

What was tried:
Extended `clvledger` with cellwise required multipliers, underbound flags, and
deficit-priority worklists; reran K=3 and K=3.5 audits.

Minimal example:
At `K=3`, `ell=0.75`, `delta=0.5`, `ledger_cells=80`, cell 39
`[5.850,6.000]` contains the `left_edge_jump`, has abs residual `~0.44824`,
sampled exact bound `~0.09982`, and needs multiplier `~4.49`.  Cell 36
`[5.400,5.550]` has abs residual `~0.36867`, sampled exact bound `~0.02712`,
and needs multiplier `~13.59`.

Question for Proshka:
Should the next proof object be a theorem-producing interval arithmetic
generator for `V_J`, or is there an analytic endpoint-shoulder cancellation
identity for the K=3 cells that would avoid finite envelope work?
