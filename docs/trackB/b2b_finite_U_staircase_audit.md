# Track B B2b: Finite Chebyshev `U_J` Staircase Audit

Status: RP4/B2 diagnostic and proof-contract refinement.  This is not a proof
of E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_mesh_stability_audit.md`.  The mesh audit
showed that the global Stieltjes budget is the right acceptance criterion.
The next improvement is to remove one sampled ingredient entirely:

```text
U_J >= sup_{a in J} |psi(exp(a)) - exp(a)|.
```

For the finite packet range, `U_J` can be computed from a finite Chebyshev
staircase candidate list, not from a mesh.

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

Chebyshev staircase on the finite packet range:

```text
psi(exp(a)) = sum_{r log p <= a} Lambda(p^r)
            = sum_{r log p <= a} log p.
```

This matches the script's prime-power shifts:

```text
shift a = r log p,
shift weight in prime matrix = log(p) exp(-a/2),
Chebyshev jump size = shift_weight * exp(a/2) = log(p).
```

## Allowed Inputs

- `UNCONDITIONAL`: exact finite definition of the Chebyshev staircase
  `psi(x)=sum_{n<=x} Lambda(n)` on a bounded range.
- `UNCONDITIONAL`: elementary monotonicity.  Between jumps,
  `psi(exp(a))-exp(a)` has derivative `-exp(a) < 0`.
- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Stieltjes integration by parts for bounded-variation
  functions.
- `UNCONDITIONAL / finite-dimensional linear algebra`: packet eigenvectors
  and finite B-spline profiles in the Step13 model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Finite `U_J` Lemma Shape

Let the shifts inside a cell `J=[alpha,beta]` be:

```text
alpha <= a_1 <= ... <= a_m <= beta.
```

Write

```text
E(a) = psi(exp(a)) - exp(a).
```

On every open interval with no shift, `E'(a)=-exp(a)`, so `E` is strictly
decreasing.  Therefore `|E|` reaches its supremum on `J` at:

```text
alpha left/right value,
beta left/right value,
each jump left-limit E(a_i^-),
each jump right-value E(a_i).
```

Thus `U_J` is a finite maximum.  This removes a sampled dependency from the
future certificate.  In Lean terms, this should become a finite-list max
certificate over endpoints and prime-power jumps.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvledger` now reports, for each cell:

```text
finite_sup_abs_psi_minus_x
finite_sup_location
finite_sup_side
finite_sup_candidate_count
finite_jump_count
finiteU_continuous_variation_bound
finiteU_with_exact_jumps_bound
finiteU_conservative_total_variation_bound
finiteU_over_grid_sup_abs_psi_minus_x
```

and, for each direction:

```text
finiteU_with_exact_jumps_bound
finiteU_bound_over_abs_residual
finiteU_bound_over_exact_grid_bound
finiteU_underbound_cell_count
finiteU_cell_deficit_sum
top_cells_by_finiteU_bound
top_cells_by_finiteU_deficit
```

`clvmesh` carries the finite-`U_J` global fields as well.

Important: `finiteU_with_exact_jumps_bound` still uses sampled variation for
`V_J`.  The `U_J` side is finite-staircase exact in shape; the `V_J` side is
still diagnostic.

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
ledger residual                         ~= -0.3170596346
exact-grid global bound                 ~= 0.3187032966
exact-grid / |residual|                 ~= 1.00518

finite-U global bound                   ~= 0.9463133666
finite-U / |residual|                   ~= 2.98465
finite-U / exact-grid bound             ~= 2.96926

finite-U underbound cells               = 30
finite-U local deficit sum              ~= 0.63444
```

Top finite-`U` bound cells:

```text
cell 39: [5.850, 6.000], left_edge_jump
  finite U_J ~= 7.37848
  finite-U bound ~= 0.31487

cell 36: [5.400, 5.550]
  finite U_J ~= 11.50229
  finite-U bound ~= 0.09100

cell 35: [5.250, 5.400]
  finite U_J ~= 9.90870
  finite-U bound ~= 0.09013
```

Interpretation: after replacing sampled `U_J` by finite-staircase `U_J`, K=3
has comfortable global diagnostic coverage at `quad_na=4001`, but the bound is
about `3x` larger than the weighted exact-grid budget.  This is the price of a
certificate-shaped sup bound.

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
ledger residual                         ~= 0.3189677222
exact-grid global bound                 ~= 0.7543074488
exact-grid / |residual|                 ~= 2.36484

finite-U global bound                   ~= 1.5347151960
finite-U / |residual|                   ~= 4.81151
finite-U / exact-grid bound             ~= 2.03460

finite-U underbound cells               = 40
finite-U local deficit sum              ~= 0.07817
```

Top finite-`U` bound cells:

```text
cell 61: [6.990, 7.104], left_edge_jump
  finite U_J ~= 14.78576
  finite-U bound ~= 0.62632

cell 59: [6.760, 6.875]
  finite U_J ~= 12.48670
  finite-U bound ~= 0.19368

cell 58: [6.646, 6.760]
  finite U_J ~= 16.27098
  finite-U bound ~= 0.19002
```

Interpretation: K=3.5 stays safe under finite `U_J`.  The dominant work is
again the left endpoint shoulder.  Local finite-U deficits remain worklist
heuristics, not proof failures.

## Corrected Proof Contract

The finite Chebyshev side can now be split:

```text
U_J: finite staircase max over endpoints and jump one-sided values.
V_J: certified variation/quadrature envelope for
     exp(-a/2)|H_v'(a)-H_v(a)/2|.
jumps: exact finite terms U(a0)exp(-a0/2)|Delta H_v(a0)|.
```

Therefore the remaining proof-grade blocker is no longer `U_J`.  It is the
`V_J` envelope and the continuum quadrature convention for `H_v`.

## Verdict

`PARTIAL(finite Chebyshev U_J extracted)`.

`GAP(certified V_J variation/quadrature envelope still missing)`.

`FATAL(treating finite-U plus sampled-V as a proof certificate)`.

Track B remains active.  The next implementation step is a theorem-producing
`V_J` envelope generator for the same cells, preferably starting with K=3
cells `35,36,39` and K=3.5 cells `58,59,61`.

Follow-up:

- `docs/trackB/b2b_V_variation_shape_audit.md` adds sampled `V_J` shape
  diagnostics: continuous variation, jump variation, and sign-change worklists
  for `H_v'(a)-H_v(a)/2`.  It keeps the same blocker status: sampled signs are
  not certificates, but the live `V_J` work is now localized to endpoint
  shoulder cells.
- `docs/trackB/b2b_sign_partition_audit.md` refines that blocker: non-jump
  shoulder cells are numerically close to endpoint-exact after sampled
  sign partitions, while edge-jump cells must be split before theorem
  production.

## Proshka Audit Block

Claim:
The `U_J` side of the finite Stieltjes ledger can be made exact by a finite
Chebyshev staircase max over endpoints and jump one-sided values.  The
remaining missing proof object is `V_J`, not `U_J`.

Point of blockage:
`finiteU_with_exact_jumps_bound` still multiplies exact finite `U_J` by
sampled variation.  This is not a certificate until `V_J` is interval- or
theorem-bounded.

What was tried:
Added finite Chebyshev staircase helpers to `clvledger`; reran K=3 and K=3.5
at the mesh-stable quadrature choices.

Minimal example:
At K=3, `quad_na=4001`, the exact-grid global bound barely covers the residual
(`~1.00518x`), while finite `U_J` gives `~2.98465x`.  The largest finite-U
cell is cell 39 `[5.850,6.000]`, containing `left_edge_jump`, with
`U_J ~= 7.37848` and finite-U bound `~0.31487`.

Question for Proshka:
Should `V_J` be certified by interval arithmetic over the explicit Vaaler and
B-spline formulas, or can the endpoint shoulder variation be bounded by a
closed-form monotonicity/total-variation identity?
