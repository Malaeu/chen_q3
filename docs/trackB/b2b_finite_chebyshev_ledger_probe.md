# Track B B2b: Finite Chebyshev Ledger Probe

Status: RP4/B2 diagnostic.  This is not a proof of E5p, not a proof of RH,
and not a Lean proof file.

This note follows `docs/trackB/b2b_fourier_psd_probe.md`.  At this point the
simple routes are known not to close E5p:

- global explicit PNT error plus total variation is too large;
- direct zero-side PSD fails because `E_delta*F_v` is Fourier-sign-changing.

The remaining nonconditional route is a finite Chebyshev staircase ledger for
the smooth correction:

```text
integral phi_v(x) d(psi(x)-x),
phi_v(x)=x^(-1/2) E_delta(log x) F_v(log x).
```

This probe asks whether such a ledger is small and localized enough to become
a certified interval theorem.

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

The correction weight is:

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a).
```

Important: `E_delta` has jumps at `a=2K` and `a=4K`, because of the hard
indicator.  A real ledger must account for these jumps explicitly; they cannot
be hidden inside a sampled derivative.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV receiver formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: exact finite Chebyshev staircase
  `psi(x)=sum_{n<=x} Lambda(n)` on a bounded range.
- `UNCONDITIONAL`: Stieltjes partial summation / integration by parts for
  bounded-variation test functions.
- `UNCONDITIONAL`: explicit Chebyshev/PNT bounds are still available as a
  comparison baseline.  Source: https://arxiv.org/abs/2204.02588
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected correction
  eigenvectors and packet profiles in the current Step13 packet model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Local Search Synthesis

Local `q3_docs` searches for:

```text
finite Chebyshev staircase ledger psi-x interval envelope prime bucket certificate
prime_heat_bucket interval endpoint envelope vonMangoldt Chebyshev psi certificate
Stieltjes partial summation bounded variation Chebyshev function prime term Lean
```

returned:

- PrimeCert and bucket-envelope infrastructure;
- older plans for theorem-producing prime-sum bucket generators;
- `Q_Lipschitz` / prime-term bridge material;
- RKHS prime-cap finite/integral domination notes.

This confirms that the repo already has a nearby formal style: finite buckets,
endpoint envelopes, and theorem-producing generators.  It does not provide the
specific smooth correction ledger for `E_delta*F_v`.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvledger \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 \
  --p0-na 401 --quad-na 4001 \
  --ledger-cells 120 --top-cells 8
```

The mode:

1. builds the opnorm correction eigenvector;
2. forms `H(a)=E_delta(a)F_v(a)`;
3. splits raw `a in [0,max_a]` into finitely many ledger cells;
4. computes cellwise prime-minus-continuum residuals;
5. computes an exact-grid `psi-x` variation ledger;
6. adds explicit jump contributions at `a=2K` and `a=4K`;
7. reports top cells by bound and by actual residual.

This is a diagnostic.  It samples derivatives on a grid, so it is not yet a
certificate.  A proof-grade version needs interval derivative envelopes for
`H` and certified sup/variation bounds per cell.

## K = 3.5 Detailed Result

At:

```text
K = 3.5,
ell = 1.375,
delta = 1,
p0_na = 401,
quad_na = 4001,
ledger_cells = 120,
```

the opnorm direction reports:

```text
matrix correction opnorm             ~= 0.2381603793
ledger direct residual               ~= 0.3189677222
matrix / ledger mismatch             ~= 0.0808073429

exact-grid ledger bound with jumps   ~= 0.7543074488
exact bound / |ledger residual|      ~= 2.36484

explicit-PNT ledger bound            ~= 1013.8781534
explicit-PNT / |ledger residual|     ~= 3178.62

sum_abs_cell_residuals               ~= 0.7560455443
|total| / sum_abs_cells              ~= 0.42189
```

The matrix/ledger mismatch is expected at this diagnostic level: the matrix
uses the `P0` quadrature convention selected by `p0_na`, while the ledger uses
its own `quad_na` continuum grid and cell decomposition.  A certificate must
choose one convention and interval-bound it.

Localization:

```text
cells needed for 50% of exact bound: 1 / 120
cells needed for 80% of exact bound: 5 / 120
cells needed for 95% of exact bound: 14 / 120

cells needed for 50% of abs residual: 2 / 120
cells needed for 80% of abs residual: 5 / 120
cells needed for 95% of abs residual: 17 / 120
```

Top exact-bound cell:

```text
cell 61: a in [6.990, 7.104]
exact-grid bound ~= 0.4061
jump contribution ~= 0.1526
jump label = left_edge_jump
prime shifts in cell = 19
```

Top residual cell:

```text
cell 61: a in [6.990, 7.104]
direct residual ~= 0.3406
jump label = left_edge_jump
prime shifts in cell = 19
```

This is the first genuinely encouraging ledger signal: at K=3.5 the smooth
correction ledger is mostly a small endpoint neighborhood near `a=2K`.

## Four-K Compact Schedule

Using `p0_na=201`, `quad_na=2001`, `ledger_cells=80`:

```text
K=2.0, ell=0.75, delta=0.5:
  matrix opnorm ~= 0.101954
  ledger residual ~= 0.137715
  exact-grid ledger bound ~= 0.838497
  exact/residual ~= 6.089
  PNT/residual ~= 828.1
  cells for 95% exact bound ~= 34 / 80
  cells for 95% abs residual ~= 29 / 80

K=2.5, ell=1.375, delta=1.0:
  matrix opnorm ~= 0.419749
  ledger residual ~= -0.327445
  exact-grid ledger bound ~= 1.34234
  exact/residual ~= 4.099
  PNT/residual ~= 725.3
  cells for 95% exact bound ~= 9 / 80
  cells for 95% abs residual ~= 12 / 80

K=3.0, ell=0.75, delta=0.5:
  matrix opnorm ~= 0.112782
  ledger residual ~= -0.521228
  exact-grid ledger bound ~= 0.342204
  exact/residual ~= 0.6565
  PNT/residual ~= 790.4
  cells for 95% exact bound ~= 38 / 80
  cells for 95% abs residual ~= 21 / 80

K=3.5, ell=1.375, delta=1.0:
  matrix opnorm ~= 0.236491
  ledger residual ~= 0.180335
  exact-grid ledger bound ~= 0.682385
  exact/residual ~= 3.784
  PNT/residual ~= 5558
  cells for 95% exact bound ~= 11 / 80
  cells for 95% abs residual ~= 12 / 80
```

The K=3 line is the warning: the sampled derivative ledger can underbound the
observed residual.  Therefore the current `clvledger` output is not a
certificate and should not be treated as a proof.  It is a worklist generator
for interval cells and jump terms.

Follow-up:

- `docs/trackB/b2b_interval_envelope_audit.md` upgrades this warning into a
  finite certificate contract.  `clvledger` now reports cellwise required
  multipliers, underbound flags, and deficit-priority worklists.  The first
  hard target is the K=3 left-endpoint shoulder, where sampled bounds need a
  roughly `4.44x` uniform safety factor over the sum of absolute cell
  residuals.
- `docs/trackB/b2b_mesh_stability_audit.md` corrects the proof interpretation:
  cell residual ratios are worklist heuristics, while the global Stieltjes
  budget is the proof criterion.  The K=3 underbound at `quad_na=2001` is
  downgraded to a mesh/continuum-convention warning; `quad_na=4001` already
  gives global coverage.

## Interpretation

Positive signal:

- the finite ledger is often localized, especially at K=2.5 and K=3.5;
- the leading cells are exactly where the previous anatomy predicted:
  near the left endpoint `a=2K`;
- jump accounting matters and is now explicit.

Negative signal:

- the current sampled derivative estimate is not proof-safe;
- K=3 shows underestimation, so interval envelopes are mandatory;
- global PNT remains far too large even after localization.

What this route would need:

```text
For each ledger cell J:
  certified sup bound on |psi(e^a)-e^a| over J,
  certified variation / derivative envelope for H(a),
  explicit jump contribution if J contains 2K or 4K,
  cellwise residual budget in the mu-ledger normalization.
```

This is much smaller than proving all raw edge chunks, but it is still a
finite certified computation route unless a new analytic cancellation theorem
appears.

## Verdict

`PARTIAL(finite Chebyshev ledger localizes the smooth correction)`.

`GAP(interval-certified derivative/variation envelopes missing)`.

`FATAL(sampled clvledger output as proof certificate)`.

Track B remains active.  The next proof-grade step is not another global
estimate; it is a cell-envelope generator for the finite smooth correction
ledger, or a Proshka theorem shape that replaces this finite ledger by a
closed-form cancellation identity.

## Proshka Audit Block

Claim:
The finite `psi-x` staircase ledger is structurally plausible for the smooth
Selberg correction.  At K=3.5, 95% of the exact-grid bound is captured by
14/120 cells, and the top cell is the left endpoint jump cell near `a=2K`.

Point of blockage:
The current probe is sampled, not certified.  On the compact K schedule, K=3
already shows underestimation (`exact/residual ~= 0.6565`), so proof-grade
interval derivative envelopes are missing.

What was tried:
Added `scripts/trackb_edge_operator_probe.py clvledger`; included explicit
jump contributions at `a=2K` and `a=4K`; ran detailed K=3.5 and compact
K=2,2.5,3,3.5 schedules.

Minimal example:
At `K=3.5`, `ell=1.375`, `delta=1`, `ledger_cells=120`, the opnorm direction
has ledger residual `~0.31897`, exact-grid jump-aware ledger bound `~0.75431`,
and 95% of the bound lies in 14 cells.  The largest cell is
`[6.990,7.104]`, contains the `left_edge_jump`, and has exact-grid bound
`~0.4061`.

Question for Proshka:
Should we build a theorem-producing interval-envelope generator for these
finite Chebyshev ledger cells, or is there a closed-form endpoint cancellation
identity that would avoid certified cell work?
