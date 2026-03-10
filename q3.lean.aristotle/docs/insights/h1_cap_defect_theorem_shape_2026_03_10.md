# H1 cap-defect theorem shape (2026-03-10)

## Status

In-progress freeze for `H-bridge.9`.

This note does **not** rewrite the public stack
`H1^f -> H2^f -> H3^f -> H4^f`.
It freezes the honest working theorem-shape inside the `H1` brick after the
raw route `w_{rs}(a)=\kappa(a)q_{rs}` is structurally dead and after the
filtered classifier shows small-rank structure without pure low-mode support.

## Frozen working theorem-shape

The right live statement is no longer plain exact filtered equality.
Freeze instead:

`filtered kernel intertwining modulo joint finite-rank cap defect after the right joint basis / Gram projection`.

Working form:

```tex
M_{M,N_a}^{\sigma\tau}(a)
=
\kappa(a)\,\widetilde Q_{M,N_a}^{\sigma\tau}
+ U_{a,M}^{\sigma} K_a^{\sigma\tau} (U_{a,M}^{\tau})^*,
\qquad
(\sigma,\tau)\in\{(++),(+-)\},
```

with one shared finite-dimensional defect space `C_a`,
`U_{a,M}^{+},U_{a,M}^{-}` the synthesis maps from `C_a` into the positive and
negative filtered tails, and the remaining blocks recovered by Hermitian
symmetry:

```tex
M^{--}=\overline{M^{++}}^{\,T},
\qquad
M^{-+}=\overline{M^{+-}}^{\,T}.
```

Exact `H1^f` is now treated as the special case `dim C_a = 0`, not as the
default live expectation.

## Working conjecture

Freeze only `dim C_a < \infty` as the theorem-shape.

Use

```tex
\dim C_a \le 3
```

only as the current implementation target / conjectural specialization.
Do **not** promote `r_a=3` to a theorem fact yet.

## Gate split

- Gate A: prove
  `M=\kappa(a)\widetilde Q + F_{a,N}` with one joint finite-rank cap-type
  defect for `(++),(+-)`.
- Gate B: prove positivity of the augmented cap matrix
  `H_a^{aug}` obtained by adjoining that defect block to the Suzuki cap.

If Gate A and Gate B close, the route keeps the same public architecture and
the remaining work is just `H2^f -> H3^f -> H4^f`.

## Current evidence

- raw route is structurally false: Q3 raw entries are Toeplitz with constant
  diagonal, while the Suzuki raw entries in the `\chi_n[a]` basis have
  logarithmic diagonal growth;
- filtered residuals are strongly compatible with a small-rank correction and
  strongly incompatible with a pure low-mode-supported defect;
- canonical rank-`3` joint projector:
  `a=1.25, M=4, zeros=20` gives
  `proj_rel_resid ~7.88e-3` for `++` and `~1.10e-3` for `+-`;
- second real bulk-size run:
  `a=1.0, M=4, zeros=20` gives
  `~1.92e-2` for `++` and `~1.67e-3` for `+-`.

So the honest live label is:

`shared rank-3 defect candidate, worth freezing as the working cap-defect hypothesis`.

## Stability protocol

Run the checker in four numerical layers before any manuscript rewrite:

1. rank stability:
   inspect top singular values and the stable gap
   `sigma_{r+1} / sigma_r`;
2. subspace stability:
   compare principal angles of the joint shared basis across neighboring
   `(M, zeros, a)` runs;
3. same-space test across families:
   train one shared projector and measure
   `proj_rel_resid` on both `++` and `+-`;
4. `M`-consistency after embedding:
   embed the shared basis from size `M` into `M+1` and check whether the
   target residual is still well explained.

Augmented cap positivity is the next gate only after these four stability
checks stop looking noisy.

## Checker commands

Canonical single run:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py --a 1.25 --M 4 --B 0.2 --t 0.15 --zeros 20 --defect-rank 3
```

Rank/subspace stability grid:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py \
  --sweep \
  --sweep-a-values 0.8,1.0,1.25,1.5 \
  --sweep-M-values 4,5,6,7 \
  --sweep-zero-values 20,40,80 \
  --defect-rank 3
```

The checker now reports:

- `sigma_next/sigma_rank`;
- principal angles for cross-family and shared-basis comparisons;
- `proj_rel_resid` for the same-space test;
- embedded shared-basis transfer across neighboring runs.
