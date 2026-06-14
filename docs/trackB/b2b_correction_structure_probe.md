# Track B B2b: Selberg Correction Structure Probe

Status: RP4/B2 diagnostic.  This is not a proof of E5p, not a proof of RH,
and not a Lean proof file.

This note follows `docs/trackB/b2b_correction_anatomy.md`.  The previous note
showed that the Selberg receiver correction

```text
B_R = (P(M^+) - P(1_I)) - (P0(M^+) - P0(1_I))
```

has endpoint-halo ordinary-prime structure on the prime side, while the
continuum side often carries most of the absolute Rayleigh budget.  This note
checks the next possible RP4 shortcut:

```text
Is B_R essentially a low-rank or row/column boundary operator?
```

If yes, the old PO3a row/column reduction style could be a theorem template.
If no, the route must prove a smooth prime-continuum quadrature theorem for
the whole receiver correction.

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

All finite probes below are in raw `a` coordinates using the Step13 raw prime
weights.  No Q3 evenization factor is silently inserted.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV receiver formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: explicit-formula linearity for the selected test function.
  This imports no RH positivity.
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected generalized
  eigenvalue, spectral-rank, and row/column diagnostics on the current packet
  `kerQ`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

External refresh:

- Toeplitz/Hankel/commutator literature confirms that boundary terms can have
  finite-rank or structured finite-section shadows in special settings, but it
  does not provide a Track B theorem for this Selberg correction.
- Explicit PNT/Chebyshev-error literature gives unconditional smooth-prime-sum
  ingredients to inspect later, e.g. Fiori--Kadiri--Swidinsky on explicit
  `psi(x)-x` bounds.  Source: https://arxiv.org/abs/2204.02588

## Local Search Synthesis

Local `q3_docs` searches for:

```text
matched endpoint continuum cancellation commutator Toeplitz Hankel boundary cap prime cone
rank low endpoint boundary correction compact support prime matrix continuum bulk cancellation
Selberg correction Mplus chi interval P0 endpoint continuum matrix cone cancellation
```

returned:

- `H1 boundary/cap reset`: boundary/cap corrections can look like moving
  Toeplitz-Hankel / commutator / near-edge defects.
- `PO3` cross-sign boundary cancellation and `PO3a` row-column reduction:
  if the boundary correction matrix is supported on finitely many rows and
  columns in a sign-adapted basis, it can be reduced to a finite row/column
  object.
- target-cone and prime-cap notes: the cone remains structured
  autocorrelation/positive-definite data, not arbitrary coefficients.

No local theorem states that this Selberg correction has the finite row/column
support needed by the PO3a shortcut.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvstructure \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 --p0-na 401 \
  --top-eigs 6 --top-rows 8
```

The new `clvstructure` mode builds operator-level pieces:

```text
P_corr  = P(M^+)  - P(1_I)
C_corr  = P0(M^+) - P0(1_I)
B_R     = P_corr - C_corr
```

and reports:

- spectral summaries of `P_corr`, `C_corr`, and `B_R`;
- endpoint / bulk / far signed correction summaries;
- cancellation ratios such as
  `||B_R|| / (||P_corr|| + ||C_corr||)`;
- low-rank indicators from the eigenvalue distribution;
- row/column concentration in the standardized projected `kerQ` basis.

The continuum side uses the same D2 two-grid convention as the matrix
construction:

```text
P0(M^+) uses a full [0,max_a] quadrature grid.
P0(1_I) uses the dedicated interval grid [2K,4K].
```

## K = 3.5 Detailed Operator Structure

At:

```text
K = 3.5,
ell = 1.375,
delta = 1,
I_K = [7, 14],
p0_na = 401,
kerQ_dim = 21,
```

the prime/continuum totals are large but almost cancel:

```text
||P_corr||_G      ~= 12.5346257301
||C_corr||_G      ~= 12.3336139897
||B_R||_G         ~= 0.2381603793

||B_R|| / (||P_corr|| + ||C_corr||) ~= 0.00958
Frobenius analogue                  ~= 0.01187
```

This is the important positive signal: the correction is not just a hard-edge
norm of size `0.238`; it is the small remainder after a very strong
prime-continuum match for the smooth Selberg receiver error.

Endpoint/bulk/far split:

```text
endpoint correction opnorm ~= 0.9193568883
bulk correction opnorm     ~= 0.7679551738
far correction opnorm      ~= 0.0028622557
total correction opnorm    ~= 0.2381603793

total / (endpoint + bulk + far) ~= 0.14091
```

So endpoint and bulk pieces cancel each other substantially.  Paying endpoint
and bulk separately is the wrong theorem shape.

Spectral-rank check:

```text
effective_rank_fro(B_R) ~= 15.31   out of kerQ_dim = 21
top abs eigenvalue fraction ~= 0.07316
top Frobenius eigenvalue fraction ~= 0.08197
```

This is not a low-rank boundary operator.

Row/column concentration in the standardized projected `kerQ` basis:

```text
top 1 row/column union captures ~= 0.14633 of Frobenius mass
top 2 row/column union captures ~= 0.28815
top 4 row/column union captures ~= 0.56067
top 8 row/column union captures ~= 0.94838

top 8 principal block captures only ~= 0.15485
```

This is a row/column-star pattern, not a small principal block.  It is also not
fixed finite rank: at this scale one needs a substantial fraction of the
projected basis to capture the mass.

## Four-K Compact Schedule

Using the same stable packet widths and receiver bandwidths as the previous
Track B schedule, with `p0_na=201`:

```text
K=2.0, ell=0.75, delta=0.5:
  ||B_R||_G ~= 0.1019538109
  ||B_R|| / (||P_corr||+||C_corr||) ~= 0.01464
  endpoint/bulk/far split ratio ~= 0.9455
  effective_rank_fro ~= 9.79 of kerQ_dim=12
  top 8 row/column union captures ~= 0.96625

K=2.5, ell=1.375, delta=1.0:
  ||B_R||_G ~= 0.4197486858
  ||B_R|| / (||P_corr||+||C_corr||) ~= 0.05711
  endpoint/bulk/far split ratio ~= 0.6694
  effective_rank_fro ~= 8.23 of kerQ_dim=13
  top 8 row/column union captures ~= 0.99514

K=3.0, ell=0.75, delta=0.5:
  ||B_R||_G ~= 0.1127822731
  ||B_R|| / (||P_corr||+||C_corr||) ~= 0.00478
  endpoint/bulk/far split ratio ~= 0.02307
  effective_rank_fro ~= 17.32 of kerQ_dim=20
  top 8 row/column union captures ~= 0.85542

K=3.5, ell=1.375, delta=1.0:
  ||B_R||_G ~= 0.2364908844
  ||B_R|| / (||P_corr||+||C_corr||) ~= 0.00951
  endpoint/bulk/far split ratio ~= 0.1592
  effective_rank_fro ~= 15.32 of kerQ_dim=21
  top 8 row/column union captures ~= 0.94668
```

The prime-continuum cancellation is consistent and strong.  The low-rank story
is not.

## Interpretation

This probe changes the RP4 target.

Positive result:

```text
P_corr and C_corr match extremely well as operators.
```

That means the right theorem is probably a smooth prime-continuum quadrature
estimate for the Selberg correction weight:

```text
E_delta(a) = M^+_{[2K,4K],delta}(a) - 1_[2K,4K](a),

| sum_{p,r} log(p)/p^(r/2) * E_delta(r log p) * F_v(r log p)
  - integral e^(a/2) * E_delta(a) * F_v(a) da |
  <= epsilon_K * <v,Gv>.
```

Here `F_v` must keep the Q3 cross-correlation structure.  This is a real
mathematical theorem target, not a scalar bridge.

Negative result:

```text
B_R is not low-rank in the current standardized projected basis.
```

So the simple PO3a-style finite row/column shortcut is not justified by the
current packet diagnostics.  A theorem that pays only a few endpoint rows or a
fixed-rank boundary block would be proving the wrong object.

Second negative result:

```text
endpoint and bulk correction pieces cancel each other.
```

Therefore an endpoint-only estimate, even if true, is too crude unless it is
paired with the matching continuum/bulk piece.  The theorem should keep the
whole smooth receiver error together.

## Verdict

`PARTIAL(matched prime-continuum cancellation observed)`.

`GAP(smooth structured quadrature theorem for E_delta * F_v missing)`.

`FATAL(simple fixed-rank / few-row boundary shortcut in the current basis)`.

This is not fatal for Track B.  It points to the next live theorem shape:
an unconditional smooth weighted prime-sum theorem for the structured
cross-correlation family, likely using a Chebyshev/PNT error term plus explicit
variation/derivative control of `E_delta(a) * F_v(a)`.

Follow-up:

- `docs/trackB/b2b_smooth_quadrature_probe.md` tests this partial-summation
  route.  The theorem shape matches the correction: empirical `psi-x`
  variation bounds are within a small constant factor of the observed residual.
  However, the off-the-shelf explicit PNT bound is hundreds to thousands of
  times too large on the tested small-K schedule, so plain global
  Chebyshev-error plus total variation is not a B3 closure route.

## Proshka Audit Block

Claim:
For the Selberg receiver correction `B_R`, the large prime correction
`P_corr = P(M^+) - P(1_I)` and continuum correction
`C_corr = P0(M^+) - P0(1_I)` match very closely as projected operators.
At `K=3.5`, `||P_corr||_G ~= 12.53`, `||C_corr||_G ~= 12.33`, but
`||B_R||_G ~= 0.238`, so the ratio is about `0.96%`.

Point of blockage:
The remainder is not low-rank: effective Frobenius rank is about `15.3` in a
`21`-dimensional projected space, and the top absolute eigenvalue carries only
about `7.3%` of nuclear mass.  Row/column union capture is visible, but not as
a fixed finite-rank principal block.

What was tried:
Added `scripts/trackb_edge_operator_probe.py clvstructure`; decomposed
`B_R` into prime/continuum, endpoint/bulk/far, spectral rank, and row/column
capture; ran detailed `K=3.5` and compact `K=2,2.5,3,3.5` schedules.

Minimal example:
At `K=3.5`, `ell=1.375`, `delta=1`, `p0_na=401`, `kerQ_dim=21`,
`||B_R||/(||P_corr||+||C_corr||) ~= 0.00958`, but
`effective_rank_fro(B_R) ~= 15.31`.  Endpoint correction opnorm is about
`0.919`, bulk correction opnorm about `0.768`, while total correction opnorm
is only `0.238`, so endpoint and bulk must be kept together.

Question for Proshka:
Can we turn this into an unconditional smooth quadrature theorem for
`E_delta(a) * F_v(a)` using Chebyshev/PNT error plus explicit derivative
control on the Q3 cross-correlation family, or is there a better basis in which
the row/column-star pattern becomes a theorem-level finite boundary operator?
