# Goal 058 G3 — DLMF 30.16 even-count crosswalk source packet

Date: `2026-08-14`

Status: `SOURCE_PACKET_READY_FOR_PROSHKA_REVIEW_LEAN_HEAD_NOT_READY`

Boundary: source acquisition, convention lock, and import-contract synthesis
only. This packet proves no Lean theorem, supplies no endpoint count, creates no
classical-spectrum object, closes neither G1 nor G3, authorizes no Aristotle
job, promotes no route, and makes no RH claim.

## Binding origin

Proshka accepted the exact finite-to-literal negative-count transport and set
the next bounded leaf to this packet. Her remaining stop was:

```text
SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING
```

The accepted kernel-checked transport is:

```lean
mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
```

It transports an eventual finite count to the literal fixed-carrier Schur
count at a fixed nonsingular endpoint. It does not identify that finite count
with a classical PSWF index or provide the numerical counts `2` and `3`.

## Knowledge preflight receipt

Before writing this packet, the exact queries

```text
./orchestrator/kb.py ask 'Goal058 G3 DLMF 30.16 ordered finite eigenvalues alpha p d negative count crosswalk'
./orchestrator/kb.py ask 'mode4ActualFiniteJacobiTruncation DLMF positive diagonal similarity reversal offset zero'
```

both exited `1` with `no hits`. The packet therefore records a new
source-to-repo convention crosswalk rather than relabeling an indexed result.

## Review inputs

- Proshka verdict:
  `proshka/PROSHKA_VERDICT_GOAL058_G3_FINITE_TO_LITERAL_NEGATIVE_COUNT_2026-08-14.md`.
- Existing broad source packet:
  `GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`.
- Existing exact PSWF index packet:
  `GOAL058_G3_PSWF_INDEX_SOURCE_PIN_PACKET_2026-08-14.md`.
- Exact external-source lock: `D0_3F_EXTERNAL_SOURCE_LOCK.json`.
- Mythos hostile audit:
  `GOAL058_G3_DLMF_3016_EVEN_COUNT_CROSSWALK_MYTHOS_VERDICT_2026-08-14.md`.

Mythos independently fetched the five linked repository artifacts, checked
the live DLMF pages and official TeX endpoints, and found one load-bearing
unit bug in the broad packet: shifting the DLMF `lambda`-matrix by
`Lambda + G` is wrong unless the matrix was first explicitly rewritten into
`chi`-units. This packet replaces that sentence with the exact two-unit ledger
below.

## Primary-source locks

### DLMF

NIST DLMF version `1.2.7`, release `2026-06-15`, checked on `2026-08-14`:

- <https://dlmf.nist.gov/30.2> — differential equation and spectral parameter;
- <https://dlmf.nist.gov/30.3> — eigenvalue ordering and the zero-coupling
  anchor at `gamma^2 = 0`;
- <https://dlmf.nist.gov/30.4> — parity and interior-zero indexing;
- <https://dlmf.nist.gov/30.8> — Ferrers coefficient recurrence;
- <https://dlmf.nist.gov/30.16> — finite tridiagonal approximants and their
  limits.

Official DLMF 30.16 TeX endpoint SHA-256 pins, rechecked against the live
endpoints in the Mythos audit:

```text
5ded12f503ce3a658a73687976926264d51aae185838993f0bc27b9cd1326f22  30.16.E1a.tex
146c9d584200e12850b5bfa7cb2fea7b2e515aa63993080730da31070141506a  30.16.E1b.tex
d194f48cbc8f81930dbf9546864a5e2041307f21024093a33a7091d40feffb5e  30.16.E1c.tex
c0e5f1b968b4bcb1b61a6d72dcb739f6b8228c3934987b992595bc4168854cbd  30.16.E2.tex
35b0b61b184dd56ecd3b17a20de6f9e13f00533b56fbfa0b4a6e544820629e4d  30.16.E3.tex
76e0d10814b5793154042604984c77f26c1b94408ec299290154b71c0f6d9524  30.16.E4.tex
c0f3812292eb10516d92e9d2dcfa9ff162df7a87acb9fd9f84249de01f25e1a5  30.16.E7.tex
9457aa9ba839c63ba3bd4dfbd370947e79b83a14e7ef0172d28f88ee60a4b05c  30.16.E8.tex
87b58c2c8add1d9b80681f6447f605d27b5f1dda1467f35172491c289dcfe383  30.16.E9.tex
```

Equation 30.16.4 is pinned only as an exclusion: it is a constant-free
big-`O` statement and is neither needed nor suitable as a certified numerical
bound. Equations 30.16.7--30.16.9 remain reserved for the heavier indexed-row
route and are not imported by the count route.

### Local primary PDFs

1. Osipov, Yale TR-1450, `docs/routeB_bus/litreview/pdfs/TR1450.pdf`,
   SHA-256
   `98f4aa8448d8b09fe5982361d2c489bfb41e592acc6695251c9939bd7a4fce57`,
   physical pages 4--5, Theorems 1 and 3.
2. Bonami--Karoui, arXiv:1405.3676v2,
   `docs/routeB_bus/litreview/pdfs/1405.3676.pdf`, SHA-256
   `9fe8dc39e4440200a29ff94bb640b693c06a176d28b7e38a468dce98afa7d7b8`,
   physical pages 1, 3, and 5.
3. Katsnelson, arXiv:1603.07542v1, locked by
   `D0_3F_EXTERNAL_SOURCE_LOCK.json`; lock SHA-256
   `6822e3e5b254bb0280262020ab2cd2d3bcc57b1f0453b560144a13bbae2b7919`.

These sources pin the ordered regular prolate family, its parity and zero
index, and the exact project ODE crosswalk. They do not state the negative
count of the project's exact-tail Schur matrix.

## Exact DLMF 30.16 semantics

For even `n-m`, 30.16.1 constructs a `d x d` tridiagonal matrix whose rows are
one-based `j = 1, ..., d`. Its entries are

```text
A[j,j] = (m+2j-2)(m+2j-1)
         - 2 gamma^2 ((m+2j-2)(m+2j-1)-1+m^2)
           / ((2m+4j-5)(2m+4j-1)),

A[j,j+1] = -gamma^2 (2m+2j-1)(2m+2j)
             / ((2m+4j-1)(2m+4j+1)),

A[j,j-1] = -gamma^2 (2j-3)(2j-2)
             / ((2m+4j-7)(2m+4j-5)).
```

For `m=0`, row `j=q+1` is exactly the even Legendre degree `2q`. The
left-lower entry at `j=1` vanishes because `(2j-3)(2j-2)=0`; the finite matrix
therefore starts at degree zero without an omitted lower coordinate.

The raw matrix is generally nonsymmetric. For `gamma^2 > 0`, matching upper
and lower off-diagonal entries are both negative and have positive product.
Consequently a positive diagonal similarity symmetrizes it. With a consistent
choice of positive diagonal `D`, the ratio is fixed entrywise by

```text
D[j+1,j+1] / D[j,j] = sqrt(A[j+1,j] / A[j,j+1]).
```

This is a similarity `D⁻¹ A D`, hence it preserves eigenvalues. It is not the
later Schur-complement congruence.

### Ordered eigenvalues and direction

Let `alpha_(p,d)` mean the `p`-th smallest eigenvalue **by value** of the
symmetrized matrix. DLMF prose says "ascending order of magnitude", which is
ambiguous if read as absolute value. The by-value interpretation is the only
one coherent with all three source anchors:

1. at `gamma^2=0`, the diagonal values increase as
   `(m+2q)(m+2q+1)`;
2. 30.16.2 is the Cauchy-interlacing direction for leading principal blocks;
3. 30.16.3 recovers the continuously ordered DLMF eigenvalue family.

The exact direction of 30.16.2 is

```text
alpha_(j,d+1) <= alpha_(j,d).
```

The surrounding qualification is retained honestly: import it eventually in
`d` if it is imported at all. The count proof below does not need this
monotonicity; ordinary convergence at finitely many selected positions is
enough. The inequality is useful as a one-sided canary: finite counts cannot
overcount the classical count once the stated regime applies.

Equation 30.16.3 states

```text
lambda_n^m(gamma^2) = lim_(d -> infinity) alpha_(p,d),
p = floor((n-m)/2) + 1.
```

Thus

```text
(m,n) = (0,0)  -> p = 1,
(m,n) = (0,4)  -> p = 3.
```

Equivalently, for the even family, the zero-based classical index is
`r=p-1`, and the DLMF position `p` tends to mode `n=2r`. No `+1` or `-1` may
be silently moved across this ledger.

## Exact unit ledger and repaired shift

For `m=0`, DLMF 30.2.1 is

```text
(1-x^2) w'' - 2x w' + (lambda + gamma^2 - gamma^2 x^2) w = 0.
```

The project stores

```text
-(1-x^2) S'' + 2x S' + G x^2 S = (Lambda + G) S,
G = mode4JacobiG mProject.
```

Therefore

```text
gamma^2 = G,
lambda = Lambda,
chi_n = lambda_n^0(G) + G.
```

There are two equivalent but non-interchangeable formulations:

```text
lambda-units:
  negativeCount(sym(A_d(G)) - Lambda I)
    = #{p <= d | alpha_(p,d) < Lambda};

chi-units:
  the corresponding classical threshold is
    chi_(2r)(sqrt G) < Lambda + G.
```

The shift applied to the DLMF `lambda`-matrix is `-Lambda I`, not
`-(Lambda+G) I`. Applying the latter directly would count `chi` below
`Lambda+2G`. This packet supersedes the incorrect literal reading of the
older broad packet's phrase "shift by Lambda + G".

## Repo-side finite matrix and orientation

The physical Lean definitions were inspected locally, not inferred from the
external audit.

`mode4ActualFiniteJacobiTruncation mProject Lambda K d` is a Hermitian block
matrix on `Fin K ⊕ Fin d`:

- retained coordinates are reversed, with `q=K-1` first;
- eliminated coordinates run forward through `q=K, ..., K+d-1`;
- the single cross-block edge is `q=K-1 <-> q=K`;
- the finite final row has the terminal-zero convention.

The exact scalar definitions use

```text
mode4JacobiIndex q = 2q,
mode4JacobiCenter G Lambda q = B_q(G) - Lambda,
mode4JacobiLower G q = -A_q(G),
mode4JacobiUpper G q = -C_q(G),
```

with positive Hermitian off-diagonal magnitude obtained from the matching
upper/lower product. Hence the source-to-project connector must prove an
entrywise equality after:

1. the one-based/zero-based map `j=q+1`;
2. positive diagonal **similarity** from the raw DLMF matrix to its symmetric
   Jacobi matrix;
3. the `-Lambda I` shift in `lambda`-units;
4. the explicit permutation that reverses only the retained `Fin K` block and
   leaves the forward `Fin d` tail in order.

The later block elimination uses a **congruence**, which preserves inertia but
not eigenvalues. Similarity and congruence are separate proof steps.

The order of operations is load-bearing. For a nontrivial diagonal factor
`E`, in general

```text
E (S - Lambda I) E^T != E S E^T - Lambda I.
```

Therefore any connector theorem must state the shifted factorization
entrywise; naming only the factors is insufficient.

## Minimal source-faithful analytic carrier

The tree does not yet contain a source-locked Lean object for the ordered
classical even family `chi_(2r)(sqrt G)`. Until that object exists, an exact
Lean theorem head for the DLMF carrier would either use invented placeholders
or hide the missing source construction in hypotheses. The next Lean head is
therefore honestly:

```text
NOT_READY
```

After Proshka accepts this packet and the ordered classical family is
materialized source-faithfully, the only genuinely new analytic carrier should
say:

```text
for every p >= 1,
  the p-th smallest-by-value eigenvalue of the Lean-defined d x d
  m=0, gamma^2=G matrix from DLMF 30.16.1
  tends, as d -> infinity, to
  chi_(2*(p-1))(sqrt G) - G.
```

This carrier is exactly DLMF 30.16.3 plus the same-index identification from
DLMF 30.2/30.3 and Osipov Theorem 3. It imports no finite numerical result,
no endpoint counts, no eigenvector row, and no effective estimate from
30.16.4.

The same-index identification has two pinned routes:

- ordering route: DLMF and Osipov describe the same regular spectrum after
  `chi=lambda+G`; both sequences are strictly increasing, so the enumerations
  coincide termwise;
- zero-count cross-check: DLMF 30.4 and Osipov Theorems 1 and 3 assign the same
  number of interior zeros to the same regular mode.

The first route is minimal. The zero-count route remains an independent
cross-check.

## Eventual-count theorem contract after the carrier

Let `M_d` be the project truncation after the entrywise connector has proved
the exact permutation, positive diagonal transformation, and shift placement.
The desired theorem is

```text
eventually in d,
  negativeCount(M_d)
    = #{r : chi_(2r)(sqrt G) - G < Lambda}
    = #{r : chi_(2r)(sqrt G) < Lambda + G}.
```

Required premises are separate:

1. the analytic carrier above;
2. `alpha_(p,d)` defined as the `p`-th smallest eigenvalue by value;
3. strict increase and unboundedness of the classical `chi` family;
4. the classical separator
   `Lambda + G != chi_(2r)(sqrt G)` for every `r`;
5. the already proved finite-tail positivity and finite-to-literal transport;
6. sufficiently large `d`, absorbed by `Filter.atTop`.

The classical separator in item 4 is not the same statement as

```text
(mode4HermitianSchurMatrix mProject Lambda K).det != 0.
```

Both must remain explicit until a theorem connects them. The existing
finite-to-literal transport consumes the literal determinant premise; the
source count consumes the classical separator.

Once the limit carrier exists, eventual equality is finite reasoning: modes
below the separator are eventually below the finite threshold, the first mode
above it is eventually above, and the by-value ordering forces all later
positions above. DLMF 30.16.2 is not required for this step.

## Offset-zero obligations

No offset is assumed. Offset zero is the conjunction of three theorems:

1. the DLMF even truncation begins at degree zero because its left coupling
   vanishes;
2. the explicit reversal and positive diagonal transformations preserve the
   relevant spectrum/inertia in their respective steps;
3. the eliminated `q >= K` tail is positive definite and contributes zero
   negative directions.

The third item is now kernel checked in
`mode4ActualFiniteJacobiTruncation_tailBlock_posDef`; the first and second must
be part of the future entrywise crosswalk. No endpoint count is allowed before
all three are composed.

## Planted falsifiers

### F1 — reversed convergence direction

Mutation:

```text
alpha_(j,d+1) >= alpha_(j,d)
```

Expected rejection: it contradicts the pinned 30.16.E2 bytes and reverses the
one-sided count canary.

### F2 — index-base/offset mutation

Mutations:

```text
p = floor((n-m)/2)
r = p
```

Expected rejection: `(m,n)=(0,0)` must select one-based `p=1`, and `(0,4)`
must select `p=3`; the `gamma^2=0` diagonal anchor detects either mutation.

### F3 — unit/shift mutation

Mutation:

```text
negativeCount(sym(A_d(G)) - (Lambda+G) I)
  eventually equals #{r : chi_(2r)(sqrt G) < Lambda+G}.
```

Expected rejection: the left side actually uses a `lambda` threshold
`Lambda+G`, hence a `chi` threshold `Lambda+2G`.

Additional registered mutations: swap even 30.16.1 with odd 30.16.6; shift
outside a diagonal congruence; drop the sign convention in any future
30.16.9 row route; conflate the classical separator with the literal
determinant premise.

## Route and execution boundary

```text
PRIMARY_ROUTE: ROUTE_INERTIA_FINITE_LIMIT
SECONDARY_ROUTE: ROUTE_DLMF_INDEXED_ROW_LIMIT
EXACT_NEXT_LEAN_HEAD: NOT_READY
ARISTOTLE_BOUNDARY: NOT_AUTHORIZED
```

The indexed-row route remains a secondary root-existence spur only. It needs
finite-vector sign selection, normalization, function identification, and
simplicity in addition to the count machinery; it is not the minimal supplier
for the production consumer's counts `2` and `3`.

If Proshka accepts the source contract, the queued order is:

1. materialize the source-locked ordered classical even `chi` family;
2. prove the pure finite entrywise DLMF-to-project crosswalk with exact shift
   placement;
3. materialize the single analytic convergence carrier;
4. prove the eventual classical count;
5. compose with the accepted finite-to-literal transport and only then derive
   endpoint counts from separately proved separators.

Aristotle becomes eligible only for step 2 after the classical object and
exact theorem head are accepted. The analytic carrier is a source import, not
an Aristotle proof task.

## Requested Proshka verdict

Return exactly:

1. `PRIMARY_VERDICT`: `ACCEPT`, `REVISE`, or `REJECT` for this source packet;
2. whether the repaired `lambda`/`chi` unit ledger is correct;
3. whether by-value ordering is the source-faithful interpretation required by
   30.16.2--30.16.3;
4. whether the three offset-zero obligations are complete and noncircular;
5. the smallest source-faithful object that must precede any Lean theorem
   head;
6. `EXACT_NEXT_LEAN_HEAD` or `NOT_READY`;
7. Aristotle authorization boundary;
8. G1/G3 status and one typed stop code.

## Packet stop code

```text
DLMF_3016_SOURCE_CONTRACT_PACKED_UNIT_SHIFT_REPAIRED_CLASSICAL_CHI_OBJECT_AND_ANALYTIC_CARRIER_NOT_MATERIALIZED
```
