# Goal 058 G3 — literal DLMF even finite matrix closeout

Date: 2026-08-14

Route state: `CHALLENGER / NOT_RH`

Node verdict: `PROVED`

Goal 058: `OPEN`

## Address

This node materializes the smallest exact source object accepted by the
Goal 058 DLMF 30.16 source verdict: the literal even finite matrix of DLMF
30.16.1 in project units, its positive diagonal symmetrization, and its exact
reversal into the existing Hermitian left-continuant matrix.

It is a finite algebraic source crosswalk. It is not the classical spectral
limit, an endpoint count, indexed `psi_4` selection, G3 closure, Route B
promotion, or an RH claim.

## Knowledge preflight receipt

Before the object was created, the exact query

```text
./ask.sh --deep 'mode4DLMFEvenFiniteMatrix DLMF 30.16.1 positive diagonal similarity permutation reindex'
```

found the registered source packets and adjacent linear-algebra machinery but
no existing exact Lean supplier for the literal matrix/conjugator target. The
enabled external Lean denominator was `[zeta23]`; its matches were generic
inertia/reindex candidates, not an interface-equivalent supplier.

After the proof and registered inventory sync, the same query resolves the new
definitions and theorem heads in
`Q3/Proofs/RouteB/D0Mode4DLMFEvenFiniteMatrix.lean`. This second query is a
catalogue check, not evidence that the supplier existed before the node.

## Source lock

- Primary equation: DLMF 30.16.1, already pinned and reviewed in
  `GOAL058_G3_DLMF_3016_EVEN_COUNT_CROSSWALK_SOURCE_PACKET_2026-08-14.md`.
- Sector: spheroidal order `m = 0`, even degree, with source row `j = q + 1`
  corresponding to Legendre degree `2q`.
- Units: `G = gamma^2`, `Lambda = lambda`; the literal matrix already contains
  the shift `-Lambda I`.
- Orientation: the DLMF matrix is in forward source order `q = 0, ..., d-1`;
  `Fin.rev` is proved explicitly before identification with the existing
  left-continuant orientation.
- Transformation: positive diagonal similarity, not a congruence and not a
  silently symmetric source matrix.

## Kernel-checked output

Production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMFEvenFiniteMatrix.lean
SHA-256 bd949708c2d2c6df75b9e216b8d16c6c6a579ea6db04d6c213f6bc3eb7f1399d
```

Main public supplier:

```text
mode4DLMFEvenFiniteMatrix_similar_hermitianLeftContinuantMatrix
```

It packages three exact facts for `0 < G`:

1. `A * D = D * H` for the literal DLMF matrix `A`, a positive diagonal
   scale `D`, and the forward Hermitian Jacobi matrix `H`;
2. `submatrix H Fin.rev Fin.rev` is exactly the existing
   `mode4HermitianLeftContinuantMatrix`;
3. every diagonal scale entry is strictly positive.

Supporting public heads expose the literal entries, the scalar crosswalks, the
positive scale, the entrywise/matrix similarity equations, and the reversal
identity without importing an ordered classical spectrum or a negative-count
claim.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0Mode4DLMFEvenFiniteMatrix.lean
  PASS
lake build Q3.Proofs.RouteB.D0Mode4DLMFEvenFiniteMatrix
  PASS (7753 jobs)
lake build
  PASS (7817 jobs)
bash scripts/q3_check.sh Q3/Proofs/RouteB/D0Mode4DLMFEvenFiniteMatrix.lean
  PASS
```

Every printed public axiom surface is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `admit`, `exact?`, new `axiom`, or `unsafe` declaration.
The registered RouteB inventory and `aristotle_proofs.db` were refreshed after
the source file and this closeout were present.

## Honest boundary and next source object

This node closes the verdict's previously `NOT_READY` literal matrix and exact
conjugator leaf. It does not prove that the ordered eigenvalues of these finite
matrices converge to the classical even spheroidal eigenvalues, and therefore
does not yet supply the endpoint negative counts `2/3` or the identification
of the count-two crossing with indexed degree four.

The next source theorem must provide a source-faithful classical even spectral
carrier and an ordered finite-eigenvalue convergence/count crosswalk. It may
then feed the already proved finite-to-literal negative-count transport. A
theorem taking the desired endpoint counts as binders is not a supplier.

```text
STOP_CODE:
DLMF_EVEN_FINITE_MATRIX_AND_EXACT_SIMILARITY_PROVED_ORDERED_EIGENVALUE_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING
AUTOPSY: dropped=SPECTRAL_ORDERING; note=the finite source matrix is exact, but no source-locked ordered eigenvalue limit supplies the classical endpoint counts
AUTOPSY: dropped=SOURCE_IDENTITY; note=the indexed classical even spectrum and its degree-four identification are not yet materialized as Lean source objects
```

G1 remains independently open at the full complex complement floor: the
recovered odd-tail coercivity supplier does not provide the even finite head,
the shift/schedule bridge, or the cofinal connector.
