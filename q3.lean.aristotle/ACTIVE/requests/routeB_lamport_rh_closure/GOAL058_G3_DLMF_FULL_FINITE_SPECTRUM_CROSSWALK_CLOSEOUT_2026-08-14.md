# Goal 058 G3 — full finite DLMF spectrum crosswalk closeout

Date: 2026-08-14

Route state: `CHALLENGER / NOT_RH`

Node verdict: `PROVED`

Goal 058: `OPEN`

## Address

This node closes the finite-carrier orientation gap between the actual Jacobi
truncation used by the Schur/inertia chain and the literal even DLMF 30.16.1
matrix.  The actual carrier is `Fin K ⊕ Fin d`; the source carrier is
`Fin (K + d)`.  The exact equivalence reverses the retained `Fin K` block and
leaves the tail in forward source order.

The result is finite algebra.  It is not DLMF 30.16.3, a classical
spheroidal spectral carrier, an endpoint count, the indexed degree-four
selection, G3 closure, Route B promotion, or an RH claim.

## Source lock and preflight

The source contract remains the byte-pinned DLMF packet
`GOAL058_G3_DLMF_3016_EVEN_COUNT_CROSSWALK_SOURCE_PACKET_2026-08-14.md`.
In particular, DLMF 30.16.1 supplies the forward finite matrix, while the
ordered classical limit belongs to the still-unmaterialized 30.16.3 object.

Before production writing, a declared full `lean-env-dump` invocation exited
`0` and published 1,568 declarations with zero `sorryAx` and zero extra
axioms.  Exact environment and all-disk searches found the left-block reversal
theorem but no full-carrier permutation, full characteristic-polynomial
crosswalk, or ordered finite-to-classical supplier.  The global environment
index remained honestly `INCOMPLETE` because unrelated Route B modules were
stale or never built; both direct imports used by this node were current and
indexed.

## Kernel-checked output

Production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMFFullFiniteSpectrumCrosswalk.lean
SHA-256 0938a76ff07b6e0e0ff20cbc2d20b635e39027c65fab287b00869502151c0fd8
```

The principal public outputs are:

1. `mode4ActualFiniteForwardEquiv`, with exact `inl` and `inr` coordinate
   formulas `mode4ActualFiniteForwardEquiv_inl` and
   `mode4ActualFiniteForwardEquiv_inr`;
2. `mode4ActualFiniteJacobiTruncation_eq_reindex_forwardHermitianFiniteMatrix`;
3. `mode4ActualFiniteJacobiTruncation_charpoly_eq_forwardHermitianFiniteMatrix`;
4. `mode4ForwardHermitianFiniteMatrix_isHermitian`;
5. `mode4ForwardHermitianFiniteMatrix_eq_unshifted_sub_scalar`;
6. the zero-based ascending family `mode4DLMFEvenFiniteEigenvalue` and its
   monotonicity theorem `mode4DLMFEvenFiniteEigenvalue_monotone`;
7. `mode4DLMFEvenFiniteMatrix_charpoly_eq_forwardHermitianFiniteMatrix`;
8. `mode4ActualFiniteJacobiTruncation_charpoly_eq_DLMFEvenFiniteMatrix`.

The recursive tail calculation is kept private as
`mode4ActualFiniteJacobiTruncation_tail_entry`; it exists only to prove the
public full-carrier reindexing identity.

Thus the actual finite truncation and the literal DLMF matrix have exactly the
same characteristic polynomial on the complete `K + d` carrier.  The scalar
parameter is also proved to be the literal shift `H(G,Lambda) = H(G,0) -
Lambda I`.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0Mode4DLMFFullFiniteSpectrumCrosswalk.lean
  PASS
lake build Q3.Proofs.RouteB.D0Mode4DLMFFullFiniteSpectrumCrosswalk
  PASS (7756 jobs)
lake build
  PASS (7817 jobs)
bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMFFullFiniteSpectrumCrosswalk.lean
  PASS (q3_check ok)
```

`git diff --check` passes, and the production source contains no `sorry`,
`admit`, `exact?`, declared `axiom`, or `unsafe`.  Every printed public axiom
surface is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only build warning is the pre-existing local-change warning for the
external `UnicodeBasic` dependency.

## Honest boundary

This crosswalk removes any remaining ambiguity about the finite matrix,
orientation, shift, or characteristic polynomial.  It does not construct the
classical ordered even spheroidal eigenvalue family and does not prove that the
finite eigenvalues converge to that family with the required zero-based Lean
index / one-based DLMF selector / even degree correspondence.

Therefore it cannot yet manufacture the fixed-endpoint negative counts `2/3`
or identify their crossing with classical degree four.  Those facts must be
supplied by a source-faithful analytic carrier, not inserted as hypotheses.

```text
STOP_CODE:
DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_PROVED_ORDERED_FINITE_TO_CLASSICAL_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING
AUTOPSY: dropped=SPECTRAL_LIMIT; note=the exact finite ordered family exists, but no Lean carrier proves the DLMF 30.16.3 same-index classical limit
AUTOPSY: dropped=SOURCE_IDENTITY; note=the classical degree-four selector and endpoint counts remain unmaterialized
```

G1 remains independently open at the even-head/shift/cofinal full-complement
floor.  The recovered odd-tail coercivity supplier does not close that wall.
