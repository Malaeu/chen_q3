# Goal 058 G3 — actual finite backward-tail Schur crosswalk

Date: 2026-08-14

Status code:

`G3_MODE4_ACTUAL_FINITE_SCHUR_CROSSWALK_PROVED`

Boundary:

`BOUNDED_G3_LEAF_ONLY / G1_OPEN / G3_OPEN / NO_ROUTE_PROMOTION / NO_RH_CLAIM`

## Exact artifact

- Lean file: `Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteSchurCrosswalk.lean`
- base `rh_clean` HEAD before the leaf: `fdb7b60f`
- Lean SHA-256: `c8866f89a138ba2d4b4ea76c4a2178dec4c5d62b522684c70a1649ab3c64990d`
- exactly one direct Q3 import:
  `Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence`

## Knowledge preflight

Exact query:

```text
./orchestrator/kb.py ask "D0Mode4BackwardTailFiniteSchurCrosswalk exact finite Jacobi truncation Schur complement terminal zero"
```

Result: exit `0`, exact response `no hits ... in any layer`.

Boundary: retrieval receipt only; not proof evidence.

## Source and orientation lock

The source packet
`GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`
pins DLMF 30.16.1 as the finite even-sector tridiagonal matrix and pins the
existing DLMF 30.8 coefficient crosswalk.  The already checked Hermitian
similarity uses

```text
-sqrt(mode4JacobiLower G (q+1) * mode4JacobiUpper G q)
```

on the `q ↔ q+1` edge.

The new truncation uses the exact split orientation required by the accepted
Proshka directive:

- retained carrier: fixed `Fin K`;
- retained order: the existing reversed left-continuant order, with `q=K-1`
  at coordinate `0`;
- eliminated carrier: `Fin d` in forward order `q=K,...,K+d-1`;
- sole cross-block edge: retained `0` to tail `0`, with coefficient
  `-mode4JacobiSymmetricOff G (K-1)`;
- terminal convention: the last finite row has no outgoing edge, exactly the
  terminal value `0` in `mode4BackwardTail mProject Λ K d 0`.

No reindexing or post-hoc relabeling is used in the Schur equality.

## Public surface

Exactly one public definition:

```lean
mode4ActualFiniteJacobiTruncation
```

It is the literal block matrix on `Fin K ⊕ Fin d` with blocks `A,B,Bᴴ,D`.

Exactly two public theorems:

```lean
mode4ActualFiniteJacobiTruncation_isHermitian
mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx
```

The second theorem proves literally

```lean
M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁
  = mode4BackwardTailSchurApprox mProject Λ K d
```

under `mProject ≥ 2`, `K ≥ 3`, and explicit recursive nonvanishing of the
finite elimination pivots.  The pivot hypothesis is a private interface: at
depth `d+1` it states that the current continued-fraction denominator is
nonzero and that all suffix pivots are nonzero.  The proof derives, rather
than assumes, nonzero determinants of all corresponding finite tail blocks.

This is an invertibility boundary only.  It is not a tail positivity theorem.

## Algebraic proof spine

1. Define the forward finite Hermitian tail matrix recursively.
2. Prove its `0`-minor is the next suffix and prove the exact two-step
   determinant recurrence.
3. Induct on depth to prove simultaneously:
   - the finite tail determinant is nonzero from the declared pivots;
   - `mode4BackwardTail ... (d+1) 0` is the exact lower-coefficient times
     suffix-determinant/full-determinant quotient.
4. Use `Matrix.inv_def` and
   `Matrix.adjugate_fin_succ_eq_det_submatrix` to identify `(D⁻¹) 0 0` with
   that determinant quotient.
5. Collapse the rank-one coupling with `Matrix.single_mul_mul_single`, use
   `mode4JacobiSymmetricOff_sq`, and obtain the exact existing `Approx`
   matrix entrywise.

The `d=0` boundary is proved separately and reduces exactly to the retained
left-continuant block.

## Validation on exact Lean bytes

All commands below passed on the SHA recorded above.

```text
lake env lean Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteSchurCrosswalk.lean
  PASS

lake build Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk
  PASS — 7752 jobs

lake build
  PASS — 7817 jobs

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteSchurCrosswalk.lean
  PASS — q3_check ok

git diff --check
  PASS
```

Forbidden scan is empty for:

```text
sorry | admit | exact? | native_decide | new axiom | opaque
```

Both public theorem axiom profiles are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only build diagnostic is the pre-existing warning that dependency
`UnicodeBasic` has local changes; this leaf does not touch that dependency.

## Independent Aristotle attempt

The exact same contract was also submitted to Aristotle as project
`58cbc619-8fec-4253-9788-3d6375ffcc50` using a 48 MiB source-only context.
It was still running when this report was written.  The local kernel proof
above was completed independently and does not consume Aristotle output as a
supplier.

## Nonclaims and next wall

This leaf does **not** prove:

- finite tail positive definiteness;
- Haynsworth or inertia additivity;
- any finite negative-eigenvalue count;
- the zero offset or endpoint counts `2/3`;
- G1 or G3 closure;
- Route B promotion or RH.

The next source-locked G3 leaf remains the finite-tail positivity supplier
under the current production separation inequality, followed only then by
finite block inertia additivity.

