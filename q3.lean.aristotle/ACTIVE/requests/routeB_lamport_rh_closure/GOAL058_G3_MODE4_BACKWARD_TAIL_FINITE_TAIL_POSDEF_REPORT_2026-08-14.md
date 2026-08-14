# Goal 058 G3 — actual finite tail PosDef and public Schur crosswalk

Date: 2026-08-14

Status code:

`G3_MODE4_FINITE_TAIL_POSDEF_AND_PUBLIC_SCHUR_CROSSWALK_PROVED`

Boundary:

`BOUNDED_G3_LEAF_ONLY / G1_OPEN / G3_OPEN / NO_ROUTE_PROMOTION / NO_RH_CLAIM`

## Exact artifact

- Lean file: `Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean`
- base `rh_clean` HEAD before the leaf: `c65ea047d68642e66f23dac089298d97af98ffde`
- Lean SHA-256: `19a20a506f5b6a264b469efac555553e3f9565791c8a7da903117c8a22c40e7e`
- Lean size: `13167` bytes, `324` lines
- exactly one direct Q3 import:
  `Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk`

## Knowledge preflight

The exact query

```text
./ask.sh "D0Mode4BackwardTailFiniteTailPosDef actual finite Jacobi tail block positive definite separation"
```

exited `0` and returned only broad, unrelated metadata names.  The exact
`kb.py ask` query exited `1` with no hits, and
`kb.py flags D0_MODE4_BACKWARD_TAIL_FINITE_TAIL_POSDEF` exited `1` because
the territory had not previously been searched.

Semantic queries identified the current Jacobi-tail contraction sources,
especially `mode4JacobiCenter_sub_upper_mul_lower_bound` and
`mode4TailMap_mapsTo_and_contracts`, together with the accepted finite-Schur
report and verdict.  They found no ready positive-definiteness theorem.

Boundary: this is a retrieval receipt, not proof evidence.

## Exact public surface

The file has no public definition, structure, or axiom.  Its only two public
declarations are:

```lean
mode4ActualFiniteJacobiTruncation_tailBlock_posDef
mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
```

Both use exactly the production hypotheses

```lean
mProject K d : Nat
Lambda : Real
2 <= mProject
3 <= K
forall q >= K,
  (31 / 24 : Real) * mode4JacobiG mProject <=
    mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20
Lambda <= 20
```

The first concludes that the literal eliminated block

```lean
(mode4ActualFiniteJacobiTruncation mProject Lambda K d).toBlocks22
```

is `Matrix.PosDef`.  The second concludes the exact public Schur identity

```lean
M.toBlocks11 - M.toBlocks12 * M.toBlocks22.inverse * M.toBlocks21 =
  mode4BackwardTailSchurApprox mProject Lambda K d
```

without exposing or assuming the predecessor's private recursive-pivot
predicate.

Eight supporting declarations are private: one literal forward-tail matrix
definition and seven theorems for the actual-block equality, the quadratic
recurrence, Young's inequality, the coercive bound, Hermitianity, positive
definiteness, and the backward-tail interval invariant.

## Proof spine

1. The literal actual tail block is identified entrywise with a forward
   recursive Jacobi tail at indices `K,K+1,...`.
2. Its quadratic form is split at the first coordinate with the exact source
   off-diagonal coefficient.
3. `mode4JacobiSymmetricOff_sq` supplies the weighted Young inequality.
4. The production separation inequality and `Lambda <= 20` give the inductive
   coercive estimate

   ```text
   mode4JacobiLower G K * x_0^2 + (G/12) * sum_i x_i^2
     <= star x dot (A x).
   ```

5. Since `G = mode4JacobiG mProject` is positive for `mProject >= 2`, every
   nonzero finite vector has strictly positive quadratic form.  The empty
   `d=0` carrier is handled explicitly.
6. The public backward-tail `MapsTo` theorem keeps every suffix value in
   `[0,1/2]`.  The existing center-minus-upper-times-lower bound therefore
   makes each hidden elimination pivot at least `2G/3`, hence nonzero.
7. The accepted conditional finite-Schur theorem is applied after unfolding
   its private premise only inside the proof.  No private predicate survives
   in the public theorem type.

This proves positivity and legal finite elimination.  It is not a finite
negative-eigenvalue count and not a limit theorem.

## Mandatory planted falsifiers

Scratch-only plant file:

```text
/tmp/Goal058Mode4FiniteTailPosDefPlants.lean
SHA-256 6e5b2583578e378668dd700ad614aeacdb60c9f4f2519ffd5337873e71999b31
4223 bytes, 113 lines
```

Direct command:

```text
lake env lean /tmp/Goal058Mode4FiniteTailPosDefPlants.lean
  PASS
```

All four public plant theorems compile with only
`[propext, Classical.choice, Quot.sound]`:

- `MODE4_FINITE_TAIL_HERMITIAN_NOT_POSDEF`: the `Fin 1` matrix `[-1]` is
  Hermitian but not positive definite.  Hermitianity alone is insufficient.
- `MODE4_FINITE_TAIL_SEPARATION_MISSING`: the actual `d=1` tail at
  `(mProject,K,Lambda)=(10,3,20)` satisfies the other public inputs, violates
  production separation already at `q=3`, and is not positive definite.
- `MODE4_FINITE_TAIL_LAMBDA_UPPER_MISSING`: the actual `d=1` tail at
  `(mProject,K,Lambda)=(2,8,1000)` satisfies the canonical separation theorem,
  violates `Lambda <= 20`, and is not positive definite.
- `MODE4_FINITE_TAIL_ORIENTATION_MISMATCH`: reversing the exact public
  backward-tail approximation changes the matrix; the original `(0,0)` entry
  is `20` while the reversed source `(2,2)` entry is `0`.

The scratch forbidden-token scan has no hits.  The plant file is not a
repository artifact and is not proposed for commit.

## Validation on exact Lean bytes

All commands below passed on the recorded Lean SHA-256:

```text
lake env lean Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean
  PASS

lake build Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteTailPosDef
  PASS — 7753 jobs

lake build
  PASS — 7817 jobs

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean
  PASS — q3_check ok

git diff --check -- \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean
  PASS
```

The forbidden scan is empty for

```text
sorry | admit | exact? | axiom | unsafe
```

Both public theorem axiom profiles are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only build diagnostic is the pre-existing warning that dependency
`UnicodeBasic` has local changes; this leaf does not touch that dependency.

After the leaf was added, the semantic index was refreshed.  Strict startup
then returned `P9_STRICT_PASS` with no discrepancies; the remaining
cartographer diagnostic was only the expected uncommitted Lean artifact.

## Independent Aristotle boundary

The predecessor finite-Schur contract remains under independent Aristotle
project `58cbc619-8fec-4253-9788-3d6375ffcc50`.  It was still running at this
leaf's validation point.  The present proof was constructed and checked
locally and consumes no Aristotle output as a supplier.

## Nonclaims and next wall

This leaf does **not** prove:

- Haynsworth or any other block-inertia additivity theorem;
- the negative-eigenvalue count of the finite truncation;
- stability of that count in the finite limit;
- the zero offset or endpoint counts `2/3`;
- the actual G3 prolate constructor, Fourier identification, CCM Lemma 7.2,
  or denominator floor;
- the parallel G1 uniform spectral gap and cofinal tracking package;
- G1 or G3 closure, Route B promotion, or RH.

The next honest finite-Jacobi wall is a source-faithful finite block-inertia
additivity theorem consuming this `PosDef` tail and the exact Schur crosswalk,
followed by an exact finite negative count and the source endpoint accounting.
Those are separate leaves and remain open.

# STATUS: PROVED — BOUNDED FINITE TAIL POSDEF AND PUBLIC SCHUR CROSSWALK
