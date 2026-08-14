# Goal 058 G3 — DLMF 30.3.5 characteristic object closeout

Date: 2026-08-14

## Verdict

```text
DLMF3035_RIGHT_BRANCH_AND_LOCAL_CHARACTERISTIC_ADAPTER_PROVED
G3_STATUS: OPEN
STOP_CODE: G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED
```

This transaction materializes the independent local representation of the
order-zero even DLMF 30.3.5 characteristic equation.  It does not materialize
the DLMF solution-set theorem or identify the internal finite-limit carrier
with an independently constructed differential spectrum.

## Source lock

- NIST DLMF 30.3.5: <https://dlmf.nist.gov/30.3.E5>
- NIST DLMF 30.3.7: <https://dlmf.nist.gov/30.3.E7>
- NIST DLMF 30.16.3: <https://dlmf.nist.gov/30.16.E3>
- `G = gamma^2`;
- project `Lambda =` DLMF `lambda`;
- differential energy `chi = Lambda + G`;
- even split degree `2 * (K - 1)`;
- zero-based internal mode index `j` corresponds to DLMF degree `2*j` and
  one-based finite selector `j+1`.

The live official DLMF check confirms that 30.3.5 has the even solution set
`lambda_(m+2j)^m(gamma^2)`, that 30.3.7 supplies the literal
`alpha/beta/gamma` coefficients, and that 30.16.3 uses selector
`floor((n-m)/2)+1`.

## Kernel-checked files

### Right branch

`Q3/Proofs/RouteB/D0Mode4DLMF3035EvenRightBranchCrosswalk.lean`

SHA-256:

```text
0822a3593ce11984bca31c2c619420af02868447a5a31c54db5697d8a3d1ab06
```

It provides:

- literal `mode4DLMF3037Alpha/Beta/Gamma`;
- exact even-index identities with the project Jacobi coefficients;
- `mode4DLMF3035EvenSplitDegree K = 2 * (K - 1)`;
- an independent literal right map and terminal-zero finite fractions;
- termwise equality of those fractions with `mode4BackwardTail`;
- an independent `limUnder` ratio;
- `mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit` in the certified
  production domain.

The proof uses coefficient rewriting, Cauchy convergence, and uniqueness of
the limit.  It does not use a root, a characteristic solution set, endpoint
counts, or a classical carrier.

### Finite-left source object and local adapter

`Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean`

SHA-256:

```text
5ee718a3868f0698712a296ab37ec09469de07bcb5b88b94b26c5cd4bbe4919c
```

It provides:

- independent literal `mode4DLMF3035EvenLeftPair` with the regular parity
  boundary and only the DLMF 30.3.7 coefficients;
- pole-safe `mode4DLMF3035EvenCharacteristicEquation`, with an explicit even
  split guard and first right index `splitDegree / 2 + 1`;
- `mode4DLMF3035EvenLeftPair_eq_mode4LeftPair`;
- `mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero` at the
  exact split `2 * (K - 1)` in the production contraction domain.

The source predicate is not defined through `mode4RootFunction`, project
`mode4LeftPair`, or project `mode4RightTailLimit`.

## Validation

For both files:

- direct `lake env lean`: PASS;
- named `lake build`: PASS;
- `scripts/q3_check.sh`: PASS;
- forbidden hole/unsafe/claim scans: no hits;
- whitespace checks: PASS;
- public axiom surfaces: only `propext`, `Classical.choice`, and `Quot.sound`
  (the arithmetic split lemma does not need `Classical.choice`).

## Mandatory nonclaims

The following theorem remains absent:

```lean
mode4DLMF30163_3035_evenCharacteristicSolutions
```

The current `mode4ClassicalEvenEigenvalue` is the internal `iInf` of the
finite DLMF matrix family.  The tree still has neither an independent indexed
differential-even spectrum carrier nor a proof that DLMF 30.3.5 solutions are
exactly that differential spectrum and that DLMF 30.16.3 identifies it with
the internal finite limit.  Adding the desired equivalence as a binder or
structure field would be a receiver, not the missing supplier.

Therefore this closeout proves neither endpoint counts, degree-four mode
selection, actual-mode existence, CCM Lemma 7.2, a projected denominator
floor, G1, G3, Route B promotion, nor RH.

## Parallel G1 discriminator

The current G1 audit also rejects exact source-row evenness as the next target.
The source-faithful statement is a quantitative odd-contamination estimate via
the existing inversion-even comparison receiver.  Its first missing producer
is actual-mode existence for `IsActualProlateModePair`; after that the genuine
CCM Lemma 7.2 approximation rate is still required.  No unconditional G1
producer is theorem-head ready at this node.
