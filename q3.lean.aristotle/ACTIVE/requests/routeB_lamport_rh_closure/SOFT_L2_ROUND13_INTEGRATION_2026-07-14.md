# SOFT_L2 Round13Integration

Status: `SOFT_L2_ROUND13_INTEGRATION_LOCKED / NOT_RH`

Authority: `SOFT_L2_PRO_VERDICT_ROUND13_2026-07-13.md`, verbatim V1,
sha256 `71f4e1276c774c5a857afea2d511f0c5e45cc31710f4689666b417f75b69b9dd`.

This contract changes the SOFT_L2 theorem map only.  It does not close the
physical Route B `H2a` sector-ordering obligation, prove L2.2, create a new
ground-to-autocorrelation node, or prove RH.

## 1. `SOFT_SAME_COFINAL_SUBSEQUENCE`

There is one parent diagonal sequence

```text
j : Nat -> Index,   j_k -> infinity,
```

such that both contracts are asserted on every parent index:

```text
forall k, H2a_cofinal(j_k);
forall k, S1(j_k).
```

S2 may pass only to a nested subsequence.  It must supply a strictly
increasing extraction `kappa : Nat -> Nat` and consume

```text
j_(kappa(ell)).
```

It may not introduce an independent sequence `n_ell`.  A proof object must
therefore carry the literal factorization

```text
S2_index(ell) = j(kappa(ell)).
```

The guard name is `SOFT_SAME_COFINAL_SUBSEQUENCE`.  Its fail-closed code is

```text
SOFT_COFINAL_SUBSEQUENCE_MISMATCH
```

and it fires whenever H2a-cofinal, S1, and S2 cannot be placed on this one
parent/nested carrier.

The Lean carrier `SoftSameCofinalSubsequence` types the parent sequence,
H2a/S1 premises, and strictly increasing extraction.  Its `s2Sequence` is by
definition `parent (extract ell)`.

## 2. H2a derived corollary — no new node

Inside complex ground space, simplicity gives, for any two normalized ground
representatives,

```text
q_tilde_j = exp(i theta_j) q_j;
A_q(t) := <U_t q,q>;
A_(q_tilde_j)(t) = A_(q_j)(t).
```

Thus H2a exports the derived corollary

```text
simple normalized ground eigenspace
  -> canonical phase-independent autocorrelation A_j.
```

`GroundEigenspaceToCanonicalAutocorrelation` is not created as a node.
Isolation is not consumed by this corollary; it remains relevant to spectral
tracking/stability.  Real-even structure is also not needed for phase
independence and retains its separate downstream roles.

Lean candidate/proof:
`Q3/Proofs/RouteB/SoftL2Round13Integration.lean`, theorem
`simpleGround_canonicalPhaseIndependentAutocorrelation`.  It has no holes.

## 3. Frozen L2.2 contract

```text
L2.2 := GlobalPositiveDefiniteUniqueness.
```

Type:

```text
Distribution := D'(R)
A, A_Phi : Distribution
```

Exactly five inputs:

1. one diagonal subsequence `j_k`, valid on every compact;
2. `A_(j_k) -> A` in `D'(R)`;
3. `A` is positive-definite;
4. `A` satisfies the limiting equation in `D'(R)`;
5. the frozen scale satisfies `c > 0`.

Output:

```text
A = c * A_Phi in D'(R).
```

Status: `TYPED_OPEN_NOT_PROVED`.  The Lean definition
`GlobalPositiveDefiniteUniqueness` freezes this five-premise theorem type; it
does not construct a proof.

Neither a uniform autocorrelation tail nor edge mass is an input to L2.2.
One compatible global distribution obtained from one diagonal subsequence on
all compacts already removes the alleged `D'_loc` versus `D'` obstruction.

## 4. Optional source-level leaf

`SourceCompactnessToFullAutocorrelation` is registered as
`OPTIONAL / INACTIVE_UNLESS_DOWNSTREAM_REQUIRES_LIMIT_SOURCE`.

Inputs, and only these two:

```text
spatial tightness;
uniform translation continuity.
```

Expected output after a subsequence:

```text
q_j -> q strongly in L2(R);
sup_t |A_(q_j)(t)-A_q(t)| -> 0.
```

This leaf is representation-level.  It is not a dependency, premise, or
hidden lemma of `GlobalPositiveDefiniteUniqueness`.

Its three registered validators are mandatory:

| plant | target | required fire code |
|---|---|---|
| spatial shift `q_j(u-a_j)` | autocorrelation cannot determine absolute source center | `SOURCE_CENTER_NOT_VISIBLE_TO_AUTOCORRELATION` |
| scale `a_j^(1/2) q(a_j u)` | spatial/edge concentration alone does not give uniform translation continuity or a nonzero local A-limit | `EDGE_TIGHTNESS_ALONE_KILLED` |
| `A_0(t) cos(beta_j t)` | a uniform A-tail alone does not prevent frequency escape or the zero local-distribution limit | `UNIFORM_TAIL_ALONE_KILLED` |

All three are validator plants, not theorem evidence.

## 5. TailCheck recoding and map repair

The numerical verdict on `(13,120)` remains

```text
TAIL_DOMINATED.
```

Its role is now exactly

```text
OPTIONAL_SOURCE_COMPACTNESS_SPATIAL_TIGHTNESS_DIAGNOSTIC.
```

It may support investigation of the first optional-leaf input, spatial
tightness.  It does not establish uniform translation continuity and is not an
input to L2.2.

The repaired map is

```text
H2a-cofinal(parent j_k) + S1(parent j_k)
                 |
                 | SOFT_SAME_COFINAL_SUBSEQUENCE
                 v
        S2 on j_(kappa(ell))
                 |
                 v
   one global positive-definite A in D'(R)
                 |
                 v
 L2.2 GlobalPositiveDefiniteUniqueness [OPEN]
                 |
                 v
            A = c A_Phi

OPTIONAL SIDE LEAF, not feeding L2.2:
spatial tightness + uniform translation continuity
                 -> SourceCompactnessToFullAutocorrelation
```

The former edge

```text
D'_loc convergence -> full-autocorrelation tail hypothesis -> L2.2
```

is deleted and registered as

```text
FALSE_WALL_REMOVED_ROUND13.
```

`NOT_RH`.  Bus 010 is outside this contract and must remain absent.
