# GOAL 056 / Phase 4A — D0 Pstar to Müntz centered coordinate lock (XW.6)

```yaml
GOAL: 056
PHASE: 4A
NODE: D0PstarMuntzCenteredCoordinateLock
STATUS: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 0
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Exact target

Materialize the first no-proof production discriminator for XW.6 in
`Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock`.

For `S : ProlateCanonicalSourceData` and `k : ℕ`, every new object must use
literally

```text
i_k = (S.canonical.parent (S.canonical.extract k)).1
P_k = S.source.pair i_k
lambda_k = lambda_m i_k
```

and no independently supplied family, pair, window, parent, extract, or
subsequence.  The transform-coordinate convention is

```text
Gwin (prolateCombination P_k) lambda_k (-i*z)
    <-> rawFplus S.canonical.kTrial i_k (-z).
```

This phase defines the two exact sides, the `sTrial_m_N`-scaled Müntz main
coordinate, and their coordinate defect.  It proves only definitional/index,
source-pair, lambda, normalization-shape, and algebraic decomposition lemmas.
It does not prove that the defect vanishes or tends to zero.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_objects:
    - Q3.Proofs.RouteB.D0ProlateKTrialSource@3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1
    - Q3.Proofs.RouteB.D0CanonicalApproximation@60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
    - Q3.Proofs.RouteB.MuntzV3.ProlateCombinationReceiver@505e4ae0bdbedcb467110c185ad6933f0c35bfc4d4fc85194c06c22ad72e357c
    - Q3.Proofs.RouteB.MuntzV3.Core@7df74238ff1462eb750b0f975f4b87f4b9eec5f1f46c104890d1345b8e2cf1ca
    - D0_6_EXACT_TRANSFORM_CONVENTION@db4b185e9e9ba750936410f9c4e37d90b10586624e06315f1e045d604a0ac3ff
  terminal_consumer: strict SlotS2 bridge under Goal 056
  relation_under_test: exact same-index Gwin(-i*z) to rawFplus(-z) coordinate contract
  preserved_invariants:
    - selected index is definitionally S.canonical.parent (S.canonical.extract k)
    - source trial is the exact prolateCombination stored by XW.8 at that index
    - source bandwidth equals production lambda_m through the stored lambda_eq proof
    - raw coordinate keeps the source-locked minus-z orientation
    - Gwin coordinate keeps the Mellin exponent substitution s=-i*z
    - normalized main coordinate contains the exact sTrial_m_N scalar
    - all nonzero and carrier witnesses are reused from S.source
  forbidden_shortcuts:
    - a surrogate approximation family or a fresh parent/extract schedule
    - an independent ProlatePair, lambda, MemLp, or TrialNonzero supplier
    - rawFplus(z) in place of rawFplus(-z)
    - Gwin(i*z) in place of Gwin(-i*z) at the transform-coordinate layer
    - defining the defect to be zero or assuming its convergence
    - importing RequestProject.*, either roof, or the raw Aristotle file
    - claiming finite-residual decay, tail decay, strict SlotS2, promotion, or RH
```

## Exact declarations required

1. `selectedCentralIndex`, `selectedPairIndex`, `selectedProlatePair`, and
   `selectedProlateTrial` with definitional `parent (extract k)` exposure.
2. `selectedGwinTransformCoordinate S k z :=
   Gwin (selectedProlateTrial S k) (lambda_m (selectedPairIndex S k)) (-I*z)`.
3. `selectedRawTransformCoordinate S k z :=
   rawFplus S.canonical.kTrial (selectedPairIndex S k) (-z)`.
4. The exact `sTrial_m_N` scalar at the same pair index and source trial.
5. A centered Müntz main coordinate and a separately named coordinate defect,
   together with the algebraic reconstruction theorem.
6. An expansion of `selectedFamily (canonicalApproximation S.canonical) k`
   showing the same raw coordinate after the `z -> -z` substitution.

## Plants and validation

- `P056J_1`: replacing `parent (extract k)` by `parent k` breaks the exact
  index theorem.
- `P056J_2`: replacing `rawFplus ... (-z)` by `rawFplus ... z` breaks the
  orientation theorem at a symbolic variable.
- `P056J_3`: dropping `sTrial_m_N` changes the main-coordinate normalizer and
  is detected by declaration-shape audit.
- `P056J_4`: a theorem asserting the coordinate defect is zero is forbidden
  in this phase and detected by theorem inventory.
- Direct Lean 4.26, target build, `q3_check`, hole/taint/forbidden-import scan,
  public axiom inventory, proof-DB reimport, and strict Spine run.

## Boundary

Phase 4A may close the XW.6 type and orientation contract only.  The next
phase must identify the coordinate defect with the finite Galerkin residual
and prove its compact-open decay on the same `parent ∘ extract` sequence.
No tail-smallness, every-cluster identification, strict `SlotS2`, route
promotion, or RH claim follows here.
