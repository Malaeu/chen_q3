# Goal 058 literal complex trial-line Feshbach closeout

Date: 2026-08-13

## Verdict

```yaml
TARGET_ID: GOAL058_ARISTOTLE_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH
VERDICT: PASS_FINITE_EXACT_IDENTITY
SUCCESS: GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_PROVED
SCOPE: FINITE_CELL
VERIFIER: LEAN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Source lock and Aristotle provenance

The source-locked task was pinned to commit
`9109c42be4f981df40968edb01e6d33660676208`.  Its controlling inputs were:

```text
prompt sha256:    466f52bb6cd2e8fd9c8e5e4684cb289ad3002958299fc8fee86b54eff555a9f5
harness sha256:   512a614297078e831071e6a4630a273d4c56a58f475db7489d865def49095044
connector sha256: dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb
```

Aristotle project `0bf0fd63-4122-4627-8920-66dba6a7b98e`, task
`7b561338-a1e8-4535-b301-98c5eb880918`, returned
`GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH_PROVED`.  The downloaded archive
had SHA-256
`41c99a1b5c608ef924142a2602788302e965f685eb195948454ffc0a1dbdf4a8`.
The accepted candidate source had SHA-256
`27e79fb9927a350e40583c5b27490d1a81d573864d4a6e8cbe3847bec3c09b16`.

Aristotle reported two service-environment limitations: its checkout could not
replay the repository commit relock, and an unrelated transitive module did not
elaborate against its newer vendored Mathlib.  Neither limitation was used as
proof evidence.  The returned file was independently validated below in the
canonical production checkout and production Lean toolchain.

## Integrated theorem

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59ComplexTrialLineFeshbach.lean
sha256: 27e79fb9927a350e40583c5b27490d1a81d573864d4a6e8cbe3847bec3c09b16
```

The sole direct import is
`Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector`.  The two public
definitions and two source-specialized public theorems are:

```text
Q3.RouteB.complexTrialLineComplement
Q3.RouteB.sourceCCMComplexTrialComplementBlock
Q3.RouteB.sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
Q3.RouteB.sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
```

For the literal source objects

```text
q = D0Pstar.sourceCCMComplexRow S i
K = D0Pstar.sourceCCMFiniteMatrix i
a = D0Pstar.sourceCCMFiniteRayleigh S i
r = D0Pstar.sourceCCMFiniteResidual S i
Q = I - |q><q|
```

the main theorem proves exactly

```text
K - a I = |q><r| + |r><q| + Q (K - a I) Q.
```

The proof derives the right-block conjugation from Hermiticity, uses the
literal residual orientation `K q - a q`, and includes the zero-residual
branch without dividing by a residual, overlap, or gap.

## Plants and validation

The mandatory finite plants passed:

1. P5 distinguishes `vecMulVec q (star q)` from the reversed complex
   orientation on the exact row `(3/5, 4i/5)`.
2. P6 detects the sign mutation `Kq-aq -> aq-Kq` on the swap matrix.
3. P7 shows that the unit hypothesis cannot be dropped using `q=(2,0)`.
4. P8 accepts the exact zero-residual Hermitian eigenvector branch.

Production validation:

```text
direct lake env lean: PASS
target lake build: PASS (7793 jobs)
full lake build: PASS (7817 jobs)
q3_check: PASS
forbidden proof/circularity scans: PASS
git diff --check: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

The only diagnostics were three unused-binder linter warnings for `hq` on
private block helpers whose locked interfaces intentionally retain the unit
hypothesis.  No source theorem or public head was weakened.

## Exact evidence boundary

This is `[FINITE_CELL][LEAN]` exact representation progress.  It identifies
the literal off-diagonal coupling as `r` and the remaining shifted complement
as `Q(K-aI)Q`.  It does **not** prove:

```text
a positive complement floor
a spectral gap or simplicity
simple-even ground existence
smallness or decay of r
residual/floor decay
a coupled cofinal schedule
ground-to-trial tracking
G1 or G3
Route B promotion
RH
```

The next source boundary is therefore no longer an unnamed Schur block: it is
the joint derivation of a positive literal complement floor and decay of the
literal residual divided by that floor on one precommitted coupled schedule.

## Search flags and rejected alternatives

```yaml
SEARCH_FLAGS:
  - GOAL058_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH
  - LITERAL_CCM_COMPLEMENT_FLOOR
  - LITERAL_RESIDUAL_OVER_FLOOR_DECAY
ARSENAL_USED:
  - exact Hermitian four-block decomposition
  - literal source residual
  - source-locked Aristotle draft
  - production Lean validation
REJECTED:
  - scalar commutator as coupling: tautological and wrong observable
  - realification or parity of the complex trial row: unavailable and unnecessary
  - hgap/hfloor receiver as source supplier: circular at the open boundary
AUTOPSY: dropped=DEPENDENCY; note=Finite algebra now names the two exact source quantities, but neither the floor nor its cofinal residual ratio is supplied.
```
