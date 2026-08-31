# Codex task — Goal 058 source-Weil even nonzero-tail carrier pre-gate

Date: 2026-08-31
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / fixed-shift even head-tail Feshbach route

## Exact outcome

Introduce the first source-Weil even carrier pre-gate in production Lean:

- keep the physical zero mode separate;
- index every nonzero reflection-even pair as `±(n+1)`;
- define the closed tail starting at physical frequencies `±(R+1)`;
- prove the exact ambient crosswalk;
- prove that every coefficient with `|n| ≤ R` vanishes on the algebraic span
  and on its closure;
- prove ambient orthogonality of the zero mode to the closed nonzero-even tail.

The implementation path is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroTailCarrier.lean
```

## Downstream consumer

The next consumer is the nonzero-even orthonormal synthesis and finite
low-band assembly needed before any selected-row parity or Feshbach estimate.

## Shelf preflight

The repository-wide query

```text
./ask.sh "source Weil even nonzero tail carrier orthonormal low band"
```

found existing source-Weil graph/Fourier infrastructure and unrelated
candidates, but no exact supplier for this carrier split.  The new file reuses
the existing graph carrier, lift, ambient map, Fourier modes, and their
orthonormality theorem; it introduces no new analytic hypothesis.

## Exact scope

```text
CLOSES:
  D0PSTAR_SOURCE_EVEN_NONZERO_TAIL_CARRIER_PRE_GATE

OPENS:
  D0PSTAR_SOURCE_EVEN_NONZERO_ORTHONORMAL_SYNTHESIS_LOW_BAND_ASSEMBLY
```

## Non-goals

This task does not assert:

- an exhaustive even-sector direct sum;
- graph-inner-product orthogonality;
- orthonormal synthesis of the nonzero-even modes;
- compatibility with the selected production row;
- a Rayleigh-shift floor, Schur margin, complement floor, Route promotion, or
  RH.

## Proof obligations

The source package must pass:

```text
env -u LD_LIBRARY_PATH lake env lean Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroTailCarrier.lean
env -u LD_LIBRARY_PATH lake build Q3.Proofs.RouteB.D0PstarSourceEvenNonzeroTailCarrier
scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroTailCarrier.lean
env -u LD_LIBRARY_PATH lake build Q3.Main
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

Public declarations may depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The source must contain no `sorry`, `admit`, `exact?`,
`native_decide`, or new axiom.

## Semantic quarantine

Kernel acceptance is not semantic admission.  After the source package is
committed, register exactly one `KERNEL_GREEN` entry bound to the task blob,
source commit/blob, theorem IDs, consumer, scope, normalization, domain, and
quantifiers.  Do not consume the new declarations downstream until an
independent `q3_semantic_attestation.v1` receipt admits that exact entry.

Route status remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
