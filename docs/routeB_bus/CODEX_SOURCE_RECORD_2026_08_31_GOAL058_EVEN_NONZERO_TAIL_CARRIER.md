# Codex source record — Goal 058 source-Weil even nonzero-tail carrier pre-gate

```yaml
schema: q3_codex_source_record.v1
date: 2026-08-31
branch: rh_clean
implementation_parent: ce3fc969588d85ba8f7d337d83c990f6382422cb
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: D0PSTAR_SOURCE_EVEN_NONZERO_TAIL_CARRIER_PRE_GATE
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
task:
  path: docs/Codex/TASK_2026-08-31_goal058_even_nonzero_tail_carrier.md
  git_blob: 48520f7921668fc5acbf668afa9278e502637cec
source:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroTailCarrier.lean
  git_blob: d71832913a0d6e9258b2940a0842e7f0e7b5f426
  sha256: 57d3e5129eeefb7f4a041dcaebe217276458e1328b42489684ad3b8837707719
  bytes: 7278
  lines: 170
  final_lf: true
```

## Result

The source introduces a separate zero graph mode, normalized nonzero-even
pairs `±(n+1)`, and the closed nonzero-even tail beginning at physical
frequencies `±(R+1)`.  It proves the literal ambient crosswalk, low-frequency
coefficient cancellation on the algebraic span and its closure, and ambient
orthogonality of the zero mode to the closed tail.

Public theorem surface:

```text
Q3.RouteB.D0Pstar.sourceWeilGraphAmbient_evenZeroMode
Q3.RouteB.D0Pstar.sourceWeilGraphAmbient_evenNonzeroMode
Q3.RouteB.D0Pstar.sourceWeilGraphEvenNonzeroTailAlgebraic_low_fourier_vanish
Q3.RouteB.D0Pstar.sourceWeilGraphEvenNonzeroTail_low_fourier_vanish
Q3.RouteB.D0Pstar.sourceWeilGraphEvenZeroMode_orthogonal_nonzeroTail
```

## Gates

```text
direct Lean: PASS
target build: PASS (7811 jobs)
q3_check: PASS
Q3.Main build: PASS (7809 jobs)
routeb_status.py --check: CHECK OK
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
independent scope review: GO / narrow_carrier_pre_gate_only
```

```text
CLOSES:
  D0PSTAR_SOURCE_EVEN_NONZERO_TAIL_CARRIER_PRE_GATE

OPENS:
  D0PSTAR_SOURCE_EVEN_NONZERO_ORTHONORMAL_SYNTHESIS_LOW_BAND_ASSEMBLY
```

## Provenance and semantic boundary

```yaml
hypothesis_provenance: []
hypothesis_provenance_sha256: 4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945
```

The node adds no new theorem hypothesis and reuses only existing committed
source-Weil graph/Fourier declarations.  It does not prove an exhaustive even
direct sum, graph orthogonality, orthonormal synthesis, selected-row
compatibility, a Rayleigh-shift floor, Schur margin, complement floor, Route
promotion, or RH.

This package is kernel-green only.  Its declarations must not be consumed by
the next node until an independent `q3_semantic_attestation.v1` receipt admits
the exact task/source commit and scope.

`PX_RH_CLAIM: NOT_MADE`.
