# Codex source record — Goal 058 source-Weil even low-band/head assembly

```yaml
schema: q3_codex_source_record.v1
date: 2026-08-31
branch: rh_clean
implementation_parent: d2bc89524e70ba7842041dd20a40656bce37ce11
source_commit: 556ad653b7b6588472dc1af40572195050c3511d
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: D0PSTAR_SOURCE_EVEN_NONZERO_ORTHONORMAL_SYNTHESIS_LOW_BAND_ASSEMBLY
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
task:
  path: docs/Codex/TASK_2026-08-31_goal058_even_nonzero_low_band_assembly.md
  git_blob: 4aa7af2dccd702f3b927ab1deb38eeb38b69d71d
  sha256: 5444b3439333e4ba22526b106d7b917339753a298d82a0172cc8ce1a14331b17
source:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroLowBandAssembly.lean
  git_blob: f9f354eb41f1a3326800fdaf5cc07c22dc420519
  sha256: 6ddd8cdabdd6b682160e55277f3a35d28fbbe8fa577e4eb58041ff7cdce41681
  bytes: 7035
  lines: 176
  final_lf: true
```

## Result

The source proves ambient orthonormality of the normalized nonzero-even graph
modes, assembles the finite low band and zero-plus-low-band head, and proves
their exact ambient orthogonality to the closed nonzero-even tail.

Public theorem surface:

```text
Q3.RouteB.D0Pstar.sourceWeilGraphAmbient_evenNonzeroMode_orthonormal
Q3.RouteB.D0Pstar.sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis
Q3.RouteB.D0Pstar.sourceWeilGraphAmbient_evenHeadSynthesis
Q3.RouteB.D0Pstar.sourceWeilGraphEvenNonzeroLowBandSynthesis_orthogonal_tail
Q3.RouteB.D0Pstar.sourceWeilGraphEvenHeadSynthesis_orthogonal_tail
```

## Gates

```text
direct Lean: PASS
target build: PASS (7812 jobs)
q3_check: PASS
Q3.Main build: PASS (7809 jobs)
complete EnvDump: PASS (373/373 modules, 3390 declarations)
supplier preflight: EXACT_FIT in fresh harness
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
P9 strict: PASS
```

```text
CLOSES:
  D0PSTAR_SOURCE_EVEN_NONZERO_ORTHONORMAL_SYNTHESIS_LOW_BAND_ASSEMBLY

OPENS:
  SELECTED_FERRERS_EVEN_HEAD_TAIL_EXACT_SHIFT_COERCIVITY_OR_FESHBACH
```

## Provenance and semantic boundary

```yaml
hypothesis_provenance: []
hypothesis_provenance_sha256: 4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945
```

The node adds no theorem hypothesis.  It does not prove graph-inner-product
orthonormality, an exhaustive even direct sum, selected-row compatibility, a
Rayleigh-shift floor, positive Schur margin, G1, G3, Route promotion, or RH.

This package is kernel-green only.  Its declarations must not be consumed by
the selected-shift node until an independent `q3_semantic_attestation.v1`
receipt admits the exact task/source commit and scope.

`PX_RH_CLAIM: NOT_MADE`.
