# Codex source record — Goal 058 explicit source-Weil even-tail coercivity

```yaml
schema: q3_codex_source_record.v1
date: 2026-09-01
branch: rh_clean
implementation_parent: a8535a8a93fd35a01fbc3ec30db728d8e20141ea
source_commit: 8a8010f846990c462cfec80921ec51ba32b0df75
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: D0PSTAR_SOURCE_WEIL_EVEN_TAIL_EXPLICIT_UNSHIFTED_COERCIVITY
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
task:
  path: docs/Codex/TASK_2026-09-01_goal058_even_tail_explicit_coercivity.md
  git_blob: 686b4854333f85df9b30e383513cf873336e6251
  sha256: 227682ba827e770f19ae24fccb0c14a3d21e0ddb43b2f3a14759609e90a18e9c
primary_source:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
  git_blob: 1c61823b4eff8790a40e86d0a0f1a13630a0721a
  sha256: 003e7d21bc3e8fb5735b914eb8241ec804aa4518fb8ec9a72a5cd1a849f22ac8
  bytes: 29404
  lines: 659
  final_lf: true
supporting_sources:
  - path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCoercivityClosure.lean
    git_blob: 87046415791f712d6117823a231c5645a9eaf07b
    sha256: 6031c727be06b12616e197d412dd402e2d9574060b5e6805e1775b630362e5d9
  - path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailExplicitCoercivity.lean
    git_blob: d47ec0437b7394653af1ed5a997b92c73d7493c3
    sha256: 481ab9c95e9dc79f2ebe6902e610e63dd9e4e27aaced63ba0dc81299d4861586
```

## Result

The source proves the parity-even analogue of the admitted explicit odd-tail
coercivity theorem.  The normalized symmetric source modes are orthonormal,
their literal Fourier representatives satisfy the same coarse inverse-mode
low-band envelope, and the integrated `1/R` loss can be absorbed against the
source archimedean form.  After W02/Prime absorption, the algebraic estimate
extends through the exact graph topology to the closed nonzero-even tail.

Public theorem surface admitted by this package:

```text
Q3.RouteB.D0Pstar.sourceWeilGraphTailAmbientCoercive_of_algebraic
Q3.RouteB.D0Pstar.sourceWeilEvenAmbientMode_orthonormal
Q3.RouteB.D0Pstar.coeFn_sourceLogWindowFourierL2Isometry_apply_evenAmbientMode
Q3.RouteB.D0Pstar.norm_sourceWeilEvenAmbientModeFourier_le_lowBand_inv
Q3.RouteB.D0Pstar.norm_sourceWeilEvenAmbientFinsuppShift_sq
Q3.RouteB.D0Pstar.integral_norm_sourceWeilEvenFourierFinsuppShift_sq_le_lowBand
Q3.RouteB.D0Pstar.sourceArchimedeanSesquilinearForm_re_self_lower_evenGraphFinsuppShift
Q3.RouteB.D0Pstar.sourceWeilSesquilinearForm_re_self_lower_evenGraphFinsuppShift
Q3.RouteB.D0Pstar.sourceWeilEvenTailAlgebraicCoercive_explicit
Q3.RouteB.D0Pstar.sourceWeilEvenTailAmbientCoercive_explicit
```

## Gates

```text
direct Lean: PASS (3/3 touched modules)
target build: PASS (7817/7817 jobs)
q3_check: PASS (3/3 touched modules)
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
git diff --check: PASS
independent review: GO, 0 CRITICAL/HIGH/MEDIUM/LOW findings
```

```text
CLOSES:
  D0PSTAR_SOURCE_WEIL_EVEN_TAIL_EXPLICIT_UNSHIFTED_COERCIVITY

OPENS:
  SELECTED_CUTOFF_SCHEDULE_DOMINATION_OR_DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY
  SELECTED_RAYLEIGH_UPPER_ENVELOPE
  FULL_ROW_RAYLEIGH_TO_EVEN_PROBE_LEDGER
  FINITE_EVEN_HEAD_SCHUR_MARGIN
```

## Provenance and semantic boundary

```yaml
hypothesis_provenance: []
hypothesis_provenance_sha256: 4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945
```

The result is unshifted and begins only at the explicit common odd/even
cutoff.  It does not assert that this cutoff lies below the selected `i.N`,
does not subtract the selected Rayleigh scalar, and does not supply any finite
head or Schur margin.  Those are separate open dependencies.

This package is kernel-green only.  Its declarations must not be consumed by a
selected-shift theorem until an independent `q3_semantic_attestation.v1`
receipt admits the exact task/source package and scope.

`PX_RH_CLAIM: NOT_MADE`.
