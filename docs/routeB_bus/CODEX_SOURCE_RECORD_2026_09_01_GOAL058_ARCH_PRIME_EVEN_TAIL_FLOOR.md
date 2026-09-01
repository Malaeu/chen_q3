# Codex source record — Goal 058 Arch-Prime even-tail floor

```yaml
schema: q3_codex_source_record.v1
date: 2026-09-01
branch: rh_clean
implementation_parent: 8bddaa6faf35e093f0a8459d15381c4c6d27305e
source_commit: 4632841fbe5aba839e5535c9175d497f085e8103
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_EXPLICIT_ALGEBRAIC_FLOOR
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
task:
  path: docs/Codex/TASK_2026-09-01_goal058_arch_prime_even_tail_floor.md
  git_blob: 4b5e85dc2ab0fc74ff8b0b3efd5b0caa5b5589f5
  sha256: 0fd590aa2ae287b4170bbf9518a56e00b3b1d5ca90906a73eeb754b73d248540
primary_source:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
  git_blob: f9dc5ce21e00802fcb2488a61c504e957c372691
  sha256: 1a5d37851bd0092ad6e3c6942293900b71e7566be86d58ed36649a668c68665b
  bytes: 31581
  lines: 703
  final_lf: true
```

## Result

The source adds exactly one theorem:

```text
Q3.RouteB.D0Pstar.sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift
```

It combines the already admitted source Archimedean lower bound with the
global Prime form-norm upper bound.  On every algebraic nonzero-even tail
synthesis after `sourceWeilEvenTailCutoff i`, the real Arch-Prime quadratic
form dominates

```text
(‖sourceW02AmbientContinuousSesquilinearForm i‖ + 1/2) * ‖v‖².
```

No new definition, hypothesis, source object, or cutoff enters the result.

## Gates

```text
direct Lean: PASS
target build: PASS (7817/7817 jobs)
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
git diff --check: PASS
independent semantic reviews: ADMIT / PRODUCTION_THEOREM
```

```text
CLOSES:
  D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_EXPLICIT_ALGEBRAIC_FLOOR

OPENS:
  ADAPTIVE_SELECTED_FINITE_TAIL_TO_LITERAL_TOBLOCKS22_CROSSWALK
  ADAPTIVE_SELECTED_CUTOFF_DOMINATION_R_LE_N
  FINITE_EVEN_HEAD_CORRECTED_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

## Provenance and semantic boundary

```yaml
hypothesis_provenance: []
hypothesis_provenance_sha256: 4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945
```

This is a genuine but tail-local dependency reduction: retained Prime decay
is no longer a separate input on the coarse algebraic even tail.  It does not
place that tail inside the selected finite carrier, does not subtract the
exact selected Rayleigh scalar with a positive gap, and supplies no corrected
finite-head Schur margin.  The selected consumer remains open.

This package is kernel-green only.  Its declaration must not be consumed by a
later theorem until an independent `q3_semantic_attestation.v1` receipt admits
the exact task/source package and scope.

`PX_RH_CLAIM: NOT_MADE`.
