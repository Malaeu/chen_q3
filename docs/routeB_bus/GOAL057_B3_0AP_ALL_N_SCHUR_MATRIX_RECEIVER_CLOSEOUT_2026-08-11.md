# STATUS: CORRECTED CLOSED HELPER — B3.0AP ALL-N SCHUR MATRIX RECEIVER PROVED; SIGN OPEN

Date: 2026-08-11
Route: `CHALLENGER / NOT_RH`
Goal: `057_unified_chain_program_delegated_review`
Child: `B3.0AP`
Result code: `GOAL057_B3_0AP_ALL_N_SCHUR_MATRIX_RECEIVER_PROVED`
Correction: the earlier canonical-`N = 0` closeout was invalidated by a clean
source rebuild and is superseded by this record.
Parent B3.0: `OPEN`

## What was proved

The production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurMatrixReceiver.lean`
keeps the exact B3.0AO target

```lean
SourceWeilOddTargetFloorSchurPositive13 :=
  ∀ N, (sourceWeilOddTargetFloorSchurComplement
    (PairIndex.mk 13 N (by norm_num))).IsPositive
```

literally unchanged and proves, for every auxiliary `N`:

1. the ambient component of the literal odd graph-head synthesis is the
   normalized odd CCM synthesis;
2. the graph-domain head has an explicit finite sum of normalized
   antisymmetric source modes;
3. after finite sesquilinear expansion, the source-Weil form on this sum is
   independent of the auxiliary coordinate;
4. the finite sum crosses exactly to the existing B3.0AF odd-form pullback;
5. the normalized odd synthesis preserves the ambient inner product;
6. the target-floor head pairing is the exact
   `ccmWeilMatFinite 13 sourceWeilOddTailCutoff` form minus the target-floor
   scalar form;
7. the Schur pairing additionally subtracts the actual inverse-weighted
   infinite-tail correction;
8. the original all-`N` target is equivalent to nonnegativity of that exact
   corrected CCM energy for every `N`.

No equality of the large source graph carriers or Schur operators across
different `N` is claimed.

## Correction of the stale-olean false positive

The superseded B3.0AP record claimed that the carrier, target-floor graph
operator, Schur operator and Schur energy were definitionally independent of
`PairIndex.N`, and reduced the target to `N = 0`. A forced clean build showed
that the source did not establish those equalities: the large reductions timed
out or exceeded recursion depth, and the advertised graph-head `rfl` was not a
valid source proof. Earlier PASS evidence came from a stale `.olean`.

The repair does not weaken the registered target. It removes the invalid
canonical reduction and proves the exact all-`N` receiver through a small,
explicit mode-sum crosswalk.

## What was not proved

- no nonnegativity/sign certificate for the corrected CCM energy;
- no proof of `SourceWeilOddTargetFloorSchurPositive13`;
- no global equality or definitional independence of graph carriers,
  target-floor graph operators, Schur operators or Schur energies across `N`;
- no literal odd-mode form-core theorem;
- no whole odd-space `10^-58` floor;
- no selected-`kTrial` operator domain, projection-leakage decay or continuum
  numerator bridge;
- no N=480/N=960 promotion, Route B promotion, PX claim or RH claim.

## Evidence

- Lean SHA-256:
  `48d5f17bc4d6094db69fd52ad36376bc3062eaaeb678d0c2e862911319435fd8`.
- Shape: `12069` bytes, `266` newline-terminated lines, final LF.
- Public surface: `1` definition and `8` theorems; `9` named declarations.
- Direct source Lean: PASS.
- Forced clean target module build: PASS (`7821/7821`).
- External production-import consumer: PASS for all nine declarations and the
  exact all-`N` corrected-energy equivalence.
- `Q3/Main.lean`: PASS (`7809/7809`); the existing main axiom chain is
  unchanged.
- `scripts/q3_check.sh`: PASS independently on all three touched Lean files.
- Unit tests: `102/102` PASS after registry synchronization.
- Proof registry: `9/9` B3.0AP declarations present; `204/204` Route B files
  matched; `1756` declarations total; no missing, ambiguous or stale rows.
- Public axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden-token scan: no `sorry`, `admit`, `native_decide` or `unsafe`.
- Negative-scope judge: no theorem directly exports
  `SourceWeilOddTargetFloorSchurPositive13`; only exact equivalences are added.
- Strict Spine: `P9_STRICT_PASS`, semantic index PASS, tool manifest PASS after
  the final corrective goal-close refresh.

## Decision and corrected rationale

- Chosen: preserve the literal all-`N` predicate and descend only on the finite
  odd-mode span, where an explicit mode-sum expansion makes the source-form
  crosswalk kernel-checkable.
- What was rejected and why: the canonical `N = 0` operator reduction was
  rejected because a clean source build disproved its claimed proof status;
  treating auxiliary `N` as a head dimension, replacing the symbolic cutoff
  by N=480/N=960, using a scalar inverse, or dropping the actual
  `R† C⁻¹ R` correction would change the object.
- Guarded risk: the exact receiver equivalence must not be reported as the
  missing sign.

## Stop and next action

Stop code:
`EXACT_ALL_N_CORRECTED_CCM_ENERGY_NONNEGATIVITY_CERTIFICATE_MISSING`.

Next action: source-lock the B3.0AO strategic MINT packet to this corrected
all-`N` receiver and, only after separate owner approval for the outbound
message, ask the same living Proshka phase chat for a source-faithful sign
certificate architecture. The first coarse checkpoint remains open: `0/10`
closed.

## Search and arsenal

`SEARCH_FLAGS: KB_ASK_SOURCE_WEIL_ODD_TARGET_FLOOR_SCHUR_POSITIVE13_NO_HIT · WHOLE_REPO_TARGET_SEARCH · DECLARATION_CATALOG_CHECK`

`ARSENAL_USED: C04 · C07 · C09 · C10`

`ARSENAL_KILLED: CANONICAL_N0_LARGE_OPERATOR_REDUCTION · AUXILIARY_N_AS_HEAD_SIZE · FINITE_N480_N960_AS_SYMBOLIC_CUTOFF · SCALAR_OUTER_INVERSE · DROP_ACTUAL_RSTAR_CINV_R · RECEIVER_EQUIVALENCE_AS_SIGN`

## ACTIONS LOG

1. Forced a clean source build and invalidated the stale-olean canonical-`N`
   result instead of preserving a false green record.
2. Exposed the finite shifted-domain synthesis expansion and the normalized
   odd mode-sum crosswalk.
3. Rebuilt B3.0AP as an exact all-`N` corrected CCM receiver with no global
   graph/operator equality.
4. Verified direct Lean, forced clean target build, external consumer, full
   main, all touched-file q3 checks, public axioms and negative scope.
5. Synchronized the proof registry from `8` missing and `7` stale rows to zero
   drift and reran all `102` unit tests.
6. Preserved the unrelated PDF and made no Proshka call, Aristotle submission,
   N=480/N=960 run, route promotion or claim.

Boundaries remain:
`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4A1B OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
