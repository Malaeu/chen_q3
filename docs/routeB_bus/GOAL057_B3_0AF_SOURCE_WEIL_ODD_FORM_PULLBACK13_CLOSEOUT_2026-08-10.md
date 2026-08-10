# GOAL 057 B3.0AF SOURCE WEIL ODD FORM PULLBACK13 CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0AF`

SEARCH_FLAGS: `WHOLE_REPO_NO_IGNORE`, `MATHLIB_API`,
`SOURCE_ADDRESSED_POST_AE_VERDICT`, `EXCLUDE_Q3_PROOFS_PRIMECERT`

ARSENAL_USED: `C04,C09,C10`

## Outcome

The exact normalized odd coefficient carrier at `m = 13` is now embedded
isometrically into literal CCM order `-N,...,0,...,N`, synthesized
isometrically into the existing shifted source-Weil form domain, and pulled
back through the already-proved source Weil sesquilinear form.

This closes only `OddSourceWeilCompression13_FORM_PULLBACK`.  It does not
prove an odd form core, a direct full-domain odd tail theorem, Yoshida tail
coercivity, a residual/Feshbach lower bound, an associated operator, selected
trial operator-domain membership, projection-leakage decay, or the continuum
numerator.

## Controlling verdict

- Archived Proshka verdict:
  `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL057_B3_0_POST_AE_REPRESENTATION_RERANK_2026-08-10.md`
- Exact SHA-256:
  `11604d7711176e8bc88309d0d02aaf1bf2e0edf014670023d9e90933db38ac8d`
- Adopted PRIMARY:
  `TRY_GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT`
- Verdict argument: the immediate G-LOWER target is a form lower bound, so an
  associated operator is not a prerequisite for the exact finite odd
  form-pullback child.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddFormPullback13.lean`
- SHA-256:
  `d6012feac269da284ce0a2a9a54a14142aff70046d9bd5ab77a1ba11daa849e4`
- Shape: 7,104 bytes, 196 newline-terminated lines, final LF.
- Exact direct imports:
  `D0PstarSourceWeilClosedForm`,
  `D0PstarShiftedArchFiniteModeDomain`,
  `D0PstarCCMFiniteRieszOperator`.

## Exact public surface

Exactly three public declarations:

1. `ccmOddCoefficientIsometry`;
2. `sourceWeilOddSynthesis13`;
3. `sourceWeilOddFormPullback13`.

There is no public `OddWeilMatrix` alias.  The theorem retains the literal
`ccmWeilMatFinite 13 N`, conjugate-linear first slot, and linear second slot.
The file contains 12 private helpers and 15 total named declarations.

## Validation

- direct Lean and target build `7807` jobs: pass;
- full `lake build` `7817` jobs: pass;
- direct `Q3/Main.lean`: pass;
- `bash scripts/q3_check.sh`: pass;
- orchestrator unit tests: 90/90 pass;
- external consumer compiled against the actual production import: both public
  isometries preserve norm, the public form-pullback theorem consumes exactly,
  and the shifted-energy identity keeps the explicit lower-bound shift;
- public axiom chain for all three declarations:
  `propext`, `Classical.choice`, `Quot.sound` only;
- proof database: 15/15 declarations imported as proven; repeat import
  idempotent;
- no `sorry`, `admit`, `native_decide`, new `axiom`, public matrix alias,
  operator graph/domain, selected-trial-domain, compression-operator,
  projection-leakage, continuum-numerator, N=480, PX, or RH declaration;
- the required third import supplies the finite synthesis carrier, but the
  production body does not use `sourceCCMFiniteRieszOperator` as a form
  supplier.

## Mandatory judges

- `P057_GLOWER_ODD_PULLBACK_POSITIVE_CONTROL_N1`: PASS.  The unit vector maps
  to `(-1/sqrt 2, 0, +1/sqrt 2)`, has norm one, is odd under reflection, and
  yields the diagonal-minus-antipodal matrix entry.
- `GLOWER_ODD_PULLBACK_PARITY_SIGN_MISMATCH`: FIRED.  Replacing the negative
  coefficient by a positive one breaks orthonormality and the N=1 sign control.
- `GLOWER_ODD_PULLBACK_NORMALIZATION_MISMATCH`: FIRED.  Removing
  `1/sqrt 2` breaks the isometry/norm control.
- `GLOWER_SHIFTED_ENERGY_RAW_FORM_CONFLATION`: FIRED.  Deleting the explicit
  shift leaves the unsolved equality
  `raw + sourceWeilLowerBoundConstant * norm_sq = raw`.
- All mutations were reverted; the final source recompiled afterwards.

## Decision record

- Chosen: the verdict's narrow form-level normalized odd pullback, with exactly
  the three allowed public declarations.
- What was rejected and why: operator-first G-LOWER work, generic Kato
  infrastructure, source acquisition, and N=480 were rejected as the current
  action because none is required to restrict the existing form.  Within the
  implementation, direct reuse of `ccmFiniteSynthesisEquiv` was rejected
  because its only apply bridge is private; a private exact synthesis isometry
  was reconstructed from `ccmFiniteShiftedFormDomainSynthesis` and the
  existing orthonormal mode family instead of widening the upstream API.
- Risk guarded: parity-sign drift, missing `1/sqrt 2`, first-slot conjugation
  drift, raw/shifted-energy conflation, redundant matrix API, and an
  operator/domain claim smuggled into a form theorem.

## Preserved boundary

```text
PARENT_B3_0_OPEN
ODD_SOURCE_WEIL_COMPRESSION13_FORM_PULLBACK_CLOSED
ODD_MODE_SPAN_FORM_CORE13_OR_DIRECT_ODD_TAIL_DOMAIN_CLOSURE_OPEN
YOSHIDA_TAIL_COERCIVITY13_EXPLICIT_OPEN
ODD_FORM_RESIDUAL_FESHBACH_LOWER13_OPEN
SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH_OPEN
SELECTED_KTRIAL_OPERATOR_DOMAIN_OPEN
NO_PROJECTION_LEAKAGE_DECAY
NO_CONTINUUM_NUMERATOR
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
H4A1B_OPEN
CHALLENGER_NOT_RH
BUS_010_VOID
GOAL_055_HOLD
N480_HOLD
PX_RH_CLAIM_NOT_MADE
```

## Next real boundary

`GLOWER_ODD_FORM_CORE_OR_DIRECT_TAIL_DOMAIN_MISSING`: prove either an explicit
odd form core adequate for the tail passage or a direct odd-tail theorem
already quantified over the full odd form domain.  Hilbert-norm density alone
is not a form-core proof.

## ACTIONS LOG

- archived and consumed the exact post-AE Proshka rerank;
- preflighted the exact public surface and dependencies before writing;
- proved the normalized odd coefficient isometry, shifted-domain synthesis
  isometry, and exact source-Weil form pullback;
- ran the positive N=1 control and all three mandatory negative mutations;
- ran direct/target/full Lean builds, external API judge, q3_check, direct main,
  90 orchestrator tests, and exact axiom extraction;
- imported 15/15 declarations into the proof database twice without row growth;
- kept N=480 on HOLD and made no Aristotle submission, route promotion,
  checkpoint decrement, Bus 010 creation, Goal 055 mutation, PX claim, or RH
  claim.

PROSHKA_CALL: CONSUMED_ARCHIVED_POST_AE_VERDICT
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
N480: HOLD
PX_RH_CLAIM: NOT_MADE

