# GOAL 057 B3.0T SHIFTED ARCHIMEDEAN SESQUILINEAR FORM WELL-DEFINEDNESS CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0T`

## Outcome

The exact square-root-weighted map is now constructed on the locked B3.0P
shifted archimedean form domain as a complex linear map into whole-line
`L²`.  Its `L²` inner product defines a genuine complex sesquilinear form on
that domain.  The production module also proves the literal application
formula, Hermitian symmetry, and nonnegativity of the real diagonal.

This closes well-definedness of the shifted form only.  It does not identify
the form with the multiplier integral, remove the explicit shift, define an
associated operator, prove closedness or lower semicontinuity, or construct
ambient W02/Prime extensions.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchSesquilinearForm.lean`
- SHA-256:
  `3f706b4847c5459f244e8bb215adb1254e465f8e8d855d36f1eda9e8a4de3f20`
- Shape: 7,167 bytes, 166 lines, final LF.
- Direct import:
  `Q3.Proofs.RouteB.D0PstarShiftedArchFormDomain`
- Parent SHA-256:
  `d2fc68954ae6604d1573bbe37b83e08577f60f4d39f5b9b9f3548821ce866a50`

## Exact public surface

Definitions:

1. `sourceArchimedeanShiftedWeightedLpLinearMap`
2. `sourceArchimedeanShiftedSesquilinearForm`

Theorems:

1. `coeFn_sourceArchimedeanShiftedWeightedLpLinearMap`
2. `sourceArchimedeanShiftedSesquilinearForm_apply`
3. `sourceArchimedeanShiftedSesquilinearForm_conj_symm`
4. `sourceArchimedeanShiftedSesquilinearForm_re_self_nonneg`

Private implementation surface: two definitions and three theorems.  Total
named declarations: eleven.

## Dependency and quotient audit

The map consumes the exact B3.0P subtype.  Membership supplies `MemLp` for
the literal square-root-weighted a.e. representative.  `MemLp.toLp` then
produces the quotient-safe `L²` element.  Additivity and scalar linearity are
proved by `Lp.ext` and a.e. representative equalities; no representative is
chosen as a public datum.

The form is built from the `L²` inner product with the first slot conjugate
linear and the second slot linear.  No finite matrix, Riesz surrogate,
generated PSD certificate, or new premise enters the construction.

## Validation

- knowledge-base preflight: no prior B3.0T object found;
- forbidden tokens: no `sorry`, `admit`, `native_decide`, or new `axiom`;
- direct `lake env lean`: pass;
- target `lake build`: `7773/7773`, pass;
- external positive import/API judge: pass;
- negative scope judges: associated shifted operator absent; integral
  realization theorem absent from the production import;
- public declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- `lake build Q3.Main`: `7809/7809`, pass;
- direct `Q3.Main.RH_of_Weil_and_Q3` axiom extraction unchanged;
- audit invariants: pass;
- `scripts/q3_check.sh`: pass;
- orchestrator unit tests: 90/90 pass.

The aggregate `scripts/check_axioms.sh` wrapper stops before its axiom phase
on pre-existing dead absolute links under `/Users/emalam/Documents/GitHub/`.
That migration defect is outside B3.0T and was not edited or relabelled as a
pass.  The underlying main build and direct axiom extraction both pass.

## Decision record

- Chosen: the narrow T split — weighted `L²` map plus shifted form and its
  intrinsic Hermitian/nonnegative laws.
- Rejected: minting the 394-line scratch monolith, because it also contains
  the future integral, unshifted, literal-mode, finite synthesis and `-WR`
  layers.
- Risk guarded: double subtraction of the shift, conjugate/linear slot
  reversal, and form-domain to operator-domain scope drift.

## Preserved boundary

```text
PARENT_B3_0_OPEN
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
NO_INTEGRAL_REALIZATION
NO_UNSHIFTED_ARCHIMEDEAN_FORM
NO_CLOSEDNESS_OR_LOWER_SEMICONTINUITY
NO_ASSOCIATED_OPERATOR_GRAPH
NO_OPERATOR_DOMAIN
NO_SELECTED_KTRIAL_OPERATOR_DOMAIN
NO_WHOLE_SPACE_W02_EXTENSION
NO_WHOLE_SPACE_PRIME_EXTENSION
NO_COMPRESSION_IDENTITY
NO_PROJECTION_LEAKAGE_DECAY
NO_CONTINUUM_NUMERATOR
H4A1B_OPEN
CHALLENGER_NOT_RH
BUS_010_VOID
GOAL_055_HOLD
PX_RH_CLAIM_NOT_MADE
```

## Next local boundary

The next mathematical layer is the exact integral realization of the shifted
form, followed separately by removal of the explicit shift and the finite
literal/CCM restriction.  No successor is production-authorized by this
closeout.

## ACTIONS LOG

- queried the canonical knowledge base before production validation;
- compared the 394-line scratch surface with the 166-line narrow production
  child;
- ran direct Lean, target build, external API and negative scope judges;
- ran the full main build, direct axiom extraction, audit invariants, Q3 check,
  and orchestrator tests;
- recorded the unrelated aggregate link-check failure without editing it;
- made no Proshka call, Aristotle submission, N=480 run, Route B promotion,
  Bus 010 creation, Goal 055 mutation, PX claim, or RH claim.
