# GOAL 057 B3.0U ARCHIMEDEAN FORM INTEGRAL REALIZATION CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0U`

## Outcome

The shifted B3.0T form is now identified with its exact whole-line multiplier
integral.  On the same locked form-domain carrier, the explicit B3.0N scalar
shift is removed exactly once to define the unshifted archimedean
sesquilinear form.  The unshifted form is Hermitian and is proved equal to the
integral with the original source archimedean multiplier.

This closes integral realization and shifted/unshifted decomposition only.
It does not construct literal mode elements, identify mode values, synthesize
finite vectors, or prove the finite `-WR` restriction.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchSesquilinearFormIntegral.lean`
- SHA-256:
  `b6dc6d37d18f3d0ca93a3c823187c34f8b45c20fd33f905d75aa5aff0b8ac869`
- Shape: 6,637 bytes, 154 lines, final LF.
- Direct import:
  `Q3.Proofs.RouteB.D0PstarShiftedArchSesquilinearForm`
- B3.0T SHA-256:
  `3f706b4847c5459f244e8bb215adb1254e465f8e8d855d36f1eda9e8a4de3f20`

## Exact public surface

1. `sourceArchimedeanShiftedSesquilinearForm_eq_integral`
2. `sourceArchimedeanSesquilinearForm`
3. `sourceArchimedeanSesquilinearForm_apply`
4. `sourceArchimedeanSesquilinearForm_conj_symm`
5. `sourceArchimedeanSesquilinearForm_eq_integral`

There are no private declarations and no added premises.

## Validation

- canonical KB preflight: no prior B3.0U object or recorded search;
- forbidden tokens: no `sorry`, `admit`, `native_decide`, or new `axiom`;
- direct `lake env lean`: pass;
- target build: `7774/7774`, pass;
- external positive import/API judge: pass;
- negative scope judges: literal-mode wrapper absent; finite synthesis absent;
- all five declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- no finite matrix, Riesz surrogate, generated certificate, W02, Prime,
  compression, or operator-domain input is consumed.

## Decision record

- Chosen: one U module containing the integral realization and the exact
  shifted/unshifted decomposition.
- Rejected: placing the integral theorem back into T, because T's lawful
  meaning is form well-definedness and its smaller import surface is already
  closed.
- What was rejected and why: literal-mode and finite `-WR` results remain in
  V; including them here would re-create the monolithic scratch boundary.
- Risk guarded: double subtraction of the B3.0N shift, replacing the exact
  multiplier by a surrogate, and smuggling a finite restriction into an
  ambient domain-form statement.

## Preserved boundary

```text
PARENT_B3_0_OPEN
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
NO_LITERAL_MODE_FORM_VALUE
NO_FINITE_SYNTHESIS
NO_FINITE_NEG_WR_RESTRICTION
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

The next exact layer is the literal source-mode value and finite
coefficient/`-WR` restriction on the existing B3.0P domain.  It remains a
separate unselected local layer until its own proof and scope audit.

## ACTIONS LOG

- searched the canonical knowledge base and recorded that the territory was
  previously unsearched;
- extracted only the U layer from the compiled scratch candidate;
- ran direct Lean, target build, public API and negative scope judges;
- made no Proshka call, Aristotle submission, N=480 run, route promotion,
  Bus 010 creation, Goal 055 mutation, PX claim, or RH claim.

