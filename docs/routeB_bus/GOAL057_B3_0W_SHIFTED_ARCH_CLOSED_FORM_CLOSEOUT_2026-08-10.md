# GOAL 057 B3.0W SHIFTED ARCHIMEDEAN CLOSED-FORM CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0W`

## Outcome

The exact B3.0T square-root-weight multiplication map is now packaged as a
maximal partial linear map with exactly the already locked shifted
archimedean form domain, and that partial map is proved closed.

Its extended `L2` root energy on the whole ambient Hilbert space is proved
lower semicontinuous and finite exactly on the form domain. Squaring that
energy gives an extended nonnegative quadratic form which is also lower
semicontinuous and agrees, on the domain, with the real diagonal of the exact
B3.0T shifted sesquilinear form.

This is the closed-form analytic layer only. It is not the source-associated
Weil operator and it does not consume or construct W02, Prime, the full source
Weil form, compression, or the continuum numerator.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchClosedForm.lean`
- SHA-256:
  `710b840837c2ecb4ec2da3a7a146f16d9c93ce0738466b5089f5a07d598af24c`
- Shape: 10,912 bytes, 248 lines, final LF.
- Direct project import:
  `Q3.Proofs.RouteB.D0PstarShiftedArchSesquilinearForm`
- Execution predecessor B3.0V is closed, but the honest direct proof
  dependency is B3.0T; no false V-to-W dependency is asserted.

## Exact public surface

1. `sourceArchimedeanShiftedWeightedLpPMap`
2. `sourceArchimedeanShiftedWeightedLpPMap_apply`
3. `sourceArchimedeanShiftedWeightedLpPMap_isClosed`
4. `sourceArchimedeanShiftedFormRootEnergy`
5. `mem_sourceArchimedeanShiftedFormDomain_iff_rootEnergy_lt_top`
6. `sourceArchimedeanShiftedFormRootEnergy_lowerSemicontinuous`
7. `sourceArchimedeanShiftedExtendedQuadraticForm`
8. `sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous`
9. `sourceArchimedeanShiftedFormRootEnergy_eq_enorm`
10. `sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re`
11. `mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top`

One private pointwise image definition and one private measurability theorem
bring the total proof-database import to 13 named declarations.

## Validation

- canonical KB preflight: no prior B3.0 post-V closed-form object or recorded
  search;
- forbidden tokens: no `sorry`, `admit`, `native_decide`, or new `axiom`;
- direct `lake env lean`: pass;
- target build: `7774/7774`, pass;
- external positive import/API judge: pass;
- negative scope judges: bounded Weil perturbation absent; full source Weil
  form absent; source-associated Weil operator absent;
- all eleven public declarations depend only on `propext`,
  `Classical.choice`, and `Quot.sound`;
- `lake build Q3.Main`: `7809/7809`, pass;
- direct `Q3.Main.RH_of_Weil_and_Q3` axiom extraction unchanged;
- `bash scripts/q3_check.sh`: pass;
- orchestrator unit tests: 90/90 pass;
- proof database: 13/13 declarations imported.

## Decision record

- Chosen: extract only the maximal square-root multiplier, closedness, root
  energy, and lower-semicontinuity layer from the compiled scratch.
- What was rejected and why: the 372-line scratch monolith was rejected
  because it imports and bundles future W02/Prime bounded perturbations and the
  full source Weil extended form into an analytic fact that needs none of them.
- Also rejected: naming this partial map the source-associated Weil operator;
  the operator representation graph and its single-valuedness remain open.
- Risk guarded: form-domain/operator-domain collapse, dependency inversion,
  finite-dimensional surrogate closedness, and W02/Prime scope smuggling.

## Preserved boundary

```text
PARENT_B3_0_OPEN
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
SHIFTED_ARCH_ROOT_MULTIPLIER_CLOSED
SHIFTED_ARCH_EXTENDED_QUADRATIC_FORM_LSC
NO_SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH
NO_OPERATOR_DOMAIN
NO_SELECTED_KTRIAL_OPERATOR_DOMAIN
NO_WHOLE_SPACE_W02_EXTENSION
NO_WHOLE_SPACE_PRIME_EXTENSION
NO_SOURCE_WEIL_AMBIENT_FORM
NO_COMPRESSION_IDENTITY
NO_PROJECTION_LEAKAGE_DECAY
NO_CONTINUUM_NUMERATOR
H4A1B_OPEN
CHALLENGER_NOT_RH
BUS_010_VOID
GOAL_055_HOLD
N480_HOLD
GLOWER_CERT_NOT_FOUND_READONLY
PX_RH_CLAIM_NOT_MADE
```

## Next local boundary

The next candidate layer is the bounded W02/Prime construction needed before
the full lower-semicontinuous source Weil form can be assembled. It remains a
separate unselected production child pending exact import and carrier audit.

## ACTIONS LOG

- searched the canonical knowledge base before minting the W object;
- split the closed-form analytic layer from the later bounded perturbations;
- ran direct Lean, target and full builds, public API and negative scope
  judges, axiom extraction, q3_check, and all orchestrator unit tests;
- imported 13/13 declarations into the proof database;
- made no Proshka call, Aristotle submission, N=480 run, route promotion,
  Bus 010 creation, Goal 055 mutation, PX claim, or RH claim.

