# GOAL 057 B3.0V ARCHIMEDEAN FORM FINITE `-WR` RESTRICTION CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0V`

## Outcome

The exact unshifted B3.0U archimedean sesquilinear form is now evaluated on
literal source modes and on the pre-existing finite CCM synthesis. In the
locked `CCMModeFinite` order, its finite restriction is proved equal to the
negative `ccmWREntry` matrix form.

The finite synthesis is lifted into the shifted-form domain through the
already closed B3.0R inclusion `E_m_N_le_sourceArchimedeanShiftedFormDomain`.
Its carrier in `H_m` remains definitionally the existing
`ccmFiniteSynthesis`; no second finite space, coefficient order, or surrogate
matrix is introduced.

This closes the literal-mode and finite `-WR` restriction layer only. It does
not construct an ambient W02 form, a Prime form, the full source Weil form, an
associated operator, compression, or the continuum numerator.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchSesquilinearFormFiniteRestriction.lean`
- SHA-256:
  `678714fea101cd484a1b98b863cc1b594f1c2f4fc09625d4d793e78754b3030b`
- Shape: 5,865 bytes, 146 lines, final LF.
- Direct source locks:
  - `D0PstarArchSesquilinearFormIntegral.lean`
  - `D0PstarShiftedArchFiniteModeDomain.lean`
  - `D0PstarSourceArchModePairingKernel.lean`
  - `D0PstarCCMFiniteSourceResidual.lean`
  - `D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean`

## Exact public surface

1. `sourceArchimedeanModeInShiftedFormDomain`
2. `sourceArchimedeanSesquilinearForm_apply_mode`
3. `ccmFiniteShiftedFormDomainSynthesis`
4. `coe_ccmFiniteShiftedFormDomainSynthesis`
5. `sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis`
6. `sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR`

Two private bridge theorems prove membership in the existing `E_m_N` and
identify the canonical lifted synthesis with its literal finite sum. The
proof database imported all eight named declarations.

## Validation

- canonical KB preflight: no prior B3.0V object or recorded search;
- forbidden tokens: no `sorry`, `admit`, `native_decide`, or new `axiom`;
- direct `lake env lean`: pass;
- target build: `7792/7792`, pass;
- external positive import/API judge: pass;
- negative scope judges: ambient W02 form absent; full source Weil form absent;
  associated source Weil operator absent;
- all six public declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- `lake build Q3.Main`: `7809/7809`, pass;
- direct `Q3.Main.RH_of_Weil_and_Q3` axiom extraction unchanged;
- `bash scripts/q3_check.sh`: pass;
- orchestrator unit tests: 90/90 pass.

## Decision record

- Chosen: lift the existing `ccmFiniteSynthesis` through the exact B3.0R
  inclusion, then evaluate the B3.0U form on that unchanged carrier.
- What was rejected and why: the scratch-style duplicate proof from a freshly
  written subtype sum was rejected because it would duplicate the carrier and
  make coefficient order and membership provenance easier to drift.
- Also rejected: bundling W02, Prime, the full Weil form, or an associated
  operator into V; none is required for the exact finite `-WR` restriction.
- Risk guarded: finite-to-ambient scope smuggling, sign loss, carrier/order
  drift, and silently replacing an exact source identity by a numerical or
  generated certificate.

## Preserved boundary

```text
PARENT_B3_0_OPEN
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
NO_CLOSEDNESS_OR_LOWER_SEMICONTINUITY
NO_ASSOCIATED_OPERATOR_GRAPH
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

The B3.0V successor is intentionally unselected. The next action is local
post-V cartography of the closedness/operator and bounded W02/Prime candidates,
followed by selection of the smallest lawful successor. No Proshka call or
production successor is implied by this closeout.

## ACTIONS LOG

- searched the canonical knowledge base before minting the V object;
- reused the exact B3.0R carrier inclusion and the existing finite synthesis;
- ran direct Lean, target and full builds, public API and negative scope
  judges, axiom extraction, q3_check, and all orchestrator unit tests;
- imported 8/8 declarations into the proof database;
- made no Proshka call, Aristotle submission, N=480 run, route promotion,
  Bus 010 creation, Goal 055 mutation, PX claim, or RH claim.

