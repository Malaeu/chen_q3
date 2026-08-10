# GOAL 057 B3.0AC ARCH-PRIME SHIFTED LEDGER CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0AC`

## Outcome

The bounded Prime form is now restricted to the dense shifted Arch form
domain, and the exact Arch-minus-Prime sesquilinear ledger is proved there.
On the canonical finite synthesis it is exactly the double sum for
`-ccmWREntry - ccmPrimeEntryN1`.

The first T-only import attempt was rejected by Lean because the required
finite carrier API belongs to B3.0V. The production module therefore imports
the precise V restriction API plus B3.0AB. It does not import W02 or construct
the full source Weil form.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarArchPrimeSesquilinearForm.lean`
- SHA-256:
  `f48968defbe9566f2dc9095f993a10381acde92d3598a303ff2079d8b1047ec6`
- Shape: 5,971 bytes, 151 lines, final LF.
- Direct imports: B3.0V finite Arch restriction and B3.0AB ambient Prime.

## Exact public surface

Two definitions and seven theorems: shifted-domain Prime, its application and
Hermitian symmetry, the Arch-minus-Prime form and symmetry, and exact finite
mode-ledger plus `-WR - Prime` crosswalks.

## Validation

- canonical KB preflight completed before minting;
- direct Lean and target build `7796/7796`: pass;
- positive import/API judge and negative W02/full-Weil/operator/leakage/
  continuum scope judge: pass;
- no `sorry`, `admit`, `native_decide`, or new `axiom`;
- public axiom chain: `propext`, `Classical.choice`, `Quot.sound` only;
- full main build `7817/7817`, q3_check, direct main check, and orchestrator
  tests 90/90: pass;
- proof database: 9/9 declarations imported as proven;
- foreign staged patch SHA remained
  `291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b`.

## Decision record

- Chosen: depend on B3.0V for the canonical shifted finite carrier and combine
  only Arch with the independently closed Prime layer.
- What was rejected and why: the apparent T-only dependency was rejected after
  Lean exposed that it relied on APIs formerly hidden by a monolithic scratch
  import; adding W02 here was rejected as premature full-Weil assembly.
- Risk guarded: false dependency provenance, duplicate carrier construction,
  sign/order drift, and Arch-Prime-to-Weil scope collapse.

## Preserved boundary

```text
PARENT_B3_0_OPEN
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
AMBIENT_PRIME_FORM_CLOSED
SHIFTED_ARCH_PRIME_LEDGER_CLOSED
FINITE_NEG_WR_NEG_PRIME_CROSSWALK_CLOSED
SOURCE_WEIL_FORM_OPEN
SOURCE_WEIL_ASSOCIATED_OPERATOR_OPEN
NO_COMPRESSION_IDENTITY
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

Combine B3.0AA W02 with this shifted Arch-Prime ledger only after eliminating
the scratch-only conditional pairing premise.

## ACTIONS LOG

- replaced the false scratch-shaped import surface with exact V+AB production
  dependencies;
- ran direct Lean, target/full builds, positive and negative judges, axiom
  extraction, q3_check, direct main, and 90 orchestrator tests;
- imported 9/9 declarations into the proof database;
- made no Proshka call, Aristotle submission, N=480 run, route promotion,
  Bus 010 creation, Goal 055 mutation, PX claim, or RH claim.

