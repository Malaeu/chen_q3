# OWNER INPUT REQUEST — ExactDetectorBDefinition

Target node: `D0.7e ExactDetectorBDefinitionAndCrosswalk`

Current status:

```text
D0.1--D0.6 PROVED
D0.7a--D0.7d PROVED
D0.7e BLOCKED
Route B CHALLENGER / NOT_RH
```

This is not a Bus 010 goal. It is the minimal source statement required from
Mythos/owner before the owner-authorized compiler can close D0.7.

## Required immutable statement

Please provide all fields below without numerical reconstruction.

```text
DETECTOR_B_NAME:

PARAMETER_REGIME:
  finite (m,N) OR an already-proved selector/family theorem

SCALAR_FIELD_AND_TYPE:
  bDet_(m,N) : ?

EXACT_FORMULA:
  bDet_(m,N) := ?

NORMALIZED_OBJECT:
  exact carrier and exact object (trial/eigenvector/transform/entire function)

NORMALIZATION_IDENTITY:
  F_(m,N)(z) = bDet_(m,N) * G_(m,N)(z)
  with exact definitions of F and G

DOMAIN_AND_NONVANISHING:
  can bDet vanish?
  if normalization is dependent, state the exact nonzero locus

REAL_COMPLEX_PHASE:
  real or complex?
  what exact convention fixes its phase?

W_PRIME_CROSSWALK:
  theorem statement proving that this same bDet is the b in
  WPrime_(m,N)^2
    = |bDet_(m,N)|^2 * lambda_m * alpha_(m,N) / DeltaE_(m,N)

SOURCE_POINTER:
  authoritative file/paper/theorem/lines or an explicit owner-ratified new
  definition plus the new proof obligation connecting it to ZEO
```

## Mandatory firewall

The answer must explicitly confirm:

```text
bDet is not bWeil_j;
bDet is not OCR xihat;
bDet is not automatically bPilot=||E(g04)||;
bDet is not automatically sTrial^(-1)=||gTrial||;
the definition itself does not claim H4d uniform bounds;
the W-prime crosswalk is not obtained by tautologically redefining W-prime.
```

## Acceptance

The input unlocks D0.7e only if the formula, type, normalization identity, and
non-circular `W'`/ZEO crosswalk are all present. Numerical agreement or a bare
symbol rename is rejected as `D0_7_BPILOT_BDET_CROSSWALK_MISSING`.
