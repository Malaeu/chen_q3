# D0.7e — Pro architecture decision

Date: 2026-07-11

Route status: `CHALLENGER / NOT_RH`.

Primary verdict:

```text
C. EXTERNAL_OWNER_INPUT_REQUIRED
```

## Decision

The current source corpus does not determine the detector scalar `b` consumed
by the Route B `W'`/ZEO identity.

Option A, canonicalizing from the trial norm, is rejected. The exact scalar

```text
sTrial_(m,N)=||gTrial_(m,N)||^(-1)
```

normalizes a vector in the finite Hilbert carrier. The missing detector `b`
normalizes an entire-function approximant/transform in the ZEO consumer. A
theorem identifying these categories is required, and none exists in the
audited sources.

Option B, inventing a new formula such as an inverse boundary value, is
rejected. Without a source theorem proving that the proposed scalar is the
normalization in the ZEO identity, this would reconstruct the target object
and could make `W'` small by normalization degeneracy rather than by the
claimed approximation mechanism.

The superseded pilot assignment

```text
bPilot=||E(g04)||
```

is not promotable. It is diagnostic, has the wrong role/type, and has no
theorem bridge to the entire-function/ZEO normalization.

## Minimal external input

Mythos/owner must provide one exact source statement containing:

1. an exact formula for the detector `b`;
2. its parameter carrier, including whether it is indexed by `(m,N)` or by a
   legally defined one-parameter family;
3. the object it normalizes: trial, selected eigenvector, transform, or entire
   function;
4. an exact normalization identity such as
   `F_(m,N)(z)=bDet_(m,N)*G_(m,N)(z)` with every object typed;
5. whether `b` can vanish and on which dependent domain it is defined;
6. whether it is real or complex and what fixes its phase;
7. the exact theorem/crosswalk showing that this same `b` is consumed by the
   `W'`/ZEO identity.

Uniform lower and growth bounds are not part of this definition input; they
remain H4d obligations.

## Operational result

```text
D0.7e = BLOCKED_EXTERNAL_OWNER_INPUT
D0.7  = BLOCKED / 4_OF_5_COMPONENTS_PROVED
STOP_CODE = D0_7_DETECTOR_B_DEFINITION_MISSING
NO_BUS_010_CREATED
NOT_RH
```
