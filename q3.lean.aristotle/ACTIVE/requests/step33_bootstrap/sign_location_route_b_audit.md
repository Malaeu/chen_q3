# Step33A Route-B Sign-Location Audit

Date: 2026-06-04.

Gate:

```text
Step33A.1-A / finite-Weil A sign-location fork
```

## Proshka Route Choice

Proshka chose route B as the next semantic test:

```text
keep C = A - P
keep the eta-normalization bridge
do not choose raw A merely because it passes PSD
locate the missing sign between the analytic Arch profile and the finite A
matrix used in C = A - P
```

Candidate theorem shape:

```lean
centeredBSplineFiniteWeilAProfile_eq_neg_centeredBSplineArchKernelProfile
```

or repo-style:

```lean
centeredBSplineArchAEntryForFiniteWeil_eq_neg_step22OmegaEtaTransformedProfileWithArchSign
```

## Local Definition Audit

The current Lean wiring does **not** contain a separate signed
`finiteWeilAProfile`.

The contract path is:

```text
BSplineAnalyticKernelContract
→ BSplineBasisFormulaContract
→ BSplineFormulaContract
→ C = A - P
```

Concrete sign facts:

```text
PSD_BSplineAnalyticKernelContract.lean:
  archKernel : PacketKernelPairingData
  archForm_eq : archForm(synth v) = archKernel.form(synth v, synth v)

PSD_BSplineEntryExpansion.lean:
  toFormulaContract.A := B.archExpansion.M

PSD_BSplineFormulaContract.lean:
  C := matrixSub B.A B.P

PSD_CenteredCardinalBSpline.lean:
  centeredBSplineArchPacketCoeffKernelData.kernel :=
    centeredBSplineArchKernelProfile k ell (center j - center i)

PSD_CenteredCoeffBaseAHboxImport.lean:
  primaryK11AnalyticA_entry :
    primaryK11AnalyticA i j =
      centeredBSplineArchKernelProfile ...
```

So the existing exported `primaryK11AnalyticA` / `controlK9AnalyticA` receiver
is the **positive** Arch profile.

Therefore this theorem is not available from current definitions:

```lean
primaryK11AnalyticA i j =
  - centeredBSplineArchKernelProfile ...
```

It would contradict the compiled positive receiver unless a new signed receiver
or a changed contract is introduced.

## Decision

Route B is still the minimal semantic route, but it is **not** a local theorem
over the current `primaryK11AnalyticA`.

The real next implementation target is a signed finite-Weil receiver:

```lean
centeredBSplineSignedArchPacketCoeffKernelData
centeredBSplineSignedCoeffAnalyticKernelContract
centeredBSplineSignedCoeffWeilForm_eq_matrixSub_quadForm
```

Semantic meaning:

```text
finite-Weil A = - centeredBSplineArchKernelProfile
C = A - P remains unchanged
```

This must be justified by the actual Weil/Arch sign convention.  It should not
be introduced as a proof patch.

## If Signed Receiver Fails

If the signed receiver cannot be proved from the project definitions, the next
blocker becomes:

```text
Definitions force A = + centeredBSplineArchKernelProfile.
But C = A - P is negative on ker(Q).
Therefore the current Step32/Step33 formula contract is sign-incompatible with
the finite PSD truth.
```

Then the route must escalate to a `C` / WeilForm assembler sign audit, not to
CSV, `ARadius`, radius-floor, LDL, `Q3.Main`, or H1/PO3.

## Next Codex Target

Do not mutate data.

First inspect whether a signed finite-Weil contract can be added locally:

```lean
def negPacketKernelPairingData ...
theorem negPacketKernelPairingData_form_synth_eq_quadForm ...
noncomputable def centeredBSplineSignedCoeffAnalyticKernelContract ...
theorem centeredBSplineSignedCoeffWeilForm_eq_matrixSub_quadForm ...
```

If this compiles and is semantically accepted, then rerun the A hbox/recenter
route against `-transformed` Step22-Omega.

## Compiled Prototype

Implemented and checked:

```text
Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
```

New checked names:

```lean
negPacketKernelPairingData
negPacketKernelPairingData_matrix
centeredBSplineSignedArchPacketCoeffKernelData
centeredBSplineSignedArchPacketCoeffKernelData_matrix_entry
centeredBSplineSignedCoeffAnalyticKernelContract
centeredBSplineSignedCoeffWeilForm_eq_matrixSub_quadForm
```

Meaning:

```text
The route-B signed finite-Weil receiver is algebraically expressible in Lean:
  signed A entries = - centeredBSplineArchKernelProfile
  C = A - P remains unchanged
```

Validation:

```text
lake env lean Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
rg -n "sorry|exact\?|admit|axiom|unsafe" Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
```

Result:

```text
pass; no holes found
```

Status boundary:

```text
This prototype is not yet wired into ActiveCenteredCoeffEntryHboxCert.
It proves the route-B receiver shape, not the downstream A hbox closure.
```

## Concrete Primary/Control Surface

The prototype has been extended to the active primary/control dictionaries.

New checked names:

```lean
primaryK11SignedCoeffAnalyticKernelContract
controlK9SignedCoeffAnalyticKernelContract
primaryK11SignedAnalyticA
primaryK11SignedAnalyticP
primaryK11SignedAnalyticC
controlK9SignedAnalyticA
controlK9SignedAnalyticP
controlK9SignedAnalyticC
primaryK11SignedAnalyticA_entry
controlK9SignedAnalyticA_entry
primaryK11SignedAnalyticA_entry_index_delta
controlK9SignedAnalyticA_entry_index_delta
primaryK11SignedAnalyticC_eq_matrixSub
controlK9SignedAnalyticC_eq_matrixSub
```

Concrete meaning:

```text
primary/control signed A entries are
  -centeredBSplineArchKernelProfile(... center_j - center_i ...)
with index-delta variants using
  -centeredBSplineArchKernelProfile(... (j - i) / 4 ...)

and the signed contract still has
  C = A - P
```

Validation:

```text
lake env lean Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffSignedArchReceiver.lean
hole scan: clean
```

Remaining boundary:

```text
This is still not an A hbox closure.  The existing ActiveCenteredCoeffEntryHboxCert
surface expects the old positive primaryK11AnalyticA/controlK9AnalyticA, so the
next target is a signed-A hbox/recenter receiver plus an explicit adapter
decision for the Step33A cert surface.
```
