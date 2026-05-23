# Codex request: Step32F Arch pairing linearity/integrability

## Task

Close the remaining Arch pairing proof obligation after commit:

`6c17342c [MacOS][rh_clean] Add Arch pairing bundling layer`

This is a local Lean task. Do not try to prove RH. Do not touch `Q3.Main`.

## Strategic context

The previous node added:

- `realBilinearFormOfPairing`
- `PacketTranslationKernelData.ofPairing`
- `centeredBSplineArchPairing`
- `centeredBSplineArchPairing_scaledTranslated_closed`
- `centeredBSplinePacketTranslationArchData_ofPairing`

The API/bundling gap is closed.

The remaining concrete Arch work is now:

```text
prove the linearity / integrability / well-definedness facts for
centeredBSplineArchPairing
so it can instantiate PacketTranslationKernelData.ofPairing
on the centered B-spline packet span.
```

Do not add another receiver layer.

## Target files

Primary:

```text
Q3/Proofs/PSD_CenteredCardinalBSpline.lean
Q3/Proofs/PSD_BSplineTranslationIdentities.lean
```

Only create a new file if the imports become too heavy:

```text
Q3/Proofs/PSD_CenteredBSplineArchPairing.lean
```

Do not create unrelated files.

## Required first search

Search the repo for:

- `centeredBSplineArchPairing`
- `centeredBSplineArchPairing_scaledTranslated_closed`
- `centeredBSplinePacketTranslationArchData_ofPairing`
- `PacketTranslationKernelData.ofPairing`
- `realBilinearFormOfPairing`
- `pairing_translate_ident`
- `map_add`
- `map_smul`
- `ContinuousLinearMap`
- `intervalIntegral`
- `Integrable`
- `a_star`
- `complexBumpLaplace`
- `scaledTranslated`

Then run:

```lean
#check centeredBSplinePacketTranslationArchData_ofPairing
#check PacketTranslationKernelData.ofPairing
#check realBilinearFormOfPairing
#check centeredBSplineArchPairing
#check centeredBSplineArchPairing_scaledTranslated_closed
```

Use the exact signatures found in the repo. Do not guess theorem types.

## Prove

Prefer the smallest theorem that eliminates the remaining assumptions of:

```lean
centeredBSplinePacketTranslationArchData_ofPairing
```

Expected theorem shape, adjusted to actual local types:

```lean
centeredBSplineArchPairing_add_left
centeredBSplineArchPairing_smul_left
centeredBSplineArchPairing_add_right
centeredBSplineArchPairing_smul_right
```

or, if the repo expects bundled maps:

```lean
centeredBSplineArchPairing_bilinear
centeredBSplineArchPairing_linear_left
centeredBSplineArchPairing_linear_right
centeredBSplineArchPairing_toRealBilinearForm
```

The final useful theorem should be one of:

```lean
centeredBSplinePacketTranslationArchData
```

or

```lean
centeredBSplinePacketTranslationArchData_closed
```

or a theorem with the local naming convention that instantiates the concrete Arch
`PacketTranslationKernelData` without leaving linearity/integrability assumptions
as parameters.

## Obstruction wall

Add this Lean comment near the final theorem:

```lean
/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form / Coordinate
- role: tactical Step32F Arch assembly
- input: concrete centeredBSplineArchPairing, translated profile identity, ofPairing bundling layer
- output: concrete Arch PacketTranslationKernelData for centered B-spline packets
- reviewer question answered: is the Arch matrix entry produced by an actual analytic bilinear form, not just by a profile-level formula or receiver wrapper?
-/
```

## Hard constraints

- No new `sorry`.
- No new `admit`.
- No new `axiom`.
- Do not weaken theorem statements.
- Do not create another abstract receiver layer.
- Do not touch `Q3.Main`.
- Do not start Step 33.
- Do not redo the sinc/phase/profile calculations unless the proof genuinely needs a local helper.
- Do not use numerical evidence as proof.

## Work loop

1. Inspect exact signatures.
2. Identify the smallest missing assumptions for `centeredBSplinePacketTranslationArchData_ofPairing`.
3. Prove linearity/integrability facts locally.
4. Instantiate the concrete Arch `PacketTranslationKernelData`.
5. Run:

```bash
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
lake build Q3.Main
```

6. Run hole/axiom checks:

```bash
rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
```

If a new file is created, include it in the checks.

## Return report

Write:

```text
ACTIVE/requests/step32f_arch_pairing_linear_integrable/report.md
```

with:

- theorem names added;
- files touched;
- exact commands run;
- compile status;
- whether `centeredBSplinePacketTranslationArchData_ofPairing` is now fully instantiated;
- remaining blocker, if any;
- next smallest lemma if blocked.
