# Report: Step32F Arch pairing linearity/integrability

## Theorem names added

- `centeredBSplineArchIntegrand`
- `complexBumpLaplace_add_of_integrable`
- `complexBumpLaplace_smul`
- `centeredBSplineArchPairing_add_left`
- `centeredBSplineArchPairing_smul_left`
- `centeredBSplineArchPairing_add_right`
- `centeredBSplineArchPairing_smul_right`
- `centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable`
- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable`

## Files touched

- `ACTIVE/requests/step32f_arch_pairing_linear_integrable/node.md`
- `ACTIVE/requests/step32f_arch_pairing_linear_integrable/report.md`
- `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `q3.lean.aristotle/docs/INSIGHTS.md`

## Exact commands run

- `sed -n '1,220p' /Users/emalam/.codex/skills/x-rh-compiler/SKILL.md`
- `pwd && git status --short && git rev-parse --abbrev-ref HEAD && uname -s`
- `test -f AGENTS.md && sed -n '1,260p' AGENTS.md; test -f Q3_OBSTRUCTION_ATLAS.md && sed -n '1,220p' Q3_OBSTRUCTION_ATLAS.md || true`
- `sed -n '1,220p' q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `test -f q3.lean.aristotle/Q3_OBSTRUCTION_ATLAS.md && sed -n '1,220p' q3.lean.aristotle/Q3_OBSTRUCTION_ATLAS.md || true; test -f Q3_OBSTRUCTION_ATLAS.md && sed -n '1,220p' Q3_OBSTRUCTION_ATLAS.md || true`
- `rg -n "centeredBSplineArchPairing|centeredBSplineArchPairing_scaledTranslated_closed|centeredBSplinePacketTranslationArchData_ofPairing|PacketTranslationKernelData\\.ofPairing|realBilinearFormOfPairing|pairing_translate_ident|map_add|map_smul|ContinuousLinearMap|intervalIntegral|Integrable|a_star|complexBumpLaplace|scaledTranslated" Q3 -t lean`
- `./scripts/research_oracle.py query "centeredBSplineArchPairing linearity integrability packet span PacketTranslationKernelData ofPairing" -c q3_docs`
- `./scripts/research_oracle.py query "Arch pairing bilinear form centered B-spline packet span linearity" -c q3_docs`
- `./scripts/research_oracle.py query "Step32F Arch pairing bundling layer matrix identification receiver" -c q3_docs`
- `lake env lean --stdin` with the required `#check` block from `node.md`
- `lake env lean --stdin` for local proof prototypes
- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

## Follow-up commands run

- `rg -n "centeredBSplineEta.*(continuous|Continuous|hasCompact|HasCompact|integrable|Integrable)|centeredCardinalBSpline.*(hasCompact|HasCompact|integrable|Integrable|continuous|Continuous)|ConvPower.*(hasCompact|HasCompact|integrable|Integrable|continuous|Continuous)|complexBumpLaplace.*integrable|scaledTranslated.*integrable|complexScaledTranslatedBump" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean Q3/Proofs -g '!PrimeCert/**'`
- `lake env lean --stdin` for the translated-packet integrability prototypes
- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

## Compile status

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed
- `lake build Q3.Main`: passed
- hole scan on touched Lean files: clean
- `./scripts/check_axioms.sh`: passed, 5 axioms total, no new axioms

## Instantiation status

`centeredBSplinePacketTranslationArchData_ofPairing` is not fully instantiated yet.

This pass closed the local linearity algebra for the concrete
`centeredBSplineArchPairing`:

- both real-scalar homogeneity laws are unconditional;
- both additivity laws are proved with the exact weighted Bochner-integrability
  hypotheses required by Lean.

## Remaining blocker

The remaining blocker is now narrower.  The lower `x`-side weighted
Bochner-integrability hypotheses for finite translated packet sums are closed;
what remains is the `t`-side Arch-integrand integrability:

```text
prove centeredBSplineArchIntegrand integrability for B-spline translated packet
sums, then feed the four Arch-pairing laws into
centeredBSplinePacketTranslationArchData_ofPairing.
```

No new profile, sinc, phase, or receiver calculation is needed for this next
step, but the proof likely needs `a_star_linear_growth` plus sinc-power decay.

## Next smallest lemma if blocked

Add a finite-sum integrability packet for translated normalized B-spline
packets:

```lean
centeredBSplineArchIntegrand_translatedPacket_integrable
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

The next likely proof route is the existing closed translated imaginary-axis
profile, `a_star_linear_growth`, and an integrable sinc-power envelope.  The
degree-zero case should be treated carefully; the positive-degree branch is the
current safe mainline.

## Follow-up: packet-span bilinear wiring

After the later packet `t`-side theorem
`centeredBSplineArchIntegrand_translatedPacketSum_integrable` was closed, this
request was resumed and the concrete packet-span bilinear layer was added.

### Additional theorem names added

- `centeredBSplineTranslatedPacketSum`
- `centeredBSplineTranslatedPacketSum_add_coeff`
- `centeredBSplineTranslatedPacketSum_smul_coeff`
- `centeredBSplineArchPacketCoeffPairing`
- `centeredBSplineArchPacketCoeffPairing_add_left`
- `centeredBSplineArchPacketCoeffPairing_smul_left`
- `centeredBSplineArchPacketCoeffPairing_add_right`
- `centeredBSplineArchPacketCoeffPairing_smul_right`
- `centeredBSplineArchPacketCoeffBilinearForm`

### Additional files touched

- `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `q3.lean.aristotle/docs/INSIGHTS.md`
- `q3.lean.aristotle/ACTIVE/requests/step32f_arch_pairing_linear_integrable/report.md`

### Updated status

The concrete Arch pairing is now pulled back to finite centered B-spline packet
coefficient space and packaged as a real bilinear form through
`realBilinearFormOfPairing`.

`centeredBSplinePacketTranslationArchData_ofPairing` is still not fully
instantiated by this follow-up.  The next smallest blocker is the
coordinate/receiver bridge from the coefficient-space bilinear form to the
existing packet translation kernel/matrix-identification contracts, without
adding a new abstraction layer.

### Additional commands run

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake build Q3.Main`
- `rg -n "sorry|admit|exact\\?|ring\\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

### Additional compile status

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`: passed
- `lake build Q3.Main`: passed
- hole/tactic-placeholder scan on touched Lean files: clean
- `./scripts/check_axioms.sh`: passed, 5 axioms total, no new axioms
