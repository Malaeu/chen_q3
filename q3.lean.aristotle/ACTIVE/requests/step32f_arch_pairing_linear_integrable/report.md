# Report: Step32F Arch pairing linearity/integrability

## Theorem names added

- `centeredBSplineArchIntegrand`
- `complexBumpLaplace_add_of_integrable`
- `complexBumpLaplace_smul`
- `centeredBSplineArchPairing_add_left`
- `centeredBSplineArchPairing_smul_left`
- `centeredBSplineArchPairing_add_right`
- `centeredBSplineArchPairing_smul_right`

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

The remaining blocker is now narrower:

```text
prove the finite packet-span integrability hypotheses for B-spline translated
packet sums, then feed the four Arch-pairing laws into
centeredBSplinePacketTranslationArchData_ofPairing.
```

No new profile, sinc, phase, or receiver calculation is needed for this next
step.

## Next smallest lemma if blocked

Add a finite-sum integrability packet for translated normalized B-spline
packets:

```lean
centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
centeredBSplineArchIntegrand_translatedPacket_integrable
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

The likely proof route is compact support plus the existing closed translated
imaginary-axis profile.
