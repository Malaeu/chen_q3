# STATUS: GATE_RED_ROUND3 — TWO ERRORS LEFT, BOTH ONE FLOOR: preAnchorTail_muntzLimit DIES ON KERNEL TIMEOUT

```yaml
PRIMARY: G6_N1_PREANCHOR_ROUND3_ONE_HEAVY_FLOOR
NIGHT_GRANT: NIGHT_GRANT_2026-08-20
SOURCE_COMMIT: cfee730a
TRAJECTORY: 36 -> 5 -> 2 errors
ALL_NINE_AXIOM_PROFILES: clean prints, but kernel certification blocked by:
  :508 (kernel) deterministic timeout on private preAnchorTail_muntzLimit
  :532 downstream unknown-constant of that same failed floor
RETURNED: REQ-2026-08-20-C round 3 — final ping of the night budget
```

```
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:508:16: error: (kernel) deterministic timeout
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:532:18: error: (kernel) unknown constant '_private.Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell.0.Q3.RouteB.D0Pstar.preAnchorTail_muntzLimit'
'Q3.RouteB.D0Pstar.preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.preAnchorGwin_zero_eq_sqrtL_mul_innerV0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.trialNonzero_of_preAnchorGwin_zero_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.eventually_preAnchorGwin_zero_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort]
'Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.goalG6N1ZeroTarget_nonvanishing_not_free' depends on axioms: [propext, Classical.choice, Quot.sound]
```
