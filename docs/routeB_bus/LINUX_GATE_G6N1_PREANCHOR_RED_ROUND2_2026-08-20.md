# STATUS: GATE_RED_ROUND2 — 36 -> 5 ERRORS; THE MAIN THEOREM DIES ON A KERNEL DETERMINISTIC TIMEOUT

```yaml
PRIMARY: G6_N1_PREANCHOR_REPAIR_ROUND2_KERNEL_MISMATCH
GATE_RUN_BY: LINUX_BODY_NIGHT_LOOP
NIGHT_GRANT: NIGHT_GRANT_2026-08-20
SOURCE_COMMIT: 02d21ef9
ERRORS: 5 (was 36)
CLEAN_NOW: 6 theorems incl. trialNonzero_of_preAnchorGwin_zero_ne, eventually_preAnchorGwin_zero_ne
STRUCTURAL: kernel deterministic timeout at :354 on selectedProlateCofinalSourceDataOfPreAnchorPort
            — proof term too heavy for the kernel; not a tactic repair, restructure required
ALSO: two omega failures :379 :389, unsolved :441 (slotAnchor carries sorryAx)
RETURNED: same REQ-2026-08-20-C, round 2
```

## Full kernel output (round 2)
```
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:379:28: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 1
where
 b := ↑(Classical.choose hEventually)
 c := ↑(shift k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:389:28: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 1
where
 b := ↑(Classical.choose hEventually)
 c := ↑(shift k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:354:18: error: (kernel) deterministic timeout
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:354:18: error: (kernel) unknown constant 'Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort._proof_8'
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:441:42: error: unsolved goals
D : SelectedProlateCofinalSourceData
k : ℕ
⊢ centeredXi 0 * D.rawFplus k 0 / D.rawFplus k 0 = centeredXi 0
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
 sorryAx,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.goalG6N1ZeroTarget_nonvanishing_not_free' depends on axioms: [propext, Classical.choice, Quot.sound]
```
