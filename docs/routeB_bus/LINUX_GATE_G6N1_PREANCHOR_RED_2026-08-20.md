# STATUS: GATE_RED — G6N1 SOURCE DOES NOT COMPILE: 36 ERRORS, SIX OF SEVEN THEOREMS CARRY sorryAx

```yaml
PRIMARY: G6_N1_PREANCHOR_SOURCE_KERNEL_MISMATCH
GATE_RUN_BY: LINUX_BODY_NIGHT_LOOP
NIGHT_GRANT: NIGHT_GRANT_2026-08-20
SOURCE_COMMIT: ccb664b6
LEAN_BLOB: 04893ae10b51fcec3acc76cce25247b755c2fb6a
ERRORS: 36
CLEAN: [preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate]
SORRYAX: 6 theorems including the main selectedProlateCofinalSourceDataOfPreAnchorPort
REPAIR_BY_TACTIC: NOT_ATTEMPTED — beyond the two-attempt night rule at 36 errors
RETURNED_TO_JUDGE: REQ-2026-08-20-C
ROUTE: CHALLENGER_NOT_RH
```

## Full kernel output
```
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:140:50: error: unsolved goals
case h
i : PairIndex
h : ℝ → ℂ
hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i))
hsqrt : √(L_m i) ≠ 0
hrep : (fun u => ↑↑(gTrial_m i h hLp) u) =ᶠ[ae (dStar.restrict (I_m i))] E_star h
hmode :
  (fun u => ↑↑(V_n_m i 0) u) =ᶠ[ae (dStar.restrict (I_m i))] fun u =>
    (↑√(L_m i))⁻¹ * cexp (2 * ↑Real.pi * I * ↑0 * (↑(Real.log (lambda_m i * u)) / ↑(L_m i)))
u : ℝ
hrep_u : ↑↑(gTrial_m i h hLp) u = E_star h u
hmode_u : ↑↑(V_n_m i 0) u = (↑√(L_m i))⁻¹ * cexp (2 * ↑Real.pi * I * ↑0 * (↑(Real.log (lambda_m i * u)) / ↑(L_m i)))
⊢ E_star h u = ↑√(L_m i) * (E_star h u * (↑√(L_m i))⁻¹)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:164:8: warning: This simp argument is unused:
  RCLike.inner_apply'

Hint: Omit it from the simp argument list.
  simp [R̵C̵L̵i̵k̵e̵.̵i̵n̵n̵e̵r̵_̵a̵p̵p̵l̵y̵'̵,̵ ̵hsqrt]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:164:29: warning: This simp argument is unused:
  hsqrt

Hint: Omit it from the simp argument list.
  simp [RCLike.inner_apply',̵ ̵h̵s̵q̵r̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:186:62: error: unsolved goals
case hLp
i : PairIndex
h : ℝ → ℂ
hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i))
hzero : preAnchorGwinTransformCoordinate i h 0 ≠ 0
hinner_zero : inner ℂ (V_n_m i 0) (gTrial_m i h hLp) = 0
⊢ MemLp (E_star h) 2 (dStar.restrict (I_m i))
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:230:50: error: unsolved goals
case hLp
i : PairIndex
h : ℝ → ℂ
hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i))
hNonzero : TrialNonzero i h hLp
⊢ MemLp (E_star h) 2 (dStar.restrict (I_m i))
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:257:19: error: Invalid field notation: Type of
  pair k
is not known; cannot resolve field `pw`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:259:19: error: Function expected at
  prolateCombination
but this term has type
  ?m.22

Note: Expected a function because this term is being applied to the argument
  (pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:274:25: error: Function expected at
  prolateCombination
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  (D.pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:284:21: error: Function expected at
  prolateCombination
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (D.pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:293:27: error: Function expected at
  prolateCombination
but this term has type
  x✝

Note: Expected a function because this term is being applied to the argument
  (D.pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:284:61: error: unsolved goals
x✝ : Sort u_1
prolateCombination : x✝
D : SelectedProlatePreAnchorData
P : CCMLemma73PreAnchorPort D
hzero_mem : 0 ∈ centeredCriticalStrip
⊢ ∀ᶠ (k : ℕ) in atTop, preAnchorGwinTransformCoordinate (D.index k) sorry 0 ≠ 0
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:314:19: error: Invalid field notation: Type of
  pair k
is not known; cannot resolve field `pw`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:316:19: error: Function expected at
  prolateCombination
but this term has type
  ?m.22

Note: Expected a function because this term is being applied to the argument
  (pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:319:28: error: Function expected at
  prolateCombination
but this term has type
  ?m.37

Note: Expected a function because this term is being applied to the argument
  (pair k)
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:323:7: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:348:9: error(nested.lean.propRecLargeElim): Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

SelectedProlateCofinalSourceData : Sort ?u.259354
D : SelectedProlatePreAnchorData
P : CCMLemma73PreAnchorPort D
x✝ : ∃ a, ∀ b ≥ a, preAnchorGwinTransformCoordinate (D.index b) sorry 0 ≠ 0
⊢ SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:400:5: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:400:17: error(lean.unknownIdentifier): Unknown identifier `prolateCombination`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:401:5: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:401:23: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:406:2: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:408:7: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:408:19: error(lean.unknownIdentifier): Unknown identifier `prolateCombination`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:413:17: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:413:34: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:417:4: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:426:12: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:431:25: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:431:37: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:429:23: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:430:25: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:438:30: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:440:2: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:445:15: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:447:8: error: Invalid field notation: Type is not of the form `C ...` where C is a constant
  D
has type
  SelectedProlateCofinalSourceData
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:454:43: error: unsolved goals
⊢ ∀ (x : ℕ), ∃ x_1, x ≤ x_1
'Q3.RouteB.D0Pstar.preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.preAnchorGwin_zero_eq_sqrtL_mul_innerV0' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.trialNonzero_of_preAnchorGwin_zero_ne' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.D0Pstar.eventually_preAnchorGwin_zero_ne' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:463:14: error(lean.unknownIdentifier): Unknown constant `SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi`
Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:464:14: error(lean.unknownIdentifier): Unknown constant `SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor`
'Q3.RouteB.D0Pstar.goalG6N1ZeroTarget_nonvanishing_not_free' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
