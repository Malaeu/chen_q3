# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS N2 COMPACT DECAY ASSEMBLY

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_K (commit 1473ea0a)
MODE: ONE_GOAL_ONE_COMMIT
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
    CHANGE: append_only_public_cofinal_reindex_receipt
    DIFF_NUMSTAT: "33 insertions, 0 deletions"
    LEAN_GIT_BLOB: 69d9004c034ad6f1cc29ca909780bb6db0a9de33
    SHA256: 99199fcc04007e9f61bcac5f776f5da2e8dbb506635fa003b471bcf00f80cdef
    LINES: 696
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: e200b829f5e0e7589a0e885e8999781f3fd989a9
    SHA256: 190fed60932a6e748bab7e75b9309ac382924a62d5bbbf8d094e6792b81a6356
    LINES: 1228
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY_2026-08-26.md
PUBLIC_SURFACE:
  - selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex
  - selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
  - selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
  - selectedFerrersCofinalSlotS2_of_modeChiThetaRates
  - centeredXi_neg
  - preAnchorProjectedMellinCoordinate_neg_eq_rawTransformCoordinate
  - preAnchorRawTransformCoordinate_eq_normalizer_mul_projected
EXPECTED_AXIOM_PROFILES:
  ALL_PUBLIC_THEOREMS:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  - N2_6_COMPACT_DECAY_ASSEMBLY
  - N3_SAME_FAMILY_LIMIT_ASSEMBLY
  - N4_SLOT_S2_ASSEMBLY
OPENS: []
CARRIES_OPEN:
  - F72_LITERAL_CENTER_ANCHORED_MODE_RATE_FAMILY
  - F72_CHI_DEFECT_RATE_FAMILY
  - SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY
  - SLOT_H2A_SIMPLE_EVEN_GROUND
  - THEOREM510_REAL_ZERO_BRIDGE
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell"
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersN2CompactDecayAssembly"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean"
NEXT_LOAD_BEARING_GAP: SLOT_H2A_SIMPLE_EVEN_GROUND
UNVERIFIED_EXTERNAL_NAME: none
GATE_FINDING_FIXED: docstring_word_admitted_matches_q3_check_hole_regex_replaced_by_ratified
ORIENTATION_NOTE: FPLUS_CONVENTION_SEE_PROSE
```

## Публичная поверхность

1. `selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex` —
   append-only квитанция в шелл-файле: один сдвиг φ, его кофинальность,
   `k ≤ φ k` и точные равенства index / pair / sourceScale между
   theorem-generated шеллом и литеральным pre-anchor семейством. Ни одна
   существующая декларация не изменена (33 вставки, 0 удалений).
2. `selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates`
   — N2: центрированное конечное семейство минус Müntz-заякоренный главный
   член стремится к нулю локально равномерно на centeredCriticalStrip.
3. `selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates`
   — N3: `centeredPstar → centeredXi` локально равномерно.
4. `selectedFerrersCofinalSlotS2_of_modeChiThetaRates` — N4: SlotS2 с
   `c = 1` и калибровкой `1`.

Входы всех трёх последних — ровно замороженные hmode / hχ / hθ, те же, что
в admitted W5-леджере. Новых аналитических входов нет.

## Ориентация Fplus (важно для чтения теоремы 2)

Шелл определяет `preAnchorRawTransformCoordinate i h … z :=
proposition59RawTransform … (−z)` — бумажная конвенция `Fplus(z) = T(k)(−z)`.
Координата `Gwin` берётся при `u^{−iz}` без отражения. Поэтому точное
тождество спаривает `centeredPstar` в точке `z` с Müntz-семейством в точке
`−z`; это отражено в формулировке теоремы 2. Теоремы 3 и 4 ориентационно
свободны: чётность `centeredXi (−z) = centeredXi z` доказана здесь
(`centeredXi_neg`) из функционального уравнения
`completedRiemannZeta₀_one_sub`, и отражение исчезает в пределе.

## Конструкция (шаги вердикта K)

1. **Квитанция реиндексации** (шелл, append-only): φ := preAnchorTailShift,
   все равенства определительные.
2. **Порт Phase-4E** в источник-параметрической форме:
   `preAnchorProjectedMellinCoordinate i h hLp hNz (−z) =
   preAnchorRawTransformCoordinate i h hLp hNz z` — через конечное
   лог-фурье-представление, транспорт меры и Proposition-5.9.
3. **Конверт ядра**: масса `dStar (I_m i) = ofReal (L_m i)` (точный
   withDensity-счёт); поточечно `‖u^{−iw}‖ = u^{Im w} ≤ λ^σ` на окне;
   Cauchy–Schwarz через `L2.inner_def` даёт
   `‖∫ f·u^{−iw}‖ ≤ λ^σ·√L·‖f‖`.
4. **Точное сокращение нормализатора** до неравенств:
   `centeredPstar k z − Ξ(0)/Gwin_k(0)·Gwin_k(−z) =
   Ξ(0)/Gwin_k(0)·∫ (g_N − g)·u^{−i(−z)}` — из `raw(0) = s_k·Gwin(0)` и
   `raw(z) = s_k·Proj(−z)`; конечный нормализатор `s_k` исчезает.
5. **Транспорт rate**: admitted
   `selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate`
   композируется с φ; равенства квитанции переносят норму (subst-хелпер).
6. **Компактная сборка**: σ_K из компакт-подполосного хелпера; бюджет
   `‖ratio_k‖·(λ^σ√L·‖scale·(g_N − g)‖) → 0`; `tendstoLocallyUniformlyOn_zero_of_compact_envelopes`.
7. **Предел и SlotS2**: заякоренный член → `centeredXi` (ratio → 1,
   Müntz-предел на компакте `−K`, чётность Ξ); сумма даёт N3; N4 —
   единственность предела на том же семействе.

SUCCESS_CODE: SELECTED_FERRERS_N2_N3_N4_COMPACT_CLOSURE_LEAN
