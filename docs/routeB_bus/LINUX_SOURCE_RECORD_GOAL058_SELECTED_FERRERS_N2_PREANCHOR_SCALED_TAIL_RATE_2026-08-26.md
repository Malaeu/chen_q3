# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS N2 PREANCHOR SCALED TAIL RATE

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_J (commit 106074d4)
MODE: ONE_GOAL_ONE_COMMIT
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
    CHANGE: append_only_public_export_wrapper
    DIFF_NUMSTAT: "39 insertions, 0 deletions"
    LEAN_GIT_BLOB: 6f00ac6dab94b0804ec6e22766fc5990617972a1
    SHA256: 767f446afef22171d35f02d35ba5f9bc7894746cd58171eb1b95506a227890cb
    LINES: 6049
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: 3b2f5f309b0a7ea0aa53e465afee19f18ff40271
    SHA256: 8ed297d015bbf4873ec371272665a057b1041720fc2b5c729ecaf9b7beb498a3
    LINES: 944
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE_2026-08-26.md
PUBLIC_SURFACE:
  - selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
  - selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
EXPECTED_AXIOM_PROFILES:
  selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates:
    - propext
    - Classical.choice
    - Quot.sound
  selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
OPENS: []
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly"
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersN2SourceScaledTailRate"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean"
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
UNVERIFIED_EXTERNAL_NAME: none
```

## Публичная поверхность

1. `selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates` —
   append-only обёртка в конце сборки W5: экспортирует уже kernel-green
   приватный `etw13_fourier_budget_rate` (эвентуально
   `budget_k ≤ AF·(k+2)^{1/4}·√(log(k+2)+2)`). Ни одна существующая
   декларация сборки не изменена (diff: 39 вставок, 0 удалений).

2. `selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate` —
   для каждого σ, 0 ≤ σ < 1/2:
   `√L_k · λ_k^σ · ‖scale73_k • ((gTrial_N : H_m) − gTrial)‖ → 0`
   на literal pre-anchor Ferrers объектах, от замороженных hmode/hχ/hθ.
   Без hFamily, без S, без normalizer, без scale-bound, без
   подпоследовательностей, без compact-rate посылки; σ = 1/2 не заявлен.

## Конструкция (шаги вердикта J)

1. Точная скалярная однородность: `scale73 • gTrial = selectedFerrersEStarHm`
   (Lp.ext + coeFn_toLp + tsum_mul_left; proof-irrelevance rfl для toLp).
2. Скаляр коммутирует через литеральную проекцию Галёркина
   (P_m_N — ContinuousLinearMap: map_smul + Submodule.coe_smul):
   scale73 • (P g − g) = P E − E. Нормы не берутся до этого тождества.
3. Публичный коэффициентный конверт
   `selectedFerrersEStarHm_physicalCoefficient_sq_le` + обёртка бюджета +
   F72.6 центр-rate (клон по публичному порт-rate) дают эвентуальную
   константу `A_k = AF·(k+2)^{1/4}·√(log(k+2)+2) + Cp/(4π)`.
4. Parseval (`norm_sub_coe_P_m_N_sq_eq_tsum_complement`, public) +
   реконструированный двусторонний 1/n²-хвост (`n2r*`-клоны receiver'а,
   Mathlib `sum_Ioo_inv_sq_le`): `‖P E − E‖² ≤ 4·A_k²·L_k/(k+3)`.
5. Точные rpow-тождества `√x·x^σ/x = x^{−(1/2−σ)}`, `x^σ/x ≤ x^{−(1/2−σ)}`;
   квадрат бюджета ≤ (8AF²+8(Cp/4π)²)·(log(k+2)+2)³·(k+2)^{−(1/2−σ)}.
6. Предел `(log x+2)³/x^ε → 0` (isLittleO_log_rpow_rpow_atTop, ε = 1/2−σ),
   композиция с k↦k+2, squeeze на квадратах, `Tendsto.sqrt`.

## Гейт (фактические результаты — см. журнал коммита)

Оба модуля: прямой lean EXIT 0; lake build OK; q3_check ok на оба файла;
`#print axioms` обеих публичных теорем — только
propext, Classical.choice, Quot.sound. Diff-аудит сборки: только append.

SUCCESS_CODE: SELECTED_FERRERS_N2_PREANCHOR_SOURCE_SCALED_TAIL_RATE_LEAN
