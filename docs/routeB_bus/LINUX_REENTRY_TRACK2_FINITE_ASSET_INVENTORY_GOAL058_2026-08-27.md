# LINUX TRACK 2 PHASE 0 — FINITE ASSET DECLARATION INVENTORY (READ-ONLY)

```yaml
TASK_ID: GOAL058_REENTRY_GATE_A_DUAL_TRACK_EXECUTION / TRACK2_PHASE0
PARENT_VERDICT: 071d3eb0
BASE_HEAD: 071d3eb0
MODE: READ_ONLY_INVENTORY
```

## Инвентарная таблица (required node / existing / mismatch / source needed)

| Узел | Требуемый объект | Существующая декларация | Файл (blob) | Тип/аксиомы | Semantic mismatch | Source needed |
|---|---|---|---|---|---|---|
| A1 | C = Q(K−εI)Q+P PosDef | НЕТ (`trialLineComplement` только def в Feshbach-preflight, без C и без PosDef) | CCMProposition59SourceTrialFeshbachPreflight.lean (29b4d595) | — | оператор C не определён | YES |
| A2 | C·(ξ−d·q) = −d·r | НЕТ | — | — | — | YES |
| A3 | C⁻¹r = q − d⁻¹ξ (обратная форма) | НЕТ | — | — | — | YES |
| A4 | graph-transform = ненулевой скаляр × ground-transform | НЕТ (real-zero теорема для tracked ground ЕСТЬ — импорт) | G6N1SelectedFerrersTrackedGroundTransform.lean (0a1d4640) | чистая тройка | скалярная нормировка d⁻¹ отсутствует | YES (тонкая) |
| B1 | (n_j−ζ(z))·h_j(z) = c(z) на ВСЁМ ℂ (решётка включена) | НЕТ | Proposition59EntireTransform.lean (9e1aca78) даёт poleKernel/dslope-строительные блоки — импорт | — | тождество не сформулировано | YES |
| B2 | (D−ζ̄)((M−a)κ) = c̄(M𝟙−a𝟙) + (𝟙ᵀκ)β − (βᵀκ)𝟙 (целая форма, без обратных) | НЕТ; коммутатор ЕСТЬ (вещественный) — импорт + ℂ-порт | CCMFiniteWeilSourceCommutator.lean (6d1379ff) | чистая тройка | комплексификация не оформлена | YES |
| C1 | penalty-конверты (I- и Gram-): ε ≥ a−s, s ≥ 0 | НЕТ (H2aPenaltyCoercivity — РЕСИВЕР пакета ground-state, не конверт) | H2aPenaltyCoercivity.lean (b18294f0) | чистая тройка | другой вывод (spectral package) | YES |
| C2 | Schur s_min = r*(C_b⁻¹r) на точном положительном комплемент-домене | НЕТ (mode4-Schur — 2×2 Jacobi, другой носитель) | D0Mode4BackwardTailFiniteSchurCrosswalk.lean (de13c078) | чистая тройка | C04: другой carrier | YES |
| D1 | centering-бонд ‖Ξ(0)/rawFplus(0)‖ ≤ ‖Ξ(0)‖/√c* при поле c* | НЕТ (якорь rawFplus(0)=√L·c₀ ЕСТЬ — импорт) | G6N1PreAnchorLimitZeroModeAndSelectedShell.lean (69d9004c) | чистая тройка | сборка не оформлена | YES (лёгкая) |
| D2 | kernelL2 компакт-конверт ≤ C_σ·λ^σ·√L | НЕТ (только nonneg) | LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail.lean (73685ca6) | — | нужны sin/решёточные оценки — аналитический вес выше остального банка | YES (тяжёлая) |

## Импорт-не-дубликат (существующие точные узлы, входят в манифест декларацией)

- `selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors` — same-witness real zeros (импорт для A4).
- `sourceOrderedCCMRawTransform_sub_projection_le` — P59 source-order/reflection/CS-цепь.
- `preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0` — центральный якорь (импорт для D1).
- `ccmWeilMatFinite_commutator` — полный ранг-2 коммутатор (импорт для B2).
- `selectedFerrersFiniteCCMResidual_orthogonal` — ⟨q,r⟩=0 (импорт для A2).
- `weighted_projective_defect_le_rayleigh_excess_div_gap`, `H2a_SimpleEvenGround_FromPenaltyCoercivity` — generic-ядра, НЕ дублируются.

## План Phase 1 (один файл G6N1SelectedFerrersFiniteAssetBank.lean)

Порядок стройки: B1 (кейс-анализ полюса, без аналитического продолжения) →
A1–A3 (позитивная определённость + точное тождество + обратная форма) →
C1 (конверты) → C2 (Schur через точное завершение квадрата в C_b-метрике,
без блочных матриц) → B2 (ℂ-порт коммутатора + целая формула) → D1 (сборка).
D2 объявляю ОТЛОЖЕННЫМ в этой транзакции: его вес — реальные sin/решёточные
оценки, на порядок выше остального банка; чтобы не рисковать всей
транзакцией, prezenterую его судье отдельным bounded-узлом. Публичная
поверхность: только конечные тождества, ноль Tendsto/Eventually/rate.
