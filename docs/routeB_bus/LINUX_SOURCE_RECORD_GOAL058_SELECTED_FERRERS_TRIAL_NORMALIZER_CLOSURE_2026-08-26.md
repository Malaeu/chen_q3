# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS TRIAL NORMALIZER CLOSURE

DATE: 2026-08-26
BODY: Linux-Claude (второе тело, наблюдатель-исполнитель)
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_H (82ac9628),
TASK_ID GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE,
MODE ONE_GOAL_ONE_COMMIT.
GRANT: LINUX_STANDING_GRANT_2026-08-25 (дневная петля).

## DELIVERABLE

Файл: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean`
(~1350 строк, один новый файл, существующие файлы не тронуты).

Публичные теоремы (REQUIRED_PUBLIC_THEOREMS, обе):

    selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
      (S : ProlateCanonicalSourceData)
      (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
      (C0 C4 Cχ Cθ : ℝ) (…неотрицательности…)
      (hmode : F72.6-семья mode-rate обеих мод)
      (hχ : χ-defect-семья)
      (hθ : узловая eigenvalue-defect-семья, μ₀ = 2π, μ₄ = 18π) :
      SelectedTrialNormalizerBounded S

    selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger
      (те же входы) :
      Tendsto (fun k => ‖selectedNormalizedGalerkinResidual S k‖) atTop (𝓝 0)

Входы — ровно REQUIRED_PUBLIC_INPUTS вердикта (S, hFamily, hmode, hχ, hθ —
идентичны сигнатуре admitted-сборки W5). NEW_ANALYTIC_INPUT: none.
Ни подпоследовательностей, ни новых owner-гипотез; V₀-глобальное среднее,
ζ(½) и Γ-Меллин-константы не используются (запреты вердикта соблюдены).

## VALIDATION

- Прямой Lean файла: EXIT 0, 0 ошибок.
- `lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrialNormalizerClosure` — OK.
- `scripts/q3_check.sh` — см. журнал коммита.
- Тройка аксиом: `#print axioms` на обеих публичных теоремах —
  только `propext, Classical.choice, Quot.sound`.

## CONSTRUCTION (пять шагов вердикта, всё приватное)

1. **STEP_1 scale-upper** (`tnc_scale_upper`): из точных якорных локов
   `‖a₀·I₀−1‖ ≤ CI/λ²`, `‖a₄·I₄−3‖ ≤ CI/λ²` (committed центр-интегральный
   rate), unit-L² нормировки обеих мод и явных полиномиально-гауссовых
   L²-мажорантов (`∫ctW₀² ≤ 1`, `∫ctW₄² ≤ 355²`) — эвентуальные
   `‖a₀‖ ≤ √3`, `‖a₄‖ ≤ √(2·355²+1)`; денумератор `D ≤ |I₀|+|I₄|`;
   итог `‖scale73‖ = ‖a₀‖‖a₄‖D/4 ≤ M := (√(2·355²+1)(1+CI)+√3(3+CI))/4+1`.
2. **STEP_2 клеточный E⋆-floor** (`tnc_scaled_cell_floor`): на клетке
   `u ∈ [1, 9/8]` комб конечен (committed WindowFiniteSupport);
   активные индексы `n·u ≤ λ` считаются: card ≤ λ (инъекция в `Icc 1 ⌊λ⌋`);
   неактивные слагаемые = 0 (носитель comb в [−λ,λ]); каждый активный
   член ≥ 4·H(nu) − Cp/λ² (committed F72.6 порт-rate); H(y) > 0 при y ≥ 1;
   n = 1 даёт floor `4H(u) ≥ tnc_cellFloor = 4·(π/2)(2π−3)e^{−π(9/8)²}`;
   суммарная ошибка ≤ λ·Cp/λ² = Cp/λ ≤ tnc_cellFloor/2 эвентуально;
   `Re ≤ ‖·‖` и `√u ≥ 1` дают floor tnc_cellFloor/2 для нормы.
3. **STEP_3 полный norm-floor** (`tnc_full_norm_floor`): поточечный floor
   `‖E⋆ u‖ ≥ (tnc_cellFloor/2)/M` на клетке; dStar-масса клетки
   ∈ [1/9, 1/8] (withDensity-вычисление, u⁻¹ ∈ [8/9, 1]); Lp-цепь
   eLpNorm_const → eLpNorm_mono_ae → eLpNorm_mono_measure даёт
   `‖gTrial_m‖ ≥ c := (tnc_cellFloor/2)/M · (1/3)` (√(1/9) = 1/3 —
   заниженная оценка массы log(9/8) ≈ 0.118 ≥ 1/9).
4. **STEP_4 projected floor**: hFamily-транспорт норм (subst-хелпер);
   admitted `selectedProjectionTailDecay_of_selectedFerrersW5RateLedger`
   даёт residual < c/2 эвентуально; обратный треугольник
   `‖g_N‖ ≥ ‖g‖ − ‖g_N − g‖ ≥ c/2`.
5. **STEP_5 normalizer + ресивер**: `selectedTrialNormalizer = ‖g_N‖⁻¹ ≤ 2/c`
   (rfl-цепь через sTrial_m_N); IsBoundedUnder конструктором;
   существующий двухпосылочный ресивер
   `selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded`
   замыкает нормированный резидуал.

## CLOSES / OPENS

CLOSES: NEXT_LOAD_BEARING_GAP вердикта f9b9c169
(SELECTED_TRIAL_NORMALIZER_BOUNDED_OR_DIRECT_WEIGHTED_PRODUCT) — маршрут R1
(normalizer-путь) закрыт на замороженных входах; оба саплаера ресивера
произведены из одного W5-леджера.
OPENS: ничего нового — потребители нормированного резидуала уже существуют
(D0PstarGalerkinResidualDecay); замороженные входы hmode/hχ/hθ остаются
прежними открытыми входами W5-фронта (без изменений).

SUCCESS_CODE: SELECTED_FERRERS_TRIAL_NORMALIZER_AND_NORMALIZED_RESIDUAL_LEAN
