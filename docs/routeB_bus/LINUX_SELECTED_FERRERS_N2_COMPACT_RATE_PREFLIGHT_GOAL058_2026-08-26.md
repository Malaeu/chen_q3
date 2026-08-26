# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT
PARENT_VERDICT: REQ-2026-08-26-I (commit 6fa17654)
BASE_HEAD: b057fda3d6d759c47a6cdc4427298224c2215d51
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
RESULT_CODE: SELECTED_FERRERS_N2_COMPACT_RATE_LEAN_READY
PRIMARY_DISCRIMINATOR_RESOLVED: CENTER_NORMALIZER_CANCELLATION_WINS
N2_OBJECT: sourceScale_weighted_UNNORMALIZED_projection_residual
NORMALIZER_RETAINED_AS_N2_PREMISE: false
NEW_ANALYTIC_INPUT_REQUIRED: none
PRIVATE_W5_RECONSTRUCTION: PARTIAL_SEE_SECTION_6
CLOSES_ON_IMPLEMENTATION:
  - SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
OPENS_ON_IMPLEMENTATION: []
NEXT_LOAD_BEARING_GAP_AFTER: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY (assembly N2.6 only)
```

## 1. Centered identity and the residual object (DO-1)

Точная цепь в репозитории (всё public, всё proved):

    selectedGalerkinResidualMellinCoordinate S k z
      = selectedProjectedMellinCoordinate S k z
        − (selectedTrialNormalizer S k : ℂ) · selectedFullMellinCoordinate S k z
    (D0PstarMuntzGalerkinResidualCrosswalk.lean:
     selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull)

и контракт rawFplus − scaledGwin
(D0PstarMuntzGalerkinResidualCrosswalkContract_proved).

Вердикт 2026-08-20 (N2.2, NORMALIZER_CANCELLATION): из raw_k(0) = s_k·G_k(0)
следует F_k(z) − A_k(z) = (Ξ(0)/G_k(0))·M(P_k g_k − g_k)(z) — конечный
нормализатор s_k сокращается ТОЧНО.

РЕШЕНИЕ ДИСКРИМИНАТОРА: preferred route. Объект N2 — sourceScale-взвешенный
НЕнормированный резидуал M(P_k g_k − g_k). SelectedTrialNormalizerBounded
(вчерашний узел) НЕ входит в N2-посылки: он остаётся саплаером literal
normalized L²-decay (уже закрыт) и только там. Fallback-маршрут (через
нормированный резидуал) не нужен: он внёс бы фактор s_k, который точная
алгебра уже сократила.

Замечание N2.0: координата ∫(g_N − g)·u^(−iz) dStar (ненормированная) в
репозитории пока не именована (selectedProjectedMellinCoordinate — координата
НОРМИРОВАННОГО kTrial). Определение — тривиальный порт; для rate-теоремы
ниже она не нужна (теорема формулируется через
selectedUnnormalizedGalerkinResidualNorm, уже существующий).

## 2. Точная количественная W5-оценка резидуала (DO-2)

Внутри admitted-цепи (сборка + receiver) доказано эвентуально:

    residual_k² ≤ 8π · C_k² · bandwidth_k⁻¹                  (hres_sq)
    C_k = 8·( AF·(k+2)^{1/4}·√(log(k+2)+2) + Cp/(4π) )
    (сборка G6N1SelectedFerrersW5RateAssembly.lean, refine на ~5679;
     receiver D0PstarFirstOrderProjectionTailReceiver.lean,
     selectedProjectionTailDecay_of_firstOrderCoefficientRate, have hres_sq)

где AF — константа приватного etw13_fourier_budget_rate, Cp — константа
F72.6 порт-rate. КРИТИЧЕСКИЙ ФАКТ: эта оценка ВНУТРЕННЯЯ (have внутри
доказательств); публичная поверхность обеих теорем — только качественный
SelectedProjectionTailDecay. Для N2 нужен публичный количественный экспорт
(секция 6).

## 3. Точные формулы C_k и bandwidth (DO-3)

На отобранном расписании i_k = selectedFerrersPreAnchorIndex k = ⟨k+2, k+2⟩
(hFamily эвентуально отождествляет selectedPairIndex S k с i_k):

    m_k = k+2;  N_k = k+2;  λ_k = √(k+2);  L_k = L_m i_k = log(k+2)
    bandwidth_k = physicalFourierBandwidth i_k
                = 2π·(N_k+1)/L_k = 2π·(k+3)/log(k+2)
    (D0PstarPhysicalFourierEnergyControl.lean:47)
    C_k — как в секции 2 (рост (k+2)^{1/4}·√log)
    ‖selectedFerrersLemma73SourceScale k‖ ≤ M эвентуально
    (доказано вчера, tnc_scale_upper — ПРИВАТНАЯ в
     G6N1SelectedFerrersTrialNormalizerClosure.lean)

## 4. L²-норма Mellin-ядра на движущемся окне (DO-4, paper-доказательство)

Для z с |Im z| ≤ σ и u > 0: |u^(−iz)| = e^{Re(−iz·log u)} = u^{Im z}.
Тогда (y := Im z, |y| ≤ σ, подстановка u = e^t):

    ‖u^(−iz)‖²_{L²(dStar, [λ⁻¹,λ])} = ∫_{λ⁻¹}^{λ} u^{2y} du/u
      = ∫_{−log λ}^{log λ} e^{2yt} dt ≤ (2 log λ)·e^{2|y|·log λ}
      = L_k · λ_k^{2|y|} ≤ L_k · λ_k^{2σ}     (λ_k ≥ 1)

⟹ ‖ядро‖ ≤ √L_k · λ_k^σ. Cauchy–Schwarz даёт для любого r ∈ H_m:

    sup_{|Im z|≤σ} |M(r)(z)| ≤ √L_k · λ_k^σ · ‖r‖.

Это точный конверт N2.3 вердикта 2026-08-20 (√(log m)·m^{σ/2} = √L·λ^σ),
без скрытых констант; в Lean — элементарный интеграл экспоненты на отрезке.

## 5. Полный леджер экспонент (DO-5)

Для фиксированного σ ∈ [0, 1/2), δ := 1/4 − σ/2 > 0:

    ‖scale73_k‖ · √L_k · λ_k^σ · residual_k
      ≤ M · √(log(k+2)) · (k+2)^{σ/2} · √(8π) · C_k · √(log(k+2)/(2π(k+3)))
      = 2M · C_k · log(k+2) · (k+2)^{σ/2} · (k+3)^{−1/2}
      ≤ 16·M·AF · (log(k+2)+2)^{3/2} · (k+2)^{−δ} · ((k+2)/(k+3))^{1/2}
        + (4·M·Cp/π) · log(k+2) · (k+2)^{σ/2} · (k+3)^{−1/2}

Оба слагаемых → 0 при каждом σ < 1/2: степень бьёт лог
((log x + 2)^{3/2}/x^δ → 0 — тот же движок isLittleO_log_rpow_rpow_atTop,
Mathlib, имя и применимость проверены в W5-сборке 26.08). При σ ↑ 1/2
δ ↓ 0 — диапазон точный, как предсказано (P_N2_RATE_1 подтверждается:
combined_shape = log^{3/2}·k^{σ/2−1/4}). Никакой новой аналитической
посылки; расписание — то же прекоммитированное (k+2, k+2), никаких
подпоследовательностей.

## 6. Одна публичная Lean-теорема и одна имплементационная транзакция (DO-6)

ПУБЛИЧНАЯ ТЕОРЕМА (единственная; форма — ровно MINIMAL_MISSING_IDENTITY
вердикта 2026-08-20, m^{σ/2} = λ^σ):

    theorem selectedFerrersSourceScaledMellinProjectionTailRate
        (S : ProlateCanonicalSourceData)
        (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
        (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
        (hCχ : 0 ≤ Cχ) (hCθ : 0 ≤ Cθ)
        (hmode : …дословно как в W5-сборке…)
        (hχ : …дословно…) (hθ : …дословно…)
        (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
        Filter.Tendsto (fun k : ℕ =>
          ‖selectedFerrersLemma73SourceScale k‖ *
            (Real.sqrt (L_m (selectedPairIndex S k)) *
              lambda_m (selectedPairIndex S k) ^ σ *
              selectedUnnormalizedGalerkinResidualNorm S k))
          Filter.atTop (nhds 0)

Файл: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean

ИМПОРТЫ: G6N1SelectedFerrersW5RateAssembly (замороженные входы, порт-scale),
G6N1SelectedFerrersTrialNormalizerClosure (цепь импортов; см. ниже),
D0PstarGalerkinResidualDecay; Mathlib: Analysis.PSeries
(sum_Ioo_inv_sq_le — Mathlib/Analysis/PSeries.lean:382, проверено rg),
SpecialFunctions.Log/Pow (движок лога-против-степени).

PRIVATE_W5_RECONSTRUCTION — ЧАСТИЧНАЯ, одно упаковочное решение судьи:

  (a) Квантитативный residual-rate: Parseval
      norm_sub_coe_P_m_N_sq_eq_tsum_complement — PUBLIC
      (D0LogWindowVNMCompletenessBridge.lean:517); хвостовая w5r-механика
      receiver'а (~180 строк) — приватная, реконструируется дёшево
      (PRIVATE_RECONSTRUCTION_ALLOWED-прецедент W5).
  (b) БЛОКЕР 1: коэффициентный конверт C_k живёт в ПРИВАТНОМ
      etw13_fourier_budget_rate (~6000 строк контекста сборки).
      Реконструкция невменяема. РЕКОМЕНДАЦИЯ: append-only публичный
      королларий (~35 строк) В КОНЦЕ файла сборки, экспортирующий
      эвентуальный коэффициентный конверт с явной C_k — внутри файла
      etw13 в области видимости; ни одна существующая строка не меняется.
  (c) БЛОКЕР 2: ‖scale73‖ ≤ M — приватный tnc_scale_upper в замороженном
      вчерашнем файле. Два пути: append-only публичный королларий
      (~10 строк) там же, ЛИБО реконструкция цепи C+A+B (~500 строк
      механической копии, только public-входы). Рекомендую первый.

  ⟹ Транзакция: один коммит, ОДИН новый файл + два append-only
  короллария (сборка + closure; существующие строки нетронуты, запрет
  reopen_W5_edge_analysis не задет — правки чисто экспортные).
  Если append-only правки замороженных файлов запрещены — реконструкция
  (c) выполнима, (b) нет: тогда нужен отдельный публичный экспорт-узел
  от судьи.

CLOSES: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE (N2.5 — главная стена
вердикта 2026-08-20; N2.3-конверт доказывается тем же файлом как лемма).
OPENS: ничего. После этого до N2 остаются только алгебра N2.0/N2.2
(определительный порт + точное тождество) и сборка N2.6 — обе без новых
аналитических входов.

ЗАПРЕТЫ СОБЛЮДЕНЫ: без free-compact-rate-посылки; без L²→compact-open;
normalizer НЕ в посылках N2; без подпоследовательностей; W5-edge не
переоткрывается; ground-tracking не смешан с projection-tail.
