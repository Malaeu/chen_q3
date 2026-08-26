# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS W5 RATE ASSEMBLY

DATE: 2026-08-26
BODY: Linux-Claude (второе тело, наблюдатель-исполнитель)
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_F (66362fe1),
TASK_ID GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY, MODE ONE_GOAL_ONE_COMMIT.
GRANT: LINUX_STANDING_GRANT_2026-08-25 (ночная петля, продолжена днём).

## DELIVERABLE

Файл: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean`
(~6000 строк, один новый файл, существующие файлы не тронуты).

Публичная теорема (REQUIRED_PUBLIC_THEOREM):

    selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
      (S : ProlateCanonicalSourceData)
      (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
      (C0 C4 Cχ Cθ : ℝ) (…неотрицательности…)
      (hmode : F72.6-семья mode-rate обеих мод)
      (hχ : χ-defect-семья)
      (hθ : узловая eigenvalue-defect-семья
        |Λ_j + G(k+2) − (k+2)·μ_j| ≤ Cθ, μ₀ = 2π, μ₄ = 18π) :
      SelectedProjectionTailDecay S

Входы — ровно REQUIRED_PUBLIC_INPUTS вердикта: S, hFamily-кроссволк,
существующие F72-семьи, точные eigenvalue-rate-входы узла 1.
NEW_ANALYTIC_INPUT: none. Вывод — SelectedProjectionTailDecay S.

## VALIDATION

- Прямой Lean файла: EXIT 0, 0 ошибок.
- Полный build: `lake build` — **Build completed successfully (7817 jobs)**,
  `${PIPESTATUS[0]} = 0`; Q3.Main replayed: `RH_of_Weil_and_Q3 : RH`.
- `scripts/q3_check.sh` — **q3_check ok** (7782 jobs + скан hole-маркеров).
- Тройка аксиом: `#print axioms` на публичной теореме и на двух главных
  внутренних узлах (`etw10_budget_rate`, `etw13_fourier_budget_rate`) —
  только `propext, Classical.choice, Quot.sound`.

## CONSTRUCTION (внутренние стадии, всё приватное)

1. **Энерго-инстанциация узла 1** (`sturm_defect_energy_rate_ledger`,
   a3c84e45) для обеих отобранных мод: χ-инклюзивный дефект
   `gd_j = c_j·φd_j − χ_j·ctW_jd`, χ-скалированный цилиндровый профиль
   `W := χ·ctW`; якоря вещественны (committed `_im`-леммы); итог
   `E_j ≤ CE_j/(k+2)` с явными CE_j.
2. **Транспорт и массы**: ring-тождества `y²W″ + 2yW′ = ctT_j`;
   `∫|ctW₀| ≤ 1`, `∫|ctW₄| ≤ 533` (элементарный суб-экспоненциальный
   конверт, без гауссовых моментов); Dtr из committed
   `cylinderTransport_L1_bounded` (2b630d14).
3. **Бюджет производной**: приватная редукция W5DerivativeBudgetRate
   реконструирована как `etw_`-копии (PRIVATE_RECONSTRUCTION_ALLOWED);
   обе integrability-гипотезы разряжены (measurable_deriv +
   константные мажоранты + a.e. вне счётного множества швов);
   мастер-разрез комба при не-шовных x:
   `ΣQ = H-комб(⌊λ/u⌋) + nonTop-дефект + strict-top` (трихотомия);
   H-часть — committed `explicit H`-бюджет (17d7a5a8) заменой переменных
   `u = e^x/λ` с разрезом при u = 1; nonTop-дефект — 3B-консюмер
   (1a229b3a) по модам с энергией из (1): вклад ≤ √(½·log(k+3))·√(CE_j+1);
   χ-junk — грубый счёт card ≤ λ/u, |ctW₀d| ≤ 8, |ctW₄d| ≤ 4056:
   вклад ≤ 2040·Cχ·(k+2)^{1/4}; strict-top — committed
   `selectedFerrersDefectEdgeTopBudget_bound` (c5c88de8): вклад ≤ const.
   Итог: `budget_k ≤ A·(k+2)^{1/4}·√(log(k+2)+2)` — честный растущий темп,
   в точности b1-ветка вердикта c47b75a8.
4. **Фурье-закрытие**: зеркало committed
   `selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates`
   с растущим бюджетом вместо открытого uniform-D-поставщика;
   те же публичные rate-леммы (l1/endpoint/seam/port).
5. **Сборка**: зеркало b1-application (`etw2_`-копии) с
   `C_k = 8·(A_F·(k+2)^{1/4}√(log(k+2)+2) + Cp/(4π))`; hScale — committed
   `selectedFerrersSourceScale_inverse_bounded` (M = 8, 7d27b5ad); финал —
   rate-aware ресивер `selectedProjectionTailDecay_of_firstOrderCoefficientRate`
   (a39c28e5) с пределом `C_k²·bandwidth⁻¹ → 0`:
   bandwidth(i'_k) = 2π(k+3)/log(k+2) (точная формула, rfl-редукции),
   мажоранта `(log+2)²/√(k+2) → 0` через `isLittleO_log_rpow_rpow_atTop`.
   RATE_COMBINATION_GUARD соблюдён: квадраты через явные суммы квадратов
   (`(a+b)² ≤ 2a²+2b²`-семейство, pow_le_pow_left₀), никакого informal-O.

## FORBIDDEN COMPLIANCE

Не использовано: uniform-D для полосы; общий eigenvalue на
prolateCombination; deriv в точке шва (швы исключены a.e., точечно
deriv = 0 доказан только СТРОГО за окном); W4-jump не входит в
top-интеграл (jump-бюджет живёт отдельно в committed Fourier-закрытии);
литеральный top-бюджет (не экзистенциальный мажорант); sup-норм
производной нет (только a.e.-мажоранты для интегрируемости — темп через
них не течёт); δ″ нет; scale-inverse не используется как индивидуальный
якорный бонд; нумерика — нигде; O-нотация — нигде; существующие Lean-файлы,
вердикты, route state, Q3.Main — не тронуты.

## LEDGER

CLOSES: [GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY,
  W5_LOG_DERIVATIVE_BUDGET_BOUNDED → заменён доказанным растущим темпом,
  W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE → потреблён]
OPENS: [] — публичная теорема ест только замороженные семьи.

SUCCESS_CODE: SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL_LEAN
