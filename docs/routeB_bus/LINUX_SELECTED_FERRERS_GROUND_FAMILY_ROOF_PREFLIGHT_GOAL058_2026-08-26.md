# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_GROUND_FAMILY_ROOF_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_FAMILY_ROOF_PREFLIGHT
PARENT_VERDICT: REQ-2026-08-26-M (commit c5524509)
BASE_HEAD: 2bd981ee9c5c9d451afd35849012f161acaa36cb
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
RESULT_CODE: SELECTED_FERRERS_GROUND_FAMILY_ROOF_SINGLE_NEXT_NODE_LOCKED
DISCRIMINATOR_RESOLVED: BRANCH_B_ONE_MINIMAL_MISSING_IDENTITY
MISSING_IDENTITY_CODE: SELECTED_CCM_GROUND_LINE_ETA_NONVANISHING
REALIFICATION_STATUS: PROVABLE_NOT_ASSUMED
KILL_ACCEPTED: true
```

## 0. Принятие kill'а

Вердикт M прав. Мой предикат `SelectedFerrersSimpleEvenGroundAt` содержал
последним полем точную идентификацию «строка пробной функции = ненулевой
скаляр × вещественная грунтовая строка». Это не следствие
simple/even/bottom, и ни один существующий движок H2a её не производит.
Узел переносил нагрузку в более сильную гипотезу вместо сокращения фронта —
нарушение W9. Предсказания P_H2A_PREFLIGHT_1 и P_THEOREM510_ASSEMBLY_1
опровергнуты как заявлено; ретроактивного ремонта не делаю.

## 1. Извлечение грунта из complement floor (RETURN 1)

Существует и kernel-green, на старом интерфейсе `ProlateCanonicalSourceData`:

    sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
      (S) (i) (beta) (hfloor : sourceCCMComplexTrialComplementFloor S i beta)

через него определены (LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail.lean):
`selectedCCMGroundEigenvalue` (345), `selectedCCMGroundVector` (357),
`selectedCCMGroundVector_spec` (372), `selectedCCMGroundOverlap` (399),
`selectedCCMResidualFloorRatio` (410), `selectedCCMGroundScale` (421),
`selectedCCMGroundTransform` (432).

`selectedCCMGroundVector_spec` даёт `complexHermitianGroundGapAtLeast`
(unit + собственность + bottom Rayleigh + зазор на дополнении) И точную
проективную оценку дефекта `1 − |⟨ξ,q⟩|² ≤ residual/β²`.

## 2. Комплексный грунт → вещественный грунт (RETURN 2)

КЛЮЧЕВОЙ ФАКТ ИСТОЧНИКА: `sourceCCMFiniteMatrix i j k = (ccmWeilMatFinite i.m i.N j k : ℂ)`
(D0PstarCCMFiniteSourceResidual.lean:94-97) — поэлементная комплексификация
ВЕЩЕСТВЕННОЙ симметричной матрицы.

Следствие: если `sourceCCMFiniteMatrix i *ᵥ ξ = (ε:ℂ) • ξ` при вещественном ε,
то, взяв вещественную и мнимую части покоординатно,
`ccmWeilMatFinite i.m i.N *ᵥ (Re ξ) = ε • (Re ξ)` и то же для `Im ξ`.
Обе части лежат в вещественном собственном подпространстве; при простоте
комплексной линии они пропорциональны, и хотя бы одна ненулевая, поскольку
`‖ξ‖ = 1`. Нормируя, получаем вещественный единичный представитель той же
линии и единичную фазу `phase` с `phase • ξ = (ξ_ℝ : ℂ)`.

ЭТО ДОКАЗУЕМО, а не постулируется — в отличие от пробной строки, где
фазовая реализация является отдельным допущением (см. существующий файл
`CCMProposition59SourceTrialFeshbachPreflight.lean`: `phaseRealifies` (33),
`sourceCCMPhaseRealification` (41), и явный анти-плант
`phaseOne_realPart_requires_exact_reality` (59), показывающий, что для
произвольной комплексной строки «взять Re» — не конструкция).

Именно в этом разница между убитым маршрутом и ремонтом R1: реализация
ГРУНТОВОЙ линии выводится из вещественности матрицы, реализация ПРОБНОЙ
строки — нет.

## 3. η-нормировка и невырождение (RETURN 3) — ЗДЕСЬ ЩЕЛЬ

Консюмер `Proposition59GroundLagrangeZeroSetBridge` требует
`ccmEtaFinite N ⬝ᵥ ξ_ℝ = 1`, где `ccmEtaFinite N = fun _ => 1`
(CCMFiniteWeilSourceMatrix.lean:51-53), то есть **сумма координат
вещественного грунтового вектора равна единице**.

Из §2 мы получаем вещественный представитель с точностью до вещественного
ненулевого множителя. Отнормировать его по η МОЖНО ровно тогда, когда

    ccmEtaFinite N ⬝ᵥ ξ_ℝ ≠ 0.

Это НЕ следует ни из простоты, ни из bottom-свойства, ни из зазора: η —
фиксированный вектор, и ортогональность грунтовой линии к нему логически
допустима. Никакого источника этого факта в репозитории нет — я проверил
`ccmEtaFinite`-потребителей: невырождение всюду является гипотезой
(`hnormalized`), а не выводом.

**ЭТО И ЕСТЬ ЕДИНСТВЕННАЯ МИНИМАЛЬНАЯ НЕДОСТАЮЩАЯ ИДЕНТИЧНОСТЬ.**
Кандидат-источник: η — это (с точностью до нормировки) вектор `ccmDeltaFinite`,
константный источник CCM; невырождение ⟨η, ground⟩ ≠ 0 есть утверждение
«грунтовое состояние имеет ненулевую перекрышку с постоянным источником»,
то есть аналог «ground state has no node». Для матрицы Вейля это ожидаемо,
но требует доказательства (позитивность/Перрон-тип или знаковая структура
ядра `ccmWeilTauN1`), и это НЕ входит в предлагаемую транзакцию.

## 4. Грунтовая P59-трансформа и центрирование (RETURN 4)

При §2+§3 получаем `ξ_ℝ` с `ccmEtaFinite ⬝ᵥ ξ_ℝ = 1`, bottom Rayleigh над ℝ
(редукция комплексного bottom к вещественному — тот же каст, вещественные
векторы вкладываются) и простотой вещественного собственного подпространства
(из простоты комплексной линии). Тогда:

    Proposition59GroundLagrangeZeroSetBridge ⟹
      ZerosRealOn Set.univ (proposition59CCMTransform (ccmL i.m) i.N ξ_ℝ)

Квоциентный базис поставщиком НЕ является: он строится внутренне
(`Module.Basis.ofVectorSpace`), поле из предиката удаляю по указанию вердикта.

Центрирование: `selectedCCMGroundTransform = selectedCCMGroundScale ·
sourceOrderedCCMRawTransform(...)`, а `sourceOrderedCCMRawTransform L N ξ z =
proposition59RawTransform L (Icc (−N) N) (sourceOrderedCCMCoefficient N ξ) (−z)`.
Связь с `proposition59CCMCoefficient` — переиндексация `n ↦ −n`
(`ccmModeFiniteEquivIcc`, `neg_mem_Icc_of_mem_Icc`), то есть отражение
аргумента; вещественность нулей отражение сохраняет.
Ненулевой скаляр гасится `zerosRealOn_smul`
(D0ZerosRealOnScalarTransfer.lean:42); ненулевость `selectedCCMGroundScale`
даёт `selectedCCMGroundScale_ne_zero_of_ratio_lt_one` (474).

## 5. Грунтовое каноническое приближение и трекинг (RETURN 5, 6)

Каноническое приближение строится из `selectedCCMGroundTransform` на том же
расписании (`parent = extract = id`), якорь — тот же центрирующий множитель.
Трекинг УЖЕ ДОКАЗАН:

    selectedCCMGroundTransform_sub_selectedFamily_le (490)
      ‖ground_k(z) − trial_k(z)‖ ≤ ‖centeringFactor‖ · kernelL2 · √(residual/β²)
    literalCCMCofinalResidualFloorEnvelopeAndTransformTail (541)
      из compact-budget + trial→Müntz TLU ⟹ ground→Müntz TLU
      И эвентуальная ненулевость ground-scale

ВАЖНО: обе теоремы сформулированы на СТАРОМ интерфейсе
`ProlateCanonicalSourceData` + `selectedPairIndex`, а отобранный шелл — это
`SelectedProlateCofinalSourceData`. Нужен точный порт (как в N2-транзакции),
а НЕ предположение о равенстве семейств.

## 6. Ответ по дискриминатору и следующий узел (RETURN 7)

ВЕТКА B. Все компоненты крыши грунтового семейства — сборочные, КРОМЕ одного:
η-невырождения грунтовой линии. Поэтому предлагаю ОДНУ теорему, которая
делает реализацию доказанной, а η-невырождение оставляет ЧЕСТНОЙ явной
гипотезой (не пряча её в предикат H2a):

    theorem ccmComplexGroundLine_real_etaNormalized_representative
        (mProject N : ℕ) (ε : ℝ) (ξ : CCMModeFinite N → ℂ)
        (hm : 2 ≤ mProject) (hN : 1 ≤ N)
        (hunit : star ξ ⬝ᵥ ξ = 1)
        (heig : (fun j k => (ccmWeilMatFinite mProject N j k : ℂ)) *ᵥ ξ
                  = (ε : ℂ) • ξ)
        (hsimple : Module.finrank ℝ
          ((ccmWeilOpFinite mProject N).eigenspace ε) = 1)
        (hbottom : ∀ x : CCMModeFinite N → ℂ,
          ε * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ ((fun j k =>
            (ccmWeilMatFinite mProject N j k : ℂ)) *ᵥ x)).re)
        (heta : ccmEtaFinite N ⬝ᵥ (fun j => (ξ j).re) ≠ 0 ∨
                ccmEtaFinite N ⬝ᵥ (fun j => (ξ j).im) ≠ 0) :
        ∃ (ξR : CCMModeFinite N → ℝ) (c : ℂ),
          c ≠ 0 ∧
          (∀ j, (ξR j : ℂ) = c * ξ j) ∧
          Matrix.mulVec (ccmWeilMatFinite mProject N) ξR = ε • ξR ∧
          ccmEtaFinite N ⬝ᵥ ξR = 1 ∧
          (∀ x : CCMModeFinite N → ℝ,
            ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite mProject N) x)

Файл: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CCMGroundLineRealification.lean`

Гипотеза `heta` — это ровно названная щель §3, выставленная НАРУЖУ как
дизъюнкция по вещественной и мнимой части (слабейшая честная форма).
Всё остальное доказывается: пропорциональность Re/Im через простоту,
ненулевость одной из частей через `‖ξ‖ = 1`, редукция bottom с ℂ на ℝ
через вложение вещественных векторов.

CLOSES при исполнении: `SELECTED_FERRERS_GROUND_LINE_REALIFICATION`.
OPENS: ничего — щель `SELECTED_CCM_GROUND_LINE_ETA_NONVANISHING` уже открыта
как несущая и лишь получает точное имя и точную форму.

## 7. Импорты (RETURN 8)

    Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
    Q3.Proofs.RouteB.CCMFiniteWeilBottomSpectral
    Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementSpectral
    Mathlib (LinearAlgebra.Eigenspace, Analysis.RCLike)

Имена внешних лемм при написании узла проверяются `rg` по Mathlib;
в этом отчёте внешние имена не объявлены несущими.

## 8. Код (RETURN 9)

SUCCESS_CODE: SELECTED_FERRERS_GROUND_FAMILY_ROOF_SINGLE_NEXT_NODE_LOCKED
