# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_GROUND_COMPACT_TRACKING_RATE_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_COMPACT_TRACKING_RATE_PREFLIGHT
PARENT_VERDICT: 2026-08-27 tail-reindex admission (commit 05e5cd13)
BASE_HEAD: 3b0832ac
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
DISCRIMINATOR_RESULT: FAIL
RESULT_CODE: GOAL058_WEIGHTED_RESIDUAL_ONLY_DOES_NOT_CONTROL_GROUND_TRACKING
JUDGE_COUNTEREXAMPLE_CONFIRMED: true
GAP_LOCALISED_EXACTLY: true
NEW_ANALYTIC_INPUT_REQUIRED: one_scalar_limit
```

## 1. Точное произведение трекинга на выбранном хвосте

Из ратифицированного узла, в точке `φ n`:

    ‖G_k(z) − P_k(z)‖ ≤ ‖Ξ(0)/rawFplus_k(0)‖ · KernelL2_k(z) · √(E_res,k / β²)

где `E_res,k = selectedFerrersFiniteCCMResidualEnergy P k` — СЫРАЯ энергия
остатка (вещественная часть self-dot литерального рэлеевского остатка,
`G6N1SelectedFerrersFiniteCCMResidualVariance.lean:349`).

## 2. Что источник даёт на самом деле (RETURN: статус теорем)

| поставщик | вывод | вес |
|---|---|---|
| `selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio` (`...CommutatorResidualDefect.lean:693`) | `√(oddMass_k)·√(E_res,k) → 0` | `oddMass` |
| `selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates` (`...CenterCoefficientFloor.lean:1382`) | то же, из `L_k·oddMass_k·G_k → 0` | `oddMass` |

**Прямого поставщика `E_res,k → 0` в корпусе НЕТ.** Проверено через
`./ask.sh` (секция объявлений) и чтением файлов, а не только каталогом.

## 3. Контрпример судьи подтверждён

`η_k = k⁻⁴`, `E_res,k = k²` дают `√η·√E = k⁻¹ → 0` при расходящемся сыром
остатке. Взвешенный поставщик не может занять квантор компактного трекинга
переименованием. **Дискриминатор: FAIL.**

## 4. Но щель локализуется ТОЧНО — и она скалярная

Ключевая цепь уже доказана в репозитории:

    (a) |centerCoeff_k|² · E_res,k ≤ G_k
        `selectedFerrersFiniteCCMCenterCoeff_normSq_mul_residualEnergy_le_commutatorDefectEnergy`
        (`...CommutatorResidualDefect.lean:501`)

    (b) ∃ cCenter > 0, эвентуально: cCenter ≤ L_k · |centerCoeff_k|²
        `selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates`
        (`...CenterCoefficientFloor.lean:1081`)

Отсюда немедленно:

    E_res,k ≤ (L_k / cCenter) · G_k      (эвентуально)

где `G_k = selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k`.

Следовательно **сырой остаток УЖЕ контролируется** — но множителем
`L_k·G_k`, а не `L_k·oddMass_k·G_k`. Разница ровно на `oddMass_k`, который
сам стремится к нулю: существующий вход **слабее нужного ровно на этот
множитель**, и никакой другой зазор в цепи не обнаружен.

## 5. Минимальная недостающая идентичность

**`SELECTED_FERRERS_LOG_COMMUTATOR_DEFECT_ENERGY_TENDSTO_ZERO`**

    Tendsto (fun k => L_k · G_k) atTop (𝓝 0)

Это ровно тот же скалярный объект, что уже фигурирует в гипотезе теоремы
`...:1382`, но БЕЗ множителя `oddMass_k`. Всё остальное в цепи —
доказанные неравенства.

При нём получаем сырой rate:

    √(E_res,k) ≤ √(L_k · G_k / cCenter) → 0

## 6. Два ремонта представления (RETURN: FAIL-ветка)

**R1 — снять `oddMass` с существующего входа (PRIMARY).**
Доказать `L_k·G_k → 0` напрямую из тех же мод/χ-ставок, которыми уже
доказан пол центрального коэффициента и коммутаторный дефект. Объект и
файлы те же, меняется только сила утверждения.
- kill-power 10/10, cost 6/10, route-fit 10/10.
- ничего не переписывается: цепь §4 уже готова принять этот вход.

**R2 — компактный конверт вместо сырого предела (RUNNER-UP).**
Не требовать `E_res → 0`, а доказать, что на каждом компакте произведение
`‖Ξ(0)/rawFplus_k(0)‖ · KernelL2_k(z) · √(E_res,k)` стремится к нулю за
счёт убывания центрирующего множителя и конверта ядра, компенсирующего
рост `E_res`. Требует явных оценок обоих множителей, которых в корпусе
сейчас нет (у `sourceOrderedCCMKernelL2` доказана только неотрицательность).
- kill-power 8/10, cost 9/10, route-fit 5/10.

## 7. Оценки двух других множителей — статус

- `‖Ξ(0)/rawFplus_k(0)‖`: `rawFplus_k(0) ≠ 0` доказано полем шелла
  `rawZeroNonzero`; **равномерной оценки сверху нет**.
- `sourceOrderedCCMKernelL2 L N z`: определение явное
  (`...TransformTail.lean:70`), доказана только неотрицательность;
  **компактной оценки роста нет**.

Для R1 они не нужны в форме пределов: их поведение поглощается уже
существующим компактным консюмером, который принимает конверт как вход.
Для R2 они обязательны и составляют основную часть его стоимости.

## 8. Код

FAILURE_CODE: GOAL058_WEIGHTED_RESIDUAL_ONLY_DOES_NOT_CONTROL_GROUND_TRACKING

Рекомендация: авторизовать R1 — одну скалярную предельную теорему
`L_k · G_k → 0`. Она превращает §4 в готовый сырой rate без единой правки
существующих формулировок.
