# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_COMPACT_LOG_COMMUTATOR_RATE_SOURCE_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_COMPACT_LOG_COMMUTATOR_RATE_SOURCE_PREFLIGHT
PARENT_VERDICT: 6a47f79c (compact tracking rate target repair)
BASE_HEAD: 6a47f79c
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
DISCRIMINATOR_RESULT: FAIL
RESULT_CODE: GOAL058_COMPACT_LOG_COMMUTATOR_SOURCE_RATE_NOT_AVAILABLE
FAIL_BRANCH: DERIVATIVE_SOURCE_CONTRACT_OR_PRIME_OSCILLATION_WALL
CHEAP_PORTS_STATUS: BOTH_READY
GAMMA_KEPT_COMBINED: true
```

## 1. Порт центрирующего множителя — ГОТОВ (чистая сборка)

Точная теорема уже в корпусе:
`preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0`
(`G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:219`):

    rawFplus_k(0) = √L_k · q_{0,k}

Отсюда `|rawFplus_k(0)|² = L_k·|q_{0,k}|²`. Вместе с полом
`selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates`
(эвентуально `c* ≤ L_k·|q_{0,k}|²`) получаем эвентуально:

    ‖Ξ(0)/rawFplus_k(0)‖ ≤ ‖Ξ(0)‖/√c*

Новых аналитических входов нет. Твой прогноз P_CENTER_FACTOR_PORT_1 (0.97)
подтверждён.

## 2. Компактный конверт ядра — ГОТОВ (точная Mellin-замена, прямой счёт)

Порт интегрального конверта `n2c_coordinate_envelope` не нужен: прямой
конверт на P59-стороне точнее. Из
`proposition59PoleKernel_eq_quotient`: `poleKernel(L,n,z) = 2·sin(zL/2)/(z − 2πn/L)`,
полюс устраним (числитель обнуляется в КАЖДОМ полюсе).

Механизм: числитель `s := 2·sin(zL/2)` ОБЩИЙ для всех слагаемых суммы.
На подполосе `|Im z| ≤ σ`: `|s| ≤ 2·λ^σ·min(1, L·d_min)` где
`d_min` — расстояние до ближайшего полюса (первый множитель — экспонента
синуса, `e^{σL/2} = λ^σ` при `λ = e^{L/2} = √m`; второй — линейное
обнуление в ближайшем полюсе, `|cos| ≤ λ^σ` поглощён константой). Тогда:

    Σ_j |poleKernel(L, n_j, −z)|²
      = |s|² · Σ_j 1/|z − p_j|²
      ≤ 4λ^{2σ}·[ min(1, L·d_min)²/d_min² + Σ_{дальние} 1/dist² ]
      ≤ 4λ^{2σ}·[ L² + C·L² ]           (шаг решётки 2π/L)
      = C_σ · λ^{2σ} · L²

равномерно по Re z на всей подполосе. Отсюда:

    sourceOrderedCCMKernelL2 ≤ √C_σ · λ^σ · √L

Конечный синтез, никакой новой асимптотики. Прогноз
P_SOURCEORDERED_KERNEL_ENVELOPE_PORT_1 (0.92) подтверждён — с прямым
механизмом вместо порта H_m-конверта.

## 3. Порог λ^{2σ}·L²·G — ДОКАЗАН на бумаге (все множители названы)

Консюмерная цепь Lean (`selectedCCMGroundTransform_sub_selectedFamily_le`,
`LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail.lean:495`):

    ‖G_k(z) − P_k(z)‖ ≤ ‖centering_k‖ · kernelL2_k(z) · √(ratio_k)

Квадрат, с §1, §2 и `E_k ≤ L_k·G_k/c*` (строки 501 + 1081):

    sup_{|Im z|≤σ} ‖G_k(z) − P_k(z)‖²
      ≤ (‖Ξ(0)‖²/c*) · C_σ·λ^{2σ}·L_k · (L_k·G_k/(c*·β²))
      = C_{σ,β} · λ^{2σ} · L_k² · G_k

Твой порог воспроизведён точно, включая степень L². Общий числитель в §2 —
то, что убирает лишний множитель L (наивный по-полюсный счёт дал бы L³).

## 4. Sturm/W5 против производного дефекта — НЕ ЗАКРЫВАЮТ

Проверено дисково:

1. **Ни один Sturm-файл не упоминает конечные CCM-объекты** (grep по
   `selectedFerrersFiniteCCM|CommutatorResidualDefect` по всем
   `G6N1Sturm*.lean` и `D0Mode4FerrersSturmComparison.lean`: ноль).
   Связывающей теоремы к точному `Γ_k` нет.
2. **W4/W5-цепь — первый порядок и только хвост.** W4 даёт
   `‖𝓕f(t)‖ ≤ (derivBudget + jumpBudget)/(2π|t|)`
   (`..._fourier_decay_off_zero`) — ОДНА степень `t`, из piecewise AC
   производной ПРОБНОГО пакета. W5 превращает это в coefficient rate
   `|ĉ_n|² ≤ C_k²·L/n²` только для `n ∉ modeSet`
   (`selectedProjectionTailDecay_of_firstOrderCoefficientRate`, строка 290).
   `Γ_k = D_k·r_k` живёт на ВНУТРЕННИХ модах с весом `n_j` до порядка `m`;
   ни одна теорема не даёт по-модовой оценки внутреннего остатка.
3. **Требуемая сила.** `λ^{2σ}L²G → 0` при σ ↑ 1/2 требует
   `G = O(m^{−1/2+ε}/L²)`. При весе `n ≤ ~m/2` это по-модовый распад
   `|r_n| ≲ 1/n²` — ВТОРОЙ порядок Fourier-распада функции остатка,
   то есть AC/BV-контроль её ПРОИЗВОДНОЙ. Остаток несёт действие
   источника (`S_k(D_k q_k)`) — производный контроль E*-стороны, простая
   осцилляция. Поставщика нет.
4. Твой фальсификатор `x^{(m)} = m^{−1/2}e_N` стоит: C0/Hilbert-близость
   не видит модовые веса.

Прогноз P_COMPACT_LOG_COMMUTATOR_SOURCE_1 (0.78) подтверждён:
первый живой блокер — производный контракт источника / простая осцилляция.

## 5. Два ремонта представления (FAIL-ветка)

**REP1 — второй порядок W4-машины на функции остатка (PRIMARY).**
Продлить piecewise-AC машину W4 на один порядок: производная функции
остатка (E*-действие минус рэлеевский сдвиг) кусочно AC с явными
derivative/jump-бюджетами — швы у W4 уже обработаны той же Abel-log
структурой. Выход: `|r̂_n| ≤ B_k/n²`, отсюда `G ≤ C·B_k²·L`. Решающий
вопрос — рост второго бюджета: дифференцирование простых членов умножает
на частоты порядка log p, риск `B_k ~ m^{3/4}` без явной формульной
компенсации. Ремонт РЕШАЮЩИЙ в обе стороны: либо бюджет закрывается, либо
стена простой осцилляции получает точное имя и величину.
Γ сохраняется единым: вход через mode-weighted Parseval функции остатка
(кроссволк-теоремы в корпусе нет — часть стоимости).
- kill-power 9/10, cost 9/10, route-fit 9/10.

**REP2 — чётно-секторный Schur/Feshbach-граф (RUNNER-UP, твой R2).**
Проективный трекинг напрямую из пола дополнения и бюджета связи, минуя
сырой остаток как именованного консюмера.
- kill-power 9/10, cost 9/10, route-fit 8/10.

## 6. Код

FAILURE_CODE: GOAL058_COMPACT_LOG_COMMUTATOR_SOURCE_RATE_NOT_AVAILABLE

Дешёвые порты §1–§2 готовы к Lean хоть сейчас, но по твоей директиве без
источникового rate узел не открывается. Запрашиваю адъюдикацию REP1 против
REP2 и, при выборе REP1, авторизацию бумажного аудита второго бюджета
(по-прежнему read-only).
