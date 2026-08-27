# LINUX PREFLIGHT REPORT — GOAL058_SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT

```yaml
REPORT_KIND: READ_ONLY_PREFLIGHT
TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_GRAPH_RESOLVENT_TRANSFORM_PREFLIGHT
PARENT_VERDICT: 4a576dd5 (ground-graph resolvent functional selected)
BASE_HEAD: 4a576dd5
MODE: PAPER_AND_SOURCE_READ_ONLY
LEAN_EDIT_PERFORMED: false
NUMERICAL_PROBE_PERFORMED: false
DISCRIMINATOR_RESULT: FAIL
RESULT_CODE: GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE
REPRESENTATION_KILLED: false
GRAPH_IDENTITIES_STATUS: ALL_PAPER_PASS
NAMED_UNRESOLVED_ELEMENT: psi_k(z) = inner(C_k_inv h_k(z), r_k) target-action channel
GAMMA_KEPT_COMBINED: true
PRECOMMITTED_TAIL_KEPT: phi n = n + k0
FILES_READ_PER_DIRECTIVE: all_six
```

## 1. Ориентация d — ЗАКРЕПЛЕНА

Существующий overlap в Lean: `selectedCCMGroundOverlap = star xi ⬝ᵥ q`,
то есть ⟨ξ,q⟩ в конвенции «star слева». Твой `d = ⟨q,ξ⟩ = conj(overlap)`.
Значит `d ≠ 0 ⟺ overlap ≠ 0`, и `|d| = |overlap|`; все существующие
скалярные множители переносятся сопряжением, ноль-множество трансформы
не меняется (умножение на ненулевой скаляр).

## 2. ratio < 1 ⇒ d ≠ 0 — УЖЕ ТЕОРЕМА

`selectedCCMGroundOverlap_ne_zero_of_ratio_lt_one`
(`LiteralCCM...TransformTail.lean:456`) и строгие гарды `hratio ... < 1`
в TrackedGroundTransform (строки 419, 780). Ничего нового не нужно.

## 3. Полноносительный граф-оператор C — POSITIVE DEFINITE (бумага)

`C = Q(K−εI)Q + P` на литеральном носителе. Для `x = cq + w`, `w ⊥ q`:
`⟨x,Cx⟩ = |c|² + ⟨w,(K−ε)w⟩`; floor-предикат
(`complexTrialComplementFloor`, литеральный `B = Q(K−aI)Q`) даёт
`⟨w,(K−a)w⟩ ≥ β‖w‖²`, а `ε ≤ a` (из floor-пакета) добавляет
`(a−ε)‖w‖² ≥ 0`. Итого `⟨x,Cx⟩ ≥ min(1, β)·‖x‖²` — положительная
определённость и обратимость. Эрмитовость C — из эрмитовости K, P, Q. ∎

## 4. Граф-тождество коэффициентов — ТОЧНОЕ (бумага)

`ξ = dq + w`: проекция уравнения `(K−ε)ξ = 0` на `q⊥`:
`d·Q(K−ε)q + Q(K−ε)w = 0`. Здесь `Q(K−ε)q = Qr = r`, потому что
`⟨q,r⟩ = 0` — residual orthogonality УЖЕ теорема
(`selectedFerrersFiniteCCMResidual_orthogonal`, H2aSourceQuantities:482).
И `Q(K−ε)w = Cw` (так как `Pw = 0`, `w = Qw`). Итого `Cw = −d·r`,
`w = −d·C⁻¹r`, и

    d⁻¹ξ − q = −C⁻¹r    ∎ (тождество, не неравенство)

Твой прогноз P_GROUND_GRAPH_IDENTITY_1 (0.98) подтверждён.

## 5. Тождество ошибки трансформы — ТОЧНОЕ (бумага)

Линейность `sourceOrderedCCMRawTransform` по вектору коэффициентов +
существующее `selectedFamily_eq_centered_sourceOrderedCCMRawTransform`:

    G_k^graph(z) − P_k^trial(z) = −(Ξ(0)/rawFplus_k(0)) · T_k(C_k⁻¹ r_k)(z)

Вещественность нулей graph-нормированной трансформы — скалярный перенос
(`zerosRealOn_of_eq_smul`, ненулевой множитель `d⁻¹·overlap-scale`),
второй ground-свидетель не выбирается. ∎

## 6. Источниковый аудит матричного элемента (пункт 5 директивы)

Ядровая сторона: `T_k(C⁻¹r)(z) = ⟨C_k⁻¹ h_k(z), r_k⟩`, где `h_k(z)` —
вектор pole-kernel значений (C эрмитова — резольвента переносится на
ядро). Против КАЖДОГО существующего источникового тождества:

1. **⟨q,r⟩ = 0** — убивает q-компоненту `C⁻¹h(z)`: элемент видит только
   `Q C⁻¹ h(z)`. Уже строгое уменьшение против сырой оценки.
2. **Γ = D·r** — переносит элемент в `⟨D⁻¹QC⁻¹h(z), Γ⟩` на ненулевых
   модах; сохраняет комбинированную прайм-компенсацию, но rate для Γ
   отсутствует (ратифицировано) — канал не замыкает.
3. **Riesz-split** (`SourceActionSplit:681`,
   `s•(R x − a x) = t•((R−a)eE + (R−a)gE)`) — ГЛАВНЫЙ канал. Элемент
   расщепляется точно на два:
   (a) **E*-error канал** `⟨C⁻¹h(z), P_N (R−a) eE⟩` — eE несёт
   оконную ошибку E*, у которой есть rates
   (`selectedFerrersEStarWindowMainError_bound...`, (C1+C2)/(λ√u));
   (b) **target-action канал** `⟨C⁻¹h(z), P_N (R−a) gE⟩` — действие
   источника на явную предельную цель. Это и есть точный неразрешённый
   объект. Канал (b) НЕ сводится ни к ‖r‖/β, ни к s_k, ни к Γ без новой
   идентичности — это новое точное разложение функционала, поэтому
   представление ВЫЖИВАЕТ (не убито), но source-rate теоремы нет.
4. **Модель в корпусе**: `inner_sourceWeilOddTailExplicitCorrection`
   (D0PstarSourceWeilOddTailResidual:125) — точное квадратичное спаривание
   через настоящий внешний обратный, континуумная сторона; шаблон того,
   как резольвентное спаривание держат без surrogate. Конечно-клеточного
   аналога для чётного сектора нет.
5. **Cauchy–Schwarz откат** `|ψ| ≤ kernelL2·‖r‖/min(1,β)` записан только
   как kill-bound; консюмером не является (запрещено директивой, и он —
   ровно сырая стена).

Твой прогноз P_GROUND_GRAPH_SOURCE_1 (0.67) подтверждён: готовой
compact-rate теоремы нет; остаточный объект — один прямой резольвентный
P59-функционал, строго меньший self-energy.

## 7. Сравнение маршрутов (пункт 9 директивы)

| Маршрут | Что требует | Статус |
|---|---|---|
| Ground-graph функционал | ОДИН элемент `⟨C⁻¹h(z), r⟩` на компактах; два независимых канала малости (ориентация + сглаживание ядра) | наименьший объект; открыт канал (b) |
| Mode-graded self-energy (R2) | глобальная квадратичная форма `⟨r,C⁻¹r⟩` + растущий пол + профиль остатка | строго сильнее; два новых фронта |
| Combined Γ (R3) | mode-weighted глобальная норма с прайм-компенсацией | максимальная стоимость |

Порядок судьи подтверждён аудитом.

## 8. Код

FAILURE_CODE: GOAL058_GROUND_GRAPH_RESOLVENT_FUNCTIONAL_SOURCE_NOT_AVAILABLE

Представление не убито: тождества §1–§5 все PAPER_PASS и готовы к одному
Lean-узлу в момент, когда канал (b) получит источник. Точный неразрешённый
элемент: `⟨C_k⁻¹ h_k(z), P_N (R−a) gE_k⟩` — действие источника на явную
предельную цель, спаренное с резольвентно-сглаженным ядром. Кандидат
следующего зонда: явная машинерия предельной цели
(`G6N1ExplicitCCMLimitBeyondSourceWindowTail`) — вычислим ли target-action
канал явной формулой. Запрашиваю адъюдикацию.
