# H2A.4.1B.1 — SELECTED FERRERS COMBINED CCM ACTION DISCRIMINATOR

```yaml
PRIMARY: H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict a08beed7 — CODEX DIRECTIVE (READ-ONLY; NO LEAN EDIT; NO ARISTOTLE; NO NUMERICS)
BASE_HEAD: a08beed7 (git rev-parse HEAD live; вершина rh_clean)
ROUTE: CHALLENGER_NOT_RH
RH_CLAIM: false

OUTCOME_CODE: COMBINED_SOURCE_ACTION_RATE_CONTRACT_FOUND
SELECTED_REPRESENTATION: R1_COMBINED_STRUCTURED_CCM_ACTION_ON_SELECTED_ROW
MINIMAL_THEOREM_CONTRACT: "sqrt(eta_k) * rho_k -> 0"
```

Ровно один outcome-код. Семь обязательных тестов — ниже; выбранное
представление и минимальный контракт — в финальной секции с точной
арифметикой допуска.

---

## TEST 1 — SEPARATE_ACTION_DECAY_IS_NOT_NECESSARY_PLANT: VERIFIED

Плант судьи, `ℂ²`: `R = diag(0,1)`, `a = 0`, `q = e₀`, `e = −e₁`,
`g = e₀ + e₁`. Проверка поэлементно:

- `e + g = (−e₁) + (e₀+e₁) = e₀ = q` ✓;
- `(R−a)q = R e₀ = (0·1, 1·0) = 0` — комбинированный дефект НУЛЬ ✓;
- `(R−a)e = −R e₁ = −e₁`, норма `1` ✓;
- `(R−a)g = R(e₀+e₁) = e₁`, норма `1` ✓.

Комбинированный дефект исчезает СОКРАЩЕНИЕМ при обоих больших
слагаемых. Любое представление, требующее раздельного распада обоих
членов как необходимого условия, отвергнуто. Треугольный бюджет
H2A.4.1A остаётся законным достаточным мажорантом — и только им.
**P_H2A41B1_2 (0.995): CONFIRMED.**

---

## TEST 2 — GENERIC_GRAPH_SCALE_PLANT: VERIFIED; generic-теорема мертва

Фиксируем допустимое `m` (например `m = 4`, `L_m = log 4`), `N → ∞`.
Carrier `E_m_N` содержит unit-моду `V_N`.

- Точный zero-extended Фурье-образ моды — транслированный
  нормированный sinc-пакет с центром `t = N/L_m`; фиксированная доля
  `L²`-массы лежит в окне ширины `~1/L_m` вокруг центра. Источник
  формул и хвостов: `logWindowZeroExtendedMode` +
  `norm_fourier_logWindowZeroExtendedMode_le_far` /
  `…_le_resonanceSafe` (D0PstarVModeLogWeightedL2.lean).
- Точный нижний рост веса на этом окне:
  `sourceArchimedeanMultiplier_ge_logNorm_sub_explicitShift`
  (D0PstarSourceArchHighFrequencyLowerBound.lean:87) — вес
  `≥ c·log(2+N/L_m) − C`.

Следовательно `‖W·F(V_N)‖² ≥ c·log(2+N/L_m) − C → ∞` при фиксированном
`L_m` — никакой константы `Cgraph` с правой частью `Cgraph·L_m` не
существует. Мой прежний generic-MISSING_A мёртв, как и постановил
вердикт (C04: забытая независимая координата `N`).
**P_H2A41B1_1 (0.99): CONFIRMED.**

**Слабейшая N-aware замена**:
`graphNorm(i,v)² ≤ Cgraph·(L_m i + log(2 + N_i/L_m i))·‖v‖²`.

**Специализация на прекоммиченное расписание** (точный факт:
`selectedFerrersPreAnchorIndex k = ⟨k+2, k+2, _⟩`,
G6N1SelectedFerrersPreAnchorDataInhabitant.lean:46 — **`m = N = k+2`
literally**): `log(2 + m/log m) ≤ log(2+m) = O(L_m)` — на расписании
N-aware форма коллапсирует обратно в `O(L_m)`-polylog. Плаузибельно,
НЕ доказано; векторный уровень обязан использовать общую
span-структуру, а не modewise-суммирование (иначе dimension-фактор
`2N+1 ~ m` — запрещён и фатален).

---

## TEST 3 — COMBINED_COEFFICIENT_LOCK: EXACT, БЕЗ ДЕЛЕНИЙ

Публичная H2A.4.1A vector identity
(`selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target`):
`s_k • x_k = t_k • (eE_k + gE_k)`, где `x_k` — точный selected kTrial,
`t_k = sTrial_m_N > 0` (обратная норма `‖gN_k‖⁻¹`, определена всегда —
TrialNonzero — и НЕ используется как uniform floor), `s_k` — точный
sourceScale. Оба направления identity точные; никакого fitted-скаляра;
Rayleigh-сдвиг не тронут. Синтез строки: `synthesis(q_k) = x_k`
(публичная H2A.2). Комбинированный объект дискриминатора — точная
строка `q_k` с точным сдвигом `a_k`.

---

## TEST 4 — STRUCTURED_CCM_ACTION_EXPANSION: ЗАКРЫТАЯ MOMENT-СТРУКТУРА, НЕ RESTATEMENT

Точные source-факты (CCMFiniteWeilSourceCommutator.lean,
CCMFiniteWeilShiftedRankOne.lean; все kernel-checked):

1. **Loewner/divided-difference off-diagonal**:
   `ccmWeilMatFinite_structured_offdiag` (…:330):
   `M_{ij} = (β_i − β_j)/(n_i − n_j)` для `i ≠ j`, где
   `β_i = n_i · M_{i,center}` (`ccmBetaFinite`, центральный столбец) —
   вся off-диагональ матрицы порождена ОДНИМ вектором β.
2. **Rank-two коммутатор**: `ccmShiftedWeilMatFinite_commutator` (…:103):
   `[M − εI, D] = η⊗β − β⊗η`, `D = diag(n_i)`, `η = (1,…,1)`
   (`ccmEtaFinite`, CCMFiniteWeilSourceMatrix.lean:51).
3. Следствие для любого вектора `q` (линейная алгебра из 2):
   `M(Dq) − D(Mq) = η·(β⬝q) − β·(η⬝q)` — действие матрицы на
   D-сдвинутый вектор выражается через D-сдвиг образа и ДВА скалярных
   момента: `η⬝q = Σ q_i` и `β⬝q`.

**Вердикт теста**: это НЕ переписывание умножения. Структура замыкает
действие в терминах: (а) центрального столбца β (явные числа
`n·τ(n,0)`); (б) двух моментных функционалов строки; (в) одного
D-сопряжения. Моменты нашей строки — физические величины:
`η⬝q_k = √L·(значение синтеза в u=1)`-типа функционал,
`β⬝q_k` — Weil-паринг строки с центральной модой. Оба лежат в радиусе
уже доказанной L73-машинерии (центральные значения — ровно то, что
контролируют anchor/Mellin-этажи L73.5–73.8).

**Ограничение (честно)**: одно rank-two тождество само по себе не
производит rate — оно редуцирует, но остаётся D-сопряжённый член.
Rate приходит из редукции + ослабленного консюмера (ниже), а не из
тождества в одиночку.

---

## TEST 5 — TARGET_R2_DISCRIMINATOR: МОМЕНТНАЯ РЕДУКЦИЯ ЕСТЬ; ЗАКРЫТОЙ RATE-IDENTITY НЕТ

На явных координатах `gE_k = (⟨V_n, G⟩)_n` структурное разложение
теста 4 применимо дословно: действие `M` на `gE_k` редуцируется к
`D(M gE_k)`-сопряжению и моментам `η⬝gE_k`, `β⬝gE_k`. Оба момента —
конкретные суммы Fourier-коэффициентов цели, вычислимые из уже
kernel-checked Mellin-фактов (`mellin_E_star_eq_riemannZeta_mul`,
L73.5-пакет; коэффициенты цели — те же, что входили в
H2A.3-сокращение). Это подлинная source-дорога R2.

Но замкнутой commutator/radical/divided-difference IDENTITY, дающей
rate для `T_k` в одиночку, в дереве нет, и моментная редукция её не
создаёт — остаётся тот же D-сопряжённый член, что в тесте 4.
**P_H2A41B1_3 (0.90): CONFIRMED** — target-структура сама по себе не
замыкается в rate; она замыкается только внутри combined-представления.
Inversion-evenness и transform-convergence не использованы.

---

## TEST 6 — PRIME_ERROR_DISCRIMINATOR: ГРАНЬ ЛОГАРИФМИЧЕСКАЯ, НЕ ПОЛИНОМИАЛЬНАЯ

Точная структура prime-члена (`ccmPrimeEntryN1`,
CCMFiniteWeilSourceMatrixN1.lean:56): **сохранённая конечная
фон-Мангольдт-сумма** `Σ_{r=2}^{m} Λ(r)/√r · Q(L; n, n'; log r)` с
ограниченным ядром `Q` (cos/sin-раздел, |Q| = O(1) на носителе).

- Generic ambient-opNorm маршрут: `Σ_{r≤m} Λ(r)/√r ≤ C√m·log m` —
  подтверждаю расчёт вердикта; при консюмере с весом это НЕ закрывается.
  **P_H2A41B1_4 (0.97): CONFIRMED.**
- Direct-оценка с L73-входом при СОХРАНЁННОЙ сумме: паринг prime-члена
  с ошибкой ≤ `Σ_{r≤m} Λ(r)/√r · O(‖e‖) = C√m·log m · O(λ^{-1/2})
  = O(m^{1/4}·log m)`. При ОСЛАБЛЕННОМ консюмере (ниже) требуется
  `o(m^{1/4}/√log m)` — разрыв составляет ровно **`log^{3/2} m`**, а не
  степень m. Значит prime-каналу нужна source-специфическая осцилляция
  (знакопеременность Q-ядра по log r) лишь лог-толщины — качественно
  более слабое требование, чем считалось до пересчёта консюмера.

---

## TEST 7 — SELECTED_GRAPH_SHAPE (fallback R3)

Если separated-graph маршрут когда-либо понадобится: ТОЛЬКО на
расписании `N = m` (тест 2), форма
`graphNorm(index_k, v)² ≤ Cgraph·L_{m_k}·‖v‖²` на selected carrier,
вывод — через общую span-структуру (единый интеграл
`∫(1+log(2+|t|))·|F(Σ c_n V_n)(t)|² dt` с точными far/resonanceSafe-
хвостами), НЕ через modewise-triangle. Generic-форма не заявляется.
Роль — high-cost fallback; при выбранном ослабленном консюмере она
перестаёт быть узким местом (субполиномиальный допуск покрывает
polylog с запасом).

---

## ВЫБОР ПРЕДСТАВЛЕНИЯ И МИНИМАЛЬНЫЙ КОНТРАКТ

**Представление: R1 — COMBINED_STRUCTURED_CCM_ACTION_ON_SELECTED_ROW.**
Один объект `(M − a)q_k` (тот же row/carrier/schedule/scale/shift),
структурная редукция теста 4, сокращение error/target сохранено
(тест 1 показывает, почему его нельзя терять).

**Решающий пересчёт консюмера** (источник допуска — точная
kernel-checked формула H2A.1):

```text
betaEff = min(β₊,β₋)·(1−η) − ((2√η+η)/√(1−η))·ρ
```

Потребителю НЕ нужен `ρ_k → 0`. При `η_k → 0` (H2A.3, kernel-checked:
`η_k ≤ C·log m_k/√m_k`) и секторных floor'ах `β± ≥ β₀ > 0` (отдельные
открытые этажи) положительность betaEff eventually следует из одного
условия:

```text
MINIMAL_THEOREM_CONTRACT (H2A.4.1B.2 candidate):
  Tendsto (fun k =>
    Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
    Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
  atTop (nhds 0)
```

то есть `√η_k · ρ_k → 0`. С H2A.3-rate это допускает
**субполиномиальный РОСТ residual'а**: `ρ_k = o(m^{1/4}/√log m)` —
вместо прежнего требования распада `(t/|s|)(A+T) → 0`. Никакая новая
гипотеза не вводится: контракт — соединение двух уже определённых
kernel-checked скаляров.

**Ledger допуска против компонентов формы** (через 4.1A-бюджет
`‖s‖·ρ_finite ≤ t·(A+T)` и якорь `t/|s| ≤ 2√L/‖Ξ₀‖`; достаточно
`A+T = o(m^{1/4}/log m)`):

| Компонент | Доступная оценка | Требуемая | Разрыв |
|---|---|---|---|
| W02 (rank-2 endpoint) | два endpoint-функционала; polylog-ожидание | o(m^{1/4}/log m) | нет (ожидаемо polylog) |
| Prime (сохранённая Λ-сумма) | O(m^{1/4}·log m) direct | o(m^{1/4}/log m) | **log^{3/2} m** — только осцилляция |
| Arch (graph, selected N=m) | polylog plausible (тест 2/7) | o(m^{1/4}/log m) | нет (при selected-graph) |
| Моментные члены (тест 4) | L73-центральные величины | — | в радиусе доказанного |

**Что осталось несущим** (честная разметка): (i) prime-осцилляция
лог-толщины; (ii) selected-schedule graph-оценка векторного уровня;
(iii) сборка структурной редукции. Ни один из пунктов не имеет
полиномиального разрыва. LIKELIEST_FAILURE вердикта
(TARGET_OR_PRIME_SOURCE_ACTION_IDENTITY_MISSING) остаётся лучшим
кандидатом на сбой — но теперь с точно измеренной лог-толщиной.

**FORBIDDEN-чек**: Lean не редактировался; generic `Cgraph·L_m` не
заявлен (убит тестом 2); N не отброшена; modewise-triangle не
использован; A+T не объявлен точным консюмером (тест 1); target-дефект
не занулён чётностью/convergence; ambient prime-opNorm не выдан за
rate; A_m/compression не привлечены; никакой новой гипотезы-поставщика;
row/schedule/scale/shift нетронуты; Aristotle не запускался; numerics
нет.

ARISTOTLE_AUTHORIZED: false.
```yaml
SUCCESS: H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR_CLASSIFIED
NEXT_AFTER_VERDICT_ONLY: true
```
