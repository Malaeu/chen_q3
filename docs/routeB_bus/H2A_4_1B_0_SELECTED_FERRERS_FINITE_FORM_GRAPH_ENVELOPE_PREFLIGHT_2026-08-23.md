# H2A.4.1B.0 — SELECTED FERRERS FINITE FORM-GRAPH ENVELOPE PREFLIGHT

```yaml
PRIMARY: H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 551d0c48 — CODEX DIRECTIVE (READ-ONLY; NO LEAN EDIT; NO ARISTOTLE; NO NUMERICS)
BASE_HEAD: 551d0c48 (git rev-parse HEAD live; вершина rh_clean)
ROUTE: CHALLENGER_NOT_RH
RH_CLAIM: false

OUTCOME_CODE: L73_L2_INPUT_INSUFFICIENT_FOR_ERROR_GRAPH_NORM
```

Ровно один outcome-код. Обоснование, точная недостающая теорема, полный
rate ledger и кандидат следующего исполнимого шага — ниже, по пяти
обязательным тестам.

---

## TEST 1 — EXACT_DUAL_DEFECT_IDENTITY: PASS (собирается из существующих теорем)

Базис-инвариантное тождество для конечного дефекта. Для `e ∈ E_m_N i`:

```text
‖(R_i − a)·e‖ = sup { ‖⟨v, (R_i − a)·e⟩‖ : v ∈ E_m_N i, ‖v‖ = 1 }
             = sup { ‖ BW_i(v, e) − a·⟨v, e⟩ ‖ : v unit in E_m_N i }
```

Сборка из существующих имён:

1. `sourceCCMFiniteRieszOperator` (D0PstarCCMFiniteRieszOperator.lean:116) —
   сопряжение literal-оператора `sourceCCMFiniteOperator =
   (sourceCCMFiniteMatrix i).mulVecLin` изометрией
   `ccmFiniteSynthesisEquiv`. Поэтому в координатах
   `⟨synth d, R_i (synth c)⟩ = Σ_j Σ_k star(d_j)·M_{jk}·c_k`
   (изометрия + евклидов inner).
2. `sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis`
   (D0PstarSourceWeilSesquilinearForm.lean:88):
   `BW_i(synth c, synth d) = Σ_j Σ_k star(c_j)·(ccmWeilMatFinite i.m i.N j k)·d_k`.
3. `sourceWeilFiniteFourierLedger_eq_ccmWeilMatrixForm`
   (D0PstarSourceWeilFiniteFourierLedger.lean:154) — ledger
   `W02 + Arch − Prime = ccmWeilMatFinite`-форма на точном конечном
   Fourier-спане.
4. `sourceCCMFiniteMatrix i = fun j k => (ccmWeilMatFinite i.m i.N j k : ℂ)`
   (D0PstarCCMFiniteSourceResidual.lean:94) — таким образом матрица
   Riesz-оператора и матрица source-формы — ОДИН литеральный объект.
5. `E_m_N_le_sourceArchimedeanShiftedFormDomain`
   (D0PstarShiftedArchFiniteModeDomain.lean:10) — конечный спан лежит в
   shifted form domain, поэтому BW_i определена на всех участниках;
   вход в домен — `ccmFiniteShiftedFormDomainSynthesis`
   (D0PstarArchSesquilinearFormFiniteRestriction.lean:57).

**Ориентация сопряжения**: обе формы ⋆-линейны в ПЕРВОМ аргументе
(`→ₗ⋆[ℂ] … →ₗ[ℂ] ℂ`, `LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)`),
как и `inner ℂ`. Согласование точное, без транспонирования.

Прямой Lean-теоремы «⟨v, R_i x⟩ = BW_i(v,x)» в дереве нет; она — одна
строка из пунктов 1–4 и войдёт в будущий 4.1B-файл как первый этаж.

---

## TEST 2 — BOUNDED_COMPONENT_LEDGER: СТРУКТУРНО ДА, ЧИСЛЕННО НЕТ

**W02**: `sourceW02AmbientContinuousSesquilinearForm` — ambient
ContinuousLinearMap-форма; оценка
`‖W02(x,y)‖ ≤ ‖W02_i‖·‖x‖·‖y‖`
(`norm_sourceW02AmbientContinuousSesquilinearForm_apply_le`,
D0PstarW02AmbientContinuousForm.lean:112). Структура — точный **rank-two
endpoint**: `sourceW02ModePairing_eq_rankTwoEndpointModeValues` через два
endpoint-функционала (`D0PstarW02EndpointFunctionals.lean`,
`sourceW02EndpointPlusFunctional/MinusFunctional` — интегральные значения
на краях окна).

**Prime**: `sourcePrimeContinuousSesquilinearForm` — ambient continuous
(cosine-L∞-мультипликатор, D0PstarPrimeAmbientSesquilinearForm.lean);
оценка `norm_sourcePrimeSesquilinearForm_apply_le`
(D0PstarSourceWeilSesquilinearForm.lean:123).

**Чего нет**: ни `‖W02_i‖`, ни `‖Prime_i‖` не имеют в дереве численной
оценки роста в `m_k`. Они существуют только как abstract opNorm.
Абсолютные row sums НЕ использованы и не предлагаются (FORBIDDEN
соблюдён). Рост в m: у W02 определяется endpoint-значениями мод на краях
`λ^{±1}` (ожидаемо полиномиально-логарифмический от `L_m`); у Prime —
sup-нормой косинус-мультипликатора (сумма фон Мангольдта по носителю
окна; ожидаемо O(λ)-масштаб ДО нормировки формы, точная нормировка —
в определении мультипликатора, численно не выписана).

**Вывод теста 2**: envelope для bounded-частей — извлекаемая программа
(две отдельные численные op-norm-оценки), но НЕ существующие теоремы.
Предсказание P_H2A41B0_2 подтверждается как «extractable», с этой
оговоркой.

---

## TEST 3 — SHIFTED_ARCH_GRAPH_LEDGER: ГЛАВНЫЙ БЛОК; L73 НЕ КОНТРОЛИРУЕТ

**Точная graph-норма**: арх-форма реализована как
`Arch_i(x,y) = ⟨ W·F(x), W·F(y) ⟩_{L²(ℝ)}`
(`sourceArchimedeanShiftedSesquilinearForm`,
D0PstarShiftedArchSesquilinearForm.lean:93), где

- `F = sourceLogWindowFourierL2Isometry i` — лог-оконное Фурье;
- `W = sourceArchimedeanShiftedSqrtWeight t = √(μ(t) + |log π| + log 4 + 6)`
  (D0PstarShiftedArchSqrtWeight.lean:23), `μ = sourceArchimedeanMultiplier`.

Требуемая graph-норма для error-члена — **‖W·F(eE_k)‖_{L²(ℝ)}**.

**Что уже есть**:
- глобальная лог-доминация символа:
  `abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope`
  (D0PstarExactArchSymbolLogDomination.lean:156):
  `|μ(t)| ≤ (|log π| + log 4 + 7)·(1 + log(2+|t|))` — аналитическая
  константа, не fit;
- хвостовые оценки Фурье-образов мод:
  `norm_fourier_logWindowZeroExtendedMode_le_far`,
  `…_le_resonanceSafe` (D0PstarVModeLogWeightedL2.lean);
- позитивность формы (`…_re_self_nonneg`), НО НЕ H_m-непрерывность —
  верхней мод-оценки `sourceArchimedeanModePairing` в дереве НЕТ
  (единственная теорема о pairing — `…_integrable`).

**Почему L73/hmode/hχ НЕ дают контроль**: H2A.3 контролирует
`‖e_k‖_{H_m} = O(λ_k^{-1/2})` — голую гильбертову норму. Вес `W²(t)`
неограничен (лог-рост по t); переход `‖e‖ → ‖W·F(eE)‖` требует либо
верхней оценки carrier-веса (мод-оценка pairing на `E_m_N`), либо
частотного контроля самого e_k. Ни того ни другого нет. Плант 1 файла
H2A.4.1A — точная конечномерная модель этого провала. Bare H_m norm не
принимается — согласен, и не предлагается.

**Предсказание P_H2A41B0_1 (0.97): CONFIRMED.**

**Недостающая точная теорема (error-side), формулировка**:

```text
MISSING_A (shifted-arch carrier envelope):
∃ Cgraph : ℝ, 0 ≤ Cgraph ∧ ∀ (i : PairIndex) (v : E_m_N i),
  ‖sourceArchimedeanShiftedWeightedLpLinearMap i ⟨v, mem⟩‖^2
    ≤ Cgraph * L_m i * ‖v‖^2
```

то есть верхняя diag/off-diag-оценка `sourceArchimedeanModePairing i n n'`
на литеральном carrier с envelope `O(L_m)` (лог-доминация символа ×
частотная локализация мод + far/resonanceSafe-хвосты — все кирпичи в
дереве уже есть; сама теорема отсутствует). Любой полиномиально-лог
envelope `O(L_m^p)` тоже проходит консюмера — см. тест 5.

---

## TEST 4 — TARGET_IDENTITY_DISCRIMINATOR: ИДЕНТИЧНОСТИ НЕТ; ЭТО СТЕНА ИСТОЧНИКА

Поиск по продакшн-дереву: единственные radical-объекты —
`sourceLagrangePolynomial_eq_signed_radical_quotient_charpoly`
(RankOneCorrectionLagrangeRadicalCharpoly.lean) и одномерный radical в
`CCMFiniteWeilRealZeros` — оба про N=1-ячейку/charpoly, НЕ про
проецированную factor-four цель. Commutator-структура
(`ccmShiftedWeilMatFinite_commutator`, `…_kills_eigenvector`,
`ccmShiftedWeil_rankOneCorrection_kernel_and_weightedSymmetric`,
CCMFiniteWeilShiftedRankOne.lean) действует на mode-diag собственный
вектор β-строки — не на `gE_k`.

Первоисточник (litreview-карточки, verbatim):
- CCM_ZST_USAGE_CARDS.md:122: «In agreement with Lemma 7.1, the educated
  guess k_λ is …» — k_λ = E(h_λ) объявлен educated guess;
- CONNES_RH2026_USAGE_CARDS.md:75: «k_λ(u) := E(h_λ)(u) … the concrete
  prolate-based educated guess for the minimal eigenvector»;
- CONNES_RH2026_USAGE_CARDS.md:15/21: simple+even lowest eigenvalue —
  ОТКРЫТАЯ гипотеза для QW_λ, числится в «Remaining steps».

**Вывод**: точной radical/window-defect/commutator-идентичности для
`gE_k` нет ни в дереве, ни в первоисточнике; источник сам называет
обоснование trial→ground главным оставшимся препятствием. Inversion-
evenность не использована как суррогат (FORBIDDEN соблюдён).
**Предсказание P_H2A41B0_3 (0.95): CONFIRMED** — target-defect `T_k`
остаётся несущим и требует НОВОЙ source-математики. Provenance НЕ
ambiguous — идентичность отсутствует однозначно, поэтому код 5 не
выбран.

---

## TEST 5 — WEIGHTED_RATE_LEDGER

Вес консюмера (из H2A.3-якоря, eventually):
`|s_k|·‖gN_k‖ ≥ ‖Ξ(0)‖ / (2√L_k)` ⇒ **`t_k/|s_k| ≤ 2√L_k / ‖Ξ(0)‖`** —
рост `O(√log m_k)`. Консюмер `(t_k/|s_k|)·(A_k + T_k) → 0` требует
`A_k + T_k = o(1/√L_k)`.

Ledger по гипотетическим legal envelope (все — при условии недостающих
теорем; ничего из этого сейчас не доказано):

| Член | Разложение | Требуемый вход | Взвешенный итог |
|---|---|---|---|
| A_k, W02-часть | ≤ ‖W02_i‖·‖eE_k‖ | численный рост ‖W02_i‖ = O(L^p) | √L·L^p·λ^{-1/2} → 0 ✓ |
| A_k, Prime-часть | ≤ ‖Prime_i‖·‖eE_k‖ | численный рост ‖Prime_i‖ = o(λ^{1/2}/√L) | нужен настоящий рост; при O(L^p) → 0 ✓ |
| A_k, Arch-часть | ≤ ‖W·F(v)‖·‖W·F(eE_k)‖ | MISSING_A на оба сомножителя | при MISSING_A: √L·(√(C·L)·√(C·L)·λ^{-1/2}) = C·L^{3/2}·λ^{-1/2} → 0 ✓ |
| A_k, сдвиг a_k | ≤ |a_k|·‖eE_k‖ | |a_k| ≤ ‖R‖-diag… при O(L^p) ✓ | ✓ |
| T_k | НЕТ разложения | новая source-идентичность/оценка | ОТКРЫТ |

Ключевые известные величины: `‖eE_k‖ ≤ ‖e_k‖ ≤ (C₁+C₂)/√λ_k`
(проекция сжимает + H2A.3-окно), `λ_k = √m_k`, `L_k = log m_k`.

**Вывод ledger**: error-сторона A_k выдерживает вес при ЛЮБОМ
полиномиально-логарифмическом envelope — запас по λ^{-1/2} огромен;
блокирует только отсутствие MISSING_A и численных норм W02/Prime.
Малый невзвешенный член нигде не засчитан. Target-сторона T_k не имеет
легального envelope вообще.

---

## КЛАССИФИКАЦИЯ И СЛЕДУЮЩИЙ ШАГ

**OUTCOME_CODE: L73_L2_INPUT_INSUFFICIENT_FOR_ERROR_GRAPH_NORM.**
Обоснование выбора: error-graph envelope НЕ найден (код 2 неприменим);
текущий L73-вход не даёт shifted-arch graph-норму (тест 3); при этом
schedule НЕ фатален (тест 5: любой лог-полиномиальный envelope проходит
— код 4 неприменим); target-identity однозначно отсутствует, не
ambiguous (код 5 неприменим).

**Выживает ли source-контракт**: для error-стороны — ДА, в виде
представления R1 (FINITE_SOURCE_WEIL_DUAL_GRAPH_DEFECT): все кирпичи
MISSING_A лежат в дереве (лог-доминация символа, far/resonanceSafe-
хвосты мод, точная mode-pairing-структура). Для target-стороны контракт
НЕ выживает без новой математики; кандидат — R2
(STRUCTURED_CCM_COMMUTATOR_DIVIDED_DIFFERENCE) на ЯВНЫХ координатах
`gE_k = (⟨V_n, G⟩)_n` — коэффициенты цели явные интегралы, и
commutator/divided-difference структура ccmWeil-элементов
(`ccmWeilTau_structured_offdiag`, `ccmWeilMatFinite_structured_offdiag`)
даёт единственную видимую source-дорогу к оценке `T_k` без row sums.

**Следующий единственный исполнимый шаг (error-сторона, где контракт
выжил)** — предлагается как H2A.4.1B.1, при отдельной авторизации:

```text
H2A_4_1B_1_SELECTED_ARCH_CARRIER_GRAPH_ENVELOPE:
верхняя оценка sourceArchimedeanModePairing на литеральном CCM-carrier
с envelope O(L_m) (форма MISSING_A выше), из
abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope +
norm_fourier_logWindowZeroExtendedMode_le_far/resonanceSafe.
Никакого rate-receiver'а; одна source-оценка формы.
```

Target-сторона (T_k) до отдельного вердикта не трогается; её
дискриминатор — R2-идентичность, не оценка.

**FORBIDDEN-чек предполёта**: row sums не использованы; operator norm
не постулирован; ambient A_m не привлечён; compression не заявлен;
никакой rate-гипотезы не добавлено; Lean не редактировался; Aristotle
не запускался; численных прогонов нет.

ARISTOTLE_AUTHORIZED: false. LEAN_WRITE: не выполнялся (read-only).
```yaml
SUCCESS: H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT_CLASSIFIED
NEXT_AFTER_VERDICT_ONLY: true
```
