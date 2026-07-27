# ОТВЕТ 016 — PROLATE_LEAN_LAYER

`PROLATE_LAYER_IMPLEMENTED`

Статус маршрута: `CHALLENGER / NOT_RH`. `BUS_010_VOID` соблюдён.

## A. Спецификация

### Source lock

| Объект | Формула / контракт | Источник |
|---|---|---|
| Формальная дифференциальная форма | `PW_lambda f = -d/dx ((lambda^2-x^2) d/dx f) + (2*pi*lambda*x)^2 f` | `011_concrete_htrial_source_lock.answer.md:69-73`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:33-43`; `fulltext.md:1293-1297` |
| Моды | `h0_lambda`, `h4_lambda : R -> C`, чётные, поддержка `[-lambda,lambda]`, `L2`-норма `1` | `D0_5_GROUND_AND_TRIAL_TYPES.md:55-75`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:45-58` |
| Индексный lock | `h0 <-> chi0`, `h4 <-> chi2`; `chi0,chi2 : R` | `PEN_3_3_G04_OBJECT_DICTIONARY.md:60-75` |
| Центральные отношения | `I0 = chi0*h0(0)`, `I4 = chi2*h4(0)` | `PEN_3_3_G04_OBJECT_DICTIONARY.md:232-243` |
| Каноническая комбинация | `(I4*h0-I0*h4)/sqrt(I0^2+I4^2)` | `D0_5_GROUND_AND_TRIAL_TYPES.md:60-68`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:93-112` |

### Типы

```lean
def prolateWaveExpression
    (lambda : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ...

structure ProlateOperatorData where
  lambda : ℝ
  action : (ℝ → ℂ) → ℝ → ℂ
  action_eq : action = prolateWaveExpression lambda

structure ProlatePair where
  pw : ProlateOperatorData
  h0 h4 : ℝ → ℂ
  chi0 chi2 I0 I4 : ℝ
  h0_even h4_even : Function.Even ...
  h0_support h4_support : Function.support ... ⊆ Set.Icc (-pw.lambda) pw.lambda
  h0_integrable h4_integrable : MeasureTheory.Integrable ...
  h0_sqNorm_integrable h4_sqNorm_integrable : MeasureTheory.Integrable ...
  h0_normalized h4_normalized : (∫ x, ‖... x‖ ^ 2) = 1
  I0_eq_integral I4_eq_integral : ...
  h0_fourier_center : (I0 : ℂ) = (chi0 : ℂ) * h0 0
  h4_fourier_center : (I4 : ℂ) = (chi2 : ℂ) * h4 0
```

`ProlateOperatorData` фиксирует только формальное действие. В типах нет
области оператора, самосопряжённости, существования собственных функций,
порядка собственных значений, знаков или ODE-сертификата.

```lean
def prolateCombination (P : ProlatePair) (x : ℝ) : ℂ :=
  ((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) /
    (P.normalizingDenominator : ℂ)
```

Деление в Lean тотально; ненулевость знаменателя не утверждается и остаётся
обязательством будущего слоя существования/нормировки.

### Маппинг D0

| D0 | Lean-объект |
|---|---|
| `lambda = sqrt(m)` | будущая конкретизация `P.pw.lambda` |
| `h0_lambda`, `h4_lambda` | `P.h0`, `P.h4` |
| `chi0`, `chi2` | `P.chi0`, `P.chi2` |
| `I0`, `I4` | `P.I0`, `P.I4` |
| `hTrial_m` | `prolateCombination P` |
| `gTrial_m = E_star(hTrial_m)|I_m` | `D0Pstar.gTrial_m i (prolateCombination P) hE_star` |
| `gTrial_m_N` | существующая `D0Pstar.gTrial_m_N` |
| `kTrial_m_N` | существующая стадия 3 после отдельного `TrialNonzero` |

Lean-коллизий имён `ProlatePair`, `ProlateOperatorData`,
`prolateWaveExpression`, `prolateCombination` не найдено. Документное имя
`PWExpr_m` не является Lean-декларацией.

Оценка до реализации: `100-140` строк. Факт: `125` строк.
Оставшиеся блокеры: конкретное существование и выбор мод, сертификат
`MemLp` для `E_star`, ненулевость знаменателя/`TrialNonzero`, спектральные
свойства и точный interval-ODE/Sturm-сертификат знака.

## B. Реализация и нотариат

- Файл: `Q3/Proofs/RouteB/ProlateLayer.lean`
- Строк: `125`
- Новые декларации: `8`
- Тривиальные теоремы: `3`
- `sorry|exact?|admit`: `0`
- Запрещённые утверждения существования/знака/спектральной теории: `0`
- `lake build Q3.Proofs.RouteB.ProlateLayer`: exit `0`
- полный `lake build`: exit `0` (`7817 jobs`)

`#print axioms` для всех восьми деклараций:

```text
[propext, Classical.choice, Quot.sound]
```

Итог: `PROLATE_LAYER_IMPLEMENTED`.
