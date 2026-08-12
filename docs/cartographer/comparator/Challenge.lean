/-
  Challenge.lean — ДОВЕРЕННЫЙ модуль вызова: ЧТО ЗАЯВЛЕНО.

  Устройство взято у Anthropic (`zeta-23-lean/comparator`, Apache-2.0), которые, в свою
  очередь, упаковали свои теоремы под `leanprover/comparator` от Lean FRO. Мы не
  изобретаем проверку: заимствован ШАБЛОН «доверенный вызов против недоверенного
  решения», а не код.

  ЗАЧЕМ ЭТОТ ФАЙЛ. Читатель, который хочет знать, ЧТО доказано, читает только его.
  Ему не нужно открывать ни поставщика, ни библиотеку. Формулировка здесь, а
  доказательство — снаружи и под подозрением.

  ПОЧЕМУ ИМПОРТ ТОЛЬКО `Core`. Здесь берутся `Rplus` и `shiftedHalfPlane` — и больше
  ничего. Настоящий поставщик `MuntzV3.RplusExactClass` НЕ импортируется: иначе решение
  могло бы сослаться на него, минуя проверку, и вызов перестал бы быть вызовом.

  `sorry` ниже намеренный. Это сторона вызова, предупреждение «declaration uses sorry»
  здесь ожидаемо.
-/
import Q3.Proofs.RouteB.MuntzV3.Core

open Set MeasureTheory Complex

namespace Q3Challenge

/-- Правый хвост цел в точном классе v3: измеримость, носитель в `Icc 0 b`,
липшицевость НА множестве `Ico 0 b`.

Три посылки выбраны дословно по потребителю, а не придуманы. Каждая слабее
соответствующей посылки обёртки R6, и в этом весь смысл пробы:
  * носитель в `Icc 0 b`, а НЕ в `Icc a b` при `0 < a`;
  * `LipschitzOnWith` на множестве, а НЕ глобальная `LipschitzWith`;
  * `Measurable` вместо непрерывности.
Поставщик с более сильными требованиями закрыть это не может: из посылок ниже
не получить ни `0 < a`, ни глобальную липшицевость. -/
theorem rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (EStarMuntzZeroMassContinuation.Rplus h Λ)
      EStarMuntzZeroMassContinuation.shiftedHalfPlane := by
  sorry

end Q3Challenge
