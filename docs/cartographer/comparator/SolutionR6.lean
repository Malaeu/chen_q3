/-
  SolutionR6.lean — ОТРИЦАТЕЛЬНАЯ ЗАКЛАДКА: правдоподобный, но негодный поставщик.

  ЭТОТ ФАЙЛ ОБЯЗАН НЕ СОБРАТЬСЯ. Успешная сборка означает, что проба мертва.

  Замысел. Обёртка R6 доказывает утверждение с тем же ИМЕНЕМ и той же формой вывода,
  что цель v3. Поиск по имени, по головным символам и по пересечению атомов вернёт её
  как отличного кандидата. Она негодна, потому что требует БОЛЕЕ СИЛЬНЫХ посылок:

      цель v3                         обёртка R6
      ────────────────────────        ─────────────────────────────
      носитель в `Icc 0 b`            носитель в `Icc a b` при `0 < a`
      `LipschitzOnWith K h (Ico 0 b)` глобальная `LipschitzWith K h`
      `Measurable h`                  (липшицевость сильнее, измеримость не нужна)

  Из посылок цели ни `0 < a`, ни глобальную липшицевость получить нельзя: функция из
  класса v3 может иметь носитель, прижатый к нулю, и вести себя как угодно вне `Ico 0 b`.
  Направление подмены именно то, которое протокол запрещает картой [C10]
  FUNCTIONAL_NOT_SURROGATE: похожий объект вместо нужного.

  Классификация ожидаемого отказа:
      STRONGER_CLASS_REQUIRES_UNAVAILABLE_HYPOTHESES

  Если система когда-нибудь примет это как закрытие цели v3, семантический слой
  конструктора мёртв, и расширять его нельзя.
-/
import Q3.Proofs.RouteB.MuntzV3.Core

open Set MeasureTheory Complex

namespace Q3ChallengeR6

/-- Формулировка обёртки R6, воспроизведённая как ОБЪЯВЛЕНИЕ БЕЗ доказательства.
Она здесь не для того, чтобы ей верить, а чтобы попытка применить её к цели v3
провалилась на типах, а не на нашем мнении. -/
axiom r6_wrapper
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (EStarMuntzZeroMassContinuation.Rplus h Λ)
      EStarMuntzZeroMassContinuation.shiftedHalfPlane

/-- Попытка закрыть точную цель v3 обёрткой R6.

Оставлено НАМЕРЕННО не доказанным: `a` неоткуда взять, `0 < a` неоткуда получить,
глобальная липшицевость из липшицевости на `Ico 0 b` не следует. Ошибка компилятора
здесь — ожидаемый результат пробы, а не поломка. -/
theorem attempt_v3_via_r6
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (EStarMuntzZeroMassContinuation.Rplus h Λ)
      EStarMuntzZeroMassContinuation.shiftedHalfPlane :=
  -- `a` не существует в контексте; `hlip` не той формы. Компилятор обязан отказать.
  r6_wrapper h 0 b (by norm_num) (by sorry) K (by sorry) hlip Λ hΛ

end Q3ChallengeR6
