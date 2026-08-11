/-
  ПРОВАЛ ПОЛНОТЫ БИБЛИОТЕЧНОГО ПОИСКА — четыре опыта, один довод.

  Наблюдение: `exact?` промахивается по цели, которая является ДОСЛОВНЫМ экземпляром
  заключения леммы `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional`,
  при её гипотезе, лежащей в контексте. Тот же терм в одну строку цель закрывает.

  ЭТОТ ФАЙЛ ОБЯЗАН РУГАТЬСЯ. Ожидаемый вывод — ровно три ошибки
  «`exact?` could not close the goal» (опыты 1–3) и чистая компиляция опыта 4
  с аксиомами [propext, Classical.choice, Quot.sound]. Отсутствие ошибок означает,
  что поведение поиска изменилось и наблюдение надо перепроверять, а не что всё хорошо.

  Прогон: 2026-08-11, пакет q3.lean.aristotle, Lean/Mathlib v4.26.0, ~8 с на опыт.
  Разбор: PROBE_H2A_RAYLEIGH_TYPED_BRIDGE_2026-08-11.md, раздел «Наблюдение,
  записанное до объяснения».

  Воспроизведение:
    cd q3.lean.aristotle
    lake env lean ../docs/cartographer/probes/Probe_ExactRecallFailure.lean
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

set_option maxHeartbeats 1000000

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/- ОПЫТ 1. Прочтение «провал склейки»: гипотеза подана прямо, композиция не нужна.
   Исход: ПРОМАХ ⟹ прочтение отпало. -/
example [Nonempty n] (A : Matrix n n ℝ)
    (hsym : (Matrix.toEuclideanLin A).IsSymmetric) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A)
      ↑(⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin A ↑x) ↑x)
            / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) := by
  exact?

/- ОПЫТ 2. Прочтение «не разрешается инстанс `Nontrivial`»: подаём его явно.
   Исход: ПРОМАХ ⟹ прочтение отпало. -/
example [Nontrivial (EuclideanSpace ℝ n)] (A : Matrix n n ℝ)
    (hsym : (Matrix.toEuclideanLin A).IsSymmetric) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A)
      ↑(⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin A ↑x) ↑x)
            / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) := by
  exact?

/- ОПЫТ 3. Прочтение «`toEuclideanLin` мешает унификации»: оператор абстрактный,
   всё дословно как в лемме. Исход: ПРОМАХ ⟹ прочтение отпало. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (T : E →ₗ[ℝ] E)
    (hsym : T.IsSymmetric) :
    Module.End.HasEigenvalue T
      ↑(⨅ x : { x : E // x ≠ 0 }, RCLike.re (inner ℝ (T ↑x) ↑x) / ‖(x : E)‖ ^ 2) := by
  exact?

/- ОПЫТ 4 — КОНТРОЛЬ. Тот же контекст, терм подан явно.
   Компилируется ⟹ цель есть дословный экземпляр заключения леммы, и промахи опытов 1–3
   суть провал ПОЛНОТЫ ПОИСКА, а не несовпадение типов. -/
theorem control_explicit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (T : E →ₗ[ℝ] E)
    (hsym : T.IsSymmetric) :
    Module.End.HasEigenvalue T
      ↑(⨅ x : { x : E // x ≠ 0 }, RCLike.re (inner ℝ (T ↑x) ↑x) / ‖(x : E)‖ ^ 2) :=
  hsym.hasEigenvalue_iInf_of_finiteDimensional

#print axioms control_explicit

/-
  ВЫЖИВШЕЕ ПРОЧТЕНИЕ (положительно не проверено, осталось единственным):
  форма заключения — громоздкое `⨅`-выражение под коэрцией `↑` — не берётся деревом
  различения библиотечного поиска.

  РАЗЛИЧАЮЩИЙ ОПЫТ, КОТОРЫЙ ЕГО ПРОВЕРИТ: та же схема на другой лемме Mathlib с крупным
  термом в заключении и без всякой связи с нашей предметной областью. Промах
  воспроизводится ⟹ прочтение верно.

  СЛЕДСТВИЕ ДЛЯ КОНСТРУКТОРА: библиотечный поиск даёт ложное «поставщика нет» при
  существующем поставщике, поэтому слоем отбора быть не может. Типизированный дамп
  окружения поднят из отложенных в необходимые.
-/
