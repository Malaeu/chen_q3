/-
  `hsimple` КАК СЧЁТ, а не как локализация — на настоящей `ccmWeilMatFinite`.

  Приём заимствован у формализации Anthropic `zeta-23-lean` (Apache 2.0: идея свободно,
  код НЕ копируется): вопрос «где сидит нижнее состояние» заменяется вопросом «сколько
  строго положительных направлений». Доказательство здесь своё, Mathlib-first.

  ПОЙМАНО ПРИ ПЕРЕПРОВЕРКЕ 2026-08-11. Первая редакция этой пробы доказывала мост
  ker ↔ eigenspace заново. Он уже стоял в проекте — `ccmShiftedWeilOpFinite_ker_eq_eigenspace`,
  `CCMFiniteWeilBottomSpectral.lean:34`, восемью строками выше posSemidef-поставщика,
  в том же файле, где живёт потребитель. Классический промах «не спросил полку»; проба
  переписана на существующую теорему. Общий случай оставлен отдельно и помечен как
  надстройка, а не как то, чего не было.

  ОЖИДАЕМЫЙ ИСХОД: компилируется, `#print axioms` даёт [propext, Classical.choice, Quot.sound].

  Прогон: cd q3.lean.aristotle && lake env lean ../docs/cartographer/probes/<этот файл>
-/
import Q3.Proofs.RouteB.CCMFiniteWeilBottomSpectral
import Mathlib
set_option maxHeartbeats 1000000
open Matrix Q3.RouteB

/-- Ранг-дефект: `rank S + dim ker S = card`. Общая лемма, в проекте отсутствовала. -/
theorem rank_add_finrank_ker {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) :
    S.rank + Module.finrank ℝ (LinearMap.ker S.mulVecLin) = Fintype.card n := by
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker (K := ℝ) S.mulVecLin

/-- **`hsimple` НАШЕГО потребителя есть утверждение о РАНГЕ сдвинутой матрицы.**
Слева — где сидит нижнее состояние. Справа — сколько их, и число конкретно: `2N`.

Мост ker ↔ eigenspace берётся готовым из проекта, не строится заново. -/
theorem ccm_hsimple_iff_rank (mProject N : ℕ) (epsilon : ℝ) :
    Module.finrank ℝ ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1
      ↔ (ccmShiftedWeilMatFinite mProject N epsilon).rank = 2 * N := by
  have hker :
      LinearMap.ker (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin
        = (ccmWeilOpFinite mProject N).eigenspace epsilon := by
    simpa [ccmShiftedWeilOpFinite] using
      ccmShiftedWeilOpFinite_ker_eq_eigenspace mProject N epsilon
  have hcard : Fintype.card (CCMModeFinite N) = 2 * N + 1 := by simp [CCMModeFinite]
  have hr := rank_add_finrank_ker (ccmShiftedWeilMatFinite mProject N epsilon)
  rw [hcard] at hr
  rw [← hker]
  omega

#print axioms ccm_hsimple_iff_rank
