-- ОЖИДАЕМЫЙ ИСХОД: компилируется, только предупреждения линтера,
-- `#print axioms` печатает [propext, Classical.choice, Quot.sound].
-- ПЕРЕВОД `SIMPLE_EVEN` В ЯЗЫК СЧЁТА, на нашей матрице.
-- Приём заимствован у Zeta23/LinAlg (Apache 2.0 — идея, не код): считать инерцией,
-- а не локализовать. Код здесь свой, через Mathlib.
import Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne
import Mathlib
set_option maxHeartbeats 1000000
open Matrix Q3.RouteB

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem eigenspace_mulVecLin_eq_ker_sub (M : Matrix n n ℝ) (e : ℝ) :
    Module.End.eigenspace M.mulVecLin e
      = LinearMap.ker (M - e • (1 : Matrix n n ℝ)).mulVecLin := by
  rw [Module.End.eigenspace_def]; congr 1; ext x i; simp [Matrix.mulVecLin]

theorem rank_add_finrank_ker (S : Matrix n n ℝ) :
    S.rank + Module.finrank ℝ (LinearMap.ker S.mulVecLin) = Fintype.card n := by
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker (K := ℝ) S.mulVecLin

/-- **`hsimple` НАШЕГО потребителя есть утверждение о РАНГЕ сдвинутой матрицы.**
Слева — где сидит нижнее состояние. Справа — сколько их. Число конкретно: `2N`. -/
theorem ccm_hsimple_iff_rank
    (mProject N : ℕ) (epsilon : ℝ) :
    Module.finrank ℝ
        ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1
      ↔ (ccmShiftedWeilMatFinite mProject N epsilon).rank = 2 * N := by
  have hshift :
      ccmShiftedWeilMatFinite mProject N epsilon
        = ccmWeilMatFinite mProject N
            - epsilon • (1 : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) := rfl
  have hcard : Fintype.card (CCMModeFinite N) = 2 * N + 1 := by
    simp [CCMModeFinite]
  rw [show (ccmWeilOpFinite mProject N) = (ccmWeilMatFinite mProject N).mulVecLin from rfl,
      eigenspace_mulVecLin_eq_ker_sub, ← hshift]
  have hr := rank_add_finrank_ker (ccmShiftedWeilMatFinite mProject N epsilon)
  rw [hcard] at hr
  omega

#print axioms ccm_hsimple_iff_rank
