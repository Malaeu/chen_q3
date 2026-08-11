import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
open Matrix
noncomputable def plantM : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
theorem plant_bridge : (Matrix.toEuclideanLin plantM).IsSymmetric :=
  isHermitian_iff_isSymmetric.mp (by rfl)
