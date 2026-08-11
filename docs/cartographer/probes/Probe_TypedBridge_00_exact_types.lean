-- Фаза 0 вердикта PROSHKA_H2A_LEAN_NATIVE_PROBE_ADJUDICATION_2026-08-11:
-- материализовать ТОЧНЫЙ тип из вывода #check, не угадывать implicit binders.
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

#check @Matrix.isHermitian_iff_isSymmetric
#check @LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
#check @Matrix.toEuclideanLin
#check @Matrix.IsHermitian
