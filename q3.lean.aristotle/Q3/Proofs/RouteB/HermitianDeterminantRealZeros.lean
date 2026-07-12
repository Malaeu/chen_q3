import Q3.Proofs.RouteB.ZeroEscapeLogic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

def periodicScalingDet (L : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.exp (-Complex.I * (L : ℂ) * z)

theorem periodicScalingDet_zerosRealOn {L : ℝ} (hL : L ≠ 0) :
    ZerosRealOn Set.univ (periodicScalingDet L) := by
  intro z _ hz
  have hone : (1 : ℂ) = Complex.exp (-Complex.I * (L : ℂ) * z) :=
    sub_eq_zero.mp (by simpa [periodicScalingDet] using hz)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone.symm
  have hre := congrArg Complex.re hn
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre
  norm_num at hre
  exact hre.resolve_left hL

theorem zerosRealOn_right_factor {f g : ℂ → ℂ}
    (hfg : ZerosRealOn Set.univ (fun z => f z * g z)) :
    ZerosRealOn Set.univ g := by
  intro z _ hgz
  apply hfg z (Set.mem_univ z)
  simp [hgz]

theorem zerosRealOn_of_hermitian_charpoly_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (F unit realFactor : ℂ → ℂ)
    (hunit : ∀ z, unit z ≠ 0)
    (hrealFactor : ZerosRealOn Set.univ realFactor)
    (hfactor : ∀ z,
      F z = unit z * (M.charpoly.eval z * realFactor z)) :
    ZerosRealOn Set.univ F := by
  intro z _ hz
  have hzprod : M.charpoly.eval z * realFactor z = 0 := by
    have : unit z * (M.charpoly.eval z * realFactor z) = 0 := by
      simpa [hfactor z] using hz
    exact (mul_eq_zero.mp this).resolve_left (hunit z)
  rcases mul_eq_zero.mp hzprod with hchar | hreal
  · have hzspec : z ∈ spectrum ℂ M :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hchar
    rw [hM.spectrum_eq_image_range] at hzspec
    rcases hzspec with ⟨r, ⟨i, hi⟩, hrz⟩
    rw [← hrz, ← hi]
    exact Complex.ofReal_im _
  · exact hrealFactor z (Set.mem_univ z) hreal

def nonHermitianPlantMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal ![Complex.I]

def nonHermitianPlantFunction (z : ℂ) : ℂ :=
  nonHermitianPlantMatrix.charpoly.eval z

theorem nonHermitian_charpoly_nonreal_zero :
    nonHermitianPlantFunction Complex.I = 0 ∧ Complex.I.im ≠ 0 := by
  have hspec : Complex.I ∈ spectrum ℂ nonHermitianPlantMatrix := by
    simp [nonHermitianPlantMatrix]
  have hroot : nonHermitianPlantMatrix.charpoly.IsRoot Complex.I :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec
  exact ⟨hroot, by norm_num⟩

def hermitianZeroMatrix1 : Matrix (Fin 1) (Fin 1) ℂ := 0

theorem hermitianZeroMatrix1_isHermitian :
    hermitianZeroMatrix1.IsHermitian := by
  simp [hermitianZeroMatrix1, Matrix.IsHermitian]

def vanishingUnitPlant (z : ℂ) : ℂ :=
  (z - Complex.I) * (hermitianZeroMatrix1.charpoly.eval z * 1)

theorem vanishing_unit_nonreal_zero :
    hermitianZeroMatrix1.IsHermitian ∧
    vanishingUnitPlant Complex.I = 0 ∧ Complex.I.im ≠ 0 := by
  exact ⟨hermitianZeroMatrix1_isHermitian,
    by simp [vanishingUnitPlant], by norm_num⟩

#print axioms periodicScalingDet_zerosRealOn
#print axioms zerosRealOn_right_factor
#print axioms zerosRealOn_of_hermitian_charpoly_mul
#print axioms nonHermitian_charpoly_nonreal_zero
#print axioms vanishing_unit_nonreal_zero

end Q3.RouteB
