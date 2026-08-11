-- ОЖИДАЕМЫЙ ИСХОД: компилируется, аксиомы [propext, Classical.choice, Quot.sound].
-- Закрывает предсказание P4 вердикта PROSHKA_CONSUMER_FIRST_CONSTRUCTOR_HERMFACT1_AUDIT
-- (conf 0.70, помечено UNTESTED): вход-базис фактора устраняется автоматикой.
-- P4 вердикта PROSHKA_CONSUMER_FIRST_CONSTRUCTOR_HERMFACT1_AUDIT: базис фактора
-- генерируется автоматически, conf 0.70, помечено UNTESTED. Проверяем.
import Q3.Proofs.RouteB.CCMFiniteWeilParity
import Mathlib
set_option maxHeartbeats 1000000
open Q3.RouteB Matrix

/-- Потребитель БЕЗ входа `b`: базис фактора строится на месте. -/
theorem ccm_realZeros_without_basis_input
    (mProject N : ℕ) (epsilon : ℝ) (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1)
    (hbottom : ∀ x : CCMModeFinite N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤ x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite mProject N) x)
    (hsimple : Module.finrank ℝ
      ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1) :
    ZerosRealOn Set.univ
      (fun z => ((sourceLagrangePolynomial
        (fun i => (ccmModeFinite N i : ℝ)) xi).map (algebraMap ℝ ℂ)).eval z) := by
  classical
  set Qt := (CCMModeFinite N → ℝ) ⧸
    LinearMap.ker (Matrix.toBilin' (ccmShiftedWeilMatFinite mProject N epsilon))
  exact ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
    mProject N epsilon xi hm hN heig hnormalized hbottom hsimple
    (Module.Basis.ofVectorSpace ℝ Qt)

#print axioms ccm_realZeros_without_basis_input
