import Q3.Proofs.RouteB.D0PstarSourceW02FiniteFormCCMW02Crosswalk
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- Generic bounded rank-two endpoint form. The W02-specific source theorem
only has to provide the two continuous endpoint functionals and their literal
mode values. -/
noncomputable def endpointRankTwoContinuousSesquilinearForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (plus minus : E →L[ℂ] ℂ) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
      (fun x y =>
        star (minus x) * plus y + star (plus x) * minus y)
      (fun _ _ _ => by simp [map_add, add_mul]; ring)
      (fun _ _ _ => by simp [map_smul, mul_add]; ring)
      (fun _ _ _ => by simp [map_add, mul_add]; ring)
      (fun _ _ _ => by simp [map_smul]; ring)).mkContinuous₂
    (2 * (‖plus‖ * ‖minus‖))
    (fun x y => by
      have hpx := plus.le_opNorm x
      have hmx := minus.le_opNorm x
      have hpy := plus.le_opNorm y
      have hmy := minus.le_opNorm y
      have h1 :
          ‖star (minus x) * plus y‖ ≤
            (‖minus‖ * ‖x‖) * (‖plus‖ * ‖y‖) := by
        rw [norm_mul, norm_star]
        exact mul_le_mul hmx hpy (norm_nonneg _) (by positivity)
      have h2 :
          ‖star (plus x) * minus y‖ ≤
            (‖plus‖ * ‖x‖) * (‖minus‖ * ‖y‖) := by
        rw [norm_mul, norm_star]
        exact mul_le_mul hpx hmy (norm_nonneg _) (by positivity)
      calc
        ‖star (minus x) * plus y + star (plus x) * minus y‖ ≤
            ‖star (minus x) * plus y‖ +
              ‖star (plus x) * minus y‖ := norm_add_le _ _
        _ ≤ (‖minus‖ * ‖x‖) * (‖plus‖ * ‖y‖) +
              (‖plus‖ * ‖x‖) * (‖minus‖ * ‖y‖) := add_le_add h1 h2
        _ = (2 * (‖plus‖ * ‖minus‖)) * ‖x‖ * ‖y‖ := by ring)

@[simp]
theorem endpointRankTwoContinuousSesquilinearForm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (plus minus : E →L[ℂ] ℂ) (x y : E) :
    endpointRankTwoContinuousSesquilinearForm plus minus x y =
      star (minus x) * plus y + star (plus x) * minus y := by
  rfl

theorem endpointRankTwoContinuousSesquilinearForm_conj_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (plus minus : E →L[ℂ] ℂ) (x y : E) :
    endpointRankTwoContinuousSesquilinearForm plus minus x y =
      star (endpointRankTwoContinuousSesquilinearForm plus minus y x) := by
  rw [endpointRankTwoContinuousSesquilinearForm_apply,
    endpointRankTwoContinuousSesquilinearForm_apply]
  change
    star (minus x) * plus y + star (plus x) * minus y =
      (starRingEnd ℂ)
        (star (minus y) * plus x + star (plus y) * minus x)
  simp only [map_add, map_mul, starRingEnd_apply, star_star]
  ring

theorem endpointRankTwoContinuousSesquilinearForm_apply_mode_eq_sourceW02
    (i : PairIndex)
    (plus minus : H_m i →L[ℂ] ℂ)
    (plusValue minusValue : ℤ → ℂ)
    (hplus : ∀ n, plus (V_n_m i n) = plusValue n)
    (hminus : ∀ n, minus (V_n_m i n) = minusValue n)
    (hpair : ∀ n r,
      sourceW02ModePairing i n r =
        star (minusValue n) * plusValue r +
          star (plusValue n) * minusValue r)
    (n r : ℤ) :
    endpointRankTwoContinuousSesquilinearForm plus minus
        (V_n_m i n) (V_n_m i r) =
      sourceW02ModePairing i n r := by
  rw [endpointRankTwoContinuousSesquilinearForm_apply,
    hplus, hplus, hminus, hminus, hpair]

theorem endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex)
    (plus minus : H_m i →L[ℂ] ℂ)
    (plusValue minusValue : ℤ → ℂ)
    (hplus : ∀ n, plus (V_n_m i n) = plusValue n)
    (hminus : ∀ n, minus (V_n_m i n) = minusValue n)
    (hpair : ∀ n r,
      sourceW02ModePairing i n r =
        star (minusValue n) * plusValue r +
          star (plusValue n) * minusValue r)
    (c d : CCMModeFinite i.N → ℂ) :
    endpointRankTwoContinuousSesquilinearForm plus minus
        (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          sourceW02ModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k := by
  classical
  change
    endpointRankTwoContinuousSesquilinearForm plus minus
        (∑ j, c j • V_n_m i (ccmModeFinite i.N j))
        (∑ k, d k • V_n_m i (ccmModeFinite i.N k)) = _
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  simp only [starRingEnd_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    endpointRankTwoContinuousSesquilinearForm_apply_mode_eq_sourceW02
      i plus minus plusValue minusValue hplus hminus hpair,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02
    (i : PairIndex)
    (plus minus : H_m i →L[ℂ] ℂ)
    (plusValue minusValue : ℤ → ℂ)
    (hplus : ∀ n, plus (V_n_m i n) = plusValue n)
    (hminus : ∀ n, minus (V_n_m i n) = minusValue n)
    (hpair : ∀ n r,
      sourceW02ModePairing i n r =
        star (minusValue n) * plusValue r +
          star (plusValue n) * minusValue r)
    (c d : CCMModeFinite i.N → ℂ) :
    endpointRankTwoContinuousSesquilinearForm plus minus
        (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmW02Entry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k := by
  rw [endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis
      i plus minus plusValue minusValue hplus hminus hpair,
    sourceW02FiniteForm_eq_ccmW02MatrixForm]

#print axioms endpointRankTwoContinuousSesquilinearForm
#print axioms endpointRankTwoContinuousSesquilinearForm_apply
#print axioms endpointRankTwoContinuousSesquilinearForm_conj_symm
#print axioms endpointRankTwoContinuousSesquilinearForm_apply_mode_eq_sourceW02
#print axioms endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis
#print axioms endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02

end Q3.RouteB.D0Pstar
