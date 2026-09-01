import Q3.Proofs.RouteB.D0PstarSourceEvenFiniteHeadCrosswalk
import Q3.Proofs.RouteB.D0PstarSourceWeilSesquilinearForm

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Selected reflection-even W02 positivity and Arch-Prime reduction

The closed CCM `W02` matrix is the difference of one reflection-even and one
reflection-odd rank-one form.  On the exact reflection-even finite carrier the
odd coordinate vanishes, so the remaining quadratic form is nonnegative.

The final theorem preserves the literal selected carrier, reflection equation,
row-complement equation, Rayleigh scalar, and eventual quantifier required by
the H2A.4.1B.2 consumer.  It removes only the favorable `W02` summand and leaves
the shifted `Arch - Prime` floor as the next supplier.  It proves no such floor,
prime estimate, complement floor, simple ground, real-zero theorem, or RH claim.

LEDGER:
  CLOSES: [SELECTED_FERRERS_EVEN_SECTOR_W02_POSITIVITY,
           SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION]
  OPENS:  [SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR]
-/

private noncomputable def w02EvenCoordinate
    (L : ℝ) (n : ℤ) : ℂ :=
  (L : ℂ) /
    ((L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ)

private noncomputable def w02OddCoordinate
    (L : ℝ) (n : ℤ) : ℂ :=
  ((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) /
    ((L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ)

private theorem ccmW02Entry_eq_rankTwoCoordinates
    (L : ℝ) (hL : 0 < L) (n r : ℤ) :
    (Q3.RouteB.ccmW02Entry L n r : ℂ) =
      ((32 * L * Real.sinh (L / 4) ^ 2 : ℝ) : ℂ) *
        (w02EvenCoordinate L n * w02EvenCoordinate L r -
          w02OddCoordinate L n * w02OddCoordinate L r) := by
  have hn : L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
    positivity
  have hr : L ^ 2 + 16 * Real.pi ^ 2 * (r : ℝ) ^ 2 ≠ 0 := by
    positivity
  norm_cast
  unfold Q3.RouteB.ccmW02Entry w02EvenCoordinate w02OddCoordinate
  push_cast
  field_simp [hn, hr]
  ring

private theorem w02OddCoordinate_neg
    (L : ℝ) (n : ℤ) :
    w02OddCoordinate L (-n) = -w02OddCoordinate L n := by
  unfold w02OddCoordinate
  push_cast
  ring

private theorem w02OddCoordinate_dotProduct_eq_zero_of_even
    (N : ℕ) (L : ℝ) (x : CCMModeFinite N → ℂ)
    (hx : ∀ j, x (ccmNegFinite N j) = x j) :
    (fun j => w02OddCoordinate L (ccmModeFinite N j)) ⬝ᵥ x = 0 := by
  classical
  let negEquiv : CCMModeFinite N ≃ CCMModeFinite N :=
    { toFun := ccmNegFinite N
      invFun := ccmNegFinite N
      left_inv := ccmNegFinite_involutive N
      right_inv := ccmNegFinite_involutive N }
  have hsum := negEquiv.sum_comp
    (fun j => w02OddCoordinate L (ccmModeFinite N j) * x j)
  dsimp [negEquiv] at hsum
  have hneg :
      (∑ j, w02OddCoordinate L (ccmModeFinite N (ccmNegFinite N j)) *
          x (ccmNegFinite N j)) =
        -(∑ j, w02OddCoordinate L (ccmModeFinite N j) * x j) := by
    calc
      (∑ j, w02OddCoordinate L (ccmModeFinite N (ccmNegFinite N j)) *
          x (ccmNegFinite N j)) =
          ∑ j, -(w02OddCoordinate L (ccmModeFinite N j) * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ccmModeFinite_neg, w02OddCoordinate_neg, hx]
            ring
      _ = -(∑ j, w02OddCoordinate L (ccmModeFinite N j) * x j) := by
        rw [Finset.sum_neg_distrib]
  rw [hneg] at hsum
  unfold dotProduct
  linear_combination (-1 / 2 : ℂ) * hsum

private theorem w02OddCoordinate_dotProduct_eq_zero_of_reflection_even
    (N : ℕ) (L : ℝ) (x : CCMModeFinite N → ℂ)
    (hx : ccmComplexReflectionMatrix N *ᵥ x = x) :
    (fun j => w02OddCoordinate L (ccmModeFinite N j)) ⬝ᵥ x = 0 := by
  apply w02OddCoordinate_dotProduct_eq_zero_of_even
  intro j
  calc
    x (ccmNegFinite N j) =
        (ccmComplexReflectionMatrix N *ᵥ x) j :=
      (ccmComplexReflectionMatrix_mulVec N x j).symm
    _ = x j := congrFun hx j

private theorem ccmW02Matrix_mulVec_eq_even_rankOne_of_reflection_even
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x) :
    (fun j k =>
        (Q3.RouteB.ccmW02Entry
          (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x =
      fun j =>
        ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
          w02EvenCoordinate (L_m i) (ccmModeFinite i.N j) *
          ((fun k => w02EvenCoordinate (L_m i) (ccmModeFinite i.N k)) ⬝ᵥ x) := by
  classical
  have hL : 0 < L_m i := logLength_pos i
  have hodd := w02OddCoordinate_dotProduct_eq_zero_of_reflection_even
    i.N (L_m i) x hx
  funext j
  unfold mulVec dotProduct
  simp_rw [ccmW02Entry_eq_rankTwoCoordinates (L_m i) hL]
  calc
    (∑ k,
        (((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
          (w02EvenCoordinate (L_m i) (ccmModeFinite i.N j) *
              w02EvenCoordinate (L_m i) (ccmModeFinite i.N k) -
            w02OddCoordinate (L_m i) (ccmModeFinite i.N j) *
              w02OddCoordinate (L_m i) (ccmModeFinite i.N k))) * x k) =
        ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
            w02EvenCoordinate (L_m i) (ccmModeFinite i.N j) *
              (∑ k, w02EvenCoordinate (L_m i) (ccmModeFinite i.N k) * x k) -
          ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
            w02OddCoordinate (L_m i) (ccmModeFinite i.N j) *
              (∑ k, w02OddCoordinate (L_m i) (ccmModeFinite i.N k) * x k) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      unfold dotProduct at hodd
      rw [hodd]
      ring

@[simp] private theorem star_w02EvenCoordinate
    (L : ℝ) (n : ℤ) :
    star (w02EvenCoordinate L n) = w02EvenCoordinate L n := by
  simp [w02EvenCoordinate]

private theorem star_dot_evenCoordinate_eq_star_dotProduct
    (N : ℕ) (L : ℝ) (x : CCMModeFinite N → ℂ) :
    star x ⬝ᵥ (fun j => w02EvenCoordinate L (ccmModeFinite N j)) =
      star ((fun j => w02EvenCoordinate L (ccmModeFinite N j)) ⬝ᵥ x) := by
  classical
  unfold dotProduct
  change
    (∑ j, star (x j) * w02EvenCoordinate L (ccmModeFinite N j)) =
      (starRingEnd ℂ)
        (∑ j, w02EvenCoordinate L (ccmModeFinite N j) * x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  rw [show (starRingEnd ℂ)
      (w02EvenCoordinate L (ccmModeFinite N j)) =
        w02EvenCoordinate L (ccmModeFinite N j) by
    exact star_w02EvenCoordinate L (ccmModeFinite N j)]
  change
    (starRingEnd ℂ) (x j) *
        w02EvenCoordinate L (ccmModeFinite N j) =
      w02EvenCoordinate L (ccmModeFinite N j) *
        (starRingEnd ℂ) (x j)
  exact mul_comm _ _

private theorem ccmW02Quadratic_eq_even_rankOne_of_reflection_even
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x) :
    star x ⬝ᵥ
        ((fun j k =>
          (Q3.RouteB.ccmW02Entry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x) =
      ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
        star ((fun j =>
          w02EvenCoordinate (L_m i) (ccmModeFinite i.N j)) ⬝ᵥ x) *
        ((fun j =>
          w02EvenCoordinate (L_m i) (ccmModeFinite i.N j)) ⬝ᵥ x) := by
  classical
  rw [ccmW02Matrix_mulVec_eq_even_rankOne_of_reflection_even i x hx]
  calc
    star x ⬝ᵥ
        (fun j =>
          ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
            w02EvenCoordinate (L_m i) (ccmModeFinite i.N j) *
            ((fun k =>
              w02EvenCoordinate (L_m i) (ccmModeFinite i.N k)) ⬝ᵥ x)) =
      ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
        (star x ⬝ᵥ
          (fun j => w02EvenCoordinate (L_m i) (ccmModeFinite i.N j))) *
        ((fun k =>
          w02EvenCoordinate (L_m i) (ccmModeFinite i.N k)) ⬝ᵥ x) := by
      unfold dotProduct
      calc
        (∑ j,
          star (x j) *
            (((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
              w02EvenCoordinate (L_m i) (ccmModeFinite i.N j) *
              (∑ k,
                w02EvenCoordinate (L_m i) (ccmModeFinite i.N k) * x k))) =
            ∑ j,
              ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
                (star (x j) *
                  w02EvenCoordinate (L_m i) (ccmModeFinite i.N j)) *
                (∑ k,
                  w02EvenCoordinate (L_m i) (ccmModeFinite i.N k) * x k) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ =
            ((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
              (∑ j, star (x j) *
                w02EvenCoordinate (L_m i) (ccmModeFinite i.N j)) *
              (∑ k,
                w02EvenCoordinate (L_m i) (ccmModeFinite i.N k) * x k) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      rw [star_dot_evenCoordinate_eq_star_dotProduct]

theorem ccmW02Quadratic_re_nonneg_of_reflection_even
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x) :
    0 ≤
      (star x ⬝ᵥ
        ((fun j k =>
          (Q3.RouteB.ccmW02Entry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x)).re := by
  rw [ccmW02Quadratic_eq_even_rankOne_of_reflection_even i x hx]
  let A : ℂ :=
    (fun j => w02EvenCoordinate (L_m i) (ccmModeFinite i.N j)) ⬝ᵥ x
  have hL : 0 < L_m i := logLength_pos i
  have hC : 0 ≤ 32 * L_m i * Real.sinh (L_m i / 4) ^ 2 := by
    positivity
  have hnorm : star A * A = ((Complex.normSq A : ℝ) : ℂ) := by
    rw [show star A = (starRingEnd ℂ) A from rfl, mul_comm,
      Complex.mul_conj]
  change
    0 ≤
      (((32 * L_m i * Real.sinh (L_m i / 4) ^ 2 : ℝ) : ℂ) *
        star A * A).re
  rw [mul_assoc]
  rw [hnorm]
  norm_cast
  exact mul_nonneg hC (Complex.normSq_nonneg A)

private theorem sourceW02AmbientContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_quadratic
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ) :
    sourceW02AmbientContinuousSesquilinearForm i
        (ccmFiniteSynthesis i x) (ccmFiniteSynthesis i x) =
      star x ⬝ᵥ
        ((fun j k =>
          (Q3.RouteB.ccmW02Entry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x) := by
  classical
  rw [sourceW02AmbientContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmW02]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ac_rfl

private theorem sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis_eq_quadratic
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ) :
    sourceWeilSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i x)
        (ccmFiniteShiftedFormDomainSynthesis i x) =
      star x ⬝ᵥ (sourceCCMFiniteMatrix i *ᵥ x) := by
  classical
  rw [sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis]
  unfold sourceCCMFiniteMatrix
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ac_rfl

private theorem sourceCCMFiniteMatrix_quadratic_eq_w02_add_archPrime
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ) :
    star x ⬝ᵥ (sourceCCMFiniteMatrix i *ᵥ x) =
      star x ⬝ᵥ
          ((fun j k =>
            (Q3.RouteB.ccmW02Entry
              (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x) +
        sourceArchPrimeSesquilinearForm i
          (ccmFiniteShiftedFormDomainSynthesis i x)
          (ccmFiniteShiftedFormDomainSynthesis i x) := by
  rw [← sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis_eq_quadratic]
  rw [sourceWeilSesquilinearForm_apply]
  rw [coe_ccmFiniteShiftedFormDomainSynthesis,
    sourceW02AmbientContinuousSesquilinearForm_apply_ccmFiniteSynthesis_eq_quadratic]

private theorem sourceCCMFiniteMatrix_shifted_quadratic_eq_w02_add_archPrime_shifted
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ) (mu : ℂ) :
    star x ⬝ᵥ
        ((sourceCCMFiniteMatrix i -
          mu • (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *ᵥ x) =
      (star x ⬝ᵥ
          ((fun j k =>
            (Q3.RouteB.ccmW02Entry
              (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ)) *ᵥ x) +
        (sourceArchPrimeSesquilinearForm i
            (ccmFiniteShiftedFormDomainSynthesis i x)
            (ccmFiniteShiftedFormDomainSynthesis i x) -
          mu * (star x ⬝ᵥ x))) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul]
  rw [sourceCCMFiniteMatrix_quadratic_eq_w02_add_archPrime]
  simp only [smul_eq_mul]
  ring

theorem sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ) (mu : ℂ) (beta : ℝ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x)
    (hfloor :
      beta * (star x ⬝ᵥ x).re ≤
        (sourceArchPrimeSesquilinearForm i
            (ccmFiniteShiftedFormDomainSynthesis i x)
            (ccmFiniteShiftedFormDomainSynthesis i x) -
          mu * (star x ⬝ᵥ x)).re) :
    beta * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ
        ((sourceCCMFiniteMatrix i -
          mu • (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *ᵥ x)).re := by
  rw [sourceCCMFiniteMatrix_shifted_quadratic_eq_w02_add_archPrime_shifted]
  rw [Complex.add_re]
  have hw := ccmW02Quadratic_re_nonneg_of_reflection_even i x hx
  linarith

/-- Reachability plant for the exact selected Arch-Prime antecedent shape.
The zero vector inhabits the literal reflection-even row complement and makes
the pointwise shifted inequality an equality for every scalar.  This proves
only pointwise non-vacuity of the carrier and equations; it is not the open
eventual uniform positive-floor supplier. -/
private theorem selectedFerrersArchPrimeShifted_zero_reachability_plant
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (beta : ℝ) :
    ∃ x : CCMModeFinite
        ((selectedFerrersCofinalSourceData P).index k).N → ℂ,
      ccmComplexReflectionMatrix
          ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x ∧
      star ((2⁻¹ : ℂ) •
        (selectedFerrersFiniteCCMRow P k +
          ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
              selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 ∧
      beta * (star x ⬝ᵥ x).re ≤
        (sourceArchPrimeSesquilinearForm
            ((selectedFerrersCofinalSourceData P).index k)
            (ccmFiniteShiftedFormDomainSynthesis
              ((selectedFerrersCofinalSourceData P).index k) x)
            (ccmFiniteShiftedFormDomainSynthesis
              ((selectedFerrersCofinalSourceData P).index k) x) -
          (((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) *
            (star x ⬝ᵥ x))).re := by
  refine ⟨0, ?_, ?_, ?_⟩
  · simp
  · simp [dotProduct]
  · simp

theorem selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (harchPrime : ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x →
        star ((2⁻¹ : ℂ) •
          (selectedFerrersFiniteCCMRow P k +
            ccmComplexReflectionMatrix
              ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
                selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 →
        beta * (star x ⬝ᵥ x).re ≤
          (sourceArchPrimeSesquilinearForm
              ((selectedFerrersCofinalSourceData P).index k)
              (ccmFiniteShiftedFormDomainSynthesis
                ((selectedFerrersCofinalSourceData P).index k) x)
              (ccmFiniteShiftedFormDomainSynthesis
                ((selectedFerrersCofinalSourceData P).index k) x) -
            (((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) *
              (star x ⬝ᵥ x))).re) :
    ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x →
        star ((2⁻¹ : ℂ) •
          (selectedFerrersFiniteCCMRow P k +
            ccmComplexReflectionMatrix
              ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
                selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 →
        beta * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix
                ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix _ _ ℂ)) *ᵥ x)).re := by
  filter_upwards [harchPrime] with k hk
  intro x hx horth
  exact sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even
    ((selectedFerrersCofinalSourceData P).index k) x
    ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta hx
    (hk x hx horth)

#print axioms ccmW02Quadratic_re_nonneg_of_reflection_even
#print axioms sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even
#print axioms selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted

end Q3.RouteB.D0Pstar
