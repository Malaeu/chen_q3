import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

namespace Q3.Proofs

/-!
Finite penalty certificates for boundary-null PSD checks.

This is the Lean landing surface for Step 24 of the PSD-pd finite-certificate
route.  It deliberately avoids zeta, primes, Archimedean kernels, eigenvalues,
and interval arithmetic.  The only statement is the finite-dimensional algebra
used by the Step 18/22 penalty guard:

if `M + tau Q^T Q` is positive on the full coefficient space, then `M` is positive
on the boundary-null subspace `Qv = 0`.
-/

/-- Real quadratic form associated to a finite matrix.  We keep the explicit
double sum instead of depending on a heavier matrix quadratic-form API. -/
def quadForm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- Boundary-null predicate for a constraint matrix `Q`. -/
def BoundaryNull {ρ ι : Type*} [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ r, ∑ i, Q r i * v i = 0

/-- Squared boundary residual `||Qv||_2^2`, written as an explicit finite sum. -/
def boundaryEnergy {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ r, (∑ i, Q r i * v i) ^ 2

/-- Penalty form `v^T M v + tau ||Qv||^2`. -/
def penaltyForm {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (v : ι → ℝ) : ℝ :=
  quadForm M v + tau * boundaryEnergy Q v

/-- Squared Euclidean norm on a finite real coefficient space. -/
def euclideanEnergy {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- Squared Euclidean energy is nonnegative. -/
lemma euclideanEnergy_nonneg {ι : Type*} [Fintype ι]
    (v : ι → ℝ) :
    0 ≤ euclideanEnergy v := by
  unfold euclideanEnergy
  exact Finset.sum_nonneg (by
    intro i _
    exact sq_nonneg (v i))

/-- A nonzero finite real vector has positive squared Euclidean energy. -/
lemma euclideanEnergy_pos_of_ne_zero {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : v ≠ 0) :
    0 < euclideanEnergy v := by
  classical
  unfold euclideanEnergy
  have h_exists : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_not.mp (not_exists.mp h i)
  rcases h_exists with ⟨i, hi⟩
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (v j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-- A finite weighted sum of explicit linear squares.

This is the algebraic landing surface for checked LDL/SOS generators: if a
penalty form is rewritten as a positive Euclidean floor plus this expression
with nonnegative weights, the lower bound follows without spectral reasoning. -/
def weightedSquareSum {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → ℝ) (L : σ → ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ s, w s * (∑ i, L s i * v i) ^ 2

/-- Matrix represented by a weighted Gram sum of linear rows. -/
def weightedSquareMatrix {σ ι : Type*} [Fintype σ]
    (w : σ → ℝ) (L : σ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ s, w s * L s i * L s j

/-- Rational matrix represented by a weighted Gram sum of rational linear rows.

Generated certificate files use this version so exact LDL/SOS identities can be
checked by rational computation and then cast into the real receiver. -/
def ratWeightedSquareMatrix {σ ι : Type*} [Fintype σ]
    (w : σ → Rat) (L : σ → ι → Rat) : Matrix ι ι Rat :=
  fun i j => ∑ s, w s * L s i * L s j

/-- A weighted sum of linear squares is nonnegative when all weights are
nonnegative. -/
lemma weightedSquareSum_nonneg {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → ℝ) (L : σ → ι → ℝ)
    (hw : ∀ s, 0 ≤ w s) (v : ι → ℝ) :
    0 ≤ weightedSquareSum w L v := by
  unfold weightedSquareSum
  exact Finset.sum_nonneg (by
    intro s _
    exact mul_nonneg (hw s) (sq_nonneg _))

/-- Convert an exact weighted-square identity into a full-space Euclidean
penalty lower bound.

Future checked generators should prove only the identity and the nonnegative
weights; this theorem supplies the reusable algebraic receiver. -/
theorem penalty_lower_bound_of_weightedSquareSum_identity
    {ρ ι σ : Type*} [Fintype ρ] [Fintype ι] [Fintype σ]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau floor : ℝ)
    (w : σ → ℝ) (L : σ → ι → ℝ)
    (hw : ∀ s, 0 ≤ w s)
    (hidentity : ∀ v : ι → ℝ,
      penaltyForm M Q tau v =
        floor * euclideanEnergy v + weightedSquareSum w L v) :
    ∀ v : ι → ℝ,
      floor * euclideanEnergy v ≤ penaltyForm M Q tau v := by
  intro v
  rw [hidentity v]
  exact le_add_of_nonneg_right (weightedSquareSum_nonneg w L hw v)

/-- The boundary residual energy is the quadratic form of the Gram matrix
`Q^T Q`, written with explicit finite sums. -/
lemma boundaryEnergy_eq_quadForm_gram {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ) :
    boundaryEnergy Q v =
      quadForm (fun i j => ∑ r, Q r i * Q r j) v := by
  unfold boundaryEnergy quadForm
  simp_rw [pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Weighted square sums are exactly the quadratic form of their weighted Gram
matrix. -/
lemma weightedSquareSum_eq_quadForm_weightedSquareMatrix {σ ι : Type*}
    [Fintype σ] [Fintype ι]
    (w : σ → ℝ) (L : σ → ι → ℝ) (v : ι → ℝ) :
    weightedSquareSum w L v = quadForm (weightedSquareMatrix w L) v := by
  unfold weightedSquareSum quadForm weightedSquareMatrix
  simp_rw [pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Casting a rational weighted Gram matrix agrees with the real weighted Gram
matrix built from the cast rows and weights. -/
lemma ratWeightedSquareMatrix_cast {σ ι : Type*} [Fintype σ]
    (w : σ → Rat) (L : σ → ι → Rat) (i j : ι) :
    weightedSquareMatrix (fun s => (w s : ℝ)) (fun s i => (L s i : ℝ)) i j =
      (ratWeightedSquareMatrix w L i j : ℝ) := by
  simp [weightedSquareMatrix, ratWeightedSquareMatrix]

/-- Pointwise scalar multiplication pulls out of the explicit quadratic form. -/
lemma quadForm_pointwise_smul {ι : Type*} [Fintype ι]
    (c : ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadForm (fun i j => c * M i j) v = c * quadForm M v := by
  unfold quadForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pointwise addition distributes through the explicit quadratic form. -/
lemma quadForm_pointwise_add {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadForm (fun i j => M i j + N i j) v =
      quadForm M v + quadForm N v := by
  unfold quadForm
  simp_rw [mul_add]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]

/-- Pointwise subtraction distributes through the explicit quadratic form. -/
lemma quadForm_pointwise_sub {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadForm (fun i j => M i j - N i j) v =
      quadForm M v - quadForm N v := by
  unfold quadForm
  simp_rw [sub_eq_add_neg]
  simp_rw [mul_add]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  simp [Finset.sum_neg_distrib]

/-- The diagonal matrix with constant `floor` has quadratic form
`floor * euclideanEnergy`. -/
lemma quadForm_diagonal_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (floor : ℝ) (v : ι → ℝ) :
    quadForm (fun i j => floor * if i = j then (1 : ℝ) else 0) v =
      floor * euclideanEnergy v := by
  unfold quadForm euclideanEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
    ring
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Pointwise-equal matrices have equal explicit quadratic forms. -/
lemma quadForm_pointwise_congr {ι : Type*} [Fintype ι]
    {M N : Matrix ι ι ℝ}
    (h : ∀ i j, M i j = N i j) (v : ι → ℝ) :
    quadForm M v = quadForm N v := by
  unfold quadForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j]

/-!
### Entrywise-radius receivers

The Step 32F imported midpoint/radius payloads cannot honestly be treated as
definitionally equal to the analytic Arch/Prime matrices.  The small receiver
below is the algebraic bridge: an entrywise error box controls the quadratic
form error by an explicit radius energy.
-/

/-- Entrywise absolute-error domination for a rectangular real matrix. -/
def matrixEntrywiseAbsLe {ρ σ : Type*}
    (A M R : Matrix ρ σ ℝ) : Prop :=
  ∀ i j, |A i j - M i j| ≤ R i j

/-- Entrywise boxes are monotone in the radius matrix.  This lets generated
or analytic sub-radius bounds feed coarser imported interval radii without
reproving the underlying entry estimate. -/
theorem matrixEntrywiseAbsLe_mono {ρ σ : Type*}
    (A M R S : Matrix ρ σ ℝ)
    (hAM : matrixEntrywiseAbsLe A M R)
    (hRS : ∀ i j, R i j ≤ S i j) :
    matrixEntrywiseAbsLe A M S := by
  intro i j
  exact le_trans (hAM i j) (hRS i j)

/-- Radius energy controlling the quadratic-form error from entrywise matrix
boxes.  The radius matrix is expected to have nonnegative entries; this follows
automatically from a `matrixEntrywiseAbsLe` hypothesis for the applications
below. -/
def quadFormAbsRadius {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, |v i| * R i j * |v j|

/-- If every matrix entry of `E` is bounded in absolute value by `R`, then the
quadratic form of `E` is bounded by the radius energy. -/
lemma abs_quadForm_le_quadFormAbsRadius {ι : Type*} [Fintype ι]
    (E R : Matrix ι ι ℝ)
    (hE : ∀ i j, |E i j| ≤ R i j)
    (v : ι → ℝ) :
    |quadForm E v| ≤ quadFormAbsRadius R v := by
  unfold quadForm quadFormAbsRadius
  calc
    |∑ i, ∑ j, v i * E i j * v j|
        ≤ ∑ i, |∑ j, v i * E i j * v j| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i| * R i j * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |∑ j, v i * E i j * v j|
            ≤ ∑ j, |v i * E i j * v j| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |v i| * R i j * |v j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg (v i)))
            (abs_nonneg (v j))

/-- Entrywise midpoint/radius control gives a quadratic-form perturbation
bound.  This is the reusable algebraic landing surface for interval-backed
Step 32F payload certificates. -/
theorem abs_quadForm_sub_le_quadFormAbsRadius {ι : Type*} [Fintype ι]
    (A M R : Matrix ι ι ℝ)
    (hAM : matrixEntrywiseAbsLe A M R)
    (v : ι → ℝ) :
    |quadForm A v - quadForm M v| ≤ quadFormAbsRadius R v := by
  rw [← quadForm_pointwise_sub A M v]
  exact abs_quadForm_le_quadFormAbsRadius
    (fun i j => A i j - M i j) R hAM v

/-- Product of two coordinate magnitudes is bounded by the full squared
Euclidean energy. -/
lemma abs_mul_le_euclideanEnergy {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (i j : ι) :
    |v i| * |v j| ≤ euclideanEnergy v := by
  classical
  have hi : (v i) ^ 2 ≤ euclideanEnergy v := by
    unfold euclideanEnergy
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (v k))
      (Finset.mem_univ i)
  have hj : (v j) ^ 2 ≤ euclideanEnergy v := by
    unfold euclideanEnergy
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (v k))
      (Finset.mem_univ j)
  have hsq : 0 ≤ (|v i| - |v j|) ^ 2 := sq_nonneg _
  have habs_sq_i : |v i| ^ 2 = (v i) ^ 2 := by
    rw [sq_abs]
  have habs_sq_j : |v j| ^ 2 = (v j) ^ 2 := by
    rw [sq_abs]
  nlinarith

/-- A crude total-mass radius bound: if all radius entries are nonnegative,
then the radius energy is controlled by the total radius mass times Euclidean
energy. -/
lemma quadFormAbsRadius_le_totalRadius_mul_euclideanEnergy
    {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℝ)
    (hR : ∀ i j, 0 ≤ R i j)
    (v : ι → ℝ) :
    quadFormAbsRadius R v ≤
      (∑ i, ∑ j, R i j) * euclideanEnergy v := by
  unfold quadFormAbsRadius
  calc
    ∑ i, ∑ j, |v i| * R i j * |v j|
        ≤ ∑ i, ∑ j, R i j * euclideanEnergy v := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc
            |v i| * R i j * |v j|
                = R i j * (|v i| * |v j|) := by ring
            _ ≤ R i j * euclideanEnergy v := by
              exact mul_le_mul_of_nonneg_left
                (abs_mul_le_euclideanEnergy v i j)
                (hR i j)
    _ = (∑ i, ∑ j, R i j) * euclideanEnergy v := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- Scalar radius-floor receiver.

This is intentionally conservative: a generator may prove that the total
nonnegative radius mass is at most `radFloor`, and this theorem converts that
fact into the radius-energy bound required by the penalty radius receiver. -/
theorem quadFormAbsRadius_le_radiusFloor_mul_euclideanEnergy
    {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℝ) (radFloor : ℝ)
    (hR : ∀ i j, 0 ≤ R i j)
    (hsum : (∑ i, ∑ j, R i j) ≤ radFloor) :
    ∀ v : ι → ℝ,
      quadFormAbsRadius R v ≤ radFloor * euclideanEnergy v := by
  intro v
  exact le_trans
    (quadFormAbsRadius_le_totalRadius_mul_euclideanEnergy R hR v)
    (mul_le_mul_of_nonneg_right hsum (euclideanEnergy_nonneg v))

/-- Matrix of the penalized quadratic form `M + tau Q^T Q`. -/
def penaltyMatrix {ρ ι : Type*} [Fintype ρ]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ) :
    Matrix ι ι ℝ :=
  fun i j => M i j + tau * ∑ r, Q r i * Q r j

/-- Boundary Gram matrix `Q^T Q` used by the penalized matrix. -/
def boundaryGramMatrix {ρ ι : Type*} [Fintype ρ]
    (Q : Matrix ρ ι ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ r, Q r i * Q r j

/-- A penalty-matrix hbox follows from a base-matrix hbox and a boundary-Gram
hbox.  This isolates the next analytic enclosure task: prove boxes for `M` and
`Q^T Q`, then compose them into the direct `penaltyMatrix` box consumed by the
finite certificate wrappers. -/
theorem penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
    {ρ ι : Type*} [Fintype ρ]
    (M M0 MR : Matrix ι ι ℝ)
    (Q Q0 : Matrix ρ ι ℝ)
    (GR : Matrix ι ι ℝ)
    (tau : ℝ)
    (hM : matrixEntrywiseAbsLe M M0 MR)
    (hG : matrixEntrywiseAbsLe
      (boundaryGramMatrix Q) (boundaryGramMatrix Q0) GR) :
    matrixEntrywiseAbsLe
      (penaltyMatrix M Q tau)
      (penaltyMatrix M0 Q0 tau)
      (fun i j => MR i j + |tau| * GR i j) := by
  intro i j
  have hMij := hM i j
  have hGij := hG i j
  unfold penaltyMatrix
  change
    |(M i j + tau * boundaryGramMatrix Q i j) -
      (M0 i j + tau * boundaryGramMatrix Q0 i j)| ≤
        MR i j + |tau| * GR i j
  calc
    |(M i j + tau * boundaryGramMatrix Q i j) -
      (M0 i j + tau * boundaryGramMatrix Q0 i j)|
        = |(M i j - M0 i j) +
            tau * (boundaryGramMatrix Q i j - boundaryGramMatrix Q0 i j)| := by
          ring_nf
    _ ≤ |M i j - M0 i j| +
          |tau * (boundaryGramMatrix Q i j - boundaryGramMatrix Q0 i j)| := by
          exact abs_add_le _ _
    _ = |M i j - M0 i j| +
          |tau| * |boundaryGramMatrix Q i j - boundaryGramMatrix Q0 i j| := by
          rw [abs_mul]
    _ ≤ MR i j + |tau| * GR i j := by
          exact add_le_add hMij
            (mul_le_mul_of_nonneg_left hGij (abs_nonneg tau))

/-- The explicit penalty form is the quadratic form of `penaltyMatrix`. -/
lemma penaltyForm_eq_quadForm_penaltyMatrix {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (v : ι → ℝ) :
    penaltyForm M Q tau v = quadForm (penaltyMatrix M Q tau) v := by
  unfold penaltyForm penaltyMatrix
  rw [boundaryEnergy_eq_quadForm_gram]
  rw [← quadForm_pointwise_smul]
  rw [← quadForm_pointwise_add]

/-- Entrywise midpoint/radius control for the penalized matrix controls the
penalty-form perturbation. -/
theorem abs_penaltyForm_sub_quadForm_le_quadFormAbsRadius
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (Pmid Rad : Matrix ι ι ℝ)
    (hbox : matrixEntrywiseAbsLe (penaltyMatrix M Q tau) Pmid Rad)
    (v : ι → ℝ) :
    |penaltyForm M Q tau v - quadForm Pmid v| ≤
      quadFormAbsRadius Rad v := by
  rw [penaltyForm_eq_quadForm_penaltyMatrix]
  exact abs_quadForm_sub_le_quadFormAbsRadius
    (penaltyMatrix M Q tau) Pmid Rad hbox v

/-- Transfer a midpoint penalty lower bound to the analytic penalty form when
the midpoint bound includes the explicit radius-error margin. -/
theorem penaltyForm_lower_bound_of_midpoint_lower_bound_with_radius
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau floor : ℝ)
    (Pmid Rad : Matrix ι ι ℝ)
    (hbox : matrixEntrywiseAbsLe (penaltyMatrix M Q tau) Pmid Rad)
    (hmid : ∀ v : ι → ℝ,
      floor * euclideanEnergy v + quadFormAbsRadius Rad v ≤
        quadForm Pmid v) :
    ∀ v : ι → ℝ,
      floor * euclideanEnergy v ≤ penaltyForm M Q tau v := by
  intro v
  have hpert :=
    abs_penaltyForm_sub_quadForm_le_quadFormAbsRadius
      M Q tau Pmid Rad hbox v
  have hlow :
      quadForm Pmid v - quadFormAbsRadius Rad v ≤
        penaltyForm M Q tau v := by
    have hleft := (abs_le.mp hpert).1
    linarith
  have hfloor :
      floor * euclideanEnergy v ≤
        quadForm Pmid v - quadFormAbsRadius Rad v := by
    have h := hmid v
    linarith
  exact le_trans hfloor hlow

/-- Practical margin form of the midpoint/radius transfer.

If the midpoint penalized matrix has an extra scalar margin `radFloor`, and the
explicit radius energy is bounded by that scalar margin times Euclidean energy,
then the analytic penalty form keeps the requested `floor` lower bound. -/
theorem penaltyForm_lower_bound_of_midpoint_lower_bound_and_radius_floor
    {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau floor radFloor : ℝ)
    (Pmid Rad : Matrix ι ι ℝ)
    (hbox : matrixEntrywiseAbsLe (penaltyMatrix M Q tau) Pmid Rad)
    (hmid : ∀ v : ι → ℝ,
      (floor + radFloor) * euclideanEnergy v ≤ quadForm Pmid v)
    (hrad : ∀ v : ι → ℝ,
      quadFormAbsRadius Rad v ≤ radFloor * euclideanEnergy v) :
    ∀ v : ι → ℝ,
      floor * euclideanEnergy v ≤ penaltyForm M Q tau v := by
  apply penaltyForm_lower_bound_of_midpoint_lower_bound_with_radius
    (M := M) (Q := Q) (tau := tau) (floor := floor)
    (Pmid := Pmid) (Rad := Rad) hbox
  intro v
  calc
    floor * euclideanEnergy v + quadFormAbsRadius Rad v
        ≤ floor * euclideanEnergy v + radFloor * euclideanEnergy v := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left (hrad v) (floor * euclideanEnergy v)
    _ = (floor + radFloor) * euclideanEnergy v := by
          ring
    _ ≤ quadForm Pmid v := hmid v

/-- Convert a matrix-level weighted-Gram identity into a full-space Euclidean
penalty lower bound.

This is the preferred receiver for generated 23-by-23 rational SOS/LDL
certificates: the generator proves one pointwise matrix identity, not a giant
expanded polynomial identity in all coefficient variables. -/
theorem penalty_lower_bound_of_weightedSquareMatrix_identity
    {ρ ι σ : Type*} [Fintype ρ] [Fintype ι] [Fintype σ] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau floor : ℝ)
    (w : σ → ℝ) (L : σ → ι → ℝ)
    (hw : ∀ s, 0 ≤ w s)
    (hidentity : ∀ i j,
      M i j + tau * (∑ r, Q r i * Q r j) =
        floor * (if i = j then (1 : ℝ) else 0) + weightedSquareMatrix w L i j) :
    ∀ v : ι → ℝ,
      floor * euclideanEnergy v ≤ penaltyForm M Q tau v := by
  apply penalty_lower_bound_of_weightedSquareSum_identity M Q tau floor w L hw
  intro v
  unfold penaltyForm
  rw [boundaryEnergy_eq_quadForm_gram]
  rw [← quadForm_pointwise_smul]
  rw [← quadForm_pointwise_add]
  have hq := quadForm_pointwise_congr
    (M := fun i j => M i j + tau * (∑ r, Q r i * Q r j))
    (N := fun i j =>
      floor * (if i = j then (1 : ℝ) else 0) + weightedSquareMatrix w L i j)
    hidentity v
  rw [hq]
  rw [quadForm_pointwise_add]
  rw [quadForm_diagonal_floor]
  rw [weightedSquareSum_eq_quadForm_weightedSquareMatrix]

/-- Convert a matrix-level rational weighted-Gram identity into a full-space
Euclidean penalty lower bound for the corresponding real matrices.

This is the generated LDL/SOS landing surface: the generated file proves the
entry identity over `Rat`, then this theorem casts it into the real penalty
receiver. -/
theorem penalty_lower_bound_of_ratWeightedSquareMatrix_identity
    {ρ ι σ : Type*} [Fintype ρ] [Fintype ι] [Fintype σ] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau floor : ℝ)
    (w : σ → Rat) (L : σ → ι → Rat)
    (hw : ∀ s, 0 ≤ w s)
    (hidentity : ∀ i j,
      M i j + tau * (∑ r, Q r i * Q r j) =
        floor * (if i = j then (1 : ℝ) else 0) +
          (ratWeightedSquareMatrix w L i j : ℝ)) :
    ∀ v : ι → ℝ,
      floor * euclideanEnergy v ≤ penaltyForm M Q tau v := by
  apply penalty_lower_bound_of_weightedSquareMatrix_identity M Q tau floor
    (fun s => (w s : ℝ)) (fun s i => (L s i : ℝ))
  · intro s
    exact_mod_cast hw s
  · intro i j
    rw [ratWeightedSquareMatrix_cast]
    exact hidentity i j

/-- Fully rational variant of the matrix-level receiver. -/
theorem penalty_lower_bound_of_ratMatrixWeightedSquare_identity
    {ρ ι σ : Type*} [Fintype ρ] [Fintype ι] [Fintype σ] [DecidableEq ι]
    (M : Matrix ι ι Rat) (Q : Matrix ρ ι Rat) (tau floor : Rat)
    (w : σ → Rat) (L : σ → ι → Rat)
    (hw : ∀ s, 0 ≤ w s)
    (hidentity : ∀ i j,
      M i j + tau * (∑ r, Q r i * Q r j) =
        floor * (if i = j then (1 : Rat) else 0) +
          ratWeightedSquareMatrix w L i j) :
    ∀ v : ι → ℝ,
      (floor : ℝ) * euclideanEnergy v ≤
        penaltyForm (fun i j => (M i j : ℝ)) (fun r i => (Q r i : ℝ)) (tau : ℝ) v := by
  apply penalty_lower_bound_of_ratWeightedSquareMatrix_identity
    (fun i j => (M i j : ℝ)) (fun r i => (Q r i : ℝ)) (tau : ℝ) (floor : ℝ) w L hw
  intro i j
  have h := congrArg (fun x : Rat => (x : ℝ)) (hidentity i j)
  by_cases hij : i = j
  · simp [hij] at h ⊢
    exact h
  · simp [hij] at h ⊢
    exact h

/-- The boundary residual energy vanishes on the boundary-null subspace. -/
lemma boundaryEnergy_eq_zero_of_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ)
    (hv : BoundaryNull Q v) :
    boundaryEnergy Q v = 0 := by
  unfold boundaryEnergy BoundaryNull at *
  simp [hv]

/-- On the boundary-null subspace, the penalty form equals the original
quadratic form. -/
lemma penaltyForm_eq_quadForm_of_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (v : ι → ℝ)
    (hv : BoundaryNull Q v) :
    penaltyForm M Q tau v = quadForm M v := by
  unfold penaltyForm
  rw [boundaryEnergy_eq_zero_of_boundaryNull Q v hv]
  simp

/-- Semidefinite penalty certificate.

If the penalized form is nonnegative on the full coefficient space, then the
unpenalized form is nonnegative on `ker Q`. -/
theorem quadForm_nonneg_on_boundaryNull_of_penalty_nonneg {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, 0 ≤ penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → 0 ≤ quadForm M v := by
  intro v hv
  simpa [penaltyForm_eq_quadForm_of_boundaryNull M Q tau v hv] using hpen v

/-- Strict positive penalty certificate.

If the penalized form is positive on every nonzero full-space vector, then the
unpenalized form is positive on every nonzero boundary-null vector. -/
theorem quadForm_pos_on_boundaryNull_of_penalty_pos {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm M v := by
  intro v hv hne
  simpa [penaltyForm_eq_quadForm_of_boundaryNull M Q tau v hv] using hpen v hne

/-- Strict full-space penalty positivity implies semidefinite positivity on
the boundary-null subspace.  This is the exact shape needed when a numerical
guard proves SPD for `M + tau Q^T Q`, but the downstream certificate only needs
PSD on `ker Q`. -/
theorem quadForm_nonneg_on_boundaryNull_of_penalty_pos {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm M v := by
  intro v hv hne
  exact le_of_lt <| quadForm_pos_on_boundaryNull_of_penalty_pos
    (M := M) (Q := Q) (tau := tau) hpen v hv hne

/-- Two-form version matching Step 23: one penalty guard for `Dtheta`, one for
`Rkappa`, both restricted to the same boundary-null subspace. -/
theorem two_penalty_guards_on_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ)
    (tauD tauR : ℝ)
    (hD : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm D Q tauD v)
    (hR : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm R Q tauR v) :
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm D v) ∧
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm R v) := by
  constructor
  · exact quadForm_nonneg_on_boundaryNull_of_penalty_pos
      (M := D) (Q := Q) (tau := tauD) hD
  · exact quadForm_pos_on_boundaryNull_of_penalty_pos
      (M := R) (Q := Q) (tau := tauR) hR

/-- A finite penalty certificate for the pair `(D, R)` relative to boundary
constraints `Q`.  In the PSD-pd kappa split, `D` is `Dtheta` and `R` is
`Rkappa`. -/
structure FinitePenaltyCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) where
  tauD : ℝ
  tauR : ℝ
  D_penalty_pos : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm D Q tauD v
  R_penalty_pos : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm R Q tauR v

/-- Lower-bound landing surface for proof-generating interval/SPD checkers.

This is the certificate shape a future checked interval layer should produce:
the penalized forms dominate a positive multiple of the squared Euclidean
energy on the full finite coefficient space.  Such a lower bound immediately
implies the strict positivity fields required by `FinitePenaltyCert`. -/
structure FinitePenaltyLowerBoundCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) where
  tauD : ℝ
  tauR : ℝ
  dFloor : ℝ
  rFloor : ℝ
  dFloor_pos : 0 < dFloor
  rFloor_pos : 0 < rFloor
  D_penalty_lower : ∀ v : ι → ℝ,
    dFloor * euclideanEnergy v ≤ penaltyForm D Q tauD v
  R_penalty_lower : ∀ v : ι → ℝ,
    rFloor * euclideanEnergy v ≤ penaltyForm R Q tauR v

namespace FinitePenaltyLowerBoundCert

/-- A full-space positive Euclidean lower bound yields the standard finite
penalty certificate consumed by the matrix-identification layer. -/
def toFinitePenaltyCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ}
    (cert : FinitePenaltyLowerBoundCert D R Q) :
    FinitePenaltyCert D R Q where
  tauD := cert.tauD
  tauR := cert.tauR
  D_penalty_pos := by
    intro v hv
    exact lt_of_lt_of_le
      (mul_pos cert.dFloor_pos (euclideanEnergy_pos_of_ne_zero v hv))
      (cert.D_penalty_lower v)
  R_penalty_pos := by
    intro v hv
    exact lt_of_lt_of_le
      (mul_pos cert.rFloor_pos (euclideanEnergy_pos_of_ne_zero v hv))
      (cert.R_penalty_lower v)

end FinitePenaltyLowerBoundCert

namespace FinitePenaltyCert

/-- A finite penalty certificate gives `D >= 0` and `R > 0` on the
boundary-null subspace. -/
theorem boundaryNull_guards {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ}
    (cert : FinitePenaltyCert D R Q) :
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm D v) ∧
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm R v) := by
  exact two_penalty_guards_on_boundaryNull
    (D := D) (R := R) (Q := Q)
    (tauD := cert.tauD) (tauR := cert.tauR)
    cert.D_penalty_pos cert.R_penalty_pos

/-- If `C = D + theta R` as quadratic forms and `theta >= 0`, then the
certificate proves `C >= 0` on `ker Q`. -/
theorem C_nonneg_on_boundaryNull {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (cert : FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      quadForm C v = quadForm D v + theta * quadForm R v)
    (htheta : 0 ≤ theta) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm C v := by
  intro v hv hne
  have hD : 0 ≤ quadForm D v := (boundaryNull_guards cert).1 v hv hne
  have hR : 0 ≤ quadForm R v := le_of_lt <| (boundaryNull_guards cert).2 v hv hne
  rw [hC v]
  exact add_nonneg hD (mul_nonneg htheta hR)

/-- Strengthened form of the finite certificate:
`C >= theta R` on the boundary-null subspace. -/
theorem C_ge_theta_R_on_boundaryNull {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (cert : FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      quadForm C v = quadForm D v + theta * quadForm R v) :
    ∀ v : ι → ℝ,
      BoundaryNull Q v → v ≠ 0 →
        theta * quadForm R v ≤ quadForm C v := by
  intro v hv hne
  have hD : 0 ≤ quadForm D v := (boundaryNull_guards cert).1 v hv hne
  rw [hC v]
  simpa [zero_add] using add_le_add_right hD (theta * quadForm R v)

end FinitePenaltyCert

end Q3.Proofs
