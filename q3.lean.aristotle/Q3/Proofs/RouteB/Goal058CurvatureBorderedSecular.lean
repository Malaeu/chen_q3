import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

set_option linter.mathlibStandardSet false

/-!
# Goal 058 bordered secular bookkeeping

Finite-dimensional identities selected in the 2026-09-03 curvature review.
They contain no cofinal estimate, spectral-gap hypothesis, or RH claim.
-/

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- The even hyperbolic pole vector in the exact CCM `W_{0,2}` split. -/
noncomputable def ccmPoleCosVector (L : ℝ) (n : ℤ) : ℝ :=
  4 * Real.sqrt L * Real.sinh (L / 4) * L /
    (L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)

/-- The odd hyperbolic pole vector in the exact CCM `W_{0,2}` split. -/
noncomputable def ccmPoleSinVector (L : ℝ) (n : ℤ) : ℝ :=
  16 * Real.pi * Real.sqrt L * Real.sinh (L / 4) * (n : ℝ) /
    (L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2)

/-- Exact source factorization `W02 = 2 C_L C_Lᵀ - 2 S_L S_Lᵀ`. -/
theorem ccmW02Entry_rank_two_factorization
    {L : ℝ} (hL : 0 ≤ L) (n m : ℤ) :
    ccmW02Entry L n m =
      2 * ccmPoleCosVector L n * ccmPoleCosVector L m -
        2 * ccmPoleSinVector L n * ccmPoleSinVector L m := by
  unfold ccmW02Entry ccmPoleCosVector ccmPoleSinVector
  have hsqrt : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring_nf
  rw [hsqrt]
  ring

/-- Matrix form of the exact rank-two factorization on any finite carrier. -/
theorem ccmW02Matrix_rank_two_factorization
    {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (mode : ι → ℤ) :
    (fun i j : ι => ccmW02Entry L (mode i) (mode j)) =
      (2 : ℝ) • Matrix.vecMulVec (fun i => ccmPoleCosVector L (mode i))
          (fun i => ccmPoleCosVector L (mode i)) -
        (2 : ℝ) • Matrix.vecMulVec (fun i => ccmPoleSinVector L (mode i))
          (fun i => ccmPoleSinVector L (mode i)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [ccmW02Entry_rank_two_factorization hL]
  ring

/-- A scalar center row, represented as a `1 × n` matrix. -/
def ccmCenterRow {n : Type*} (b : n → ℝ) : Matrix (Fin 1) n ℝ :=
  fun _ j => b j

/-- A scalar center column, represented as an `n × 1` matrix. -/
def ccmCenterCol {n : Type*} (b : n → ℝ) : Matrix n (Fin 1) ℝ :=
  fun i _ => b i

/-- Generic scalar-center Schur determinant identity. -/
theorem det_ccmCenterBlock
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : ℝ) (b : n → ℝ) (D : Matrix n n ℝ) [Invertible D] :
    det (Matrix.fromBlocks !![a] (ccmCenterRow b) (ccmCenterCol b) D) =
      det D * (a - dotProduct b ((⅟ D) *ᵥ b)) := by
  rw [Matrix.det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ccmCenterRow, ccmCenterCol,
    Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp
  ring

/-- The same identity for the shifted complement `D - zI`. -/
theorem det_ccmCenterBlock_shifted
    {n : Type*} [Fintype n] [DecidableEq n]
    (a₀ z : ℝ) (b : n → ℝ) (D : Matrix n n ℝ)
    [Invertible (D - z • (1 : Matrix n n ℝ))] :
    det (Matrix.fromBlocks !![a₀ - z] (ccmCenterRow b) (ccmCenterCol b)
        (D - z • (1 : Matrix n n ℝ))) =
      det (D - z • (1 : Matrix n n ℝ)) *
        (a₀ - z - dotProduct b ((⅟ (D - z • (1 : Matrix n n ℝ))) *ᵥ b)) := by
  exact det_ccmCenterBlock (a₀ - z) b (D - z • (1 : Matrix n n ℝ))

/-- The curvature-specific bordered deformation, already shifted by `zI`. -/
noncomputable def ccmBorderedDeformation
    {n : Type*} [Fintype n] [DecidableEq n]
    (a₀ z t : ℝ) (b c : n → ℝ) (D : Matrix n n ℝ) :
    Matrix (Fin 1 ⊕ n) (Fin 1 ⊕ n) ℝ :=
  Matrix.fromBlocks !![a₀ + t / 6 - z]
    (ccmCenterRow (b + t • c)) (ccmCenterCol (b + t • c))
    (D - z • (1 : Matrix n n ℝ))

/-- Algebraic Schur representative of the normalized bordered determinant. -/
noncomputable def ccmBorderedPhi
    {n : Type*} [Fintype n]
    (a₀ z : ℝ) (b c : n → ℝ) (R : Matrix n n ℝ) (t : ℝ) : ℝ :=
  a₀ + t / 6 - z - dotProduct (b + t • c) (R *ᵥ (b + t • c))

/-- The normalized determinant of the bordered deformation is `ccmBorderedPhi`. -/
theorem det_ccmBorderedDeformation_div
    {n : Type*} [Fintype n] [DecidableEq n]
    (a₀ z t : ℝ) (b c : n → ℝ) (D : Matrix n n ℝ)
    [Invertible (D - z • (1 : Matrix n n ℝ))]
    (hdet : det (D - z • (1 : Matrix n n ℝ)) ≠ 0) :
    det (ccmBorderedDeformation a₀ z t b c D) /
        det (D - z • (1 : Matrix n n ℝ)) =
      ccmBorderedPhi a₀ z b c (⅟ (D - z • (1 : Matrix n n ℝ))) t := by
  unfold ccmBorderedDeformation ccmBorderedPhi
  rw [det_ccmCenterBlock]
  field_simp

/-- A symmetric invertible matrix has a symmetric `invOf`. -/
theorem ccmInvOf_isSymm
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) [Invertible D] (hD : D.IsSymm) :
    (⅟ D).IsSymm := by
  rw [Matrix.invOf_eq_nonsing_inv]
  unfold Matrix.IsSymm
  rw [Matrix.transpose_nonsing_inv, hD.eq]

/-- Symmetry moves the mixed resolvent pairing from one slot to the other. -/
theorem dotProduct_mulVec_comm_of_isSymm
    {n : Type*} [Fintype n]
    (b c : n → ℝ) (R : Matrix n n ℝ) (hR : R.IsSymm) :
    dotProduct b (R *ᵥ c) = dotProduct c (R *ᵥ b) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr
  ext i
  congr
  ext j
  rw [← hR.apply]
  ring

/-- Raw derivative of the finite bordered Schur representative. -/
theorem ccmBorderedPhi_hasDerivAt_raw
    {n : Type*} [Fintype n]
    (a₀ z : ℝ) (b c : n → ℝ) (R : Matrix n n ℝ) :
    HasDerivAt (ccmBorderedPhi a₀ z b c R)
      (1 / 6 - (dotProduct c (R *ᵥ b) + dotProduct b (R *ᵥ c))) 0 := by
  unfold ccmBorderedPhi Matrix.mulVec dotProduct
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert (hasDerivAt_const (x := (0 : ℝ)) a₀).add
      ((hasDerivAt_id (x := (0 : ℝ))).div_const 6) |>.sub
      (hasDerivAt_const (x := (0 : ℝ)) z) |>.sub
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        ((hasDerivAt_const (x := (0 : ℝ)) (b i)).add
          ((hasDerivAt_id (x := (0 : ℝ))).mul_const (c i))).mul
          (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
            (hasDerivAt_const (x := (0 : ℝ)) (R i j)).mul
              ((hasDerivAt_const (x := (0 : ℝ)) (b j)).add
                ((hasDerivAt_id (x := (0 : ℝ))).mul_const (c j))))))) using 1 <;>
    simp [Finset.sum_add_distrib]

/-- For a symmetric resolvent the derivative is `1/6 - 2⟨c,Rb⟩`. -/
theorem ccmBorderedPhi_hasDerivAt
    {n : Type*} [Fintype n]
    (a₀ z : ℝ) (b c : n → ℝ) (R : Matrix n n ℝ) (hR : R.IsSymm) :
    HasDerivAt (ccmBorderedPhi a₀ z b c R)
      (1 / 6 - 2 * dotProduct c (R *ᵥ b)) 0 := by
  convert ccmBorderedPhi_hasDerivAt_raw a₀ z b c R using 1
  rw [dotProduct_mulVec_comm_of_isSymm b c R hR]
  ring

/-- The curvature bracket is one half of the bordered determinant slope. -/
theorem curvature_pairing_eq_half_borderedPhi_deriv
    {n : Type*} [Fintype n]
    (a₀ z : ℝ) (b c : n → ℝ) (R : Matrix n n ℝ) (hR : R.IsSymm) :
    1 / 12 - dotProduct c (R *ᵥ b) =
      (1 / 2 : ℝ) * deriv (ccmBorderedPhi a₀ z b c R) 0 := by
  rw [(ccmBorderedPhi_hasDerivAt a₀ z b c R hR).deriv]
  ring

/-- One finite squared-node interpolant.  It is deliberately noncanonical. -/
noncomputable def finiteOddInterpolant
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x β : ι → ℝ) : Polynomial ℝ :=
  Lagrange.interpolate s (fun i => x i ^ 2) (fun i => β i / x i)

/-- On nonzero nodes, the finite data have the odd form `β_i = x_i h(x_i²)`. -/
theorem finiteOddInterpolant_spec
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x β : ι → ℝ)
    (hinj : Set.InjOn (fun i => x i ^ 2) s)
    {i : ι} (hi : i ∈ s) (hxi : x i ≠ 0) :
    β i = x i * Polynomial.eval (x i ^ 2) (finiteOddInterpolant s x β) := by
  rw [finiteOddInterpolant, Lagrange.eval_interpolate_at_node _ hinj hi]
  field_simp

/-- Odd symbol generated by a fixed finite interpolant `h`. -/
noncomputable def ccmOddSymbol (h : Polynomial ℝ) (x : ℝ) : ℝ :=
  x * h.eval (x ^ 2)

/-- Even-sector symbol generated by the same fixed `h`. -/
noncomputable def ccmEvenSectorSymbol (h : Polynomial ℝ) (u : ℝ) : ℝ :=
  u * h.eval u

@[simp] theorem ccmOddSymbol_neg (h : Polynomial ℝ) (x : ℝ) :
    ccmOddSymbol h (-x) = -ccmOddSymbol h x := by
  simp [ccmOddSymbol]

/-- Sum of the `±y` divided differences is the divided difference of `u h(u)`. -/
theorem ccm_evenSector_dividedDifference
    (h : Polynomial ℝ) {x y : ℝ} (hxy : x ≠ y) (hxny : x ≠ -y) :
    (ccmOddSymbol h x - ccmOddSymbol h y) / (x - y) +
        (ccmOddSymbol h x - ccmOddSymbol h (-y)) / (x + y) =
      2 * (ccmEvenSectorSymbol h (x ^ 2) - ccmEvenSectorSymbol h (y ^ 2)) /
        (x ^ 2 - y ^ 2) := by
  have h1 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have h2 : x + y ≠ 0 := by
    intro hzero
    apply hxny
    linarith
  have h3 : x ^ 2 - y ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero h2 h1
  simp [ccmOddSymbol, ccmEvenSectorSymbol]
  field_simp
  ring

/-- Difference of the `±y` divided differences is governed by the symbol `h`. -/
theorem ccm_oddSector_dividedDifference
    (h : Polynomial ℝ) {x y : ℝ} (hxy : x ≠ y) (hxny : x ≠ -y) :
    (ccmOddSymbol h x - ccmOddSymbol h y) / (x - y) -
        (ccmOddSymbol h x - ccmOddSymbol h (-y)) / (x + y) =
      2 * x * y * (h.eval (x ^ 2) - h.eval (y ^ 2)) /
        (x ^ 2 - y ^ 2) := by
  have h1 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have h2 : x + y ≠ 0 := by
    intro hzero
    apply hxny
    linarith
  have h3 : x ^ 2 - y ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero h2 h1
  simp [ccmOddSymbol]
  field_simp
  ring

#print axioms ccmW02Entry_rank_two_factorization
#print axioms ccmW02Matrix_rank_two_factorization
#print axioms det_ccmCenterBlock
#print axioms det_ccmCenterBlock_shifted
#print axioms det_ccmBorderedDeformation_div
#print axioms ccmBorderedPhi_hasDerivAt
#print axioms curvature_pairing_eq_half_borderedPhi_deriv
#print axioms finiteOddInterpolant_spec
#print axioms ccm_evenSector_dividedDifference
#print axioms ccm_oddSector_dividedDifference

end Q3.RouteB
