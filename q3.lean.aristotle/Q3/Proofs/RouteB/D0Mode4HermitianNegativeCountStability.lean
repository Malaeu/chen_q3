import Q3.Proofs.RouteB.D0Mode4SchurInertiaOrientation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Eventual stability of the mode-four Hermitian negative count

For a fixed nonempty finite carrier, the number of negative eigenvalues of a
Hermitian matrix is locally constant at every nonsingular Hermitian matrix.
The proof is deliberately finite-dimensional and uses the project invariant
`mode4HermitianNegativeEigenvalueCount` directly.  It does not assume a DLMF
indexing theorem, an endpoint count, or a source-specific Schur crosswalk.
-/

noncomputable section

open Matrix Finset Submodule Unitary Filter Topology
open scoped Matrix.Norms.Elementwise

private def mode4StabilitySpecMap
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℝ :=
  conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (diagonal (fun i => f (hA.eigenvalues i)))

private theorem mode4StabilitySpecMap_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    mode4StabilitySpecMap hA (f * g) =
      mode4StabilitySpecMap hA f * mode4StabilitySpecMap hA g := by
  unfold mode4StabilitySpecMap
  rw [← map_mul, diagonal_mul_diagonal]
  rfl

private theorem mode4StabilitySpecMap_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    mode4StabilitySpecMap hA (f - g) =
      mode4StabilitySpecMap hA f - mode4StabilitySpecMap hA g := by
  unfold mode4StabilitySpecMap
  rw [← map_sub]
  congr 1
  simp only [← diagonal_sub, Pi.sub_apply]

private theorem mode4StabilitySpecMap_id
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    mode4StabilitySpecMap hA id = A := by
  unfold mode4StabilitySpecMap
  simpa [Function.comp_def] using hA.spectral_theorem.symm

private theorem mode4StabilitySpecMap_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (mode4StabilitySpecMap hA f).IsHermitian := by
  unfold mode4StabilitySpecMap
  rw [conjStarAlgAut_apply]
  refine isHermitian_mul_mul_conjTranspose _ ?_
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)

private theorem mode4StabilitySpecMap_rank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (mode4StabilitySpecMap hA f).rank =
      (univ.filter fun i => f (hA.eigenvalues i) ≠ 0).card := by
  have hdet : IsUnit (hA.eigenvectorUnitary : Matrix n n ℝ).det :=
    Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  have hdet' : IsUnit (star (hA.eigenvectorUnitary : Matrix n n ℝ)).det := by
    rw [show star (hA.eigenvectorUnitary : Matrix n n ℝ) =
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ from rfl,
      det_conjTranspose]
    exact hdet.star
  unfold mode4StabilitySpecMap
  rw [conjStarAlgAut_apply,
    rank_mul_eq_left_of_isUnit_det _ _ hdet',
    rank_mul_eq_right_of_isUnit_det _ _ hdet,
    rank_diagonal]
  simp only [Fintype.card_subtype]

private theorem mode4StabilitySpecMap_form
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (x : n → ℝ) :
    star x ⬝ᵥ (mode4StabilitySpecMap hA f *ᵥ x) =
      ∑ i, f (hA.eigenvalues i) *
        ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ x) i‖ ^ 2 := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let c := star U *ᵥ x
  have hsc : star x ᵥ* U = star c := by
    rw [show c = star U *ᵥ x from rfl, star_mulVec,
      show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  unfold mode4StabilitySpecMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, dotProduct_mulVec (star x) U, hsc]
  change star c ⬝ᵥ (diagonal (fun i => f (hA.eigenvalues i)) *ᵥ c) = _
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  exact sum_congr rfl fun i _ => by
    simp [c, Real.norm_eq_abs, sq_abs]
    ring

private theorem mode4Stability_form_conj
    {m n : Type*} [Fintype m] [Fintype n]
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) =
      star (B *ᵥ x) ⬝ᵥ (Q *ᵥ (B *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) Bᴴ, ← star_mulVec]

private def mode4StabilityNegPart
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  mode4StabilitySpecMap hA (·⁻)

private theorem mode4StabilityNegPart_rank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (mode4StabilityNegPart hA).rank =
      mode4HermitianNegativeEigenvalueCount A hA := by
  unfold mode4StabilityNegPart mode4HermitianNegativeEigenvalueCount
  rw [mode4StabilitySpecMap_rank]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, negPart_eq_zero, not_le]

private def mode4StabilityPositiveEigenvalueCount
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : ℕ :=
  (univ.filter fun i => 0 < hA.eigenvalues i).card

private theorem mode4StabilityPosPart_rank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (mode4StabilitySpecMap hA (·⁺)).rank =
      mode4StabilityPositiveEigenvalueCount hA := by
  unfold mode4StabilityPositiveEigenvalueCount
  rw [mode4StabilitySpecMap_rank]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le]

private theorem mode4StabilityPosPart_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (mode4StabilitySpecMap hA (·⁺)).PosSemidef := by
  unfold mode4StabilitySpecMap
  rw [conjStarAlgAut_apply]
  refine (Matrix.PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  exact fun _ => posPart_nonneg _

private theorem mode4StabilityNegPart_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (mode4StabilityNegPart hA).PosSemidef := by
  unfold mode4StabilityNegPart mode4StabilitySpecMap
  rw [conjStarAlgAut_apply]
  refine (Matrix.PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  exact fun _ => negPart_nonneg _

private theorem mode4StabilityPos_sub_neg
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    mode4StabilitySpecMap hA (·⁺) - mode4StabilityNegPart hA = A := by
  unfold mode4StabilityNegPart
  rw [← mode4StabilitySpecMap_sub,
    show ((·⁺) - (·⁻) : ℝ → ℝ) = id from
      funext fun x => posPart_sub_negPart x,
    mode4StabilitySpecMap_id]

private theorem mode4Stability_finrank_le_negativeCount
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Submodule ℝ (n → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0) :
    Module.finrank ℝ W ≤ mode4HermitianNegativeEigenvalueCount A hA := by
  let T : (n → ℝ) →ₗ[ℝ] (n → ℝ) := (mode4StabilityNegPart hA).mulVecLin
  have hinj : Function.Injective (T.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxT
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxT
    have hxT' : mode4StabilityNegPart hA *ᵥ x = 0 := hxT
    simp only [Submodule.mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hform_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) := by
      rw [← mode4StabilityPos_sub_neg hA, Matrix.sub_mulVec,
        hxT', sub_zero]
      exact (mode4StabilityPosPart_posSemidef hA).dotProduct_mulVec_nonneg x
    exact (not_lt_of_ge hform_nonneg) (hW x hxW hne')
  calc
    Module.finrank ℝ W =
        Module.finrank ℝ (LinearMap.range (T.domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℝ (LinearMap.range T) := by
      apply Submodule.finrank_mono
      rintro y ⟨⟨x, hxW⟩, rfl⟩
      exact ⟨x, rfl⟩
    _ = (mode4StabilityNegPart hA).rank := rfl
    _ = mode4HermitianNegativeEigenvalueCount A hA :=
      mode4StabilityNegPart_rank hA

private theorem mode4Stability_finrank_le_positiveCount
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Submodule ℝ (n → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x)) :
    Module.finrank ℝ W ≤ mode4StabilityPositiveEigenvalueCount hA := by
  let T : (n → ℝ) →ₗ[ℝ] (n → ℝ) :=
    (mode4StabilitySpecMap hA (·⁺)).mulVecLin
  have hinj : Function.Injective (T.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxT
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxT
    have hxT' : mode4StabilitySpecMap hA (·⁺) *ᵥ x = 0 := hxT
    simp only [Submodule.mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hform_nonpos : star x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
      rw [← mode4StabilityPos_sub_neg hA, Matrix.sub_mulVec,
        hxT', zero_sub, dotProduct_neg]
      exact neg_nonpos.mpr
        ((mode4StabilityNegPart_posSemidef hA).dotProduct_mulVec_nonneg x)
    exact (not_lt_of_ge hform_nonpos) (hW x hxW hne')
  calc
    Module.finrank ℝ W =
        Module.finrank ℝ (LinearMap.range (T.domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℝ (LinearMap.range T) := by
      apply Submodule.finrank_mono
      rintro y ⟨⟨x, hxW⟩, rfl⟩
      exact ⟨x, rfl⟩
    _ = (mode4StabilitySpecMap hA (·⁺)).rank := rfl
    _ = mode4StabilityPositiveEigenvalueCount hA :=
      mode4StabilityPosPart_rank hA

private def mode4StabilityNegativeProjector
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  mode4StabilitySpecMap hA (fun t => if t < 0 then 1 else 0)

private theorem mode4StabilityNegativeProjector_finrank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Module.finrank ℝ
        (LinearMap.range (mode4StabilityNegativeProjector hA).mulVecLin) =
      mode4HermitianNegativeEigenvalueCount A hA := by
  change (mode4StabilityNegativeProjector hA).rank = _
  unfold mode4StabilityNegativeProjector mode4HermitianNegativeEigenvalueCount
  rw [mode4StabilitySpecMap_rank]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  split_ifs <;> simp_all

private theorem mode4StabilityNegativeProjector_form_gap
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {gap : ℝ} (hgap : ∀ i, hA.eigenvalues i < 0 → gap ≤ -hA.eigenvalues i)
    {x : n → ℝ}
    (hx : x ∈ LinearMap.range (mode4StabilityNegativeProjector hA).mulVecLin) :
    star x ⬝ᵥ (A *ᵥ x) + gap * (star x ⬝ᵥ x) ≤ 0 := by
  obtain ⟨y, rfl⟩ := hx
  let p : ℝ → ℝ := fun t => if t < 0 then 1 else 0
  let P : Matrix n n ℝ := mode4StabilityNegativeProjector hA
  change star (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) +
      gap * (star (P *ᵥ y) ⬝ᵥ (P *ᵥ y)) ≤ 0
  have hPherm : P.IsHermitian := by
    simpa [P, p, mode4StabilityNegativeProjector] using
      mode4StabilitySpecMap_isHermitian hA p
  have hPAP :
      Pᴴ * A * P =
        mode4StabilitySpecMap hA (fun t => if t < 0 then t else 0) := by
    calc
      Pᴴ * A * P = P * A * P := by rw [hPherm.eq]
      _ = mode4StabilitySpecMap hA p *
          mode4StabilitySpecMap hA id * mode4StabilitySpecMap hA p := by
        simp only [P, p, mode4StabilityNegativeProjector,
          mode4StabilitySpecMap_id]
      _ = mode4StabilitySpecMap hA ((p * id) * p) := by
        rw [← mode4StabilitySpecMap_mul, ← mode4StabilitySpecMap_mul]
      _ = mode4StabilitySpecMap hA (fun t => if t < 0 then t else 0) := by
        congr 1
        funext t
        simp only [Pi.mul_apply, id_eq, p]
        split_ifs <;> ring
  have hformA :
      star (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) =
        ∑ i, (if hA.eigenvalues i < 0 then hA.eigenvalues i else 0) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ y) i‖ ^ 2 := by
    rw [← mode4Stability_form_conj A P y, hPAP]
    exact mode4StabilitySpecMap_form hA
      (fun t => if t < 0 then t else 0) y
  have hformI :
      star (P *ᵥ y) ⬝ᵥ (P *ᵥ y) =
        ∑ i, (if hA.eigenvalues i < 0 then 1 else 0) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ y) i‖ ^ 2 := by
    have hPP : Pᴴ * P = mode4StabilitySpecMap hA p := by
      calc
        Pᴴ * P = P * P := by rw [hPherm.eq]
        _ = mode4StabilitySpecMap hA p * mode4StabilitySpecMap hA p := by
          rfl
        _ = mode4StabilitySpecMap hA (p * p) := by
          rw [mode4StabilitySpecMap_mul]
        _ = mode4StabilitySpecMap hA p := by
          congr 1
          funext t
          simp only [Pi.mul_apply, p]
          split_ifs <;> ring
    calc
      star (P *ᵥ y) ⬝ᵥ (P *ᵥ y) =
          star (P *ᵥ y) ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ (P *ᵥ y)) := by simp
      _ = star y ⬝ᵥ (((Pᴴ * (1 : Matrix n n ℝ) * P)) *ᵥ y) :=
        (mode4Stability_form_conj (1 : Matrix n n ℝ) P y).symm
      _ = star y ⬝ᵥ (mode4StabilitySpecMap hA p *ᵥ y) := by
        rw [mul_one, hPP]
      _ = _ := by
        simpa [p] using mode4StabilitySpecMap_form hA p y
  rw [hformA, hformI, Finset.mul_sum, ← sum_add_distrib]
  apply sum_nonpos
  intro i _
  split_ifs with hi
  · have hg := hgap i hi
    have hs : 0 ≤ ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ y) i‖ ^ 2 :=
      sq_nonneg _
    nlinarith
  · simp

private def mode4StabilityPositiveProjector
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  mode4StabilitySpecMap hA (fun t => if 0 < t then 1 else 0)

private theorem mode4StabilityPositiveProjector_finrank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Module.finrank ℝ
        (LinearMap.range (mode4StabilityPositiveProjector hA).mulVecLin) =
      mode4StabilityPositiveEigenvalueCount hA := by
  change (mode4StabilityPositiveProjector hA).rank = _
  unfold mode4StabilityPositiveProjector mode4StabilityPositiveEigenvalueCount
  rw [mode4StabilitySpecMap_rank]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  split_ifs <;> simp_all

private theorem mode4StabilityPositiveProjector_form_gap
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {gap : ℝ} (hgap : ∀ i, 0 < hA.eigenvalues i → gap ≤ hA.eigenvalues i)
    {x : n → ℝ}
    (hx : x ∈ LinearMap.range (mode4StabilityPositiveProjector hA).mulVecLin) :
    gap * (star x ⬝ᵥ x) ≤ star x ⬝ᵥ (A *ᵥ x) := by
  obtain ⟨y, rfl⟩ := hx
  let p : ℝ → ℝ := fun t => if 0 < t then 1 else 0
  let P : Matrix n n ℝ := mode4StabilityPositiveProjector hA
  change gap * (star (P *ᵥ y) ⬝ᵥ (P *ᵥ y)) ≤
    star (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y))
  have hPherm : P.IsHermitian := by
    simpa [P, p, mode4StabilityPositiveProjector] using
      mode4StabilitySpecMap_isHermitian hA p
  have hPAP :
      Pᴴ * A * P =
        mode4StabilitySpecMap hA (fun t => if 0 < t then t else 0) := by
    calc
      Pᴴ * A * P = P * A * P := by rw [hPherm.eq]
      _ = mode4StabilitySpecMap hA p *
          mode4StabilitySpecMap hA id * mode4StabilitySpecMap hA p := by
        simp only [P, p, mode4StabilityPositiveProjector,
          mode4StabilitySpecMap_id]
      _ = mode4StabilitySpecMap hA ((p * id) * p) := by
        rw [← mode4StabilitySpecMap_mul, ← mode4StabilitySpecMap_mul]
      _ = mode4StabilitySpecMap hA (fun t => if 0 < t then t else 0) := by
        congr 1
        funext t
        simp only [Pi.mul_apply, id_eq, p]
        split_ifs <;> ring
  have hformA :
      star (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) =
        ∑ i, (if 0 < hA.eigenvalues i then hA.eigenvalues i else 0) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ y) i‖ ^ 2 := by
    rw [← mode4Stability_form_conj A P y, hPAP]
    exact mode4StabilitySpecMap_form hA
      (fun t => if 0 < t then t else 0) y
  have hformI :
      star (P *ᵥ y) ⬝ᵥ (P *ᵥ y) =
        ∑ i, (if 0 < hA.eigenvalues i then 1 else 0) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ y) i‖ ^ 2 := by
    have hPP : Pᴴ * P = mode4StabilitySpecMap hA p := by
      calc
        Pᴴ * P = P * P := by rw [hPherm.eq]
        _ = mode4StabilitySpecMap hA p * mode4StabilitySpecMap hA p := by
          rfl
        _ = mode4StabilitySpecMap hA (p * p) := by
          rw [mode4StabilitySpecMap_mul]
        _ = mode4StabilitySpecMap hA p := by
          congr 1
          funext t
          simp only [Pi.mul_apply, p]
          split_ifs <;> ring
    calc
      star (P *ᵥ y) ⬝ᵥ (P *ᵥ y) =
          star (P *ᵥ y) ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ (P *ᵥ y)) := by simp
      _ = star y ⬝ᵥ (((Pᴴ * (1 : Matrix n n ℝ) * P)) *ᵥ y) :=
        (mode4Stability_form_conj (1 : Matrix n n ℝ) P y).symm
      _ = star y ⬝ᵥ (mode4StabilitySpecMap hA p *ᵥ y) := by
        rw [mul_one, hPP]
      _ = _ := by
        simpa [p] using mode4StabilitySpecMap_form hA p y
  rw [hformA, hformI]
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro i _
  split_ifs with hi
  · simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hgap i hi) (sq_nonneg _)
  · simp

private theorem mode4Stability_abs_form_sub_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℝ) (x : n → ℝ) :
    |star x ⬝ᵥ (E *ᵥ x)| ≤
      (Fintype.card n : ℝ) * ‖E‖ * (star x ⬝ᵥ x) := by
  rw [show star x ⬝ᵥ x = ∑ i, |x i| ^ 2 by
    simp [dotProduct, pow_two]]
  simp only [dotProduct, mulVec, Pi.star_apply, star_id_of_comm]
  calc
    |∑ i, x i * ∑ j, E i j * x j|
        ≤ ∑ i, |x i * ∑ j, E i j * x j| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i => x i * ∑ j, E i j * x j) univ
    _ = ∑ i, |x i| * |∑ j, E i j * x j| := by
      simp only [abs_mul]
    _ ≤ ∑ i, |x i| * ∑ j, |E i j * x j| := by
      apply sum_le_sum
      intro i _
      have habs : |∑ j, E i j * x j| ≤ ∑ j, |E i j * x j| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun j => E i j * x j) univ
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = ∑ i, ∑ j, |x i| * |E i j| * |x j| := by
      simp only [abs_mul, Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, ∑ j, |x i| * ‖E‖ * |x j| := by
      gcongr with i _ j
      exact Matrix.norm_entry_le_entrywise_sup_norm E
    _ = ‖E‖ * (∑ i, |x i|) ^ 2 := by
      simp only [sq]
      calc
        ∑ i, ∑ j, |x i| * ‖E‖ * |x j| =
            ∑ i, (|x i| * ‖E‖) * (∑ j, |x j|) := by
          apply sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = (∑ i, |x i| * ‖E‖) * (∑ j, |x j|) := by
          rw [Finset.sum_mul]
        _ = ‖E‖ * ((∑ i, |x i|) * (∑ j, |x j|)) := by
          rw [← Finset.sum_mul]
          ring
    _ ≤ ‖E‖ * ((Fintype.card n : ℝ) * ∑ i, |x i| ^ 2) := by
      gcongr
      simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset n))
        (f := fun i => |x i|)
    _ = (Fintype.card n : ℝ) * ‖E‖ * ∑ i, |x i| ^ 2 := by ring

private theorem mode4Stability_negativeCount_le_negativeCount_of_close
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {L A : Matrix n n ℝ}
    (hL : L.IsHermitian) (hA : A.IsHermitian)
    {gap : ℝ}
    (hgapL : ∀ i, hL.eigenvalues i < 0 → gap ≤ -hL.eigenvalues i)
    (hclose : (Fintype.card n : ℝ) * ‖A - L‖ < gap) :
    mode4HermitianNegativeEigenvalueCount L hL ≤
      mode4HermitianNegativeEigenvalueCount A hA := by
  let W := LinearMap.range (mode4StabilityNegativeProjector hL).mulVecLin
  have hWneg : ∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0 := by
    intro x hxW hx
    have hLgap := mode4StabilityNegativeProjector_form_gap hL hgapL hxW
    have hpert := mode4Stability_abs_form_sub_le (A - L) x
    have hxnorm : 0 < star x ⬝ᵥ x :=
      Matrix.dotProduct_star_self_pos_iff.mpr hx
    have hpert' :
        star x ⬝ᵥ ((A - L) *ᵥ x) < gap * (star x ⬝ᵥ x) := by
      have habs_nonneg :
          star x ⬝ᵥ ((A - L) *ᵥ x) ≤
            |star x ⬝ᵥ ((A - L) *ᵥ x)| := le_abs_self _
      exact lt_of_le_of_lt habs_nonneg
        (lt_of_le_of_lt hpert (mul_lt_mul_of_pos_right hclose hxnorm))
    rw [show A = L + (A - L) by abel, Matrix.add_mulVec, dotProduct_add]
    linarith
  rw [← mode4StabilityNegativeProjector_finrank hL]
  exact mode4Stability_finrank_le_negativeCount hA hWneg

private theorem mode4Stability_positiveCount_le_positiveCount_of_close
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {L A : Matrix n n ℝ}
    (hL : L.IsHermitian) (hA : A.IsHermitian)
    {gap : ℝ}
    (hgapL : ∀ i, 0 < hL.eigenvalues i → gap ≤ hL.eigenvalues i)
    (hclose : (Fintype.card n : ℝ) * ‖A - L‖ < gap) :
    mode4StabilityPositiveEigenvalueCount hL ≤
      mode4StabilityPositiveEigenvalueCount hA := by
  let W := LinearMap.range (mode4StabilityPositiveProjector hL).mulVecLin
  have hWpos : ∀ x ∈ W, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x) := by
    intro x hxW hx
    have hLgap := mode4StabilityPositiveProjector_form_gap hL hgapL hxW
    have hpert := mode4Stability_abs_form_sub_le (A - L) x
    have hxnorm : 0 < star x ⬝ᵥ x :=
      Matrix.dotProduct_star_self_pos_iff.mpr hx
    have hpert' :
        -gap * (star x ⬝ᵥ x) <
          star x ⬝ᵥ ((A - L) *ᵥ x) := by
      have hnegabs :
          -|star x ⬝ᵥ ((A - L) *ᵥ x)| ≤
            star x ⬝ᵥ ((A - L) *ᵥ x) := neg_abs_le _
      have hneg :
          -gap * (star x ⬝ᵥ x) <
            -|star x ⬝ᵥ ((A - L) *ᵥ x)| := by
        have := neg_lt_neg
          (lt_of_le_of_lt hpert (mul_lt_mul_of_pos_right hclose hxnorm))
        nlinarith
      exact lt_of_lt_of_le hneg hnegabs
    rw [show A = L + (A - L) by abel, Matrix.add_mulVec, dotProduct_add]
    linarith
  rw [← mode4StabilityPositiveProjector_finrank hL]
  exact mode4Stability_finrank_le_positiveCount hA hWpos

private def mode4StabilityGap
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {L : Matrix n n ℝ} (hL : L.IsHermitian) : ℝ :=
  (univ.image fun i => |hL.eigenvalues i|).min'
    ⟨|hL.eigenvalues (Classical.arbitrary n)|,
      mem_image.mpr ⟨Classical.arbitrary n, mem_univ _, rfl⟩⟩

private theorem mode4StabilityGap_pos
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {L : Matrix n n ℝ} (hL : L.IsHermitian) (hdet : L.det ≠ 0) :
    0 < mode4StabilityGap hL := by
  have hne := mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero hL hdet
  have hmem := (univ.image fun i => |hL.eigenvalues i|).min'_mem
    ⟨|hL.eigenvalues (Classical.arbitrary n)|,
      mem_image.mpr ⟨Classical.arbitrary n, mem_univ _, rfl⟩⟩
  obtain ⟨i, -, hi⟩ := mem_image.mp hmem
  unfold mode4StabilityGap
  rw [← hi]
  exact abs_pos.mpr (hne i)

private theorem mode4StabilityGap_le_abs
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {L : Matrix n n ℝ} (hL : L.IsHermitian) (i : n) :
    mode4StabilityGap hL ≤ |hL.eigenvalues i| := by
  exact (univ.image fun j => |hL.eigenvalues j|).min'_le _
    (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

private theorem mode4Stability_neg_add_pos_eq_card
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    mode4HermitianNegativeEigenvalueCount A hA +
      mode4StabilityPositiveEigenvalueCount hA = Fintype.card n := by
  have hne := mode4IsHermitian_eigenvalues_ne_zero_of_det_ne_zero hA hdet
  unfold mode4HermitianNegativeEigenvalueCount
  unfold mode4StabilityPositiveEigenvalueCount
  rw [← card_union_of_disjoint]
  · rw [← card_univ]
    congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact lt_or_gt_of_ne (hne i)
  · rw [Finset.disjoint_left]
    intro i hneg hpos
    simp only [mem_filter, mem_univ, true_and] at hneg hpos
    linarith

private theorem
    mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero_of_pos
    {K : ℕ} (hK : 1 ≤ K)
    (A : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ d, (A d).IsHermitian)
    (L : Matrix (Fin K) (Fin K) ℝ)
    (hL : L.IsHermitian)
    (hlim : Tendsto A atTop (𝓝 L))
    (hdet : L.det ≠ 0) :
    ∀ᶠ d in atTop,
      mode4HermitianNegativeEigenvalueCount (A d) (hA d) =
        mode4HermitianNegativeEigenvalueCount L hL := by
  letI : Nonempty (Fin K) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hK⟩⟩
  let gap := mode4StabilityGap hL
  have hgap : 0 < gap := mode4StabilityGap_pos hL hdet
  have hnegGap : ∀ i, hL.eigenvalues i < 0 → gap ≤ -hL.eigenvalues i := by
    intro i hi
    simpa [abs_of_neg hi] using mode4StabilityGap_le_abs hL i
  have hposGap : ∀ i, 0 < hL.eigenvalues i → gap ≤ hL.eigenvalues i := by
    intro i hi
    simpa [abs_of_pos hi] using mode4StabilityGap_le_abs hL i
  have hdiff : Tendsto (fun d => A d - L) atTop (𝓝 0) := by
    simpa using hlim.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))
  have hscaled :
      Tendsto (fun d => (K : ℝ) * ‖A d - L‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdiff.norm
  have hclose : ∀ᶠ d in atTop, (K : ℝ) * ‖A d - L‖ < gap :=
    (tendsto_order.1 hscaled).2 gap hgap
  have hdetlim : Tendsto (fun d => (A d).det) atTop (𝓝 L.det) :=
    (continuous_id.matrix_det.tendsto L).comp hlim
  have hdetA : ∀ᶠ d in atTop, (A d).det ≠ 0 :=
    hdetlim.eventually_ne hdet
  filter_upwards [hclose, hdetA] with d hdclose hdA
  have hnegLe :
      mode4HermitianNegativeEigenvalueCount L hL ≤
        mode4HermitianNegativeEigenvalueCount (A d) (hA d) :=
    mode4Stability_negativeCount_le_negativeCount_of_close
      hL (hA d) hnegGap (by simpa using hdclose)
  have hposLe :
      mode4StabilityPositiveEigenvalueCount hL ≤
        mode4StabilityPositiveEigenvalueCount (hA d) :=
    mode4Stability_positiveCount_le_positiveCount_of_close
      hL (hA d) hposGap (by simpa using hdclose)
  have hpartitionL := mode4Stability_neg_add_pos_eq_card hL hdet
  have hpartitionA := mode4Stability_neg_add_pos_eq_card (hA d) hdA
  omega

/-- At a nonsingular Hermitian limit, the project negative-eigenvalue count is
eventually constant.  The fixed carrier is written as `Fin K` because this is
the exact surface used by the mode-four finite Schur family.  The empty carrier
is discharged directly; no positive-dimension binder leaks into the public
contract. -/
theorem mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
    {K : ℕ}
    (A : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ d, (A d).IsHermitian)
    (L : Matrix (Fin K) (Fin K) ℝ)
    (hL : L.IsHermitian)
    (hlim : Tendsto A atTop (𝓝 L))
    (hdet : L.det ≠ 0) :
    ∀ᶠ d in atTop,
      mode4HermitianNegativeEigenvalueCount (A d) (hA d) =
        mode4HermitianNegativeEigenvalueCount L hL := by
  by_cases hK0 : K = 0
  · subst K
    simp [mode4HermitianNegativeEigenvalueCount]
  · exact
      mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero_of_pos
        (Nat.one_le_iff_ne_zero.mpr hK0) A hA L hL hlim hdet

private theorem mode4Stability_neg_add_nullity_add_pos_eq_card
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    mode4HermitianNegativeEigenvalueCount A hA +
        Module.finrank ℝ (LinearMap.ker A.mulVecLin) +
        mode4StabilityPositiveEigenvalueCount hA = Fintype.card n := by
  classical
  have hrankNullity := A.mulVecLin.finrank_range_add_finrank_ker
  have hrankA :
      A.rank = (univ.filter fun i => hA.eigenvalues i ≠ 0).card := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hnonzero :
      (univ.filter fun i => hA.eigenvalues i < 0).card +
          (univ.filter fun i => 0 < hA.eigenvalues i).card =
        (univ.filter fun i => hA.eigenvalues i ≠ 0).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (hneg | hpos)
        · exact hneg.ne
        · exact hpos.ne'
      · exact lt_or_gt_of_ne
    · rw [Finset.disjoint_left]
      intro i hneg hpos
      simp only [mem_filter, mem_univ, true_and] at hneg hpos
      linarith
  have hrankNullity' :
      A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
        Fintype.card n := by
    simpa [Matrix.rank] using hrankNullity
  unfold mode4HermitianNegativeEigenvalueCount
  unfold mode4StabilityPositiveEigenvalueCount
  omega

/-- For a convergent sequence of finite real Hermitian matrices, the negative
index is lower semicontinuous, while its possible upward jump is bounded by
the nullity of the limiting matrix.  At a simple singular limit this leaves
exactly the two adjacent inertia values. -/
theorem mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto
    {K : ℕ}
    (A : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ d, (A d).IsHermitian)
    (L : Matrix (Fin K) (Fin K) ℝ)
    (hL : L.IsHermitian)
    (hlim : Tendsto A atTop (𝓝 L)) :
    ∀ᶠ d in atTop,
      mode4HermitianNegativeEigenvalueCount L hL ≤
          mode4HermitianNegativeEigenvalueCount (A d) (hA d) ∧
        mode4HermitianNegativeEigenvalueCount (A d) (hA d) ≤
          mode4HermitianNegativeEigenvalueCount L hL +
            Module.finrank ℝ (LinearMap.ker L.mulVecLin) := by
  classical
  by_cases hK0 : K = 0
  · subst K
    simp [mode4HermitianNegativeEigenvalueCount]
  letI : Nonempty (Fin K) :=
    ⟨⟨0, Nat.pos_of_ne_zero hK0⟩⟩
  by_cases hnonzero : ∃ i, hL.eigenvalues i ≠ 0
  · let S : Finset ℝ :=
      (univ.filter fun i => hL.eigenvalues i ≠ 0).image
        (fun i => |hL.eigenvalues i|)
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hnonzero
      refine ⟨|hL.eigenvalues i|, ?_⟩
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩
    let gap := S.min' hS
    have hgap_mem : gap ∈ S := by
      exact S.min'_mem hS
    have hgap_pos : 0 < gap := by
      obtain ⟨i, hi, heq⟩ := mem_image.mp hgap_mem
      have hine : hL.eigenvalues i ≠ 0 := (mem_filter.mp hi).2
      rw [← heq]
      exact abs_pos.mpr hine
    have hgap_le_abs (i : Fin K) (hi : hL.eigenvalues i ≠ 0) :
        gap ≤ |hL.eigenvalues i| := by
      exact S.min'_le _
        (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩)
    have hnegGap :
        ∀ i, hL.eigenvalues i < 0 → gap ≤ -hL.eigenvalues i := by
      intro i hi
      simpa [abs_of_neg hi] using hgap_le_abs i hi.ne
    have hposGap :
        ∀ i, 0 < hL.eigenvalues i → gap ≤ hL.eigenvalues i := by
      intro i hi
      simpa [abs_of_pos hi] using hgap_le_abs i hi.ne'
    have hdiff : Tendsto (fun d => A d - L) atTop (𝓝 0) := by
      simpa using hlim.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))
    have hscaled :
        Tendsto (fun d => (K : ℝ) * ‖A d - L‖) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hdiff.norm
    have hclose : ∀ᶠ d in atTop, (K : ℝ) * ‖A d - L‖ < gap :=
      (tendsto_order.1 hscaled).2 gap hgap_pos
    filter_upwards [hclose] with d hdclose
    have hnegLe :
        mode4HermitianNegativeEigenvalueCount L hL ≤
          mode4HermitianNegativeEigenvalueCount (A d) (hA d) :=
      mode4Stability_negativeCount_le_negativeCount_of_close
        hL (hA d) hnegGap (by simpa using hdclose)
    have hposLe :
        mode4StabilityPositiveEigenvalueCount hL ≤
          mode4StabilityPositiveEigenvalueCount (hA d) :=
      mode4Stability_positiveCount_le_positiveCount_of_close
        hL (hA d) hposGap (by simpa using hdclose)
    have hpartitionL := mode4Stability_neg_add_nullity_add_pos_eq_card hL
    have hpartitionA :=
      mode4Stability_neg_add_nullity_add_pos_eq_card (hA d)
    constructor
    · exact hnegLe
    · omega
  · have hzero : ∀ i, hL.eigenvalues i = 0 := by
      intro i
      exact not_ne_iff.mp (not_exists.mp hnonzero i)
    have hnegZero :
        mode4HermitianNegativeEigenvalueCount L hL = 0 := by
      unfold mode4HermitianNegativeEigenvalueCount
      simp [hzero]
    have hposZero : mode4StabilityPositiveEigenvalueCount hL = 0 := by
      unfold mode4StabilityPositiveEigenvalueCount
      simp [hzero]
    have hpartitionL := mode4Stability_neg_add_nullity_add_pos_eq_card hL
    have hpartitionL' :
        mode4HermitianNegativeEigenvalueCount L hL +
            Module.finrank ℝ (LinearMap.ker L.mulVecLin) +
            mode4StabilityPositiveEigenvalueCount hL = K := by
      simpa using hpartitionL
    filter_upwards [] with d
    have hcountLe :
        mode4HermitianNegativeEigenvalueCount (A d) (hA d) ≤ K := by
      unfold mode4HermitianNegativeEigenvalueCount
      calc
        (univ.filter fun i => (hA d).eigenvalues i < 0).card ≤ univ.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = K := Fintype.card_fin K
    constructor <;> omega

#print axioms
  mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto

/-!
The following two public interfaces are an independent Mathlib realization of
the subspace form of Sylvester inertia.  The proof architecture was
cross-checked against `Zeta23/LinAlg/Sylvester.lean` (Apache-2.0); no source
code is copied.  They expose exactly the part of the spectral-projector
machinery needed by finite block congruence arguments.
-/

/-- Every subspace on which a real Hermitian form is strictly negative has
dimension at most the number of strictly negative eigenvalues. -/
theorem mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Submodule ℝ (n → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0) :
    Module.finrank ℝ W ≤ mode4HermitianNegativeEigenvalueCount A hA :=
  mode4Stability_finrank_le_negativeCount hA hW

/-- The negative spectral projector supplies a strictly negative subspace
whose dimension is exactly the Hermitian negative-eigenvalue count. -/
theorem mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ W : Submodule ℝ (n → ℝ),
      (∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0) ∧
      Module.finrank ℝ W = mode4HermitianNegativeEigenvalueCount A hA := by
  let W : Submodule ℝ (n → ℝ) :=
    LinearMap.range (mode4StabilityNegativeProjector hA).mulVecLin
  refine ⟨W, ?_, mode4StabilityNegativeProjector_finrank hA⟩
  intro x hxW hx
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Submodule ℝ (n → ℝ)) := by
      rw [← hbot]
      exact hxW
    exact hx (by simpa using hxbot)
  have hcount_pos :
      0 < mode4HermitianNegativeEigenvalueCount A hA := by
    rw [← mode4StabilityNegativeProjector_finrank hA]
    exact Nat.lt_of_succ_le (Submodule.one_le_finrank_iff.mpr hWne)
  let s : Finset n := Finset.univ.filter fun i => hA.eigenvalues i < 0
  have hs : s.Nonempty := by
    rw [← Finset.card_pos]
    simpa [s, mode4HermitianNegativeEigenvalueCount] using hcount_pos
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image s (fun j => -hA.eigenvalues j) hs
  have hineg : hA.eigenvalues i < 0 := by
    exact (Finset.mem_filter.mp hi).2
  have hgap_pos : 0 < -hA.eigenvalues i := neg_pos.mpr hineg
  have hgap :
      ∀ j, hA.eigenvalues j < 0 →
        -hA.eigenvalues i ≤ -hA.eigenvalues j := by
    intro j hj
    exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  have hform := mode4StabilityNegativeProjector_form_gap
    hA hgap hxW
  have hnorm : 0 < star x ⬝ᵥ x :=
    Matrix.dotProduct_star_self_pos_iff.mpr hx
  nlinarith

#print axioms mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn
#print axioms mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount

/- P-STAB-1-SINGULAR-LIMIT.
Stop code: G3_INERTIA_STABILITY_SINGULAR_LIMIT_GUARD_DROPPED.

A singular limit really can change inertia: the one-by-one matrices
`[-1/(d+1)]` all have one negative eigenvalue and converge to the zero matrix,
whose negative count is zero.  This plant is proved below after the main leaf. -/

private def mode4StabilitySingularPlant (d : ℕ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => -(1 / ((d : ℝ) + 1))

private theorem mode4StabilitySingularPlant_isHermitian (d : ℕ) :
    (mode4StabilitySingularPlant d).IsHermitian := by
  ext i j
  simp [mode4StabilitySingularPlant]

private theorem mode4StabilitySingularPlant_count (d : ℕ) :
    mode4HermitianNegativeEigenvalueCount
        (mode4StabilitySingularPlant d)
        (mode4StabilitySingularPlant_isHermitian d) = 1 := by
  let W : Submodule ℝ (Fin 1 → ℝ) := ⊤
  have hneg : ∀ x ∈ W, x ≠ 0 →
      star x ⬝ᵥ (mode4StabilitySingularPlant d *ᵥ x) < 0 := by
    intro x _ hx
    have hx0 : x 0 ≠ 0 := by
      intro hxzero
      apply hx
      funext i
      fin_cases i
      exact hxzero
    have hden : 0 < (d : ℝ) + 1 := by positivity
    have hsq : 0 < (x 0) ^ 2 := sq_pos_of_ne_zero hx0
    simp only [dotProduct, mulVec, mode4StabilitySingularPlant,
      Pi.star_apply, star_id_of_comm, Fin.sum_univ_one]
    have hinv : 0 < 1 / ((d : ℝ) + 1) := one_div_pos.mpr hden
    nlinarith
  have hlower :
      1 ≤ mode4HermitianNegativeEigenvalueCount
        (mode4StabilitySingularPlant d)
        (mode4StabilitySingularPlant_isHermitian d) := by
    simpa [W] using mode4Stability_finrank_le_negativeCount
      (mode4StabilitySingularPlant_isHermitian d) hneg
  have hupper :
      mode4HermitianNegativeEigenvalueCount
        (mode4StabilitySingularPlant d)
        (mode4StabilitySingularPlant_isHermitian d) ≤ 1 := by
    unfold mode4HermitianNegativeEigenvalueCount
    simpa using Finset.card_le_card
      (Finset.filter_subset
        (fun i => (mode4StabilitySingularPlant_isHermitian d).eigenvalues i < 0)
        Finset.univ)
  omega

private theorem mode4StabilityZero_count :
    mode4HermitianNegativeEigenvalueCount
        (0 : Matrix (Fin 1) (Fin 1) ℝ) isHermitian_zero = 0 := by
  let hzero : (0 : Matrix (Fin 1) (Fin 1) ℝ).IsHermitian := isHermitian_zero
  have heigs :
      hzero.eigenvalues = 0 := hzero.eigenvalues_eq_zero_iff.mpr rfl
  unfold mode4HermitianNegativeEigenvalueCount
  change (Finset.univ.filter fun i => hzero.eigenvalues i < 0).card = 0
  simp [heigs]

/-- Required singular-limit plant: without the nonsingularity contract the
conclusion of eventual inertia stability is false, already in dimension one. -/
private theorem singular_limit_counterexample_must_fail_the_nonsingular_contract :
    Tendsto mode4StabilitySingularPlant atTop
        (𝓝 (0 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      (∀ d, mode4HermitianNegativeEigenvalueCount
          (mode4StabilitySingularPlant d)
          (mode4StabilitySingularPlant_isHermitian d) = 1) ∧
      mode4HermitianNegativeEigenvalueCount
          (0 : Matrix (Fin 1) (Fin 1) ℝ) isHermitian_zero = 0 := by
  refine ⟨?_, mode4StabilitySingularPlant_count,
    mode4StabilityZero_count⟩
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  change Tendsto (fun d : ℕ => -(1 / ((d : ℝ) + 1))) atTop (𝓝 0)
  simpa using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg

private theorem mode4StabilityNegOne_count {K : ℕ} :
    mode4HermitianNegativeEigenvalueCount
        (-1 : Matrix (Fin K) (Fin K) ℝ) isHermitian_one.neg = K := by
  let W : Submodule ℝ (Fin K → ℝ) := ⊤
  have hneg : ∀ x ∈ W, x ≠ 0 →
      star x ⬝ᵥ ((-1 : Matrix (Fin K) (Fin K) ℝ) *ᵥ x) < 0 := by
    intro x _ hx
    have hpos :
        0 < star x ⬝ᵥ ((1 : Matrix (Fin K) (Fin K) ℝ) *ᵥ x) :=
      Matrix.PosDef.one.dotProduct_mulVec_pos hx
    simpa only [neg_mulVec, one_mulVec, dotProduct_neg] using
      (neg_lt_zero.mpr hpos)
  have hlower : K ≤ mode4HermitianNegativeEigenvalueCount
      (-1 : Matrix (Fin K) (Fin K) ℝ) isHermitian_one.neg := by
    simpa [W] using mode4Stability_finrank_le_negativeCount
      (A := (-1 : Matrix (Fin K) (Fin K) ℝ)) isHermitian_one.neg hneg
  have hupper : mode4HermitianNegativeEigenvalueCount
      (-1 : Matrix (Fin K) (Fin K) ℝ) isHermitian_one.neg ≤ K := by
    unfold mode4HermitianNegativeEigenvalueCount
    calc
      (Finset.univ.filter fun i : Fin K =>
          ((isHermitian_one :
            (1 : Matrix (Fin K) (Fin K) ℝ).IsHermitian).neg).eigenvalues i < 0).card
          ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = K := by simp
  omega

private theorem mode4StabilityOne_count {K : ℕ} :
    mode4HermitianNegativeEigenvalueCount
        (1 : Matrix (Fin K) (Fin K) ℝ) isHermitian_one = 0 := by
  let W : Submodule ℝ (Fin K → ℝ) := ⊤
  have hpositive : ∀ x ∈ W, x ≠ 0 →
      0 < star x ⬝ᵥ ((1 : Matrix (Fin K) (Fin K) ℝ) *ᵥ x) := by
    intro x _ hx
    exact Matrix.PosDef.one.dotProduct_mulVec_pos hx
  have hposLower : K ≤ mode4StabilityPositiveEigenvalueCount
      (A := (1 : Matrix (Fin K) (Fin K) ℝ)) isHermitian_one := by
    simpa [W] using mode4Stability_finrank_le_positiveCount
      (A := (1 : Matrix (Fin K) (Fin K) ℝ)) isHermitian_one hpositive
  have hpartition : mode4HermitianNegativeEigenvalueCount
        (1 : Matrix (Fin K) (Fin K) ℝ) isHermitian_one +
      mode4StabilityPositiveEigenvalueCount
        (A := (1 : Matrix (Fin K) (Fin K) ℝ)) isHermitian_one = K := by
    simpa only [Fintype.card_fin] using mode4Stability_neg_add_pos_eq_card
      (A := (1 : Matrix (Fin K) (Fin K) ℝ)) isHermitian_one (by simp)
  omega

private def mode4StabilityDetOnlyPlant (d : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if Even d then -1 else 1

private theorem mode4StabilityDetOnlyPlant_isHermitian (d : ℕ) :
    (mode4StabilityDetOnlyPlant d).IsHermitian := by
  unfold mode4StabilityDetOnlyPlant
  split_ifs <;> simp

/- P-STAB-2-DETERMINANT-TENDSTO.
Stop code: G3_INERTIA_STABILITY_MATRIX_TENDSTO_REPLACED_BY_DET. -/
private theorem determinant_tendsto_does_not_replace_matrix_tendsto :
    (∀ d, (mode4StabilityDetOnlyPlant d).det = 1) ∧
      mode4HermitianNegativeEigenvalueCount
          (mode4StabilityDetOnlyPlant 0)
          (mode4StabilityDetOnlyPlant_isHermitian 0) = 2 ∧
      mode4HermitianNegativeEigenvalueCount
          (mode4StabilityDetOnlyPlant 1)
          (mode4StabilityDetOnlyPlant_isHermitian 1) = 0 := by
  constructor
  · intro d
    unfold mode4StabilityDetOnlyPlant
    split_ifs <;> simp [Matrix.det_fin_two]
  constructor
  · simpa [mode4StabilityDetOnlyPlant] using
      (mode4StabilityNegOne_count (K := 2))
  · simpa [mode4StabilityDetOnlyPlant] using
      (mode4StabilityOne_count (K := 2))

private def mode4StabilityTwoNegOnePos : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (fun i => if i = 2 then 1 else -1)

private theorem mode4StabilityTwoNegOnePos_isHermitian :
    mode4StabilityTwoNegOnePos.IsHermitian := by
  unfold mode4StabilityTwoNegOnePos
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)

private theorem mode4StabilityTwoNegOnePos_det :
    mode4StabilityTwoNegOnePos.det = 1 := by
  simp [mode4StabilityTwoNegOnePos, Fin.prod_univ_succ]

private theorem mode4StabilityTwoNegOnePos_count :
    mode4HermitianNegativeEigenvalueCount mode4StabilityTwoNegOnePos
        mode4StabilityTwoNegOnePos_isHermitian = 2 := by
  let ev2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 2
  let Wneg : Submodule ℝ (Fin 3 → ℝ) := LinearMap.ker ev2
  have hev2_surj : Function.Surjective ev2 := by
    intro y
    refine ⟨fun i => if i = 2 then y else 0, ?_⟩
    simp [ev2]
  have hev2_range : LinearMap.range ev2 = ⊤ :=
    LinearMap.range_eq_top.mpr hev2_surj
  have hdimNeg : Module.finrank ℝ Wneg = 2 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker ev2
    rw [hev2_range] at hdim
    simp [Wneg] at hdim ⊢
    omega
  have hneg : ∀ x ∈ Wneg, x ≠ 0 →
      star x ⬝ᵥ (mode4StabilityTwoNegOnePos *ᵥ x) < 0 := by
    intro x hxW hx
    have hx2 : x 2 = 0 := by
      simpa [Wneg, ev2, LinearMap.mem_ker] using hxW
    have hx01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      funext i
      fin_cases i
      · exact h.1
      · exact h.2
      · exact hx2
    have hform :
        star x ⬝ᵥ (mode4StabilityTwoNegOnePos *ᵥ x) =
          -(x 0) ^ 2 - (x 1) ^ 2 := by
      simp [mode4StabilityTwoNegOnePos, dotProduct, mulVec_diagonal,
        Fin.sum_univ_succ, hx2]
      ring
    rw [hform]
    rcases hx01 with hx0 | hx1
    · have := sq_pos_of_ne_zero hx0
      nlinarith [sq_nonneg (x 1)]
    · have := sq_pos_of_ne_zero hx1
      nlinarith [sq_nonneg (x 0)]
  have hnegLower : 2 ≤ mode4HermitianNegativeEigenvalueCount
      mode4StabilityTwoNegOnePos mode4StabilityTwoNegOnePos_isHermitian := by
    simpa [hdimNeg] using mode4Stability_finrank_le_negativeCount
      mode4StabilityTwoNegOnePos_isHermitian hneg

  let e2 : Fin 3 → ℝ := fun i => if i = 2 then 1 else 0
  let Wpos : Submodule ℝ (Fin 3 → ℝ) := ℝ ∙ e2
  have he2 : e2 ≠ 0 := by
    intro h
    have h2 := congrFun h (2 : Fin 3)
    norm_num [e2] at h2
  have hdimPos : Module.finrank ℝ Wpos = 1 := by
    simpa [Wpos] using finrank_span_singleton he2
  have hpositive : ∀ x ∈ Wpos, x ≠ 0 →
      0 < star x ⬝ᵥ (mode4StabilityTwoNegOnePos *ᵥ x) := by
    intro x hxW hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxW
    have ha : a ≠ 0 := by
      intro ha
      apply hx
      simp [ha]
    simpa [mode4StabilityTwoNegOnePos, e2, dotProduct, mulVec_diagonal,
      Fin.sum_univ_succ] using ha
  have hposLower : 1 ≤ mode4StabilityPositiveEigenvalueCount
      mode4StabilityTwoNegOnePos_isHermitian := by
    simpa [hdimPos] using mode4Stability_finrank_le_positiveCount
      mode4StabilityTwoNegOnePos_isHermitian hpositive
  have hpartition :
      mode4HermitianNegativeEigenvalueCount mode4StabilityTwoNegOnePos
          mode4StabilityTwoNegOnePos_isHermitian +
        mode4StabilityPositiveEigenvalueCount
          mode4StabilityTwoNegOnePos_isHermitian = 3 := by
    simpa using mode4Stability_neg_add_pos_eq_card
      mode4StabilityTwoNegOnePos_isHermitian (by
        rw [mode4StabilityTwoNegOnePos_det]
        norm_num)
  omega

/- P-STAB-3-DETERMINANT-SIGN.
Stop code: G3_INERTIA_STABILITY_DET_SIGN_NOT_COUNT. -/
private theorem determinant_sign_does_not_determine_negative_count :
    mode4StabilityTwoNegOnePos.det =
        (1 : Matrix (Fin 3) (Fin 3) ℝ).det ∧
      mode4HermitianNegativeEigenvalueCount mode4StabilityTwoNegOnePos
          mode4StabilityTwoNegOnePos_isHermitian = 2 ∧
      mode4HermitianNegativeEigenvalueCount
          (1 : Matrix (Fin 3) (Fin 3) ℝ) isHermitian_one = 0 := by
  exact ⟨by simp [mode4StabilityTwoNegOnePos_det],
    mode4StabilityTwoNegOnePos_count, mode4StabilityOne_count⟩

private def mode4StabilityNonHermitianRotation :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 1 then -1
    else if i = 1 ∧ j = 0 then 1
    else 0

/- P-STAB-4-HERMITIAN-GUARD.
Stop code: G3_INERTIA_STABILITY_HERMITIAN_GUARD_DROPPED. -/
private theorem nonHermitian_rotation_cannot_supply_the_production_guard :
    ¬ mode4StabilityNonHermitianRotation.IsHermitian := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h.eq
  norm_num [mode4StabilityNonHermitianRotation] at h01

/- P-STAB-5-FIXED-CARRIER.
Stop code: G3_INERTIA_STABILITY_FIXED_CARRIER_DROPPED.
The varying carriers cannot even be uniformly identified with one `Fin K`, so
they cannot instantiate the single fixed-`K` public theorem. -/
private theorem varying_fin_carriers_cannot_be_one_fixed_carrier :
    ¬ ∃ K : ℕ, ∀ d : ℕ, Nonempty (Fin (d + 1) ≃ Fin K) := by
  rintro ⟨K, hK⟩
  obtain ⟨eK⟩ := hK K
  have hcard := Fintype.card_congr eK
  simp only [Fintype.card_fin] at hcard
  omega

#print axioms mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
