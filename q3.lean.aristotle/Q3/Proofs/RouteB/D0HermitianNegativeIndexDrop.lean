/-
Portions copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; see the repository LICENSE and the attribution below.
Modified and specialized for the Q3 mode-four Schur inertia ladder, 2026.
-/

import Q3.Proofs.RouteB.D0Mode4SchurInertiaOrientation
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Strict Hermitian drop forces a negative-index jump

The proof architecture in this file is adapted from the positive-index/Sylvester
subspace method in Anthropic's `zeta-23-lean`, commit `3635e74`, files
`Zeta23/LinAlg/HermitianPosPart.lean` and `Zeta23/LinAlg/Sylvester.lean`
(Apache-2.0).  This is a specialized, rewritten real-Hermitian implementation:
it exposes only the strict-drop inequality needed by the mode-four Schur
ladder.

If `A - B - delta I` is positive semidefinite with `delta > 0`, then the
spectral subspace of `A` on eigenvalues at most zero is a negative-definite
subspace for `B`.  Its dimension is the negative index of `A` plus the
nullity of `A`.  Sylvester's subspace argument therefore gives

`negativeCount A + nullity A <= negativeCount B`.

No continuity of eigenvalue labels, endpoint count, or source-specific root
existence is assumed.
-/

noncomputable section

open Matrix Finset Submodule Unitary

private def d0HermitianSpecMap
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℝ :=
  conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (diagonal (fun i => f (hA.eigenvalues i)))

private theorem d0HermitianSpecMap_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    d0HermitianSpecMap hA (f - g) =
      d0HermitianSpecMap hA f - d0HermitianSpecMap hA g := by
  unfold d0HermitianSpecMap
  rw [← map_sub]
  congr 1
  simp only [← diagonal_sub, Pi.sub_apply]

private theorem d0HermitianSpecMap_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    d0HermitianSpecMap hA (f * g) =
      d0HermitianSpecMap hA f * d0HermitianSpecMap hA g := by
  unfold d0HermitianSpecMap
  rw [← map_mul, diagonal_mul_diagonal]
  rfl

private theorem d0HermitianSpecMap_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    d0HermitianSpecMap hA 0 = 0 := by
  unfold d0HermitianSpecMap
  simp

private theorem d0HermitianSpecMap_id
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    d0HermitianSpecMap hA id = A := by
  unfold d0HermitianSpecMap
  simpa [Function.comp_def] using hA.spectral_theorem.symm

private theorem d0HermitianSpecMap_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (d0HermitianSpecMap hA f).IsHermitian := by
  unfold d0HermitianSpecMap
  rw [conjStarAlgAut_apply]
  refine isHermitian_mul_mul_conjTranspose _ ?_
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)

private theorem d0HermitianSpecMap_rank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (d0HermitianSpecMap hA f).rank =
      (univ.filter fun i => f (hA.eigenvalues i) ≠ 0).card := by
  have hdet : IsUnit (hA.eigenvectorUnitary : Matrix n n ℝ).det :=
    Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  have hdet' : IsUnit (star (hA.eigenvectorUnitary : Matrix n n ℝ)).det := by
    rw [show star (hA.eigenvectorUnitary : Matrix n n ℝ) =
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ from rfl,
      det_conjTranspose]
    exact hdet.star
  unfold d0HermitianSpecMap
  rw [conjStarAlgAut_apply,
    rank_mul_eq_left_of_isUnit_det _ _ hdet',
    rank_mul_eq_right_of_isUnit_det _ _ hdet,
    rank_diagonal]
  simp only [Fintype.card_subtype]

private theorem d0HermitianSpecMap_form
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (x : n → ℝ) :
    star x ⬝ᵥ (d0HermitianSpecMap hA f *ᵥ x) =
      ∑ i, f (hA.eigenvalues i) *
        ‖(star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ x) i‖ ^ 2 := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let c := star U *ᵥ x
  have hsc : star x ᵥ* U = star c := by
    rw [show c = star U *ᵥ x from rfl, star_mulVec,
      show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  unfold d0HermitianSpecMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, dotProduct_mulVec (star x) U, hsc]
  change star c ⬝ᵥ (diagonal (fun i => f (hA.eigenvalues i)) *ᵥ c) = _
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  exact sum_congr rfl fun i _ => by
    simp [c, Real.norm_eq_abs, sq_abs]
    ring

private theorem d0HermitianForm_conj
    {m n : Type*} [Fintype m] [Fintype n]
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) =
      star (B *ᵥ x) ⬝ᵥ (Q *ᵥ (B *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) Bᴴ, ← star_mulVec]

private def d0HermitianPosPart
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  d0HermitianSpecMap hA (·⁺)

private def d0HermitianNegPart
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  d0HermitianSpecMap hA (·⁻)

private theorem d0HermitianPosPart_sub_negPart
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    d0HermitianPosPart hA - d0HermitianNegPart hA = A := by
  unfold d0HermitianPosPart d0HermitianNegPart
  rw [← d0HermitianSpecMap_sub,
    show ((·⁺) - (·⁻) : ℝ → ℝ) = id from
      funext fun x => posPart_sub_negPart x,
    d0HermitianSpecMap_id]

private theorem d0HermitianSpecMap_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (d0HermitianSpecMap hA f).PosSemidef := by
  unfold d0HermitianSpecMap
  rw [conjStarAlgAut_apply]
  refine (Matrix.PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  exact hf

private theorem d0HermitianPosPart_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (d0HermitianPosPart hA).PosSemidef :=
  d0HermitianSpecMap_posSemidef hA fun _ => posPart_nonneg _

private theorem d0HermitianNegPart_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (d0HermitianNegPart hA).PosSemidef :=
  d0HermitianSpecMap_posSemidef hA fun _ => negPart_nonneg _

private theorem d0HermitianNegPart_rank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (d0HermitianNegPart hA).rank =
      mode4HermitianNegativeEigenvalueCount A hA := by
  unfold d0HermitianNegPart mode4HermitianNegativeEigenvalueCount
  rw [d0HermitianSpecMap_rank]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, negPart_eq_zero, not_le]

private def d0HermitianNegDefOn
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (W : Submodule ℝ (n → ℝ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0

private theorem d0Finrank_le_negativeCount_of_negDefOn
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Submodule ℝ (n → ℝ)}
    (hW : d0HermitianNegDefOn A W) :
    Module.finrank ℝ W ≤ mode4HermitianNegativeEigenvalueCount A hA := by
  let L : (n → ℝ) →ₗ[ℝ] (n → ℝ) := (d0HermitianNegPart hA).mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : d0HermitianNegPart hA *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hAform_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) := by
      rw [← d0HermitianPosPart_sub_negPart hA, Matrix.sub_mulVec,
        hxL', sub_zero]
      exact (d0HermitianPosPart_posSemidef hA).dotProduct_mulVec_nonneg x
    exact (not_lt_of_ge hAform_nonneg) (hW x hxW hne')
  calc
    Module.finrank ℝ W =
        Module.finrank ℝ (LinearMap.range (L.domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℝ (LinearMap.range L) := by
      apply Submodule.finrank_mono
      rintro y ⟨⟨x, hxW⟩, rfl⟩
      exact ⟨x, rfl⟩
    _ = (d0HermitianNegPart hA).rank := rfl
    _ = mode4HermitianNegativeEigenvalueCount A hA :=
      d0HermitianNegPart_rank hA

private def d0HermitianNonpositiveProjector
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  d0HermitianSpecMap hA (fun t => if t ≤ 0 then 1 else 0)

private theorem d0HermitianNonpositiveProjector_form_nonpos
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {x : n → ℝ}
    (hx : x ∈ LinearMap.range (d0HermitianNonpositiveProjector hA).mulVecLin) :
    star x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
  obtain ⟨y, rfl⟩ := hx
  change
    star (d0HermitianNonpositiveProjector hA *ᵥ y) ⬝ᵥ
        (A *ᵥ (d0HermitianNonpositiveProjector hA *ᵥ y)) ≤ 0
  let p : ℝ → ℝ := fun t => if t ≤ 0 then 1 else 0
  let P : Matrix n n ℝ := d0HermitianNonpositiveProjector hA
  have hPherm : P.IsHermitian := by
    simpa [P, p, d0HermitianNonpositiveProjector] using
      d0HermitianSpecMap_isHermitian hA p
  have hPAP :
      Pᴴ * A * P =
        d0HermitianSpecMap hA (fun t => if t ≤ 0 then t else 0) := by
    calc
      Pᴴ * A * P = P * A * P := by rw [hPherm.eq]
      _ = d0HermitianSpecMap hA p *
          d0HermitianSpecMap hA id * d0HermitianSpecMap hA p := by
        simp only [P, p, d0HermitianNonpositiveProjector,
          d0HermitianSpecMap_id]
      _ = d0HermitianSpecMap hA ((p * id) * p) := by
        rw [← d0HermitianSpecMap_mul, ← d0HermitianSpecMap_mul]
      _ = d0HermitianSpecMap hA (fun t => if t ≤ 0 then t else 0) := by
        congr 1
        funext t
        simp only [Pi.mul_apply, id_eq, p]
        split_ifs <;> ring
  change star (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) ≤ 0
  rw [← d0HermitianForm_conj A P y, hPAP, d0HermitianSpecMap_form]
  apply sum_nonpos
  intro i _
  split_ifs with hi
  · simpa using mul_nonpos_of_nonpos_of_nonneg hi (sq_nonneg _)
  · simp

private theorem d0HermitianNonpositiveProjector_finrank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Module.finrank ℝ
        (LinearMap.range (d0HermitianNonpositiveProjector hA).mulVecLin) =
      mode4HermitianNegativeEigenvalueCount A hA +
        Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
  classical
  have hrankP :
      Module.finrank ℝ
          (LinearMap.range (d0HermitianNonpositiveProjector hA).mulVecLin) =
        (univ.filter fun i => hA.eigenvalues i ≤ 0).card := by
    change (d0HermitianNonpositiveProjector hA).rank = _
    unfold d0HermitianNonpositiveProjector
    rw [d0HermitianSpecMap_rank]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, ne_eq]
    split_ifs <;> simp_all
  have hnullity :
      Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
        (univ.filter fun i => hA.eigenvalues i = 0).card := by
    have hrankNullity := A.mulVecLin.finrank_range_add_finrank_ker
    have hrankA :
        A.rank = (univ.filter fun i => hA.eigenvalues i ≠ 0).card := by
      rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have hpartition :
        (univ.filter fun i => hA.eigenvalues i ≠ 0).card +
          (univ.filter fun i => hA.eigenvalues i = 0).card =
            Fintype.card n := by
      rw [← card_union_of_disjoint]
      · congr 1
        ext i
        simp only [mem_union, mem_filter, mem_univ, true_and]
        exact iff_true_intro (ne_or_eq _ _)
      · rw [Finset.disjoint_left]
        intro i hne heq
        simp only [mem_filter, mem_univ, true_and] at hne heq
        exact hne heq
    have hrankNullity' :
        A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
          Fintype.card n := by
      simpa [Matrix.rank] using hrankNullity
    omega
  rw [hrankP, hnullity]
  unfold mode4HermitianNegativeEigenvalueCount
  have hsplit :
      (univ.filter fun i => hA.eigenvalues i ≤ 0).card =
        (univ.filter fun i => hA.eigenvalues i < 0).card +
          (univ.filter fun i => hA.eigenvalues i = 0).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and]
      constructor
      · exact lt_or_eq_of_le
      · rintro (hlt | heq)
        · exact hlt.le
        · exact heq.le
    · apply Finset.disjoint_left.mpr
      intro i hineg hizero
      simp only [mem_filter, mem_univ, true_and] at hineg hizero
      linarith
  exact hsplit

/-- A strict positive-semidefinite drop grows the negative index by at least
the nullity of the matrix at the starting parameter. -/
theorem hermitian_negativeCount_add_nullity_le_of_strict_drop
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hdrop : (A - B - delta • (1 : Matrix n n ℝ)).PosSemidef) :
    mode4HermitianNegativeEigenvalueCount A hA +
        Module.finrank ℝ (LinearMap.ker A.mulVecLin) ≤
      mode4HermitianNegativeEigenvalueCount B hB := by
  let W := LinearMap.range (d0HermitianNonpositiveProjector hA).mulVecLin
  have hWneg : d0HermitianNegDefOn B W := by
    intro x hxW hx
    have hAnonpos : star x ⬝ᵥ (A *ᵥ x) ≤ 0 :=
      d0HermitianNonpositiveProjector_form_nonpos hA hxW
    have hdropform := hdrop.dotProduct_mulVec_nonneg x
    have hxnorm : 0 < star x ⬝ᵥ x :=
      Matrix.dotProduct_star_self_pos_iff.mpr hx
    have hineq :
        delta * (star x ⬝ᵥ x) ≤
          star x ⬝ᵥ (A *ᵥ x) - star x ⬝ᵥ (B *ᵥ x) := by
      simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul] using hdropform
    nlinarith
  calc
    mode4HermitianNegativeEigenvalueCount A hA +
          Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
        Module.finrank ℝ W :=
      (d0HermitianNonpositiveProjector_finrank hA).symm
    _ ≤ mode4HermitianNegativeEigenvalueCount B hB :=
      d0Finrank_le_negativeCount_of_negDefOn hB hWneg

#print axioms hermitian_negativeCount_add_nullity_le_of_strict_drop
