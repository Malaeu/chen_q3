import Q3.Proofs.RouteB.D0Mode4DLMFFullFiniteSpectrumCrosswalk
import Q3.Proofs.RouteB.D0Mode4HermitianNegativeCountStability
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Classical even carrier from the finite DLMF family

This file materializes the source-faithful carrier selected by the Goal 058
G3 source audit: the zero-based classical even value is the infimum of the
already kernel-checked finite DLMF eigenvalue family at the same fixed index.

The literal coefficients give a depth-independent lower bound by Gershgorin,
so the infimum is finite.  A self-contained inertia proof supplies Cauchy
interlacing for the literal principal truncations, hence antitonicity in depth
and convergence to the carrier.  This does not identify that carrier with a
separately postulated PSWF eigenvalue, and it supplies no endpoint count,
Schur count, indexed eigenfunction, or semiclassical separator.
-/

noncomputable section

open Matrix Finset
open Polynomial

private theorem mode4Roots_sub_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (t : ℝ) :
    (A - Matrix.scalar n t).charpoly.roots =
      Multiset.map (fun i => (hA.eigenvalues i - t : ℝ)) Finset.univ.val := by
  rw [Matrix.charpoly_sub_scalar, hA.charpoly_eq]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Polynomial.prod_comp]
  have hpoly :
      (∏ i, (X - C (hA.eigenvalues i)).comp (X + C t)) =
        ∏ i, (X - C (hA.eigenvalues i - t)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [sub_comp, X_comp, C_comp]
    rw [map_sub]
    ring
  rw [hpoly]
  rw [roots_prod]
  · simp only [roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ => X_sub_C_ne_zero _

private theorem mode4Roots_sub_scalar_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (t : ℝ) :
    (A - Matrix.scalar n t).charpoly.roots =
      Multiset.map (fun i => hA.eigenvalues₀ i - t) Finset.univ.val := by
  have heigs :
      Multiset.map hA.eigenvalues Finset.univ.val =
        Multiset.map hA.eigenvalues₀ Finset.univ.val := by
    calc
      Multiset.map hA.eigenvalues Finset.univ.val = A.charpoly.roots := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq, Function.comp_apply] using
          hA.roots_charpoly_eq_eigenvalues.symm
      _ = Multiset.map hA.eigenvalues₀ Finset.univ.val := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq, Function.comp_apply] using
          hA.roots_charpoly_eq_eigenvalues₀
  have hshift := congrArg (Multiset.map fun x : ℝ => x - t) heigs
  rw [Multiset.map_map, Multiset.map_map] at hshift
  exact (mode4Roots_sub_scalar A hA t).trans (by
    simpa only [Function.comp_apply] using hshift)

private theorem mode4NegativeCount_sub_scalar_eq_filter_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (t : ℝ) :
    let hB : (A - Matrix.scalar n t).IsHermitian := by
      exact hA.sub
        (isHermitian_diagonal_of_self_adjoint _ (funext fun _ => star_trivial t))
    mode4HermitianNegativeEigenvalueCount (A - Matrix.scalar n t) hB =
      (Finset.univ.filter fun i => hA.eigenvalues₀ i < t).card := by
  let hB : (A - Matrix.scalar n t).IsHermitian := by
    exact hA.sub
      (isHermitian_diagonal_of_self_adjoint _ (funext fun _ => star_trivial t))
  have heigs :
      Multiset.map hB.eigenvalues Finset.univ.val =
        Multiset.map (fun i => hA.eigenvalues₀ i - t) Finset.univ.val := by
    calc
      Multiset.map hB.eigenvalues Finset.univ.val =
          (A - Matrix.scalar n t).charpoly.roots := by
            simpa only [RCLike.ofReal_real_eq_id, id_eq,
              Function.comp_apply] using hB.roots_charpoly_eq_eigenvalues.symm
      _ = Multiset.map (fun i => hA.eigenvalues₀ i - t) Finset.univ.val :=
        mode4Roots_sub_scalar_zero A hA t
  have hc := congrArg (Multiset.countP (fun x : ℝ => x < 0)) heigs
  unfold mode4HermitianNegativeEigenvalueCount
  simpa only [Multiset.countP_map, Finset.filter_val, sub_lt_zero] using hc

private theorem mode4Card_filter_lt_ge_succ_of_antitone
    {d : ℕ} (f : Fin d → ℝ) (hf : Antitone f)
    (p : Fin d) (t : ℝ) (hpt : f p.rev < t) :
    p.val + 1 ≤ (Finset.univ.filter fun i => f i < t).card := by
  have hsub : Finset.Ici p.rev ⊆ Finset.univ.filter (fun i => f i < t) := by
    intro i hi
    rw [Finset.mem_Ici] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt (hf hi) hpt⟩
  calc
    p.val + 1 = (Finset.Ici p.rev).card := by
      rw [Fin.card_Ici]
      simp only [Fin.val_rev]
      omega
    _ ≤ (Finset.univ.filter fun i => f i < t).card := Finset.card_le_card hsub

private theorem mode4Card_filter_lt_le_of_antitone
    {d : ℕ} (f : Fin d → ℝ) (hf : Antitone f)
    (p : Fin d) (t : ℝ) (htp : t < f p.rev) :
    (Finset.univ.filter fun i => f i < t).card ≤ p.val := by
  have hsub : Finset.univ.filter (fun i => f i < t) ⊆ Finset.Ioi p.rev := by
    intro i hi
    have hit := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_Ioi]
    by_contra hnot
    have hle : i ≤ p.rev := le_of_not_gt hnot
    have hmono := hf hle
    linarith
  calc
    (Finset.univ.filter fun i => f i < t).card ≤ (Finset.Ioi p.rev).card :=
      Finset.card_le_card hsub
    _ = p.val := by
      rw [Fin.card_Ioi]
      simp only [Fin.val_rev]
      omega

private theorem mode4Block_form_conj_local
    {m n : Type*} [Fintype m] [Fintype n]
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) =
      star (B *ᵥ x) ⬝ᵥ (Q *ᵥ (B *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) Bᴴ, ← star_mulVec]

private theorem mode4NegativeCount_conj_le_local
    {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {Q : Matrix m m ℝ} (hQ : Q.IsHermitian) (B : Matrix m n ℝ) :
    mode4HermitianNegativeEigenvalueCount
        (Bᴴ * Q * B) (isHermitian_conjTranspose_mul_mul B hQ) ≤
      mode4HermitianNegativeEigenvalueCount Q hQ := by
  let M : Matrix n n ℝ := Bᴴ * Q * B
  let hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  obtain ⟨W, hWneg, hWdim⟩ :=
    mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount hM
  let LB : (n → ℝ) →ₗ[ℝ] (m → ℝ) := B.mulVecLin
  have hinj : Function.Injective (LB.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : B *ᵥ x = 0 := hxL
    simp only [Submodule.mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hneg := hWneg x hxW hne'
    change star x ⬝ᵥ ((Bᴴ * Q * B) *ᵥ x) < 0 at hneg
    rw [mode4Block_form_conj_local Q B x, hxL'] at hneg
    simp at hneg
  have hnegImage :
      ∀ y ∈ LinearMap.range (LB.domRestrict W), y ≠ 0 →
        star y ⬝ᵥ (Q *ᵥ y) < 0 := by
    rintro _ ⟨⟨x, hxW⟩, rfl⟩ hne
    simp only [LinearMap.domRestrict_apply, LB, mulVecLin_apply] at *
    have hxne : x ≠ 0 := by
      rintro rfl
      apply hne
      simp
    rw [← mode4Block_form_conj_local Q B x]
    exact hWneg x hxW hxne
  calc
    mode4HermitianNegativeEigenvalueCount
        (Bᴴ * Q * B) (isHermitian_conjTranspose_mul_mul B hQ) =
        Module.finrank ℝ W := by simpa [M, hM] using hWdim.symm
    _ = Module.finrank ℝ (LinearMap.range (LB.domRestrict W)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ mode4HermitianNegativeEigenvalueCount Q hQ :=
      mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn hQ hnegImage

private theorem mode4NegativeCount_eq_of_matrix_eq_local
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) :
    mode4HermitianNegativeEigenvalueCount A hA =
      mode4HermitianNegativeEigenvalueCount B hB := by
  subst B
  rfl

private theorem mode4NegativeCount_eq_of_charpoly_eq_local
    {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hpoly : A.charpoly = B.charpoly) :
    mode4HermitianNegativeEigenvalueCount A hA =
      mode4HermitianNegativeEigenvalueCount B hB := by
  have hroots :
      Multiset.map hA.eigenvalues Finset.univ.val =
        Multiset.map hB.eigenvalues Finset.univ.val := by
    calc
      Multiset.map hA.eigenvalues Finset.univ.val = A.charpoly.roots := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq,
          Function.comp_apply] using hA.roots_charpoly_eq_eigenvalues.symm
      _ = B.charpoly.roots := congrArg Polynomial.roots hpoly
      _ = Multiset.map hB.eigenvalues Finset.univ.val := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq,
          Function.comp_apply] using hB.roots_charpoly_eq_eigenvalues
  have hcount := congrArg (Multiset.countP fun x : ℝ => x < 0) hroots
  unfold mode4HermitianNegativeEigenvalueCount
  simpa only [Multiset.countP_map, Finset.filter_val] using hcount

private def mode4CastSuccEmbedding (d : ℕ) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun i j => if i = j.castSucc then 1 else 0

private theorem mode4CastSuccEmbedding_conj_apply
    {d : ℕ} (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (i j : Fin d) :
    ((mode4CastSuccEmbedding d)ᴴ * Q * mode4CastSuccEmbedding d) i j =
      Q i.castSucc j.castSucc := by
  simp [mode4CastSuccEmbedding, Matrix.mul_apply]

private theorem mode4ForwardHermitian_sub_scalar_conj_castSucc
    (G t : ℝ) (d : ℕ) :
    (mode4CastSuccEmbedding d)ᴴ *
        (mode4ForwardHermitianFiniteMatrix G 0 (d + 1) -
          Matrix.scalar (Fin (d + 1)) t) *
        mode4CastSuccEmbedding d =
      mode4ForwardHermitianFiniteMatrix G 0 d - Matrix.scalar (Fin d) t := by
  ext i j
  rw [mode4CastSuccEmbedding_conj_apply]
  by_cases h : i = j
  · subst j
    simp [mode4ForwardHermitianFiniteMatrix, Matrix.scalar]
  · have hcast : i.castSucc ≠ j.castSucc := fun hij =>
      h (Fin.ext (by simpa using congrArg Fin.val hij))
    simp [mode4ForwardHermitianFiniteMatrix, Matrix.scalar, h, hcast]

private theorem mode4JacobiCenter_zero_ge_neg_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    -G ≤ mode4JacobiCenter G 0 q := by
  cases q with
  | zero =>
      norm_num [mode4JacobiCenter, mode4JacobiIndex]
      linarith
  | succ q =>
      have hq : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
      have hden :
          0 < (2 * (2 * ((q + 1 : ℕ) : ℝ)) - 1) *
            (2 * (2 * ((q + 1 : ℕ) : ℝ)) + 3) := by
        exact mul_pos (by nlinarith) (by nlinarith)
      have hratio :
          2 *
                ((2 * ((q + 1 : ℕ) : ℝ)) *
                    (2 * ((q + 1 : ℕ) : ℝ) + 1) - 1) /
              ((2 * (2 * ((q + 1 : ℕ) : ℝ)) - 1) *
                (2 * (2 * ((q + 1 : ℕ) : ℝ)) + 3)) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hratio hG.le
      have hterm :
          2 * G *
                ((2 * ((q + 1 : ℕ) : ℝ)) *
                    (2 * ((q + 1 : ℕ) : ℝ) + 1) - 1) /
              ((2 * (2 * ((q + 1 : ℕ) : ℝ)) - 1) *
                (2 * (2 * ((q + 1 : ℕ) : ℝ)) + 3)) ≤ G := by
        calc
          _ = G *
              (2 *
                ((2 * ((q + 1 : ℕ) : ℝ)) *
                    (2 * ((q + 1 : ℕ) : ℝ) + 1) - 1) /
              ((2 * (2 * ((q + 1 : ℕ) : ℝ)) - 1) *
                (2 * (2 * ((q + 1 : ℕ) : ℝ)) + 3))) := by ring
          _ ≤ G := by simpa using hmul
      unfold mode4JacobiCenter mode4JacobiIndex
      norm_num at hterm ⊢
      nlinarith

private theorem mode4JacobiLower_succ_pos_all
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 < mode4JacobiLower G (q + 1) := by
  have hq : (0 : ℝ) ≤ q := by positivity
  unfold mode4JacobiLower mode4JacobiIndex
  apply div_pos
  · exact mul_pos (mul_pos hG (by norm_num; linarith)) (by positivity)
  · exact mul_pos (by norm_num; linarith) (by norm_num; linarith)

private theorem mode4JacobiLower_succ_le_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiLower G (q + 1) ≤ G := by
  have hq : (0 : ℝ) ≤ q := by positivity
  have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
  have hden :
      0 < (2 * (2 * (((q + 1 : ℕ) : ℝ))) - 3) *
        (2 * (2 * (((q + 1 : ℕ) : ℝ))) - 1) := by
    exact mul_pos (by norm_num; linarith) (by norm_num; linarith)
  have hleft : 0 ≤ 3 * (2 * (((q + 1 : ℕ) : ℝ))) - 1 := by
    nlinarith
  have hright : 0 ≤ 2 * (((q + 1 : ℕ) : ℝ)) - 2 := by
    nlinarith
  have hprod :
      0 ≤ (3 * (2 * (((q + 1 : ℕ) : ℝ))) - 1) *
        (2 * (((q + 1 : ℕ) : ℝ)) - 2) :=
    mul_nonneg hleft hright
  unfold mode4JacobiLower mode4JacobiIndex
  rw [div_le_iff₀ hden]
  nlinarith

private theorem mode4JacobiSymmetricOff_le_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiSymmetricOff G q ≤ G := by
  have hL0 : 0 ≤ mode4JacobiLower G (q + 1) :=
    (mode4JacobiLower_succ_pos_all G q hG).le
  have hU0 : 0 ≤ mode4JacobiUpper G q :=
    (mode4JacobiUpper_pos G q hG).le
  have hL := mode4JacobiLower_succ_le_G G q hG
  have hUquarter := mode4JacobiUpper_le_one_quarter_mul_G G q hG
  have hU : mode4JacobiUpper G q ≤ G := by nlinarith
  have hprod :
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤ G ^ 2 := by
    calc
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤ G * G :=
        mul_le_mul hL hU hU0 hG.le
      _ = G ^ 2 := by ring
  unfold mode4JacobiSymmetricOff
  exact (Real.sqrt_le_left hG.le).2 hprod

private theorem mode4ForwardHermitianFiniteMatrix_row_radius_le_two_mul_G
    (G : ℝ) (d : ℕ) (i : Fin d) (hG : 0 < G) :
    (∑ j ∈ Finset.univ.erase i,
        ‖mode4ForwardHermitianFiniteMatrix G 0 d i j‖) ≤ 2 * G := by
  let s : Finset (Fin d) :=
    (Finset.univ.erase i).filter fun j =>
      j.val = i.val + 1 ∨ i.val = j.val + 1
  have hs_subset : s ⊆ Finset.univ.erase i := Finset.filter_subset _ _
  have hsum :
      (∑ j ∈ Finset.univ.erase i,
          ‖mode4ForwardHermitianFiniteMatrix G 0 d i j‖) =
        ∑ j ∈ s, ‖mode4ForwardHermitianFiniteMatrix G 0 d i j‖ := by
    symm
    apply Finset.sum_subset hs_subset
    intro j hj hjs
    have hj_erase := hj
    simp only [Finset.mem_erase] at hj_erase
    have hne : i ≠ j := Ne.symm hj_erase.1
    have hnot : ¬(j.val = i.val + 1 ∨ i.val = j.val + 1) := by
      intro hadj
      apply hjs
      exact Finset.mem_filter.mpr ⟨hj, hadj⟩
    simp only [not_or] at hnot
    simp [mode4ForwardHermitianFiniteMatrix, hne, hnot.1, hnot.2]
  let code : {j // j ∈ s} → Fin 2 := fun j =>
    if j.1.val < i.val then 0 else 1
  have hcode : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have ha_adj : a.1.val = i.val + 1 ∨ i.val = a.1.val + 1 :=
      (Finset.mem_filter.mp a.2).2
    have hb_adj : b.1.val = i.val + 1 ∨ i.val = b.1.val + 1 :=
      (Finset.mem_filter.mp b.2).2
    by_cases ha : a.1.val < i.val <;>
      by_cases hb : b.1.val < i.val
    · rcases ha_adj with ha_adj | ha_adj <;>
        rcases hb_adj with hb_adj | hb_adj <;> omega
    · have haFin : a.1 < i := ha
      have hbFin : ¬b.1 < i := hb
      have hac : code a = 0 := by simp [code, haFin]
      have hbc : code b = 1 := by simp [code, hbFin]
      rw [hac, hbc] at hab
      omega
    · have haFin : ¬a.1 < i := ha
      have hbFin : b.1 < i := hb
      have hac : code a = 1 := by simp [code, haFin]
      have hbc : code b = 0 := by simp [code, hbFin]
      rw [hac, hbc] at hab
      omega
    · rcases ha_adj with ha_adj | ha_adj <;>
        rcases hb_adj with hb_adj | hb_adj <;> omega
  have hcard : s.card ≤ 2 := by
    simpa using Fintype.card_le_of_injective code hcode
  have hentry :
      ∀ j ∈ s, ‖mode4ForwardHermitianFiniteMatrix G 0 d i j‖ ≤ G := by
    intro j hj
    have hj_erase := (Finset.mem_filter.mp hj).1
    have hne : i ≠ j := Ne.symm (Finset.mem_erase.mp hj_erase).1
    have hadj := (Finset.mem_filter.mp hj).2
    have hoff0 : 0 ≤ mode4JacobiSymmetricOff G i.val := by
      unfold mode4JacobiSymmetricOff
      positivity
    rcases hadj with hright | hleft
    · have hoff := mode4JacobiSymmetricOff_le_G G i.val hG
      simp [mode4ForwardHermitianFiniteMatrix, hne, hright,
        Real.norm_eq_abs, abs_of_nonneg hoff0, hoff]
    · have hnotshift : ¬j.val = j.val + 1 + 1 := by omega
      have hoff0' : 0 ≤ mode4JacobiSymmetricOff G j.val := by
        unfold mode4JacobiSymmetricOff
        positivity
      have hoff := mode4JacobiSymmetricOff_le_G G j.val hG
      simp [mode4ForwardHermitianFiniteMatrix, hne, hnotshift, hleft,
        Real.norm_eq_abs, abs_of_nonneg hoff0', hoff]
  rw [hsum]
  calc
    (∑ j ∈ s, ‖mode4ForwardHermitianFiniteMatrix G 0 d i j‖) ≤
        ∑ _j ∈ s, G := Finset.sum_le_sum hentry
    _ = (s.card : ℝ) * G := by simp
    _ ≤ 2 * G := by
      have hcardR : (s.card : ℝ) ≤ 2 := by exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hcardR hG.le

/-- Every finite even DLMF eigenvalue is bounded below independently of the
truncation depth.  The constant is intentionally crude; only uniform
boundedness is needed for the carrier. -/
theorem mode4DLMFEvenFiniteEigenvalue_ge_neg_three_mul_G
    (G : ℝ) (d : ℕ) (p : Fin d) (hG : 0 < G) :
    -3 * G ≤ mode4DLMFEvenFiniteEigenvalue G d p := by
  let A : Matrix (Fin d) (Fin d) ℝ :=
    mode4ForwardHermitianFiniteMatrix G 0 d
  let hA : A.IsHermitian := mode4ForwardHermitianFiniteMatrix_isHermitian G 0 d
  let k : Fin (Fintype.card (Fin d)) :=
    Fin.cast (Fintype.card_fin d).symm p.rev
  let j : Fin d :=
    (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin d)))) k
  have hmu :
      hA.eigenvalues j = mode4DLMFEvenFiniteEigenvalue G d p := by
    simp [j, k, mode4DLMFEvenFiniteEigenvalue,
      Matrix.IsHermitian.eigenvalues]
  let v : Fin d → ℝ := hA.eigenvectorBasis j
  have hvec_ne : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2
      (hA.eigenvectorBasis.orthonormal.ne_zero j)
  have hvec : Module.End.HasEigenvector (Matrix.toLin' A)
      (mode4DLMFEvenFiniteEigenvalue G d p) v := by
    refine ⟨?_, hvec_ne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [← hmu]
    simpa [v] using hA.mulVec_eigenvectorBasis j
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A)
      (mode4DLMFEvenFiniteEigenvalue G d p) :=
    Module.End.hasEigenvalue_of_hasEigenvector hvec
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  have hi' :
      |mode4DLMFEvenFiniteEigenvalue G d p - A i i| ≤
        ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hi
  have hdiff :
      A i i - mode4DLMFEvenFiniteEigenvalue G d p ≤
        ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
    calc
      A i i - mode4DLMFEvenFiniteEigenvalue G d p ≤
          |A i i - mode4DLMFEvenFiniteEigenvalue G d p| := le_abs_self _
      _ = |mode4DLMFEvenFiniteEigenvalue G d p - A i i| := abs_sub_comm _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := hi'
  have hcenter : -G ≤ A i i := by
    simpa [A, mode4ForwardHermitianFiniteMatrix] using
      mode4JacobiCenter_zero_ge_neg_G G i.val hG
  have hradius :
      (∑ j ∈ Finset.univ.erase i, ‖A i j‖) ≤ 2 * G := by
    simpa [A] using
      mode4ForwardHermitianFiniteMatrix_row_radius_le_two_mul_G G d i hG
  linarith

/-- Cauchy interlacing for one literal finite-depth extension: the same
zero-based ascending eigenvalue cannot increase when the next source
coordinate is appended. -/
theorem mode4DLMFEvenFiniteEigenvalue_succ_le
    (G : ℝ) (d : ℕ) (p : Fin d) :
    mode4DLMFEvenFiniteEigenvalue G (d + 1) p.castSucc ≤
      mode4DLMFEvenFiniteEigenvalue G d p := by
  by_contra hle
  have hlt : mode4DLMFEvenFiniteEigenvalue G d p <
      mode4DLMFEvenFiniteEigenvalue G (d + 1) p.castSucc := lt_of_not_ge hle
  let t : ℝ :=
    (mode4DLMFEvenFiniteEigenvalue G d p +
      mode4DLMFEvenFiniteEigenvalue G (d + 1) p.castSucc) / 2
  have hsmall_t : mode4DLMFEvenFiniteEigenvalue G d p < t := by
    dsimp [t]
    linarith
  have ht_big : t < mode4DLMFEvenFiniteEigenvalue G (d + 1) p.castSucc := by
    dsimp [t]
    linarith
  let As := mode4ForwardHermitianFiniteMatrix G 0 d
  let Ab := mode4ForwardHermitianFiniteMatrix G 0 (d + 1)
  let hs : As.IsHermitian := mode4ForwardHermitianFiniteMatrix_isHermitian G 0 d
  let hb : Ab.IsHermitian := mode4ForwardHermitianFiniteMatrix_isHermitian G 0 (d + 1)
  let hQs : (As - Matrix.scalar (Fin d) t).IsHermitian := by
    exact hs.sub
      (isHermitian_diagonal_of_self_adjoint _ (funext fun _ => star_trivial t))
  let hQb : (Ab - Matrix.scalar (Fin (d + 1)) t).IsHermitian := by
    exact hb.sub
      (isHermitian_diagonal_of_self_adjoint _ (funext fun _ => star_trivial t))
  have hcount :
      mode4HermitianNegativeEigenvalueCount
          (As - Matrix.scalar (Fin d) t) hQs ≤
        mode4HermitianNegativeEigenvalueCount
          (Ab - Matrix.scalar (Fin (d + 1)) t) hQb := by
    have hraw := mode4NegativeCount_conj_le_local hQb (mode4CastSuccEmbedding d)
    have hmat :
        (mode4CastSuccEmbedding d)ᴴ *
            (Ab - Matrix.scalar (Fin (d + 1)) t) * mode4CastSuccEmbedding d =
          As - Matrix.scalar (Fin d) t := by
      simpa [As, Ab] using
        mode4ForwardHermitian_sub_scalar_conj_castSucc G t d
    have htransport := mode4NegativeCount_eq_of_matrix_eq_local
      (isHermitian_conjTranspose_mul_mul (mode4CastSuccEmbedding d) hQb) hQs hmat
    exact htransport.symm.trans_le hraw
  have hcount' :
      (Finset.univ.filter fun i => hs.eigenvalues₀ i < t).card ≤
        (Finset.univ.filter fun i => hb.eigenvalues₀ i < t).card := by
    have hsCount :
        mode4HermitianNegativeEigenvalueCount
            (As - Matrix.scalar (Fin d) t) hQs =
          (Finset.univ.filter fun i => hs.eigenvalues₀ i < t).card := by
      simpa using mode4NegativeCount_sub_scalar_eq_filter_zero As hs t
    have hbCount :
        mode4HermitianNegativeEigenvalueCount
            (Ab - Matrix.scalar (Fin (d + 1)) t) hQb =
          (Finset.univ.filter fun i => hb.eigenvalues₀ i < t).card := by
      simpa using mode4NegativeCount_sub_scalar_eq_filter_zero Ab hb t
    exact hsCount ▸ hbCount ▸ hcount
  let ps : Fin (Fintype.card (Fin d)) :=
    (Fin.cast (Fintype.card_fin d).symm p.rev).rev
  let pb : Fin (Fintype.card (Fin (d + 1))) :=
    (Fin.cast (Fintype.card_fin (d + 1)).symm p.castSucc.rev).rev
  have hsmall_t' : hs.eigenvalues₀ ps.rev < t := by
    simpa [mode4DLMFEvenFiniteEigenvalue, As, hs, ps] using hsmall_t
  have ht_big' : t < hb.eigenvalues₀ pb.rev := by
    simpa [mode4DLMFEvenFiniteEigenvalue, Ab, hb, pb] using ht_big
  have hlower := mode4Card_filter_lt_ge_succ_of_antitone
    hs.eigenvalues₀ hs.eigenvalues₀_antitone ps t hsmall_t'
  have hupper := mode4Card_filter_lt_le_of_antitone
    hb.eigenvalues₀ hb.eigenvalues₀_antitone pb t ht_big'
  have hps : ps.val = p.val := by
    dsimp [ps]
    simp only [Fintype.card_fin]
    have hp := p.isLt
    omega
  have hpb : pb.val = p.val := by
    dsimp [pb]
    simp only [Fintype.card_fin]
    have hp := p.isLt
    omega
  rw [hps] at hlower
  rw [hpb] at hupper
  omega

/-- Fixed-index finite DLMF eigenvalues are antitone in the truncation depth.
This is the exact finite H1 seam used by the carrier limit below. -/
theorem mode4DLMFEvenFiniteEigenvalue_antitone_in_depth
    (G : ℝ) (p : ℕ) :
    Antitone (fun d : {d : ℕ // p < d} =>
      mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩) := by
  let f : ℕ → ℝ := fun d =>
    if h : p < d then mode4DLMFEvenFiniteEigenvalue G d ⟨p, h⟩ else 0
  have hstep : ∀ d ≥ p + 1, f (d + 1) ≤ f d := by
    intro d hd
    have hpd : p < d := by omega
    have hpds : p < d + 1 := by omega
    simpa [f, hpd, hpds] using
      mode4DLMFEvenFiniteEigenvalue_succ_le G d (⟨p, hpd⟩ : Fin d)
  have hanti : AntitoneOn f {d | p + 1 ≤ d} :=
    antitoneOn_nat_Ici_of_succ_le hstep
  intro a b hab
  have ha : p + 1 ≤ a.1 := by omega
  have hb : p + 1 ≤ b.1 := by omega
  have h := hanti ha hb hab
  simpa [f, a.2, b.2] using h

/-- Zero-based classical even spectral carrier.  DLMF's one-based selector is
`p + 1`, corresponding to even degree `2 * p`. -/
noncomputable def mode4ClassicalEvenEigenvalue
    (G : ℝ) (p : ℕ) : ℝ :=
  ⨅ d : {d : ℕ // p < d},
    mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩

/-- The fixed-index finite DLMF family is uniformly bounded below. -/
theorem mode4DLMFEvenFiniteEigenvalue_bddBelow
    (G : ℝ) (p : ℕ) (hG : 0 < G) :
    BddBelow (Set.range fun d : {d : ℕ // p < d} =>
      mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩) := by
  refine ⟨-3 * G, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact mode4DLMFEvenFiniteEigenvalue_ge_neg_three_mul_G
    G d.1 ⟨p, d.2⟩ hG

/-- The classical carrier inherits the same finite lower bound. -/
theorem mode4ClassicalEvenEigenvalue_ge_neg_three_mul_G
    (G : ℝ) (p : ℕ) (hG : 0 < G) :
    -3 * G ≤ mode4ClassicalEvenEigenvalue G p := by
  letI : Nonempty {d : ℕ // p < d} := ⟨⟨p + 1, Nat.lt_succ_self p⟩⟩
  unfold mode4ClassicalEvenEigenvalue
  apply le_ciInf
  intro d
  exact mode4DLMFEvenFiniteEigenvalue_ge_neg_three_mul_G
    G d.1 ⟨p, d.2⟩ hG

/-- Generic monotone-convergence receiver retained for downstream reuse. -/
theorem mode4ClassicalEvenEigenvalue_tendsto_of_antitone
    (G : ℝ) (p : ℕ) (hG : 0 < G)
    (hanti : Antitone fun d : {d : ℕ // p < d} =>
      mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩) :
    Filter.Tendsto
      (fun d : {d : ℕ // p < d} =>
        mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩)
      Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G p)) := by
  exact tendsto_atTop_ciInf hanti
    (mode4DLMFEvenFiniteEigenvalue_bddBelow G p hG)

/-- The literal fixed-index finite DLMF eigenvalues converge to the carrier
defined above.  Interlacing and the uniform lower bound are both proved in
this file; no external limit premise is assumed. -/
theorem mode4ClassicalEvenEigenvalue_tendsto
    (G : ℝ) (p : ℕ) (hG : 0 < G) :
    Filter.Tendsto
      (fun d : {d : ℕ // p < d} =>
        mode4DLMFEvenFiniteEigenvalue G d.1 ⟨p, d.2⟩)
      Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G p)) := by
  exact mode4ClassicalEvenEigenvalue_tendsto_of_antitone G p hG
    (mode4DLMFEvenFiniteEigenvalue_antitone_in_depth G p)

/-- The inertia count of the literal scalar-shifted finite matrix is exactly
the number of zero-based finite DLMF levels below the shift.  This is the
finite H4 bridge; it contains no limiting or endpoint-count assertion. -/
theorem mode4ForwardHermitianFiniteMatrix_negativeCount_eq_finiteCount
    (G Λ : ℝ) (d : ℕ) :
    let hAΛ := mode4ForwardHermitianFiniteMatrix_isHermitian G Λ d
    mode4HermitianNegativeEigenvalueCount
        (mode4ForwardHermitianFiniteMatrix G Λ d) hAΛ =
      (Finset.univ.filter fun p : Fin d =>
        mode4DLMFEvenFiniteEigenvalue G d p < Λ).card := by
  let A₀ := mode4ForwardHermitianFiniteMatrix G 0 d
  let AΛ := mode4ForwardHermitianFiniteMatrix G Λ d
  let hA₀ : A₀.IsHermitian :=
    mode4ForwardHermitianFiniteMatrix_isHermitian G 0 d
  let hAΛ : AΛ.IsHermitian :=
    mode4ForwardHermitianFiniteMatrix_isHermitian G Λ d
  let hshift : (A₀ - Matrix.scalar (Fin d) Λ).IsHermitian := by
    exact hA₀.sub
      (isHermitian_diagonal_of_self_adjoint _
        (funext fun _ => star_trivial Λ))
  have hmat : AΛ = A₀ - Matrix.scalar (Fin d) Λ := by
    simpa [A₀, AΛ] using
      mode4ForwardHermitianFiniteMatrix_eq_unshifted_sub_scalar G Λ d
  have htransport :
      mode4HermitianNegativeEigenvalueCount AΛ hAΛ =
        mode4HermitianNegativeEigenvalueCount
          (A₀ - Matrix.scalar (Fin d) Λ) hshift :=
    mode4NegativeCount_eq_of_matrix_eq_local hAΛ hshift hmat
  have hshiftCount :
      mode4HermitianNegativeEigenvalueCount
          (A₀ - Matrix.scalar (Fin d) Λ) hshift =
        (Finset.univ.filter fun i => hA₀.eigenvalues₀ i < Λ).card := by
    simpa using mode4NegativeCount_sub_scalar_eq_filter_zero A₀ hA₀ Λ
  let e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    Fin.revPerm.trans (finCongr (Fintype.card_fin d).symm)
  have hcard :
      (Finset.univ.filter fun p : Fin d =>
          mode4DLMFEvenFiniteEigenvalue G d p < Λ).card =
        (Finset.univ.filter fun i => hA₀.eigenvalues₀ i < Λ).card := by
    apply Finset.card_equiv e
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [e, mode4DLMFEvenFiniteEigenvalue, A₀]
  exact htransport.trans (hshiftCount.trans hcard.symm)

/-- The actual finite Jacobi truncation has exactly the same negative count
as the number of source-ordered finite DLMF levels below `Λ`.  The equality
uses the proved full-carrier characteristic-polynomial crosswalk and is
pointwise in the finite depth. -/
theorem mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
    (mProject K d : ℕ) (Λ : ℝ) :
    mode4HermitianNegativeEigenvalueCount
        (mode4ActualFiniteJacobiTruncation mProject Λ K d)
        (mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d) =
      (Finset.univ.filter fun p : Fin (K + d) =>
        mode4DLMFEvenFiniteEigenvalue
          (mode4JacobiG mProject) (K + d) p < Λ).card := by
  let A := mode4ActualFiniteJacobiTruncation mProject Λ K d
  let B := mode4ForwardHermitianFiniteMatrix
    (mode4JacobiG mProject) Λ (K + d)
  let hA : A.IsHermitian :=
    mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d
  let hB : B.IsHermitian :=
    mode4ForwardHermitianFiniteMatrix_isHermitian
      (mode4JacobiG mProject) Λ (K + d)
  have hpoly : A.charpoly = B.charpoly := by
    simpa [A, B] using
      mode4ActualFiniteJacobiTruncation_charpoly_eq_forwardHermitianFiniteMatrix
        mProject Λ K d
  exact
    (mode4NegativeCount_eq_of_charpoly_eq_local hA hB hpoly).trans
      (by
        simpa [B, hB] using
          mode4ForwardHermitianFiniteMatrix_negativeCount_eq_finiteCount
            (mode4JacobiG mProject) Λ (K + d))

private def mode4DepthLift (p N : ℕ) (hp : p ≤ N) :
    {d : ℕ // N < d} → {d : ℕ // p < d} :=
  fun d => ⟨d.1, lt_of_le_of_lt hp d.2⟩

private theorem mode4DepthLift_tendsto
    (p N : ℕ) (hp : p ≤ N) :
    Filter.Tendsto (mode4DepthLift p N hp) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  let i : {d : ℕ // N < d} :=
    ⟨max (N + 1) b.1, lt_of_lt_of_le (Nat.lt_succ_self N)
      (le_max_left _ _)⟩
  refine ⟨i, ?_⟩
  intro a ha
  change i.1 ≤ a.1 at ha
  change b.1 ≤ a.1
  exact le_trans (le_max_right (N + 1) b.1) ha

/-- Away from finitely many carrier thresholds, a fixed finite head has the
same number of levels below `Λ` at every sufficiently large depth.  The
extra strict inequality at index `N` is the explicit tail separator; no
global growth or endpoint count is hidden in this statement. -/
theorem mode4DLMFEvenFiniteCount_eventually_eq_classicalHeadCount
    (G Λ : ℝ) (N : ℕ) (hG : 0 < G)
    (hsep : ∀ p < N, mode4ClassicalEvenEigenvalue G p ≠ Λ)
    (htail : Λ < mode4ClassicalEvenEigenvalue G N) :
    ∀ᶠ d : {d : ℕ // N < d} in Filter.atTop,
      (Finset.univ.filter fun p : Fin d.1 =>
        mode4DLMFEvenFiniteEigenvalue G d.1 p < Λ).card =
      ((Finset.range N).filter fun p =>
        mode4ClassicalEvenEigenvalue G p < Λ).card := by
  have hhead :
      ∀ᶠ d : {d : ℕ // N < d} in Filter.atTop,
        ∀ p : Fin N,
          (mode4DLMFEvenFiniteEigenvalue G d.1
              ⟨p.1, lt_trans p.2 d.2⟩ < Λ ↔
            mode4ClassicalEvenEigenvalue G p.1 < Λ) := by
    rw [Filter.eventually_all]
    intro p
    have hpN : p.1 < N := p.2
    have hconv :
        Filter.Tendsto
          (fun d : {d : ℕ // N < d} =>
            mode4DLMFEvenFiniteEigenvalue G d.1
              ⟨p.1, lt_trans hpN d.2⟩)
          Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G p.1)) := by
      simpa [mode4DepthLift] using
        (mode4ClassicalEvenEigenvalue_tendsto G p.1 hG).comp
          (mode4DepthLift_tendsto p.1 N hpN.le)
    rcases lt_or_gt_of_ne (hsep p.1 hpN) with hbelow | habove
    · filter_upwards [hconv.eventually_lt_const hbelow] with d hd
      exact iff_of_true hd hbelow
    · filter_upwards [hconv.eventually_const_lt habove] with d hd
      exact iff_of_false (not_lt_of_ge hd.le) (not_lt_of_ge habove.le)
  have htailConv :
      Filter.Tendsto
        (fun d : {d : ℕ // N < d} =>
          mode4DLMFEvenFiniteEigenvalue G d.1 ⟨N, d.2⟩)
        Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G N)) := by
    simpa [mode4DepthLift] using
      (mode4ClassicalEvenEigenvalue_tendsto G N hG).comp
        (mode4DepthLift_tendsto N N le_rfl)
  have htailEventually :
      ∀ᶠ d : {d : ℕ // N < d} in Filter.atTop,
        Λ < mode4DLMFEvenFiniteEigenvalue G d.1 ⟨N, d.2⟩ :=
    htailConv.eventually_const_lt htail
  filter_upwards [hhead, htailEventually] with d hdHead hdTail
  symm
  apply Finset.card_bij
    (fun p hp =>
      (⟨p, lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp hp).1) d.2⟩ :
        Fin d.1))
  · intro p hp
    have hpRange := (Finset.mem_filter.mp hp).1
    have hpBelow := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (hdHead ⟨p, Finset.mem_range.mp hpRange⟩).mpr hpBelow
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Fin.ext_iff.mp heq
  · intro q hq
    have hqBelow := (Finset.mem_filter.mp hq).2
    have hqN : q.val < N := by
      by_contra hnot
      have hNq : (⟨N, d.2⟩ : Fin d.1) ≤ q := by
        exact Fin.mk_le_mk.mpr (Nat.le_of_not_gt hnot)
      have hmono := mode4DLMFEvenFiniteEigenvalue_monotone G d.1 hNq
      linarith
    refine ⟨q.val, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hqN, ?_⟩
      exact (hdHead ⟨q.val, hqN⟩).mp (by simpa using hqBelow)
    · apply Fin.ext
      rfl

/-- The zero-based carrier is ordered increasingly in the even-mode index.
This is inherited from the finite ordered spectra by taking both limits along
the common deeper truncation filter. -/
theorem mode4ClassicalEvenEigenvalue_monotone
    (G : ℝ) (hG : 0 < G) :
    Monotone (mode4ClassicalEvenEigenvalue G) := by
  intro p q hpq
  have hpconv :
      Filter.Tendsto
        (fun d : {d : ℕ // q < d} =>
          mode4DLMFEvenFiniteEigenvalue G d.1
            ⟨p, lt_of_le_of_lt hpq d.2⟩)
        Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G p)) := by
    simpa [mode4DepthLift] using
      (mode4ClassicalEvenEigenvalue_tendsto G p hG).comp
        (mode4DepthLift_tendsto p q hpq)
  have hqconv :
      Filter.Tendsto
        (fun d : {d : ℕ // q < d} =>
          mode4DLMFEvenFiniteEigenvalue G d.1 ⟨q, d.2⟩)
        Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G q)) :=
    mode4ClassicalEvenEigenvalue_tendsto G q hG
  apply le_of_tendsto_of_tendsto' hpconv hqconv
  intro d
  apply mode4DLMFEvenFiniteEigenvalue_monotone G d.1
  exact Fin.mk_le_mk.mpr hpq

#print axioms mode4DLMFEvenFiniteEigenvalue_ge_neg_three_mul_G
#print axioms mode4DLMFEvenFiniteEigenvalue_succ_le
#print axioms mode4DLMFEvenFiniteEigenvalue_antitone_in_depth
#print axioms mode4DLMFEvenFiniteEigenvalue_bddBelow
#print axioms mode4ClassicalEvenEigenvalue_ge_neg_three_mul_G
#print axioms mode4ClassicalEvenEigenvalue_tendsto_of_antitone
#print axioms mode4ClassicalEvenEigenvalue_tendsto
#print axioms mode4ClassicalEvenEigenvalue_monotone
#print axioms mode4ForwardHermitianFiniteMatrix_negativeCount_eq_finiteCount
#print axioms mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
#print axioms mode4DLMFEvenFiniteCount_eventually_eq_classicalHeadCount
