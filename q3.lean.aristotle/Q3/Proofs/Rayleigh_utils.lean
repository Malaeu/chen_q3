/-
Rayleigh quotient utilities.
-/

import Q3.Axioms

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Matrix
open Finset

namespace Q3.Proofs

lemma RayleighQuotient_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Q3.RayleighQuotient (A + B) v =
      Q3.RayleighQuotient A v + Q3.RayleighQuotient B v := by
  classical
  unfold Q3.RayleighQuotient
  have hnum_inner :
      ∀ i : Fin n,
        (∑ j, v i * (A i j + B i j) * v j)
          = (∑ j, v i * A i j * v j) + (∑ j, v i * B i j * v j) := by
    intro i
    simpa [mul_add, Matrix.add_apply, add_comm, add_left_comm, add_assoc, add_mul]
      using (Finset.sum_add_distrib (s := Finset.univ)
        (f := fun j => v i * A i j * v j)
        (g := fun j => v i * B i j * v j))
  have hnum :
      (∑ i, ∑ j, v i * (A i j + B i j) * v j)
        = (∑ i, ∑ j, v i * A i j * v j) + (∑ i, ∑ j, v i * B i j * v j) := by
    simpa [hnum_inner]
      using (Finset.sum_add_distrib (s := Finset.univ)
        (f := fun i => ∑ j, v i * A i j * v j)
        (g := fun i => ∑ j, v i * B i j * v j))
  simp [Matrix.add_apply, hnum, add_div]

lemma RayleighQuotient_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Q3.RayleighQuotient (A - B) v =
      Q3.RayleighQuotient A v - Q3.RayleighQuotient B v := by
  classical
  unfold Q3.RayleighQuotient
  have hnum_inner :
      ∀ i : Fin n,
        (∑ j, v i * (A i j - B i j) * v j)
          = (∑ j, v i * A i j * v j) - (∑ j, v i * B i j * v j) := by
    intro i
    simpa [mul_sub, Matrix.sub_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add,
        add_mul]
      using (Finset.sum_sub_distrib (s := Finset.univ)
        (f := fun j => v i * A i j * v j)
        (g := fun j => v i * B i j * v j))
  have hnum :
      (∑ i, ∑ j, v i * (A i j - B i j) * v j)
        = (∑ i, ∑ j, v i * A i j * v j) - (∑ i, ∑ j, v i * B i j * v j) := by
    simpa [hnum_inner]
      using (Finset.sum_sub_distrib (s := Finset.univ)
        (f := fun i => ∑ j, v i * A i j * v j)
        (g := fun i => ∑ j, v i * B i j * v j))
  simp [Matrix.sub_apply, hnum, sub_div]

lemma RayleighQuotient_sub_ge {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    {a b : ℝ} (hA : Q3.RayleighQuotient A v ≥ a) (hB : Q3.RayleighQuotient B v ≤ b) :
    Q3.RayleighQuotient (A - B) v ≥ a - b := by
  calc
    Q3.RayleighQuotient (A - B) v
        = Q3.RayleighQuotient A v - Q3.RayleighQuotient B v := by
            simpa using (RayleighQuotient_sub (A:=A) (B:=B) (v:=v))
    _ ≥ a - b := by linarith

lemma RayleighQuotient_le_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hv : v ≠ 0) :
    Q3.RayleighQuotient A v ≤ ‖A‖ := by
  classical
  let vE : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm v
  have hnum_eq : (∑ i, ∑ j, v i * A i j * v j) = v ⬝ᵥ (A.mulVec vE) := by
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, vE]
  have hdenom_eq : (∑ i, v i ^ 2) = v ⬝ᵥ v := by
    simp [dotProduct, pow_two]
  have hnum_inner :
      inner ℝ ((EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)) vE
        = v ⬝ᵥ (A.mulVec vE) := by
    simpa [vE] using
      (EuclideanSpace.inner_eq_star_dotProduct (𝕜:=ℝ) (ι:=Fin n)
        ((EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)) vE)
  have hdenom_nonneg : 0 ≤ v ⬝ᵥ v := by
    exact Fintype.sum_nonneg (fun _ => mul_self_nonneg _)
  have hdenom_ne : v ⬝ᵥ v ≠ 0 := by
    intro hzero
    have hv0 : v = 0 := (dotProduct_self_eq_zero (v:=v)).1 hzero
    exact hv hv0
  have hdenom_pos : 0 < v ⬝ᵥ v := lt_of_le_of_ne hdenom_nonneg (Ne.symm hdenom_ne)
  have hinner_bound : |v ⬝ᵥ (A.mulVec vE)| ≤
      ‖(EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)‖ * ‖vE‖ := by
    have h := (abs_real_inner_le_norm
      (x:= ((EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)
        : EuclideanSpace ℝ (Fin n)))
      (y:= vE))
    simpa [hnum_inner] using h
  have hmul : ‖(EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)‖ ≤ ‖A‖ * ‖vE‖ := by
    have h := (Matrix.l2_opNorm_mulVec (A:=A) (x:=vE))
    simpa using h
  have hnorm_mul : ‖vE‖ * ‖vE‖ = ∑ i, v i ^ 2 := by
    have hnorm_sq := (EuclideanSpace.norm_sq_eq (𝕜:=ℝ) (n:=Fin n) (x:=vE))
    calc
      ‖vE‖ * ‖vE‖ = ‖vE‖ ^ 2 := by ring
      _ = ∑ i, v i ^ 2 := by simpa using hnorm_sq
  have hnum_le : |v ⬝ᵥ (A.mulVec vE)| ≤ ‖A‖ * (v ⬝ᵥ v) := by
    have h1 : |v ⬝ᵥ (A.mulVec vE)| ≤ ‖A‖ * ‖vE‖ * ‖vE‖ := by
      have h2 : |v ⬝ᵥ (A.mulVec vE)| ≤
          ‖(EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)‖ * ‖vE‖ := hinner_bound
      have h3 : ‖(EuclideanSpace.equiv (ι:=Fin n) (𝕜:=ℝ)).symm (A.mulVec vE)‖ * ‖vE‖ ≤
          ‖A‖ * ‖vE‖ * ‖vE‖ := by
        have := mul_le_mul_of_nonneg_right hmul (norm_nonneg vE)
        simpa [mul_assoc] using this
      exact le_trans h2 h3
    have h1' : |v ⬝ᵥ (A.mulVec vE)| ≤ ‖A‖ * (‖vE‖ * ‖vE‖) := by
      simpa [mul_assoc] using h1
    have hden : ‖vE‖ * ‖vE‖ = v ⬝ᵥ v := by
      simpa [hdenom_eq, hnorm_mul]
    simpa [hden, mul_assoc] using h1'
  have hdiv : |v ⬝ᵥ (A.mulVec vE)| / (v ⬝ᵥ v) ≤ ‖A‖ := by
    have h := (div_le_iff₀ hdenom_pos).2 hnum_le
    simpa [mul_comm] using h
  have hle_abs : Q3.RayleighQuotient A v ≤ |v ⬝ᵥ (A.mulVec vE)| / (v ⬝ᵥ v) := by
    unfold Q3.RayleighQuotient
    have hle : (v ⬝ᵥ (A.mulVec vE)) ≤ |v ⬝ᵥ (A.mulVec vE)| := le_abs_self _
    have hnum : (∑ i, ∑ j, v i * A i j * v j) = v ⬝ᵥ (A.mulVec vE) := hnum_eq
    have hden : (∑ i, v i ^ 2) = v ⬝ᵥ v := hdenom_eq
    simpa [hnum, hden] using (div_le_div_of_nonneg_right hle hdenom_nonneg)
  exact le_trans hle_abs hdiv

end Q3.Proofs
