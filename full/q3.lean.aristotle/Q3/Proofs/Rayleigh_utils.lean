/-
Rayleigh quotient utilities.
-/

import Q3.Axioms

open scoped BigOperators
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

end Q3.Proofs
