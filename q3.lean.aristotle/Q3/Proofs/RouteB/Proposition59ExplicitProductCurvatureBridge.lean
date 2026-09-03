import Q3.Proofs.RouteB.Proposition59EntireTransform
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.NumberTheory.ZetaValues

set_option linter.mathlibStandardSet false

/-!
# Proposition 5.9 explicit-product curvature bridge

Judge directive `926c1865` (`REQ-2026-09-03-CURVBRIDGE`), paper proof at Lean
granularity in `PROSHKA_VERDICT_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.md`
§2.1–2.7.  Everything here is finite-cell: no Hadamard factorization, no
entire-function order predicate, no global cancellation of the sine numerator
against the Cauchy denominator at a removable node.
-/

noncomputable section

open Filter Set Polynomial
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## Step 1 — the finite Cauchy numerator (`P59_FINITE_CAUCHY_NUMERATOR_IDENTITY`) -/

/-- `D_N(z) = ∏_{k ∈ S} (z - x_k)`, the finite Cauchy denominator of
Proposition 5.9 on the carrier `S`. -/
def proposition59CauchyDenominator (L : ℝ) (S : Finset ℤ) : Polynomial ℂ :=
  ∏ k ∈ S, (X - C (proposition59Pole L k))

/-- `P_N(z) = ∑_{k ∈ S} v_k ∏_{j ≠ k} (z - x_j)`, the finite Cauchy numerator.
It is a genuine polynomial: no infinite-function theorem enters. -/
def proposition59CauchyNumerator (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    Polynomial ℂ :=
  ∑ k ∈ S, C (v k) *
    ∏ j ∈ S.erase k, (X - C (proposition59Pole L j))

@[simp] theorem proposition59CauchyDenominator_eval
    (L : ℝ) (S : Finset ℤ) (z : ℂ) :
    (proposition59CauchyDenominator L S).eval z =
      ∏ k ∈ S, (z - proposition59Pole L k) := by
  simp [proposition59CauchyDenominator, eval_prod]

@[simp] theorem proposition59CauchyNumerator_eval
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) (z : ℂ) :
    (proposition59CauchyNumerator L S v).eval z =
      ∑ k ∈ S, v k * ∏ j ∈ S.erase k, (z - proposition59Pole L j) := by
  simp [proposition59CauchyNumerator, eval_finset_sum, eval_prod]

/-- The finite Cauchy denominator is nonzero exactly off the lattice. -/
theorem proposition59CauchyDenominator_eval_ne_zero
    (L : ℝ) (S : Finset ℤ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    (proposition59CauchyDenominator L S).eval z ≠ 0 := by
  rw [proposition59CauchyDenominator_eval]
  exact Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hz k hk)

/-- `P59_FINITE_CAUCHY_NUMERATOR_IDENTITY`: off the finite lattice the Cauchy
sum is the quotient of the two finite polynomials. -/
theorem proposition59_finite_cauchy_numerator_identity
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    ∑ k ∈ S, v k / (z - proposition59Pole L k) =
      (proposition59CauchyNumerator L S v).eval z /
        (proposition59CauchyDenominator L S).eval z := by
  have hD : (proposition59CauchyDenominator L S).eval z ≠ 0 :=
    proposition59CauchyDenominator_eval_ne_zero L S hz
  rw [proposition59CauchyNumerator_eval, proposition59CauchyDenominator_eval,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hsplit :
      ∏ j ∈ S, (z - proposition59Pole L j) =
        (z - proposition59Pole L k) *
          ∏ j ∈ S.erase k, (z - proposition59Pole L j) :=
    (Finset.mul_prod_erase S _ hk).symm
  have hk0 : z - proposition59Pole L k ≠ 0 := sub_ne_zero.mpr (hz k hk)
  have hrest : ∏ j ∈ S.erase k, (z - proposition59Pole L j) ≠ 0 := by
    rw [proposition59CauchyDenominator_eval] at hD
    rw [hsplit] at hD
    exact fun h => hD (by rw [h, mul_zero])
  rw [hsplit]
  field_simp

/-- The exact value of the finite Cauchy numerator at an included lattice
point: `P_N(x_j) = v_j ∏_{k ≠ j} (x_j - x_k)`. -/
theorem proposition59CauchyNumerator_eval_at_lattice
    (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    (proposition59CauchyNumerator L S v).eval (proposition59Pole L j) =
      v j * ∏ k ∈ S.erase j,
        (proposition59Pole L j - proposition59Pole L k) := by
  rw [proposition59CauchyNumerator_eval]
  refine Finset.sum_eq_single j (fun k hk hkj => ?_) (fun h => absurd hj h)
  have hjmem : j ∈ S.erase k := Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩
  have : ∏ i ∈ S.erase k,
      (proposition59Pole L j - proposition59Pole L i) = 0 :=
    Finset.prod_eq_zero hjmem (by ring)
  rw [this, mul_zero]

/-- On the lattice the numerator vanishes exactly where the coefficient does. -/
theorem proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    (proposition59CauchyNumerator L S v).eval (proposition59Pole L j) = 0 ↔
      v j = 0 := by
  rw [proposition59CauchyNumerator_eval_at_lattice L S v hj]
  have hprod : ∏ k ∈ S.erase j,
      (proposition59Pole L j - proposition59Pole L k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr ?_
    exact proposition59Pole_ne hL (Finset.mem_erase.mp hk).1.symm
  exact mul_eq_zero_iff_right hprod

#print axioms proposition59_finite_cauchy_numerator_identity
#print axioms proposition59CauchyNumerator_eval_at_lattice
#print axioms proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff

end Q3.RouteB
