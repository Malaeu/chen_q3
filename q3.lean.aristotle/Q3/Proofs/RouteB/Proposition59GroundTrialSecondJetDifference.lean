import Q3.Proofs.RouteB.Proposition59EntireTransform

set_option linter.mathlibStandardSet false

/-!
# Proposition 5.9 — the ground/trial second-jet difference identity

`GOAL058_P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY`.

For two real even full coefficient rows `v`, `q` on the symmetric window
`[-N, N]` with `v 0 ≠ 0` and `q 0 ≠ 0`, the *raw* second-jet curvature

`κ(F) = -F''(0) / (2 F(0))`

of the Proposition-5.9 raw transform
`F_v(z) = L^{-1/2} ∑_{k ∈ [-N,N]} v_k · 2 sin(zL/2)/(z - x_k)`,
`x_k = 2πk/L`, obeys the exact finite identity

`κ(F_v) - κ(F_q) = L²/(2π²) ∑_{k=1}^{N} (v_k/v_0 - q_k/q_0)/k².`

Everything here is a **finite-cell identity**.  The only inputs are the two
already-proved exact jets of the raw transform,
`proposition59RawTransform_secondDerivative_zero` and
`proposition59RawTransform_at_zero_eq_sqrt`, plus finite rearrangement of a
symmetric window sum.  In particular:

* no hypothesis on the location of the zeros of `F` enters (the closed form of
  `proposition59Curvature` in
  `Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`
  carries a `ZerosRealOn` hypothesis because it identifies the second-jet
  quotient with a *root sum*; the second-jet quotient itself needs no such
  hypothesis, and that is the quantity used here — the bridging lemma
  `proposition59SecondJetCurvature_closed_form` below reproves the same closed
  form `κ = (L²/2)(1/12 + (1/(2π²v₀)) ∑_{k≠0} v_k/k²)` directly from the two
  jets);
* no eigenvector, spectral-gap or cofinal-rate statement is used or produced.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## Step 0 — the symmetric-window rearrangement

Pairing of the punctured symmetric window `[-N,N] \ {0}` with the positive
modes `1..N`.  Complex-valued counterpart of the pairing already used for the
real closed form. -/

private theorem sum_erase_zero_Icc_symm_complex (N : ℕ) (g : ℤ → ℂ) :
    ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, g k =
      ∑ k ∈ Finset.Icc 1 N, (g (k : ℤ) + g (-(k : ℤ))) := by
  classical
  induction N with
  | zero => simp
  | succ n ih =>
      have hset : (Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)).erase 0 =
          insert ((n : ℤ) + 1)
            (insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0)) := by
        ext a
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem1 : -((n : ℤ) + 1) ∉ (Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      have hnotmem2 : ((n : ℤ) + 1) ∉
          insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [show (-(((n : ℕ) + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by push_cast; ring,
        show ((((n : ℕ) + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by push_cast; ring,
        hset, Finset.sum_insert hnotmem2, Finset.sum_insert hnotmem1, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      ring

/-! ## Step 1 — the second-jet curvature in closed form, with no zero hypothesis

`κ(F_v) = -F_v''(0) / (2 F_v(0))` evaluated by the two exact jets. -/

/-- The raw second-jet curvature of the Proposition-5.9 transform in closed
form on the coefficient row.  This is the fourth boxed formula of the judge's
§2.1, obtained here directly from the two exact jets, so that no hypothesis on
the zeros of the transform is required. -/
theorem proposition59SecondJetCurvature_closed_form
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) (hv0 : v 0 ≠ 0) :
    -(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0) =
      (L : ℂ) ^ 2 / 2 *
        (1 / 12 + 1 / (2 * (Real.pi : ℂ) ^ 2 * v 0) *
          ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, v k / (k : ℂ) ^ 2) := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  rw [proposition59RawTransform_secondDerivative_zero hL N v,
    proposition59RawTransform_at_zero_eq_sqrt hL _ v h0]
  field_simp

/-- The even-row reduction of the second-jet curvature to the positive modes. -/
theorem proposition59SecondJetCurvature_positive_modes
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hv0 : v 0 ≠ 0) :
    -(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0) =
      (L : ℂ) ^ 2 / 24 +
        (L : ℂ) ^ 2 / (2 * (Real.pi : ℂ) ^ 2 * v 0) *
          ∑ n ∈ Finset.Icc 1 N, v (n : ℤ) / (n : ℂ) ^ 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsym : ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, v k / (k : ℂ) ^ 2 =
      2 * ∑ n ∈ Finset.Icc 1 N, v (n : ℤ) / (n : ℂ) ^ 2 := by
    rw [sum_erase_zero_Icc_symm_complex N (fun k : ℤ => v k / (k : ℂ) ^ 2),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hv (n : ℤ)]
    push_cast
    ring
  rw [proposition59SecondJetCurvature_closed_form hL N v hv0, hsym]
  field_simp
  ring

/-! ## Step 2 — the ground/trial difference

The `1/12` head cancels in the difference, and only the normalized positive
modes survive. -/

/-- **`P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY`** (complex rows).  For two
even full coefficient rows with nonvanishing centre, the difference of the raw
second-jet curvatures is the `1/k²`-weighted difference of the normalized
positive modes. -/
theorem proposition59_ground_trial_second_jet_difference
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v q : ℤ → ℂ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    (-(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v 0))
      - (-(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) q) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) q 0)) =
      (L : ℂ) ^ 2 / (2 * (Real.pi : ℂ) ^ 2) *
        ∑ k ∈ Finset.Icc 1 N,
          (v (k : ℤ) / v 0 - q (k : ℤ) / q 0) / (k : ℂ) ^ 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsplit :
      (∑ k ∈ Finset.Icc 1 N, (v (k : ℤ) / v 0 - q (k : ℤ) / q 0) / (k : ℂ) ^ 2) =
        (∑ k ∈ Finset.Icc 1 N, v (k : ℤ) / (k : ℂ) ^ 2) / v 0
          - (∑ k ∈ Finset.Icc 1 N, q (k : ℤ) / (k : ℂ) ^ 2) / q 0 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [proposition59SecondJetCurvature_positive_modes hL N v hv hv0,
    proposition59SecondJetCurvature_positive_modes hL N q hq hq0, hsplit]
  field_simp
  ring

/-- **`P59_GROUND_TRIAL_SECOND_JET_FINITE_IDENTITY`** (real rows).  The same
identity for real even rows: the right-hand side is a real number, coerced. -/
theorem proposition59_ground_trial_second_jet_difference_real
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    (-(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k => (v k : ℂ))) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k => (v k : ℂ)) 0))
      - (-(iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k => (q k : ℂ))) 0) /
        (2 * proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun k => (q k : ℂ)) 0)) =
      ((L ^ 2 / (2 * Real.pi ^ 2) *
        ∑ k ∈ Finset.Icc 1 N,
          (v (k : ℤ) / v 0 - q (k : ℤ) / q 0) / (k : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hvC : ∀ k : ℤ, ((v (-k) : ℝ) : ℂ) = ((v k : ℝ) : ℂ) := fun k => by rw [hv k]
  have hqC : ∀ k : ℤ, ((q (-k) : ℝ) : ℂ) = ((q k : ℝ) : ℂ) := fun k => by rw [hq k]
  have hv0C : ((v 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv0
  have hq0C : ((q 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0
  rw [proposition59_ground_trial_second_jet_difference hL N
    (fun k => (v k : ℂ)) (fun k => (q k : ℂ)) hvC hqC hv0C hq0C]
  push_cast
  ring

#print axioms proposition59SecondJetCurvature_closed_form
#print axioms proposition59SecondJetCurvature_positive_modes
#print axioms proposition59_ground_trial_second_jet_difference
#print axioms proposition59_ground_trial_second_jet_difference_real

end Q3.RouteB
