import Q3.Proofs.RouteB.D0Mode4JacobiHermitianTailRow

/-!
# DLMF 30.8.5 weight transfer to the shifted Hermitian tail

The `m = n = 0` specialization of the DLMF 30.8.5 normalization has
coefficient weight `1 / (4 * k + 1)`.  After the source shift
`k = K - 1 + n`, that weight is exactly the square of the committed
Hermitian tail scale, up to the fixed positive factor `4 * K - 3`.

This file is a conditional receiver.  Its sequence parameter is anonymous:
the theorems neither construct nor identify a regular PSWF coefficient row.
-/

noncomputable section

/-- Exact match between the committed Hermitian scale and the
`m = n = 0` DLMF 30.8.5 coefficient weight.  No source interpretation of
`a` is asserted. -/
theorem mode4TailHermitianScale_sourceWeight_identity
    (a : ℕ → ℝ) (K n : ℕ)
    (hK : 3 ≤ K) :
    (mode4TailHermitianScale K n * a (K - 1 + n)) ^ 2 =
      (4 * (K : ℝ) - 3) *
        ((a (K - 1 + n)) ^ 2 /
          (4 * ((K - 1 + n : ℕ) : ℝ) + 1)) := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnum : 0 ≤ 4 * (K : ℝ) - 3 := by linarith
  have hden : 0 ≤ 4 * ((K + n : ℕ) : ℝ) - 3 := by
    push_cast
    linarith
  unfold mode4TailHermitianScale
  rw [mul_pow, Real.sq_sqrt (div_nonneg hnum hden)]
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
  field_simp
  ring

/-- The `m = n = 0` DLMF 30.8.5 normalization supplies global nonzeroness
and exactly the square summability required after the committed shifted
Hermitian scale.

This is a conditional source receiver.  It neither constructs nor identifies
a regular PSWF coefficient sequence. -/
theorem mode4DLMF3085_nonzero_and_shiftedHermitian_sqSummable
    (a : ℕ → ℝ) (K : ℕ)
    (hK : 3 ≤ K)
    (h3085 :
      HasSum
        (fun k : ℕ =>
          (a k) ^ 2 / (4 * (k : ℝ) + 1))
        1) :
    (∃ k : ℕ, a k ≠ 0) ∧
      Summable
        (fun n : ℕ =>
          (mode4TailHermitianScale K n *
            a (K - 1 + n)) ^ 2) := by
  have hnonzero : ∃ k : ℕ, a k ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero :
        HasSum
          (fun k : ℕ =>
            (a k) ^ 2 / (4 * (k : ℝ) + 1))
          0 := by
      simpa [h] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
    have honezero : (1 : ℝ) = 0 := h3085.unique hzero
    norm_num at honezero
  refine ⟨hnonzero, ?_⟩
  have hinjective : Function.Injective (fun n : ℕ => K - 1 + n) := by
    intro n m h
    exact Nat.add_left_cancel h
  have htail :
      Summable
        (fun n : ℕ =>
          (a (K - 1 + n)) ^ 2 /
            (4 * ((K - 1 + n : ℕ) : ℝ) + 1)) :=
    h3085.summable.comp_injective hinjective
  have hscaled :
      Summable
        (fun n : ℕ =>
          (4 * (K : ℝ) - 3) *
            ((a (K - 1 + n)) ^ 2 /
              (4 * ((K - 1 + n : ℕ) : ℝ) + 1))) :=
    Summable.mul_left (4 * (K : ℝ) - 3) htail
  exact hscaled.congr fun n =>
    (mode4TailHermitianScale_sourceWeight_identity a K n hK).symm

#print axioms mode4TailHermitianScale_sourceWeight_identity
#print axioms mode4DLMF3085_nonzero_and_shiftedHermitian_sqSummable
