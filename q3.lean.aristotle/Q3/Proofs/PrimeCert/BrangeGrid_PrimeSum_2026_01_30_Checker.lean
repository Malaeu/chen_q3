import Mathlib
import Q3.Proofs.PrimeCert.IntervalChecker
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSumTail
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_Intervals

/-!
Bucketed interval checker scaffold for the full B-grid points.

This file packages the hypotheses needed to derive the partial-sum bounds
from bucketed interval data. It does not yet provide the numeric proofs for the
bucket bounds.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_b_grid_bucket_range (k : Fin prime_b_grid_bucket_count) : Finset ℕ :=
  Finset.Icc (prime_b_grid_bucket_lo k) (prime_b_grid_bucket_hi k)

def prime_b_grid_bucket_sum (i : Fin prime_b_grid_size) (k : Fin prime_b_grid_bucket_count) : ℝ :=
  (prime_b_grid_bucket_range k).sum (fun n => prime_b_grid_weight_term i n)

/-- Fixed bucket width for the full grid certificate. -/
def prime_b_grid_bucket_width : Nat := 10000

lemma prime_b_grid_bucket_lo_eq (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_lo k = k.1 * prime_b_grid_bucket_width + 1 := by
  fin_cases k <;> rfl

lemma prime_b_grid_bucket_hi_eq (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_hi k = (k.1 + 1) * prime_b_grid_bucket_width := by
  fin_cases k <;> rfl

lemma prime_b_grid_bucket_count_mul_width :
    prime_b_grid_bucket_count * prime_b_grid_bucket_width = prime_cert_N := by
  norm_num [prime_b_grid_bucket_count, prime_b_grid_bucket_width, prime_cert_N]

lemma prime_b_grid_weight_term_zero (i : Fin prime_b_grid_size) :
    prime_b_grid_weight_term i 0 = 0 := by
  simp [prime_b_grid_weight_term, Q3.w_Q, ArithmeticFunction.vonMangoldt]

lemma Icc_eq_Ico_succ (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  simpa using (Finset.Ico_add_one_right_eq_Icc (a := a) (b := b)).symm

lemma prime_b_grid_bucket_sum_eq_Ico
    (i : Fin prime_b_grid_size) (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_sum i k =
      (Finset.Ico (k.1 * prime_b_grid_bucket_width + 1)
          ((k.1 + 1) * prime_b_grid_bucket_width + 1)).sum
        (fun n => prime_b_grid_weight_term i n) := by
  classical
  simp [prime_b_grid_bucket_sum, prime_b_grid_bucket_range,
    prime_b_grid_bucket_lo_eq, prime_b_grid_bucket_hi_eq, Icc_eq_Ico_succ]

lemma prime_b_grid_bucket_sum_range_eq
    (i : Fin prime_b_grid_size) (m : ℕ) :
    (Finset.range m).sum (fun k =>
        (Finset.Ico (k * prime_b_grid_bucket_width + 1)
            ((k + 1) * prime_b_grid_bucket_width + 1)).sum
          (fun n => prime_b_grid_weight_term i n)) =
      (Finset.Ico 1 (m * prime_b_grid_bucket_width + 1)).sum
        (fun n => prime_b_grid_weight_term i n) := by
  classical
  let f : ℕ → ℝ := fun n => prime_b_grid_weight_term i n
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have h1 : 1 ≤ m * prime_b_grid_bucket_width + 1 := by
        exact Nat.succ_le_succ (Nat.zero_le _)
      have h2 :
          m * prime_b_grid_bucket_width + 1 ≤ (m + 1) * prime_b_grid_bucket_width + 1 := by
        have hmul : m * prime_b_grid_bucket_width ≤ (m + 1) * prime_b_grid_bucket_width := by
          exact Nat.mul_le_mul_right _ (Nat.le_succ _)
        exact Nat.succ_le_succ hmul
      calc
        (Finset.range (m + 1)).sum (fun k =>
            (Finset.Ico (k * prime_b_grid_bucket_width + 1)
                ((k + 1) * prime_b_grid_bucket_width + 1)).sum f)
            = (Finset.range m).sum (fun k =>
                (Finset.Ico (k * prime_b_grid_bucket_width + 1)
                    ((k + 1) * prime_b_grid_bucket_width + 1)).sum f)
              + (Finset.Ico (m * prime_b_grid_bucket_width + 1)
                  ((m + 1) * prime_b_grid_bucket_width + 1)).sum f := by
                simp [Finset.sum_range_succ, f]
        _ = (Finset.Ico 1 (m * prime_b_grid_bucket_width + 1)).sum f +
              (Finset.Ico (m * prime_b_grid_bucket_width + 1)
                  ((m + 1) * prime_b_grid_bucket_width + 1)).sum f := by
                simp [ih, f]
        _ = (Finset.Ico 1 ((m + 1) * prime_b_grid_bucket_width + 1)).sum f := by
              simpa [f] using (Finset.sum_Ico_consecutive (f := f) h1 h2)

lemma prime_b_grid_prime_sum_up_to_eq_Ico (i : Fin prime_b_grid_size) :
    prime_b_grid_prime_sum_up_to i =
      (Finset.Ico 1 (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n) := by
  classical
  have h0 : prime_b_grid_weight_term i 0 = 0 := by
    simpa using prime_b_grid_weight_term_zero (i := i)
  have hrange : Finset.range (prime_cert_N + 1) = Finset.Ico 0 (prime_cert_N + 1) := by
    simpa using
      congrArg (fun s => s (prime_cert_N + 1)) (Finset.range_eq_Ico : Finset.range = Finset.Ico 0)
  calc
    prime_b_grid_prime_sum_up_to i
        = (Finset.range (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n) := by
            rfl
    _ = (Finset.Ico 0 (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n) := by
            rw [hrange]
    _ = prime_b_grid_weight_term i 0 +
          (Finset.Ico 1 (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n) := by
            simpa using
              (Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := prime_cert_N + 1)
                (Nat.succ_pos _) (fun n => prime_b_grid_weight_term i n))
    _ = (Finset.Ico 1 (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n) := by
            simp [h0]

lemma prime_b_grid_bucket_cover (i : Fin prime_b_grid_size) :
    prime_b_grid_prime_sum_up_to i =
      (Finset.univ.sum (fun k => prime_b_grid_bucket_sum i k)) := by
  classical
  let f : ℕ → ℝ := fun n => prime_b_grid_weight_term i n
  let g : ℕ → ℝ := fun k =>
    if h : k < prime_b_grid_bucket_count then prime_b_grid_bucket_sum i ⟨k, h⟩ else 0
  have hsum_up_to :
      prime_b_grid_prime_sum_up_to i =
        (Finset.Ico 1 (prime_cert_N + 1)).sum f := by
    simpa [f] using prime_b_grid_prime_sum_up_to_eq_Ico (i := i)
  have hsum_univ_range :
      (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count => prime_b_grid_bucket_sum i k)) =
        (Finset.range prime_b_grid_bucket_count).sum g := by
    have hfin :
        (∑ k : Fin prime_b_grid_bucket_count, g (k : ℕ)) =
          (Finset.range prime_b_grid_bucket_count).sum g := by
      simpa using (Fin.sum_univ_eq_sum_range (f := g) (n := prime_b_grid_bucket_count))
    have hfinL :
        (∑ k : Fin prime_b_grid_bucket_count, g (k : ℕ)) =
          (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count => prime_b_grid_bucket_sum i k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [g]
    calc
      (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count => prime_b_grid_bucket_sum i k))
          = ∑ k : Fin prime_b_grid_bucket_count, g (k : ℕ) := by
              simpa using hfinL.symm
      _ = (Finset.range prime_b_grid_bucket_count).sum g := hfin
  have hsum_range :
      (Finset.range prime_b_grid_bucket_count).sum g =
        (Finset.Ico 1 (prime_cert_N + 1)).sum f := by
    have hsum_range' :
        (Finset.range prime_b_grid_bucket_count).sum g =
          (Finset.range prime_b_grid_bucket_count).sum (fun k =>
            (Finset.Ico (k * prime_b_grid_bucket_width + 1)
                ((k + 1) * prime_b_grid_bucket_width + 1)).sum f) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k < prime_b_grid_bucket_count := Finset.mem_range.mp hk
      simp [g, hk', prime_b_grid_bucket_sum_eq_Ico, f]
    have hsum_range'' :
        (Finset.range prime_b_grid_bucket_count).sum (fun k =>
            (Finset.Ico (k * prime_b_grid_bucket_width + 1)
                ((k + 1) * prime_b_grid_bucket_width + 1)).sum f) =
          (Finset.Ico 1 (prime_cert_N + 1)).sum f := by
      simpa [prime_b_grid_bucket_count_mul_width] using
        (prime_b_grid_bucket_sum_range_eq (i := i) (m := prime_b_grid_bucket_count))
    exact hsum_range'.trans hsum_range''
  calc
    prime_b_grid_prime_sum_up_to i
        = (Finset.Ico 1 (prime_cert_N + 1)).sum f := hsum_up_to
    _ = (Finset.univ.sum (fun k => prime_b_grid_bucket_sum i k)) := by
          symm
          exact hsum_univ_range.trans hsum_range

structure PrimeBGridBucketData (i : Fin prime_b_grid_size) : Prop where
  h_bucket :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_bucket_sum i k ≤ prime_b_grid_bucket_ub i k
  h_sum_ub :
    (Finset.univ.sum (fun k => prime_b_grid_bucket_ub i k)) ≤
      prime_b_grid_prime_sum_ub i

lemma prime_b_grid_prime_sum_le_of_bucket
    (i : Fin prime_b_grid_size) (h : PrimeBGridBucketData i) :
    prime_b_grid_prime_sum_up_to i ≤ prime_b_grid_prime_sum_ub i := by
  calc
    prime_b_grid_prime_sum_up_to i =
        (Finset.univ.sum (fun k => prime_b_grid_bucket_sum i k)) :=
          prime_b_grid_bucket_cover (i := i)
    _ ≤ Finset.univ.sum (fun k => prime_b_grid_bucket_ub i k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h.h_bucket k
    _ ≤ prime_b_grid_prime_sum_ub i := h.h_sum_ub

end Q3.Proofs.PrimeCert
