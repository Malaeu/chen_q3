import Mathlib
import Q3.Proofs.PrimeCert.IntervalChecker
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Intervals

/-!
Bucketed interval checker scaffold for the prime-heat partial sum.

This file packages the hypotheses needed to derive the partial-sum bound from
bucketed interval data. It does not yet provide the numeric proofs for the
bucket bounds.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_heat_bucket_range (k : Fin prime_heat_bucket_count) : Finset ℕ :=
  Finset.Icc (prime_heat_bucket_lo k) (prime_heat_bucket_hi k)

def prime_heat_bucket_sum (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_range k).sum (fun n => prime_heat_weight_term n)

/-- Fixed bucket width for the prime-heat partial sum. -/
def prime_heat_bucket_width : Nat := 10000

lemma prime_heat_bucket_lo_eq (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_lo k = k.1 * prime_heat_bucket_width + 1 := by
  fin_cases k <;> rfl

lemma prime_heat_bucket_hi_eq (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_hi k = (k.1 + 1) * prime_heat_bucket_width := by
  fin_cases k <;> rfl

lemma prime_heat_bucket_count_mul_width :
    prime_heat_bucket_count * prime_heat_bucket_width = prime_cert_heat_N := by
  norm_num [prime_heat_bucket_count, prime_heat_bucket_width, prime_cert_heat_N]

lemma prime_heat_weight_term_zero : prime_heat_weight_term 0 = 0 := by
  simp [prime_heat_weight_term, Q3.w_Q, ArithmeticFunction.vonMangoldt]

lemma Icc_eq_Ico_succ (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  simpa using (Finset.Ico_add_one_right_eq_Icc (a := a) (b := b)).symm

lemma prime_heat_bucket_sum_eq_Ico (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_sum k =
      (Finset.Ico (k.1 * prime_heat_bucket_width + 1)
          ((k.1 + 1) * prime_heat_bucket_width + 1)).sum
        (fun n => prime_heat_weight_term n) := by
  classical
  simp [prime_heat_bucket_sum, prime_heat_bucket_range,
    prime_heat_bucket_lo_eq, prime_heat_bucket_hi_eq, Icc_eq_Ico_succ]

lemma prime_heat_bucket_sum_range_eq (m : ℕ) :
    (Finset.range m).sum (fun k =>
        (Finset.Ico (k * prime_heat_bucket_width + 1)
            ((k + 1) * prime_heat_bucket_width + 1)).sum
          (fun n => prime_heat_weight_term n)) =
      (Finset.Ico 1 (m * prime_heat_bucket_width + 1)).sum
        (fun n => prime_heat_weight_term n) := by
  classical
  let f : ℕ → ℝ := fun n => prime_heat_weight_term n
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have h1 : 1 ≤ m * prime_heat_bucket_width + 1 := by
        exact Nat.succ_le_succ (Nat.zero_le _)
      have h2 :
          m * prime_heat_bucket_width + 1 ≤ (m + 1) * prime_heat_bucket_width + 1 := by
        have hmul : m * prime_heat_bucket_width ≤ (m + 1) * prime_heat_bucket_width := by
          exact Nat.mul_le_mul_right _ (Nat.le_succ _)
        exact Nat.succ_le_succ hmul
      calc
        (Finset.range (m + 1)).sum (fun k =>
            (Finset.Ico (k * prime_heat_bucket_width + 1)
                ((k + 1) * prime_heat_bucket_width + 1)).sum f)
            = (Finset.range m).sum (fun k =>
                (Finset.Ico (k * prime_heat_bucket_width + 1)
                    ((k + 1) * prime_heat_bucket_width + 1)).sum f)
              + (Finset.Ico (m * prime_heat_bucket_width + 1)
                  ((m + 1) * prime_heat_bucket_width + 1)).sum f := by
                simp [Finset.sum_range_succ, f]
        _ = (Finset.Ico 1 (m * prime_heat_bucket_width + 1)).sum f +
              (Finset.Ico (m * prime_heat_bucket_width + 1)
                  ((m + 1) * prime_heat_bucket_width + 1)).sum f := by
                simp [ih, f]
        _ = (Finset.Ico 1 ((m + 1) * prime_heat_bucket_width + 1)).sum f := by
              simpa [f] using (Finset.sum_Ico_consecutive (f := f) h1 h2)

lemma prime_heat_prime_sum_up_to_eq_Ico :
    prime_heat_prime_sum_up_to prime_cert_heat_N =
      (Finset.Ico 1 (prime_cert_heat_N + 1)).sum (fun n => prime_heat_weight_term n) := by
  classical
  have h0 : prime_heat_weight_term 0 = 0 := by
    simpa using prime_heat_weight_term_zero
  have hrange : Finset.range (prime_cert_heat_N + 1) = Finset.Ico 0 (prime_cert_heat_N + 1) := by
    simpa using
      congrArg (fun s => s (prime_cert_heat_N + 1)) (Finset.range_eq_Ico : Finset.range = Finset.Ico 0)
  calc
    prime_heat_prime_sum_up_to prime_cert_heat_N
        = (Finset.range (prime_cert_heat_N + 1)).sum (fun n => prime_heat_weight_term n) := by
            rfl
    _ = (Finset.Ico 0 (prime_cert_heat_N + 1)).sum (fun n => prime_heat_weight_term n) := by
            rw [hrange]
    _ = prime_heat_weight_term 0 +
          (Finset.Ico 1 (prime_cert_heat_N + 1)).sum (fun n => prime_heat_weight_term n) := by
            simpa using
              (Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := prime_cert_heat_N + 1)
                (Nat.succ_pos _) (fun n => prime_heat_weight_term n))
    _ = (Finset.Ico 1 (prime_cert_heat_N + 1)).sum (fun n => prime_heat_weight_term n) := by
            simp [h0]

lemma prime_heat_bucket_cover :
    prime_heat_prime_sum_up_to prime_cert_heat_N =
      (Finset.univ.sum (fun k => prime_heat_bucket_sum k)) := by
  classical
  let f : ℕ → ℝ := fun n => prime_heat_weight_term n
  let g : ℕ → ℝ := fun k =>
    if h : k < prime_heat_bucket_count then prime_heat_bucket_sum ⟨k, h⟩ else 0
  have hsum_up_to :
      prime_heat_prime_sum_up_to prime_cert_heat_N =
        (Finset.Ico 1 (prime_cert_heat_N + 1)).sum f := by
    simpa [f] using prime_heat_prime_sum_up_to_eq_Ico
  have hsum_univ_range :
      (Finset.univ.sum (fun k : Fin prime_heat_bucket_count => prime_heat_bucket_sum k)) =
        (Finset.range prime_heat_bucket_count).sum g := by
    have hfin :
        (∑ k : Fin prime_heat_bucket_count, g (k : ℕ)) =
          (Finset.range prime_heat_bucket_count).sum g := by
      simpa using (Fin.sum_univ_eq_sum_range (f := g) (n := prime_heat_bucket_count))
    have hfinL :
        (∑ k : Fin prime_heat_bucket_count, g (k : ℕ)) =
          (Finset.univ.sum (fun k : Fin prime_heat_bucket_count => prime_heat_bucket_sum k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [g]
    calc
      (Finset.univ.sum (fun k : Fin prime_heat_bucket_count => prime_heat_bucket_sum k))
          = ∑ k : Fin prime_heat_bucket_count, g (k : ℕ) := by
              simpa using hfinL.symm
      _ = (Finset.range prime_heat_bucket_count).sum g := hfin
  have hsum_range :
      (Finset.range prime_heat_bucket_count).sum g =
        (Finset.Ico 1 (prime_cert_heat_N + 1)).sum f := by
    have hsum_range' :
        (Finset.range prime_heat_bucket_count).sum g =
          (Finset.range prime_heat_bucket_count).sum (fun k =>
            (Finset.Ico (k * prime_heat_bucket_width + 1)
                ((k + 1) * prime_heat_bucket_width + 1)).sum f) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k < prime_heat_bucket_count := Finset.mem_range.mp hk
      simp [g, hk', prime_heat_bucket_sum_eq_Ico, f]
    have hsum_range'' :
        (Finset.range prime_heat_bucket_count).sum (fun k =>
            (Finset.Ico (k * prime_heat_bucket_width + 1)
                ((k + 1) * prime_heat_bucket_width + 1)).sum f) =
          (Finset.Ico 1 (prime_cert_heat_N + 1)).sum f := by
      simpa [prime_heat_bucket_count_mul_width] using
        (prime_heat_bucket_sum_range_eq (m := prime_heat_bucket_count))
    exact hsum_range'.trans hsum_range''
  calc
    prime_heat_prime_sum_up_to prime_cert_heat_N
        = (Finset.Ico 1 (prime_cert_heat_N + 1)).sum f := hsum_up_to
    _ = (Finset.univ.sum (fun k => prime_heat_bucket_sum k)) := by
          symm
          exact hsum_univ_range.trans hsum_range

structure PrimeHeatBucketData (bound : ℝ) : Prop where
  h_bucket :
    ∀ k : Fin prime_heat_bucket_count,
      prime_heat_bucket_sum k ≤ prime_heat_bucket_ub k
  h_sum_ub :
    (Finset.univ.sum (fun k => prime_heat_bucket_ub k)) ≤ bound

lemma prime_heat_sum_up_to_le_of_bucket
    (bound : ℝ) (h : PrimeHeatBucketData bound) :
    prime_heat_prime_sum_up_to prime_cert_heat_N ≤ bound := by
  calc
    prime_heat_prime_sum_up_to prime_cert_heat_N =
        (Finset.univ.sum (fun k => prime_heat_bucket_sum k)) :=
          prime_heat_bucket_cover
    _ ≤ Finset.univ.sum (fun k => prime_heat_bucket_ub k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h.h_bucket k
    _ ≤ bound := h.h_sum_ub

end Q3.Proofs.PrimeCert
