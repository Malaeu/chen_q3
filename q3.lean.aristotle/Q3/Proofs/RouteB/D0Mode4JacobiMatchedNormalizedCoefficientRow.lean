import Q3.Proofs.RouteB.D0Mode4JacobiRootFunction
import Q3.Proofs.RouteB.D0Mode4PSWFTailCoefficientSquareSummable
import Q3.Proofs.RouteB.D0Mode4PSWFLegendreBoundaryFluxIdentification

/-!
# The root-spliced normalized mode-four recurrence row

This file constructs only a global normalized coefficient row from the
already committed left solution, root equation, and canonical square-summable
right tail.  It does not identify that row with a Ferrers series, a regular
first-kind solution, an ordered spectral mode, an infinite operator, or a
resolvent.
-/

noncomputable section

private theorem mode4LeftPair_fst_eq_prev
    (G Λ : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (mode4LeftPair G Λ q).1 =
      (mode4LeftPair G Λ (q - 1)).2 := by
  cases q with
  | zero => omega
  | succ n => simp [mode4LeftPair]

private theorem mode4JacobiLower_ne_zero_of_one_le
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 1 ≤ q) :
    mode4JacobiLower G q ≠ 0 := by
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold mode4JacobiLower mode4JacobiIndex
  dsimp
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero hG.ne' (by nlinarith))
      (by nlinarith)
  · exact mul_ne_zero (by nlinarith) (by nlinarith)

private theorem mode4LeftPair_row_project_recurrence
    (mProject : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    ∀ q : ℕ,
      mode4JacobiLower (mode4JacobiG mProject) q *
          (mode4LeftPair (mode4JacobiG mProject) Λ (q - 1)).2 -
        mode4JacobiCenter (mode4JacobiG mProject) Λ q *
          (mode4LeftPair (mode4JacobiG mProject) Λ q).2 +
        mode4JacobiUpper (mode4JacobiG mProject) q *
          (mode4LeftPair (mode4JacobiG mProject) Λ (q + 1)).2 = 0 := by
  intro q
  have htransfer := mode4LeftPair_succ_transfer mProject q Λ hm
  dsimp only at htransfer
  cases q with
  | zero =>
      have hlower : mode4JacobiLower (mode4JacobiG mProject) 0 = 0 := by
        simp [mode4JacobiLower, mode4JacobiIndex]
      rw [hlower] at htransfer ⊢
      norm_num at htransfer ⊢
      linarith [htransfer.2]
  | succ n =>
      have hfst := mode4LeftPair_fst_eq_prev
        (mode4JacobiG mProject) Λ (n + 1) (by omega)
      rw [hfst] at htransfer
      have hprev : n + 1 - 1 = n := by omega
      have hnext : n + 1 + 1 = n + 2 := by omega
      rw [hprev, hnext] at htransfer ⊢
      linarith [htransfer.2]

private theorem mode4LeftPair_row_pswfLegendre_recurrence
    (mProject : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal
            (mode4JacobiG mProject) q *
          (mode4LeftPair
            (mode4JacobiG mProject) Λ (q - 1)).2 +
        (mode4PSWFLegendreDiagonal
              (mode4JacobiG mProject) q -
            (Λ + mode4JacobiG mProject)) *
          (mode4LeftPair
            (mode4JacobiG mProject) Λ q).2 +
        mode4PSWFLegendreSuperdiagonal
            (mode4JacobiG mProject) q *
          (mode4LeftPair
            (mode4JacobiG mProject) Λ (q + 1)).2 = 0 := by
  intro q
  have hproject := mode4LeftPair_row_project_recurrence mProject Λ hm q
  have hcross := mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk
    (mode4JacobiG mProject) Λ q
  have hsub :
      mode4PSWFLegendreSubdiagonal (mode4JacobiG mProject) q =
        -mode4JacobiLower (mode4JacobiG mProject) q := by
    linarith [hcross.1]
  have hdiag :
      mode4PSWFLegendreDiagonal (mode4JacobiG mProject) q -
          (Λ + mode4JacobiG mProject) =
        mode4JacobiCenter (mode4JacobiG mProject) Λ q :=
    hcross.2.1.symm
  have hsuper :
      mode4PSWFLegendreSuperdiagonal (mode4JacobiG mProject) q =
        -mode4JacobiUpper (mode4JacobiG mProject) q := by
    linarith [hcross.2.2]
  rw [hsub, hdiag, hsuper]
  linarith

private theorem mode4LeftPair_tail_eq_mul_canonical_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    let r := fun q : ℕ =>
      (mode4LeftPair (mode4JacobiG mProject) Λ q).2
    r (K - 1) ≠ 0 ∧
      ∀ n : ℕ,
        r (K - 1 + n) =
          r (K - 1) *
            mode4TailCoefficientRow mProject Λ K n := by
  let G := mode4JacobiG mProject
  let r : ℕ → ℝ := fun q => (mode4LeftPair G Λ q).2
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hraw : ∀ q : ℕ,
      mode4JacobiLower G q * r (q - 1) -
        mode4JacobiCenter G Λ q * r q +
        mode4JacobiUpper G q * r (q + 1) = 0 := by
    simpa [G, r] using
      mode4LeftPair_row_project_recurrence mProject Λ hm
  have hmatchPair :=
    (mode4RootFunction_eq_zero_iff_match mProject K Λ).mp hroot
  have hfst := mode4LeftPair_fst_eq_prev G Λ K (by omega)
  have hmatch :
      r K = mode4RightTailLimit mProject Λ K * r (K - 1) := by
    simpa [G, r, hfst] using hmatchPair
  have hspliceNonzero : r (K - 1) ≠ 0 := by
    intro hzero
    have hKzero : r K = 0 := by rw [hmatch, hzero, mul_zero]
    have hbasePair : r (K - 1) = 0 ∧ r (K - 1 + 1) = 0 := by
      refine ⟨hzero, ?_⟩
      have hidx : K - 1 + 1 = K := by omega
      simpa [hidx] using hKzero
    have hpairs : ∀ j ≤ K - 1, r j = 0 ∧ r (j + 1) = 0 := by
      intro j hj
      exact Nat.decreasingInduction'
        (P := fun s => r s = 0 ∧ r (s + 1) = 0)
        (fun s _ _ ih => by
          have hrec := hraw (s + 1)
          have hlower := mode4JacobiLower_ne_zero_of_one_le
            G (s + 1) hG (by omega)
          have hmul : mode4JacobiLower G (s + 1) * r s = 0 := by
            simpa [ih.1, ih.2] using hrec
          exact ⟨(mul_eq_zero.mp hmul).resolve_left hlower, ih.1⟩)
        hj hbasePair
    have hzero0 := (hpairs 0 (by omega)).1
    have hone : r 0 = 1 := by simp [r, mode4LeftPair]
    linarith
  refine ⟨hspliceNonzero, ?_⟩
  intro n
  exact Nat.twoStepInduction
    (P := fun j =>
      r (K - 1 + j) =
        r (K - 1) * mode4TailCoefficientRow mProject Λ K j)
    (by simp)
    (by
      change
        r (K - 1 + 1) =
          r (K - 1) * mode4TailCoefficientRow mProject Λ K 1
      have hidx : K - 1 + 1 = K := by omega
      rw [hidx, hmatch, mode4TailCoefficientRow_succ]
      simp
      ring)
    (fun j hj hjSucc => by
      change
        r (K - 1 + (j + 2)) =
          r (K - 1) * mode4TailCoefficientRow mProject Λ K (j + 2)
      change
        r (K - 1 + j) =
          r (K - 1) * mode4TailCoefficientRow mProject Λ K j at hj
      change
        r (K - 1 + (j + 1)) =
          r (K - 1) * mode4TailCoefficientRow mProject Λ K (j + 1) at hjSucc
      have hr :
          mode4JacobiLower G (K + j) * r (K - 1 + j) -
            mode4JacobiCenter G Λ (K + j) * r (K - 1 + (j + 1)) +
            mode4JacobiUpper G (K + j) * r (K - 1 + (j + 2)) = 0 := by
        have hprev : K + j - 1 = K - 1 + j := by omega
        have hhere : K + j = K - 1 + (j + 1) := by omega
        have hnext : K + j + 1 = K - 1 + (j + 2) := by omega
        simpa only [hprev, hhere, hnext] using hraw (K + j)
      have ht :
          mode4JacobiLower G (K + j) *
                mode4TailCoefficientRow mProject Λ K j -
              mode4JacobiCenter G Λ (K + j) *
                mode4TailCoefficientRow mProject Λ K (j + 1) +
              mode4JacobiUpper G (K + j) *
                mode4TailCoefficientRow mProject Λ K (j + 2) = 0 := by
        simpa [G] using
          mode4TailCoefficientRow_projectJacobi_recurrence
            mProject K Λ hm hK hsep hΛ j
      rw [hj, hjSucc] at hr
      have hdiff :
          mode4JacobiUpper G (K + j) *
            (r (K - 1 + (j + 2)) -
              r (K - 1) *
                mode4TailCoefficientRow mProject Λ K (j + 2)) = 0 := by
        linear_combination hr - r (K - 1) * ht
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hdiff).resolve_left
          (ne_of_gt (mode4JacobiUpper_pos G (K + j) hG))))
    n

/-- A zero of the committed left/right matching function produces a global
unphased recurrence row with raw square summability, exact DLMF-shaped
weighted normalization, and an exact splice to the committed canonical tail.

This is a recurrence-row theorem only.  In particular, it does not attach
Ferrers-series, endpoint-regularity, first-kind, or ordered-spectrum
provenance to the row. -/
theorem exists_mode4MatchedNormalizedRecurrenceRow_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q : ℕ => (a q) ^ 2) ∧
      HasSum
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        1 ∧
      (∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) q * a (q - 1) +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) q -
              (Λ + mode4JacobiG mProject)) * a q +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) q * a (q + 1) = 0) ∧
      a (K - 1) ≠ 0 ∧
      ∀ n : ℕ,
        a (K - 1 + n) =
          a (K - 1) *
            mode4TailCoefficientRow mProject Λ K n := by
  let G := mode4JacobiG mProject
  let r : ℕ → ℝ := fun q => (mode4LeftPair G Λ q).2
  have hsplice := mode4LeftPair_tail_eq_mul_canonical_of_root
    mProject K Λ hm hK hsep hΛ hroot
  change
    r (K - 1) ≠ 0 ∧
      ∀ n,
        r (K - 1 + n) =
          r (K - 1) * mode4TailCoefficientRow mProject Λ K n at hsplice
  have hrawRec : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * r (q - 1) +
        (mode4PSWFLegendreDiagonal G q - (Λ + G)) * r q +
        mode4PSWFLegendreSuperdiagonal G q * r (q + 1) = 0 := by
    simpa [G, r] using
      mode4LeftPair_row_pswfLegendre_recurrence mProject Λ hm
  have htailSq :
      Summable (fun n : ℕ => (r (K - 1 + n)) ^ 2) := by
    have hbase := mode4TailCoefficientRow_sq_summable
      mProject K Λ hm hK hsep hΛ
    have hscaled := hbase.mul_left (r (K - 1) ^ 2)
    simpa only [hsplice.2, mul_pow] using hscaled
  have hrawSq : Summable (fun q : ℕ => (r q) ^ 2) := by
    apply (summable_nat_add_iff (K - 1)).1
    simpa only [Nat.add_comm] using htailSq
  let w : ℕ → ℝ := fun q => (r q) ^ 2 / (4 * (q : ℝ) + 1)
  have hwNonneg : ∀ q, 0 ≤ w q := by
    intro q
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hwLe : ∀ q, w q ≤ (r q) ^ 2 := by
    intro q
    have hden : (0 : ℝ) < 4 * (q : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (r q)]
  have hwSummable : Summable w :=
    Summable.of_nonneg_of_le hwNonneg hwLe hrawSq
  let S : ℝ := ∑' q : ℕ, w q
  have hSHas : HasSum w S := hwSummable.hasSum
  have hrZero : r 0 = 1 := by simp [r, mode4LeftPair]
  have hSge : 1 ≤ S := by
    have hzeroLe := hwSummable.le_tsum 0 (fun q _ => hwNonneg q)
    simpa [S, w, hrZero] using hzeroLe
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hSge
  let d : ℝ := Real.sqrt S
  have hdPos : 0 < d := by
    exact Real.sqrt_pos.2 hSpos
  have hdNe : d ≠ 0 := hdPos.ne'
  have hdSq : d ^ 2 = S := by
    exact Real.sq_sqrt hSpos.le
  let a : ℕ → ℝ := fun q => r q / d
  have haZero : 0 < a 0 := by
    simp [a, hrZero]
    exact hdPos
  have haSq : Summable (fun q : ℕ => (a q) ^ 2) := by
    have hscaled := hrawSq.mul_left (d⁻¹ ^ 2)
    simpa only [a, div_eq_mul_inv, mul_pow, mul_assoc, mul_comm] using hscaled
  have haWeighted :
      HasSum
        (fun q : ℕ => (a q) ^ 2 / (4 * (q : ℝ) + 1))
        1 := by
    have hscaled := hSHas.mul_left (d⁻¹ ^ 2)
    have hvalue : d⁻¹ ^ 2 * S = 1 := by
      rw [← hdSq]
      field_simp
    convert hscaled using 1
    · funext q
      simp only [a, w, div_eq_mul_inv, mul_pow]
      ring
    · exact hvalue.symm
  have haRec : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - (Λ + G)) * a q +
        mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0 := by
    intro q
    have hrq := hrawRec q
    unfold a
    calc
      mode4PSWFLegendreSubdiagonal G q * (r (q - 1) / d) +
            (mode4PSWFLegendreDiagonal G q - (Λ + G)) * (r q / d) +
            mode4PSWFLegendreSuperdiagonal G q * (r (q + 1) / d) =
          d⁻¹ *
            (mode4PSWFLegendreSubdiagonal G q * r (q - 1) +
              (mode4PSWFLegendreDiagonal G q - (Λ + G)) * r q +
              mode4PSWFLegendreSuperdiagonal G q * r (q + 1)) := by
        field_simp
      _ = 0 := by rw [hrq, mul_zero]
  have haSpliceNonzero : a (K - 1) ≠ 0 := by
    unfold a
    exact div_ne_zero hsplice.1 hdNe
  have haSplice : ∀ n : ℕ,
      a (K - 1 + n) =
        a (K - 1) * mode4TailCoefficientRow mProject Λ K n := by
    intro n
    unfold a
    rw [hsplice.2 n]
    field_simp
  refine ⟨a, haZero, haSq, haWeighted, ?_, haSpliceNonzero, haSplice⟩
  simpa [G] using haRec

/-- The row constructed from a root satisfies the exact hypotheses of the
already committed boundary-flux consumer, with no added source premise. -/
theorem exists_mode4MatchedNormalizedRecurrenceRow_boundaryFlux_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q : ℕ => (a q) ^ 2) ∧
      HasSum
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        1 ∧
      (∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) q * a (q - 1) +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) q -
              (Λ + mode4JacobiG mProject)) * a q +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) q * a (q + 1) = 0) ∧
      mode4JacobiSymmetricOff
            (mode4JacobiG mProject) (K - 1) *
          ((mode4TailHermitianScale K 1 * a K) /
            (mode4TailHermitianScale K 0 * a (K - 1))) =
        mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
          mode4RightTailLimit mProject Λ K := by
  rcases exists_mode4MatchedNormalizedRecurrenceRow_of_root
      mProject K Λ hm hK hsep hΛ hroot with
    ⟨a, haZero, haSq, haWeighted, haRec, _, _⟩
  refine ⟨a, haZero, haSq, haWeighted, haRec, ?_⟩
  exact mode4DLMF3084_3085_sourceBoundaryFlux_eq_schurCorrection
    mProject K Λ a hm hK hsep hΛ haRec haWeighted

#print axioms exists_mode4MatchedNormalizedRecurrenceRow_of_root
#print axioms exists_mode4MatchedNormalizedRecurrenceRow_boundaryFlux_of_root
