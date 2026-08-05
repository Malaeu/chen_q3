import Q3.Proofs.RouteB.D0Mode4JacobiHermitianTailUniqueness
import Q3.Proofs.RouteB.D0Mode4PSWFLegendreWeightedHermitianTail

/-!
# Conditional DLMF 30.8.4--30.8.5 tail identification

An anonymous coefficient sequence satisfying the exact all-index DLMF 30.8.4
recurrence and the exact DLMF 30.8.5 weighted normalization gives a nonzero
square-summable solution of the committed symmetric Jacobi tail recurrence.
Discrete-Wronskian uniqueness then identifies that shifted Hermitian row with
the canonical tail up to a nonzero scalar.

This remains a conditional receiver.  It does not construct a regular
first-kind PSWF or attach source provenance to the sequence parameter.
-/

noncomputable section

private theorem mode4SourceTailHermitianScale_pos
    (K n : ℕ) (hK : 3 ≤ K) :
    0 < mode4TailHermitianScale K n := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold mode4TailHermitianScale
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (by linarith)

private theorem mode4SourceLegendreSubdiagonal_ne_zero
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 1 ≤ q) :
    mode4PSWFLegendreSubdiagonal G q ≠ 0 := by
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold mode4PSWFLegendreSubdiagonal mode4JacobiIndex
  dsimp
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr hG.ne') (by nlinarith))
      (by nlinarith)
  · exact mul_ne_zero (by nlinarith) (by nlinarith)

private theorem mode4SourceTailHermitianScale_lower_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiLower G (K + n) * mode4TailHermitianScale K (n + 1) =
      mode4JacobiSymmetricOff G (K - 1 + n) *
        mode4TailHermitianScale K n := by
  have hq : 3 ≤ K + n := le_trans hK (Nat.le_add_right K n)
  have hidx : K - 1 + n + 1 = K + n := by omega
  have hleft :
      0 ≤ mode4JacobiLower G (K + n) *
          mode4TailHermitianScale K (n + 1) :=
    (mul_pos (mode4JacobiLower_pos G (K + n) hG hq)
      (mode4SourceTailHermitianScale_pos K (n + 1) hK)).le
  have hright :
      0 ≤ mode4JacobiSymmetricOff G (K - 1 + n) *
          mode4TailHermitianScale K n := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mode4SourceTailHermitianScale_pos K n hK).le
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, mul_pow,
    mode4JacobiSymmetricOff_sq G (K - 1 + n) hG, hidx]
  have hscaleSucc :=
    mode4TailHermitianScale_sourceWeight_identity
      (fun _ : ℕ => (1 : ℝ)) K (n + 1) hK
  have hscale :=
    mode4TailHermitianScale_sourceWeight_identity
      (fun _ : ℕ => (1 : ℝ)) K n hK
  simp only [one_pow, mul_one] at hscaleSucc hscale
  rw [hscaleSucc, hscale]
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold mode4JacobiLower mode4JacobiUpper mode4JacobiIndex
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
  field_simp
  ring

private theorem mode4SourceTailHermitianScale_upper_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiUpper G (K + n) * mode4TailHermitianScale K (n + 1) =
      mode4JacobiSymmetricOff G (K + n) *
        mode4TailHermitianScale K (n + 2) := by
  have hqSucc : 3 ≤ K + n + 1 := by omega
  have hLpos : 0 < mode4JacobiLower G (K + n + 1) :=
    mode4JacobiLower_pos G (K + n + 1) hG hqSucc
  have hlower := mode4SourceTailHermitianScale_lower_balance
    G K (n + 1) hG hK
  have hidxLower : K + (n + 1) = K + n + 1 := by omega
  have hidxOff : K - 1 + (n + 1) = K + n := by omega
  rw [hidxLower, hidxOff] at hlower
  have hsq := mode4JacobiSymmetricOff_sq G (K + n) hG
  apply mul_left_cancel₀ (ne_of_gt hLpos)
  calc
    mode4JacobiLower G (K + n + 1) *
        (mode4JacobiUpper G (K + n) * mode4TailHermitianScale K (n + 1)) =
      (mode4JacobiLower G (K + n + 1) * mode4JacobiUpper G (K + n)) *
        mode4TailHermitianScale K (n + 1) := by ring
    _ = mode4JacobiSymmetricOff G (K + n) ^ 2 *
        mode4TailHermitianScale K (n + 1) := by rw [hsq]
    _ = mode4JacobiSymmetricOff G (K + n) *
        (mode4JacobiSymmetricOff G (K + n) *
          mode4TailHermitianScale K (n + 1)) := by ring
    _ = mode4JacobiSymmetricOff G (K + n) *
        (mode4JacobiLower G (K + n + 1) *
          mode4TailHermitianScale K (n + 2)) := by rw [hlower]
    _ = mode4JacobiLower G (K + n + 1) *
        (mode4JacobiSymmetricOff G (K + n) *
          mode4TailHermitianScale K (n + 2)) := by ring

private theorem mode4DLMF3084_shiftedHermitianTail_recurrence
    (G Λ : ℝ) (K : ℕ) (a : ℕ → ℝ)
    (hG : 0 < G)
    (hK : 3 ≤ K)
    (h3084 :
      ∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
          (mode4PSWFLegendreDiagonal G q - (Λ + G)) * a q +
          mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0) :
    ∀ n,
      mode4JacobiSymmetricOff G (K - 1 + n) *
          (mode4TailHermitianScale K n * a (K - 1 + n)) -
        mode4JacobiCenter G Λ (K + n) *
          (mode4TailHermitianScale K (n + 1) * a (K + n)) +
        mode4JacobiSymmetricOff G (K + n) *
          (mode4TailHermitianScale K (n + 2) * a (K + n + 1)) = 0 := by
  intro n
  let q := K + n
  have hq : q - 1 = K - 1 + n := by
    unfold q
    omega
  have hsource := h3084 q
  have hcross := mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk G Λ q
  have hsub : mode4PSWFLegendreSubdiagonal G q = -mode4JacobiLower G q := by
    linarith [hcross.1]
  have hdiag :
      mode4PSWFLegendreDiagonal G q - (Λ + G) =
        mode4JacobiCenter G Λ q := hcross.2.1.symm
  have hsuper : mode4PSWFLegendreSuperdiagonal G q = -mode4JacobiUpper G q := by
    linarith [hcross.2.2]
  rw [hsub, hdiag, hsuper, hq] at hsource
  have hraw :
      mode4JacobiLower G (K + n) * a (K - 1 + n) -
        mode4JacobiCenter G Λ (K + n) * a (K + n) +
        mode4JacobiUpper G (K + n) * a (K + n + 1) = 0 := by
    change
      mode4JacobiLower G q * a (K - 1 + n) -
        mode4JacobiCenter G Λ q * a q +
        mode4JacobiUpper G q * a (q + 1) = 0
    linarith
  have hlower := mode4SourceTailHermitianScale_lower_balance G K n hG hK
  have hupper := mode4SourceTailHermitianScale_upper_balance G K n hG hK
  calc
    _ = mode4TailHermitianScale K (n + 1) *
        (mode4JacobiLower G (K + n) * a (K - 1 + n) -
          mode4JacobiCenter G Λ (K + n) * a (K + n) +
          mode4JacobiUpper G (K + n) * a (K + n + 1)) := by
      rw [show
        mode4JacobiSymmetricOff G (K - 1 + n) *
            (mode4TailHermitianScale K n * a (K - 1 + n)) =
          (mode4JacobiSymmetricOff G (K - 1 + n) *
            mode4TailHermitianScale K n) * a (K - 1 + n) by ring,
        ← hlower]
      rw [show
        mode4JacobiSymmetricOff G (K + n) *
            (mode4TailHermitianScale K (n + 2) * a (K + n + 1)) =
          (mode4JacobiSymmetricOff G (K + n) *
            mode4TailHermitianScale K (n + 2)) * a (K + n + 1) by ring,
        ← hupper]
      ring
    _ = 0 := by rw [hraw, mul_zero]

/-- An anonymous sequence satisfying the exact all-index DLMF 30.8.4
recurrence and DLMF 30.8.5 normalization has a shifted Hermitian tail equal
to a nonzero scalar multiple of the canonical square-summable tail.

This is a conditional receiver, not a regular-PSWF source construction. -/
theorem mode4DLMF3084_3085_shiftedHermitianTail_eq_c_mul_canonical
    (mProject K : ℕ) (Λ : ℝ) (a : ℕ → ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (h3084 :
      ∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) q * a (q - 1) +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) q -
              (Λ + mode4JacobiG mProject)) * a q +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) q * a (q + 1) = 0)
    (h3085 :
      HasSum
        (fun k : ℕ =>
          (a k) ^ 2 / (4 * (k : ℝ) + 1))
        1) :
    ∃ c : ℝ,
      c ≠ 0 ∧
      ∀ n : ℕ,
        mode4TailHermitianScale K n * a (K - 1 + n) =
          c * mode4HermitianTailCoefficientRow mProject Λ K n := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  rcases mode4DLMF3085_nonzero_and_shiftedHermitian_sqSummable a K hK h3085 with
    ⟨hglobal, hsourceSq⟩
  have hcanonicalZero :
      mode4HermitianTailCoefficientRow mProject Λ K 0 ≠ 0 := by
    rw [mode4HermitianTailCoefficientRow_zero mProject K Λ hK]
    norm_num
  have hcanonicalRec := mode4HermitianTailCoefficientRow_recurrence
    mProject K Λ hm hK hsep hΛ
  have hsourceRec := mode4DLMF3084_shiftedHermitianTail_recurrence
    G Λ K a hG hK h3084
  have hsourceRec' :
      ∀ n,
        mode4JacobiSymmetricOff G (K - 1 + n) *
            (mode4TailHermitianScale K n * a (K - 1 + n)) -
          mode4JacobiCenter G Λ (K + n) *
            (mode4TailHermitianScale K (n + 1) * a (K - 1 + (n + 1))) +
          mode4JacobiSymmetricOff G (K + n) *
            (mode4TailHermitianScale K (n + 2) * a (K - 1 + (n + 2))) = 0 := by
    intro n
    have hidxOne : K - 1 + (n + 1) = K + n := by omega
    have hidxTwo : K - 1 + (n + 2) = K + n + 1 := by omega
    simpa only [hidxOne, hidxTwo] using hsourceRec n
  have hcanonicalSq := mode4HermitianTailCoefficientRow_sq_summable
    mProject K Λ hm hK hsep hΛ
  rcases mode4HermitianTail_sqSummable_solution_unique_up_to_scale
      G Λ K hG hK
      (mode4HermitianTailCoefficientRow mProject Λ K)
      (fun n => mode4TailHermitianScale K n * a (K - 1 + n))
      hcanonicalZero hcanonicalRec hsourceRec' hcanonicalSq hsourceSq with
    ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  intro hcZero
  have hscaledZero :
      ∀ n : ℕ,
        mode4TailHermitianScale K n * a (K - 1 + n) = 0 := by
    intro n
    simpa [hcZero] using hc n
  have htailZero : ∀ n : ℕ, a (K - 1 + n) = 0 := by
    intro n
    exact (mul_eq_zero.mp (hscaledZero n)).resolve_left
      (ne_of_gt (mode4SourceTailHermitianScale_pos K n hK))
  have htailAll : ∀ j : ℕ, K - 1 ≤ j → a j = 0 := by
    intro j hj
    have hidx : K - 1 + (j - (K - 1)) = j := Nat.add_sub_of_le hj
    rw [← hidx]
    exact htailZero (j - (K - 1))
  have hallFrom : ∀ k ≤ K - 1, ∀ j, k ≤ j → a j = 0 := by
    intro k hk
    exact Nat.decreasingInduction'
      (P := fun r => ∀ j, r ≤ j → a j = 0)
      (fun r _ _ ih j hrj => by
        by_cases hj : j = r
        · subst j
          have hrec := h3084 (r + 1)
          have hnext : a (r + 1) = 0 := ih (r + 1) (by omega)
          have hnextnext : a (r + 2) = 0 := ih (r + 2) (by omega)
          have hidx : r + 1 - 1 = r := by omega
          have hmul :
              mode4PSWFLegendreSubdiagonal G (r + 1) * a r = 0 := by
            simpa [G, hidx, hnext, hnextnext] using hrec
          exact (mul_eq_zero.mp hmul).resolve_left
            (mode4SourceLegendreSubdiagonal_ne_zero G (r + 1) hG (by omega))
        · exact ih j (by omega))
      hk htailAll
  have hall : ∀ j : ℕ, a j = 0 := by
    intro j
    exact hallFrom 0 (Nat.zero_le _) j (Nat.zero_le _)
  rcases hglobal with ⟨j, hj⟩
  exact hj (hall j)

#print axioms mode4DLMF3084_3085_shiftedHermitianTail_eq_c_mul_canonical
