import Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution

/-!
# Goal 058 G3: uniqueness inside the regular Ferrers solution package

For fixed project parameters and spectral value, the exact three-term
recurrence determines the coefficient row from its zeroth coefficient.  The
positive phase at zero and the stored weighted normalization then force the
remaining scalar to be one.

This is a current-object uniqueness lemma only.  It does not identify the
packaged solution with an external DLMF spheroidal function, prove an interior
zero count, supply a Sturm oscillation theorem, close G1 or G3, promote Route
B, or make an RH claim.

Knowledge preflight query:
`Goal058 current regular Ferrers solution coefficient uniqueness same
parameters recurrence normalized zeroth coefficient positive`.
Result: no hits.
-/

noncomputable section

namespace Q3.RouteB

/-- Two accepted regular Ferrers solutions at the same parameters have the
same normalized coefficient row. -/
theorem mode4FerrersRegularEvenProlateSolution_coefficients_eq
    {mProject K : ℕ} {Λ : ℝ}
    (hm : 2 ≤ mProject)
    (S T : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    S.coefficients = T.coefficients := by
  let G : ℝ := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hsuper : ∀ q : ℕ,
      mode4PSWFLegendreSuperdiagonal G q ≠ 0 := by
    intro q
    have hu := mode4JacobiUpper_pos G q hG
    rw [mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal] at hu
    exact (neg_pos.mp hu).ne
  let c : ℝ := T.coefficients 0 / S.coefficients 0
  have hcpos : 0 < c := by
    exact div_pos T.coefficient_zero_pos S.coefficient_zero_pos
  have hzero : T.coefficients 0 = c * S.coefficients 0 := by
    dsimp only [c]
    field_simp [S.coefficient_zero_pos.ne']
  have hone : T.coefficients 1 = c * S.coefficients 1 := by
    have hS := S.recurrence 0
    have hT := T.recurrence 0
    have hdiff :
        mode4PSWFLegendreSuperdiagonal G 0 *
          (T.coefficients 1 - c * S.coefficients 1) = 0 := by
      change
        mode4PSWFLegendreSubdiagonal G 0 * T.coefficients (0 - 1) +
              (mode4PSWFLegendreDiagonal G 0 - (Λ + G)) *
                T.coefficients 0 +
              mode4PSWFLegendreSuperdiagonal G 0 * T.coefficients 1 = 0
        at hT
      change
        mode4PSWFLegendreSubdiagonal G 0 * S.coefficients (0 - 1) +
              (mode4PSWFLegendreDiagonal G 0 - (Λ + G)) *
                S.coefficients 0 +
              mode4PSWFLegendreSuperdiagonal G 0 * S.coefficients 1 = 0
        at hS
      simp only [Nat.zero_sub] at hS hT
      rw [hzero] at hT
      linear_combination hT - c * hS
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hdiff).resolve_left (hsuper 0))
  have hprop : ∀ n : ℕ, T.coefficients n = c * S.coefficients n := by
    intro n
    exact Nat.twoStepInduction
      (P := fun j => T.coefficients j = c * S.coefficients j)
      hzero hone (fun n hn hnSucc => by
        have hS := S.recurrence (n + 1)
        have hT := T.recurrence (n + 1)
        have hdiff :
            mode4PSWFLegendreSuperdiagonal G (n + 1) *
              (T.coefficients (n + 2) -
                c * S.coefficients (n + 2)) = 0 := by
          change
            mode4PSWFLegendreSubdiagonal G (n + 1) *
                  T.coefficients (n + 1 - 1) +
                (mode4PSWFLegendreDiagonal G (n + 1) - (Λ + G)) *
                  T.coefficients (n + 1) +
                mode4PSWFLegendreSuperdiagonal G (n + 1) *
                  T.coefficients (n + 1 + 1) = 0 at hT
          change
            mode4PSWFLegendreSubdiagonal G (n + 1) *
                  S.coefficients (n + 1 - 1) +
                (mode4PSWFLegendreDiagonal G (n + 1) - (Λ + G)) *
                  S.coefficients (n + 1) +
                mode4PSWFLegendreSuperdiagonal G (n + 1) *
                  S.coefficients (n + 1 + 1) = 0 at hS
          simp only [Nat.add_sub_cancel, Nat.add_left_comm,
            Nat.add_comm] at hS hT
          rw [hn, hnSucc] at hT
          linear_combination hT - c * hS
        exact sub_eq_zero.mp
          ((mul_eq_zero.mp hdiff).resolve_left (hsuper (n + 1)))) n
  have hscaled := S.normalized.mul_left (c ^ 2)
  have hscaled' : HasSum
      (fun q : ℕ =>
        (T.coefficients q) ^ 2 / (4 * (q : ℝ) + 1))
      (c ^ 2) := by
    convert hscaled using 1
    · funext q
      rw [hprop q]
      ring
    · ring
  have hcsq : c ^ 2 = 1 := hscaled'.unique T.normalized
  have hc : c = 1 := by nlinarith
  funext n
  rw [hprop n, hc, one_mul]

#print axioms mode4FerrersRegularEvenProlateSolution_coefficients_eq

end Q3.RouteB
