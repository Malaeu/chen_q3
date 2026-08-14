import Q3.Proofs.RouteB.D0Mode4PSWFLegendreCanonicalIdentification

/-!
# Conditional DLMF source-tail boundary ratio and flux

The nonzero proportionality scalar from the conditional DLMF 30.8.4--30.8.5
identification cancels in the first shifted Hermitian tail ratio.  Consequently
the anonymous source row has exactly the canonical boundary flux already used
by the finite Hermitian Schur correction.

This file remains conditional on the supplied sequence and its DLMF-shaped
hypotheses.  It does not construct or identify a regular PSWF source object.
-/

noncomputable section

/-- The first shifted Hermitian ratio of a conditional DLMF coefficient row is
the canonical Hermitian tail ratio. -/
theorem mode4DLMF3084_3085_shiftedBoundaryRatio_eq_canonical
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
    (mode4TailHermitianScale K 1 * a K) /
        (mode4TailHermitianScale K 0 * a (K - 1)) =
      mode4HermitianTailCoefficientRow mProject Λ K 1 /
        mode4HermitianTailCoefficientRow mProject Λ K 0 := by
  rcases mode4DLMF3084_3085_shiftedHermitianTail_eq_c_mul_canonical
      mProject K Λ a hm hK hsep hΛ h3084 h3085 with
    ⟨c, hc, hrow⟩
  have hrowZero := hrow 0
  have hrowOne := hrow 1
  have hidxZero : K - 1 + 0 = K - 1 := by omega
  have hidxOne : K - 1 + 1 = K := by omega
  rw [hidxZero] at hrowZero
  rw [hidxOne] at hrowOne
  rw [hrowZero, hrowOne,
    mode4HermitianTailCoefficientRow_zero mProject K Λ hK]
  field_simp [hc]

/-- The shifted source boundary flux equals the already committed finite
Hermitian Schur correction. -/
theorem mode4DLMF3084_3085_sourceBoundaryFlux_eq_schurCorrection
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
    mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) *
        ((mode4TailHermitianScale K 1 * a K) /
          (mode4TailHermitianScale K 0 * a (K - 1))) =
      mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
        mode4RightTailLimit mProject Λ K := by
  rw [mode4DLMF3084_3085_shiftedBoundaryRatio_eq_canonical
    mProject K Λ a hm hK hsep hΛ h3084 h3085]
  exact mode4HermitianTail_boundaryFlux_eq_schurCorrection
    mProject K Λ hm hK

/-- Degree-four/order-zero version of the shifted boundary-ratio theorem.
The raw DLMF 30.8.5 sum is `1 / 9`; the factor `3` needed by the current
unit-normalized tail cancels from the ratio. -/
theorem mode4DLMF3084_3085_degreeFour_shiftedBoundaryRatio_eq_canonical
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
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        (1 / 9 : ℝ)) :
    (mode4TailHermitianScale K 1 * a K) /
        (mode4TailHermitianScale K 0 * a (K - 1)) =
      mode4HermitianTailCoefficientRow mProject Λ K 1 /
        mode4HermitianTailCoefficientRow mProject Λ K 0 := by
  rcases
      mode4DLMF3084_3085_degreeFour_rescaledTail_eq_c_mul_canonical
        mProject K Λ a hm hK hsep hΛ h3084 h3085 with
    ⟨c, hc, hrow⟩
  have hrowZero := hrow 0
  have hrowOne := hrow 1
  have hidxZero : K - 1 + 0 = K - 1 := by omega
  have hidxOne : K - 1 + 1 = K := by omega
  rw [hidxZero] at hrowZero
  rw [hidxOne] at hrowOne
  rw [mode4HermitianTailCoefficientRow_zero mProject K Λ hK]
  rw [mode4HermitianTailCoefficientRow_zero mProject K Λ hK] at hrowZero
  norm_num at hrowZero ⊢
  have hden :
      mode4TailHermitianScale K 0 * a (K - 1) ≠ 0 := by
    intro hzero
    have hcZero : c = 0 := by
      calc
        c = mode4TailHermitianScale K 0 * (3 * a (K - 1)) :=
          hrowZero.symm
        _ = 3 * (mode4TailHermitianScale K 0 * a (K - 1)) := by ring
        _ = 0 := by rw [hzero, mul_zero]
    exact hc hcZero
  apply (div_eq_iff hden).2
  linear_combination
    (1 / 3 : ℝ) * hrowOne -
      (mode4HermitianTailCoefficientRow mProject Λ K 1 / 3) * hrowZero

/-- Degree-four/order-zero raw DLMF normalization supplies the exact current
Schur boundary flux after the `1 / 9 -> 1` coefficient rescaling. -/
theorem mode4DLMF3084_3085_degreeFour_sourceBoundaryFlux_eq_schurCorrection
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
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        (1 / 9 : ℝ)) :
    mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) *
        ((mode4TailHermitianScale K 1 * a K) /
          (mode4TailHermitianScale K 0 * a (K - 1))) =
      mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
        mode4RightTailLimit mProject Λ K := by
  rw [mode4DLMF3084_3085_degreeFour_shiftedBoundaryRatio_eq_canonical
    mProject K Λ a hm hK hsep hΛ h3084 h3085]
  exact mode4HermitianTail_boundaryFlux_eq_schurCorrection
    mProject K Λ hm hK

#print axioms mode4DLMF3084_3085_shiftedBoundaryRatio_eq_canonical
#print axioms mode4DLMF3084_3085_sourceBoundaryFlux_eq_schurCorrection
#print axioms mode4DLMF3084_3085_degreeFour_shiftedBoundaryRatio_eq_canonical
#print axioms mode4DLMF3084_3085_degreeFour_sourceBoundaryFlux_eq_schurCorrection
