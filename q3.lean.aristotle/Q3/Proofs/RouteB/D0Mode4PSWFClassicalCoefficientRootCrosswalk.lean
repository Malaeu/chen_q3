import Q3.Proofs.RouteB.D0Mode4PSWFLegendreBoundaryFluxIdentification

/-!
# Degree-four DLMF coefficient row forces the current matching root

This file closes the finite-left side of the classical coefficient crosswalk.
A supplied reindexed degree-four/order-zero DLMF row with its literal
30.8.4 recurrence and raw 30.8.5 normalization is nonzero at coefficient
zero, agrees with the committed normalized left solution, and has the exact
canonical minimal-tail boundary flux.  Consequently it forces the literal
current `mode4RootFunction` equality.

This is not a classical PSWF existence theorem.  In particular, it does not
construct the indexed `psi_4` row, identify an arbitrary regular solution as
the third even mode, prove a finite-Fourier relation, or address mode zero.
-/

noncomputable section

/-- A literal reindexed DLMF degree-four coefficient row forces the current
left/right matching equation.  Unlike the older canonical-tail receiver, the
normalization here is the raw degree-four value `1 / 9`; its exact rescaling
to the project unit normalization is internal. -/
theorem mode4DLMF3084_3085_degreeFour_coefficients_force_root
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
    mode4RootFunction mProject K Λ = 0 := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hproject : ∀ q : ℕ,
      mode4JacobiLower G q * a (q - 1) -
        mode4JacobiCenter G Λ q * a q +
        mode4JacobiUpper G q * a (q + 1) = 0 := by
    intro q
    have hsource := h3084 q
    have hsub :
        mode4PSWFLegendreSubdiagonal G q =
          -mode4JacobiLower G q := by
      linarith [mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal G q]
    have hdiag :
        mode4PSWFLegendreDiagonal G q - (Λ + G) =
          mode4JacobiCenter G Λ q :=
      (mode4JacobiCenter_eq_pswfLegendreDiagonal_shift G Λ q).symm
    have hsuper :
        mode4PSWFLegendreSuperdiagonal G q =
          -mode4JacobiUpper G q := by
      linarith [mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal G q]
    rw [hsub, hdiag, hsuper] at hsource
    linarith
  have hglobal : ∃ q : ℕ, a q ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero :
        HasSum
          (fun q : ℕ =>
            (a q) ^ 2 / (4 * (q : ℝ) + 1))
          0 := by
      simpa [h] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
    have hone : (1 / 9 : ℝ) = 0 := h3085.unique hzero
    norm_num at hone
  have ha0 : a 0 ≠ 0 := by
    intro ha0
    have ha1 : a 1 = 0 := by
      have hrec := hproject 0
      have hUne : mode4JacobiUpper G 0 ≠ 0 :=
        (mode4JacobiUpper_pos G 0 hG).ne'
      have hmul : mode4JacobiUpper G 0 * a 1 = 0 := by
        simpa [ha0, mode4JacobiLower, mode4JacobiIndex] using hrec
      exact (mul_eq_zero.mp hmul).resolve_left hUne
    have hall : ∀ q : ℕ, a q = 0 := by
      intro q
      exact Nat.twoStepInduction
        (P := fun n => a n = 0)
        ha0 ha1
        (fun n hn hn1 => by
          have hrec := hproject (n + 1)
          have hprev : n + 1 - 1 = n := by omega
          have hnext : n + 1 + 1 = n + 2 := by omega
          rw [hprev, hnext, hn, hn1] at hrec
          simp only [mul_zero, zero_add, sub_zero] at hrec
          exact (mul_eq_zero.mp hrec).resolve_left
            (mode4JacobiUpper_pos G (n + 1) hG).ne')
        q
    rcases hglobal with ⟨q, hq⟩
    exact hq (hall q)
  let aPrev : ℕ → ℝ := fun q => if q = 0 then 0 else a (q - 1)
  have hprojectPrev : ∀ q : ℕ,
      mode4JacobiLower G q * aPrev q -
        mode4JacobiCenter G Λ q * a q +
        mode4JacobiUpper G q * a (q + 1) = 0 := by
    intro q
    cases q with
    | zero =>
        simpa [aPrev, mode4JacobiLower, mode4JacobiIndex] using hproject 0
    | succ q =>
        simpa [aPrev] using hproject (q + 1)
  have hleft : ∀ q : ℕ,
      mode4LeftPair G Λ q =
        (aPrev q / a 0, a q / a 0) := by
    intro q
    induction q with
    | zero =>
        simp [mode4LeftPair, aPrev, ha0]
    | succ q ih =>
        rw [mode4LeftPair]
        rw [ih]
        apply Prod.ext
        · simp [aPrev]
        · dsimp
          have hUne : mode4JacobiUpper G q ≠ 0 :=
            (mode4JacobiUpper_pos G q hG).ne'
          rw [div_eq_iff hUne]
          field_simp [ha0]
          linarith [hprojectPrev q]
  have hflux :=
    mode4DLMF3084_3085_degreeFour_sourceBoundaryFlux_eq_schurCorrection
      mProject K Λ a hm hK hsep hΛ h3084 h3085
  have htailPos : 0 < mode4RightTailLimit mProject Λ K :=
    mode4RightTailLimit_pos mProject K Λ hm hK hsep hΛ
  have hUne : mode4JacobiUpper G (K - 1) ≠ 0 :=
    (mode4JacobiUpper_pos G (K - 1) hG).ne'
  have haKm1 : a (K - 1) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, div_zero, mul_zero] at hflux
    have hright :
        0 < mode4JacobiUpper G (K - 1) *
          mode4RightTailLimit mProject Λ K :=
      mul_pos (mode4JacobiUpper_pos G (K - 1) hG) htailPos
    linarith
  have hscale0 := mode4TailHermitianScale_zero_eq_one K hK
  have hbalance := mode4TailHermitianScale_boundary_balance_eq G K hG hK
  rw [hscale0] at hflux hbalance
  field_simp [haKm1] at hflux
  have hflux' :
      mode4JacobiUpper G (K - 1) * a K =
        mode4JacobiUpper G (K - 1) *
          (mode4RightTailLimit mProject Λ K * a (K - 1)) := by
    calc
      mode4JacobiUpper G (K - 1) * a K =
          (mode4JacobiSymmetricOff G (K - 1) *
              mode4TailHermitianScale K 1) * a K := by
        rw [hbalance]
        ring
      _ = mode4JacobiUpper G (K - 1) *
          (mode4RightTailLimit mProject Λ K * a (K - 1)) := by
        nlinarith [hflux]
  have haK :
      a K = mode4RightTailLimit mProject Λ K * a (K - 1) :=
    mul_left_cancel₀ hUne hflux'
  apply (mode4RootFunction_eq_zero_iff_match mProject K Λ).2
  rw [hleft K]
  have hKne : K ≠ 0 := by omega
  simp only [aPrev, if_neg hKne]
  field_simp [ha0]
  exact haK

#print axioms mode4DLMF3084_3085_degreeFour_coefficients_force_root
