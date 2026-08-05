import Q3.Proofs.RouteB.D0Mode4PSWFLegendreRecurrenceCrosswalk

/-!
# Uniqueness of the mode-four invariant-cone Riccati orbit

The contraction layer constructs a terminal-independent right tail, while the
source crosswalk supplies the exact even-Legendre recurrence coefficients.
This file proves the missing receiver between those layers: every coherent
all-index orbit in the precommitted cone `[0, 1/2]` is the constructed tail,
and every nonvanishing source-shaped coefficient row in that cone has those
ratios.

Nothing here constructs a PSWF, an ordered differential spectrum, a Weyl
function, a self-adjoint operator, or a Schur-complement inertia theorem.
-/

open Filter Set Topology

noncomputable section

/-- A coherent Riccati orbit is every finite backward composition of any one
of its later values.  Requiring the recurrence at every index is essential. -/
private theorem mode4RiccatiOrbit_eq_backwardTail
    (mProject K : ℕ) (Λ : ℝ)
    (r : ℕ → ℝ)
    (hric :
      ∀ n,
        r n =
          mode4TailMap
            (mode4JacobiG mProject) Λ (K + n)
            (r (n + 1)))
    (n N : ℕ) :
    r n =
      mode4BackwardTail mProject Λ (K + n) N
        (r (n + N)) := by
  induction N generalizing n with
  | zero => simp [mode4BackwardTail]
  | succ N ih =>
      rw [hric n, mode4BackwardTail]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

/-- A coherent Riccati orbit in the certified invariant cone is exactly the
terminal-independent right-tail orbit. -/
theorem mode4RightTailLimit_eq_of_invariantCone_riccatiOrbit
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
    (r : ℕ → ℝ)
    (hrange :
      ∀ n, r n ∈ Set.Icc 0 (1 / 2))
    (hric :
      ∀ n,
        r n =
          mode4TailMap
            (mode4JacobiG mProject) Λ (K + n)
            (r (n + 1))) :
    ∀ n,
      r n =
        mode4RightTailLimit mProject Λ (K + n) := by
  intro n
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKshift : 3 ≤ K + n := le_trans hK hKn
  have hsepShift :
      ∀ q ≥ K + n,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
    intro q hq
    exact hsep q (le_trans hKn hq)
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hlim := mode4BackwardTail_tendsto_rightTailLimit
    mProject (K + n) Λ 0 hm hKshift hsepShift hΛ hzero
  have hdist :
      Tendsto
        (fun N =>
          dist (mode4BackwardTail mProject Λ (K + n) N 0) (r n))
        atTop (𝓝 0) := by
    refine squeeze_zero
      (g := fun N => (3 / 16 : ℝ) ^ N * (1 / 2 : ℝ))
      (fun _ => dist_nonneg) (fun N => ?_) ?_
    · rw [mode4RiccatiOrbit_eq_backwardTail mProject K Λ r hric n N]
      have hlip :=
        (mode4BackwardTail_mapsTo_and_lipschitz
          mProject (K + n) N Λ hm hKshift hsepShift hΛ).2
      calc
        dist (mode4BackwardTail mProject Λ (K + n) N 0)
            (mode4BackwardTail mProject Λ (K + n) N (r (n + N))) ≤
          ((3 / 16 : ℝ) ^ N) * dist (0 : ℝ) (r (n + N)) := by
            simpa using hlip.dist_le_mul 0 hzero (r (n + N)) (hrange (n + N))
        _ ≤ ((3 / 16 : ℝ) ^ N) * (1 / 2 : ℝ) := by
          gcongr
          rw [Real.dist_eq, zero_sub, abs_neg,
            abs_of_nonneg (hrange (n + N)).1]
          exact (hrange (n + N)).2
    · have hpow :
          Tendsto (fun N : ℕ => (3 / 16 : ℝ) ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using hpow.mul_const (1 / 2 : ℝ)
  have hconstToTail :
      Tendsto (fun _ : ℕ => r n) atTop
        (𝓝 (mode4RightTailLimit mProject Λ (K + n))) :=
    hlim.congr_dist hdist
  exact (tendsto_nhds_unique hconstToTail tendsto_const_nhds).symm

/-- A nonvanishing even-Legendre coefficient row satisfying the exact source
recurrence and remaining in the contraction cone has the committed right-tail
ratios. -/
theorem mode4RightTailLimit_eq_ratio_of_pswfLegendre_invariantCone_solution
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
    (a : ℕ → ℝ)
    (ha_ne : ∀ n, a n ≠ 0)
    (hratio :
      ∀ n,
        a (n + 1) / a n ∈ Set.Icc 0 (1 / 2))
    (hrec :
      ∀ n,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) (K + n) * a n +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) (K + n) -
              (Λ + mode4JacobiG mProject)) *
            a (n + 1) +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) (K + n) *
            a (n + 2) = 0) :
    ∀ n,
      a (n + 1) / a n =
        mode4RightTailLimit mProject Λ (K + n) := by
  let G := mode4JacobiG mProject
  let r : ℕ → ℝ := fun n => a (n + 1) / a n
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hric :
      ∀ n,
        r n = mode4TailMap G Λ (K + n) (r (n + 1)) := by
    intro n
    let q := K + n
    have hqK : K ≤ q := by
      unfold q
      omega
    have hq : 3 ≤ q := le_trans hK hqK
    have hcross := mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk G Λ q
    have hsub : mode4PSWFLegendreSubdiagonal G q = -mode4JacobiLower G q := by
      linarith [hcross.1]
    have hdiag :
        mode4PSWFLegendreDiagonal G q - (Λ + G) =
          mode4JacobiCenter G Λ q := hcross.2.1.symm
    have hsuper : mode4PSWFLegendreSuperdiagonal G q = -mode4JacobiUpper G q := by
      linarith [hcross.2.2]
    have hsource := hrec n
    change
      mode4PSWFLegendreSubdiagonal G q * a n +
          (mode4PSWFLegendreDiagonal G q - (Λ + G)) * a (n + 1) +
        mode4PSWFLegendreSuperdiagonal G q * a (n + 2) = 0 at hsource
    rw [hsub, hdiag, hsuper] at hsource
    have hproject :
        mode4JacobiLower G q * a n -
            mode4JacobiCenter G Λ q * a (n + 1) +
          mode4JacobiUpper G q * a (n + 2) = 0 := by
      linarith
    have hdenLower := mode4JacobiCenter_sub_upper_mul_lower_bound
      G Λ (a (n + 2) / a (n + 1)) q hG hq (hsep q hqK) hΛ (hratio (n + 1))
    have hden :
        0 < mode4JacobiCenter G Λ q -
          mode4JacobiUpper G q * (a (n + 2) / a (n + 1)) := by
      linarith
    have hcancel :
        a (n + 1) * (a (n + 2) / a (n + 1)) = a (n + 2) := by
      field_simp [ha_ne (n + 1)]
    unfold r mode4TailMap
    rw [div_eq_div_iff (ha_ne n) hden.ne']
    change
      a (n + 1) *
          (mode4JacobiCenter G Λ q -
            mode4JacobiUpper G q * (a (n + 2) / a (n + 1))) =
        mode4JacobiLower G q * a n
    calc
      a (n + 1) *
            (mode4JacobiCenter G Λ q -
              mode4JacobiUpper G q * (a (n + 2) / a (n + 1))) =
          mode4JacobiCenter G Λ q * a (n + 1) -
            mode4JacobiUpper G q *
              (a (n + 1) * (a (n + 2) / a (n + 1))) := by ring
      _ = mode4JacobiCenter G Λ q * a (n + 1) -
            mode4JacobiUpper G q * a (n + 2) := by rw [hcancel]
      _ = mode4JacobiLower G q * a n := by linarith
  exact mode4RightTailLimit_eq_of_invariantCone_riccatiOrbit
    mProject K Λ hm hK hsep hΛ r hratio hric

#print axioms mode4RightTailLimit_eq_of_invariantCone_riccatiOrbit
#print axioms mode4RightTailLimit_eq_ratio_of_pswfLegendre_invariantCone_solution
