import Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Selected projected Mellin coordinate

This is Goal 056 / Phase 4E.  The module first identifies the chosen
representative of the normalized finite projection with its literal finite
logarithmic Fourier trial almost everywhere.  It then transports that exact
object through the multiplicative Mellin coordinate.

No full-object/Gwin equality, Phase-4B residual crosswalk, decay statement,
`SlotS2`, route promotion, or RH claim is proved here.
-/

/-- The multiplicative Mellin coordinate of the literal normalized projected
trial on the source-locked `dStar` window. -/
noncomputable def selectedProjectedMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  let hNonzero := S.source.trialNonzero i
  ∫ u : ℝ,
      (kTrial_m_N i h hLp hNonzero : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

/-- The normalized projected trial has the exact finite logarithmic Fourier
representative supplied by its source coefficient row, almost everywhere on
the multiplicative window. -/
theorem kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
    (fun u : ℝ =>
      (kTrial_m_N i hTrial_m hE_star hTrialNonzero : H_m i) u)
      =ᵐ[dStar.restrict (I_m i)]
    (fun u : ℝ =>
      finiteLogFourierTrial
        (L_m i)
        (modeSet i)
        (c_n i hTrial_m hE_star hTrialNonzero)
        (Real.log (lambda_m i * u))) := by
  classical
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  let kE : E_m_N i :=
    kTrial_m_N i hTrial_m hE_star hTrialNonzero
  have hprojection : P_m_N i (kE : H_m i) = kE := by
    rw [P_m_N]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self kE
  have hreconstruction :=
    coe_P_m_N_apply_eq_sum_inner_V_n_m_smul i (kE : H_m i)
  rw [hprojection] at hreconstruction
  have hcoe_sum
      (s : Finset ℤ) (f : ℤ → H_m i) :
      (fun u : ℝ => (∑ n ∈ s, f n) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ => ∑ n ∈ s, f n u) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (MeasureTheory.Lp.coeFn_zero ℂ (2 : ℝ≥0∞)
            (dStar.restrict (I_m i)))
    | @insert a s ha ih =>
        have hadd := MeasureTheory.Lp.coeFn_add
          (f a) (∑ n ∈ s, f n)
        have hpoint := hadd.trans
          (Filter.EventuallyEq.rfl.fun_add ih)
        simpa [Finset.sum_insert, ha] using hpoint
  have hmode (n : ℤ) :
      (fun u : ℝ => (V_n_m i n) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n *
              (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  have hterm (n : ℤ) :
      (fun u : ℝ =>
        (c_n i hTrial_m hE_star hTrialNonzero n • V_n_m i n : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        c_n i hTrial_m hE_star hTrialNonzero n *
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i)))) := by
    filter_upwards
      [MeasureTheory.Lp.coeFn_smul
        (c_n i hTrial_m hE_star hTrialNonzero n) (V_n_m i n),
        hmode n] with u hsmul hmode_u
    rw [hsmul]
    change c_n i hTrial_m hE_star hTrialNonzero n * (V_n_m i n) u = _
    rw [hmode_u]
  rw [hreconstruction]
  refine (hcoe_sum (modeSet i)
    (fun n => c_n i hTrial_m hE_star hTrialNonzero n • V_n_m i n)).trans ?_
  have hterms := eventuallyEq_sum
    (s := modeSet i) (fun n _hn => hterm n)
  filter_upwards [hterms] with u hu
  have hu' :
      (∑ n ∈ modeSet i,
        (c_n i hTrial_m hE_star hTrialNonzero n • V_n_m i n : H_m i) u) =
      ∑ n ∈ modeSet i,
        c_n i hTrial_m hE_star hTrialNonzero n *
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    simpa only [Finset.sum_apply] using hu
  rw [hu']
  unfold finiteLogFourierTrial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hexponent :
      2 * Real.pi * Complex.I * n *
          (Real.log (lambda_m i * u) / L_m i) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L_m i : ℂ) *
          (Real.log (lambda_m i * u) : ℂ) := by
    ring
  rw [hexponent]
  ring

/-- The Mellin coordinate of the literal selected normalized projection is
the source-locked reflected raw transform of its exact coefficient row. -/
theorem selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedProjectedMellinCoordinate S k z =
      selectedRawTransformCoordinate S k z := by
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  let hNonzero := S.source.trialNonzero i
  let c : ℤ → ℂ := c_n i h hLp hNonzero
  let phase : ℂ :=
    Complex.exp (Complex.I * z * (L_m i : ℂ) / 2)
  have hlam_pos : 0 < lambda_m i := by
    unfold lambda_m
    apply Real.sqrt_pos.mpr
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hlog_lambda : Real.log (lambda_m i) = L_m i / 2 := by
    rw [lambda_m, Real.log_sqrt]
    · rfl
    · positivity
  have hmem :
      ∀ᵐ u : ℝ ∂(dStar.restrict (I_m i)), u ∈ I_m i :=
    ae_restrict_mem measurableSet_Icc
  have hkernel :
      (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        phase *
          Complex.exp
            (-Complex.I * z *
              (Real.log (lambda_m i * u) : ℂ))) := by
    filter_upwards [hmem] with u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam_pos).trans_le hu.1
    have hlog_u :
        Real.log u =
          Real.log (lambda_m i * u) - L_m i / 2 := by
      rw [Real.log_mul hlam_pos.ne' hu_pos.ne', hlog_lambda]
      ring
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hu_pos.ne')]
    rw [← Complex.ofReal_log hu_pos.le]
    rw [hlog_u]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrep :=
    kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
      i h hLp hNonzero
  have hintegrand :
      (fun u : ℝ =>
        (kTrial_m_N i h hLp hNonzero : H_m i) u *
          (u : ℂ) ^ (-Complex.I * z))
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        phase *
          (finiteLogFourierTrial
              (L_m i) (modeSet i) c
              (Real.log (lambda_m i * u)) *
            Complex.exp
              (-Complex.I * z *
                (Real.log (lambda_m i * u) : ℂ)))) := by
    filter_upwards [hrep, hkernel] with u hrep_u hkernel_u
    rw [hrep_u, hkernel_u]
    ring
  have htransport :
      (∫ u : ℝ,
          finiteLogFourierTrial
              (L_m i) (modeSet i) c
              (Real.log (lambda_m i * u)) *
            Complex.exp
              (-Complex.I * z *
                (Real.log (lambda_m i * u) : ℂ))
        ∂(dStar.restrict (I_m i))) =
      ∫ x : ℝ in Set.Icc 0 (L_m i),
        finiteLogFourierTrial (L_m i) (modeSet i) c x *
          Complex.exp (-Complex.I * z * (x : ℂ)) := by
    simpa using
      (integral_comp_logWindow_dStar i
        (fun x : ℝ =>
          finiteLogFourierTrial (L_m i) (modeSet i) c x *
            Complex.exp (-Complex.I * z * (x : ℂ))))
  have hcoordinate :
      (∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
        ∂(dStar.restrict (I_m i))) =
      finiteRawCenteredIntegral (L_m i) (modeSet i) c z := by
    calc
      _ = ∫ u : ℝ,
            phase *
              (finiteLogFourierTrial
                  (L_m i) (modeSet i) c
                  (Real.log (lambda_m i * u)) *
                Complex.exp
                  (-Complex.I * z *
                    (Real.log (lambda_m i * u) : ℂ)))
          ∂(dStar.restrict (I_m i)) := integral_congr_ae hintegrand
      _ = phase *
          ∫ u : ℝ,
            finiteLogFourierTrial
                (L_m i) (modeSet i) c
                (Real.log (lambda_m i * u)) *
              Complex.exp
                (-Complex.I * z *
                  (Real.log (lambda_m i * u) : ℂ))
            ∂(dStar.restrict (I_m i)) := by
              rw [integral_const_mul]
      _ = phase *
          ∫ x : ℝ in Set.Icc 0 (L_m i),
            finiteLogFourierTrial (L_m i) (modeSet i) c x *
              Complex.exp (-Complex.I * z * (x : ℂ)) := by
              rw [htransport]
      _ = phase *
          ∫ x : ℝ in 0..L_m i,
            finiteLogFourierTrial (L_m i) (modeSet i) c x *
              Complex.exp (-Complex.I * z * (x : ℂ)) := by
              rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
              rw [← intervalIntegral.integral_of_le (logLength_pos i).le]
      _ = finiteRawCenteredIntegral (L_m i) (modeSet i) c z := by
              rfl
  have hcoeff :
      c = S.canonical.kTrial.kTrial i := by
    funext n
    exact (selectedCanonical_kTrial S k n).symm
  have hraw := rawFplus_eq_D0_integral S.canonical.kTrial i (-z)
  rw [finiteFplusCenteredIntegral_eq_raw_neg] at hraw
  simp only [neg_neg] at hraw
  calc
    selectedProjectedMellinCoordinate S k z =
        ∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by rfl
    _ = finiteRawCenteredIntegral (L_m i) (modeSet i) c z := hcoordinate
    _ = finiteRawCenteredIntegral (L_m i) (modeSet i)
          (S.canonical.kTrial.kTrial i) z := by rw [hcoeff]
    _ = rawFplus S.canonical.kTrial i (-z) := hraw
    _ = selectedRawTransformCoordinate S k z := by rfl

#print axioms kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
#print axioms selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate

end Q3.RouteB.D0Pstar
