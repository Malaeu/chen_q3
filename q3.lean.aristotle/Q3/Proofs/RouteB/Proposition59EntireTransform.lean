import Mathlib

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The apparent pole `2*pi*k/L` in Proposition 5.9. -/
def proposition59Pole (L : ℝ) (k : ℤ) : ℂ :=
  (2 * (k : ℂ) * (Real.pi : ℂ)) / (L : ℂ)

/-- Distinct integer modes give distinct Proposition-5.9 lattice points when
the log length is nonzero. -/
theorem proposition59Pole_ne
    {L : ℝ} (hL : L ≠ 0) {j k : ℤ} (hjk : j ≠ k) :
    proposition59Pole L j ≠ proposition59Pole L k := by
  intro h
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold proposition59Pole at h
  field_simp [hLC] at h
  have : (j : ℂ) = (k : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
    simpa [mul_assoc] using h
  apply hjk
  exact_mod_cast this

/-- The common sine numerator in Proposition 5.9. -/
def proposition59Numerator (L : ℝ) (z : ℂ) : ℂ :=
  2 * Complex.sin (z * (L : ℂ) / 2)

theorem proposition59Numerator_at_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    proposition59Numerator L (proposition59Pole L k) = 0 := by
  have harg : proposition59Pole L k * (L : ℂ) / 2 = (k : ℂ) * (Real.pi : ℂ) := by
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    unfold proposition59Pole
    field_simp [hLC]
  unfold proposition59Numerator
  rw [harg, Complex.sin_int_mul_pi]
  simp

/-- The removable-pole kernel in Proposition 5.9.  Using `dslope` makes the
value at the apparent pole part of the definition instead of a side condition. -/
def proposition59PoleKernel (L : ℝ) (k : ℤ) : ℂ → ℂ :=
  dslope (proposition59Numerator L) (proposition59Pole L k)

theorem hasDerivAt_proposition59Numerator (L : ℝ) (z : ℂ) :
    HasDerivAt (proposition59Numerator L)
      ((L : ℂ) * Complex.cos (z * (L : ℂ) / 2)) z := by
  have hlinear : HasDerivAt (fun w : ℂ => w * (L : ℂ) / 2) ((L : ℂ) / 2) z := by
    exact (hasDerivAt_mul_const (L : ℂ)).div_const 2
  have hsin := (Complex.hasDerivAt_sin (z * (L : ℂ) / 2)).comp z hlinear
  have hscaled := hsin.const_mul 2
  convert hscaled using 1
  ring

/-- At its own lattice point the removable kernel has the finite derivative
value `L*cos(pi*k)`, rather than a pole. -/
theorem proposition59PoleKernel_at_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L k) =
      (L : ℂ) * Complex.cos ((k : ℂ) * (Real.pi : ℂ)) := by
  have harg : proposition59Pole L k * (L : ℂ) / 2 = (k : ℂ) * (Real.pi : ℂ) := by
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    unfold proposition59Pole
    field_simp [hLC]
  rw [proposition59PoleKernel, dslope_same,
    (hasDerivAt_proposition59Numerator L (proposition59Pole L k)).deriv, harg]

/-- Away from the removable point, the kernel is exactly the quotient printed
in Proposition 5.9. -/
theorem proposition59PoleKernel_eq_quotient
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) {z : ℂ}
    (hz : z ≠ proposition59Pole L k) :
    proposition59PoleKernel L k z =
      proposition59Numerator L z / (z - proposition59Pole L k) := by
  rw [proposition59PoleKernel, dslope_of_ne _ hz]
  simp [slope, proposition59Numerator_at_pole hL, div_eq_inv_mul, mul_comm]

/-- The full Proposition-5.9 pole row: the removable diagonal entry is the
derivative value and every off-diagonal lattice entry vanishes. -/
theorem proposition59PoleKernel_at_lattice
    {L : ℝ} (hL : L ≠ 0) (k j : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L j) =
      if k = j then
        (L : ℂ) * Complex.cos ((j : ℂ) * (Real.pi : ℂ))
      else 0 := by
  by_cases hkj : k = j
  · subst k
    simp [proposition59PoleKernel_at_pole hL]
  · rw [if_neg hkj, proposition59PoleKernel_eq_quotient hL k]
    · rw [proposition59Numerator_at_pole hL j]
      simp
    · exact proposition59Pole_ne hL (Ne.symm hkj)

/-- The same pole row with its alternating sign made explicit. -/
theorem proposition59PoleKernel_at_lattice_sign
    {L : ℝ} (hL : L ≠ 0) (k j : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L j) =
      if k = j then (L : ℂ) * (j.negOnePow : ℂ) else 0 := by
  rw [proposition59PoleKernel_at_lattice hL]
  congr 1
  rw [show Complex.cos ((j : ℂ) * (Real.pi : ℂ)) = (j.negOnePow : ℂ) by
    have harg : (j : ℂ) * (Real.pi : ℂ) = ((j : ℝ) * Real.pi : ℝ) := by norm_num
    rw [harg, ← Complex.ofReal_cos, Real.cos_int_mul_pi]
    exact_mod_cast (Int.cast_negOnePow ℝ j).symm]

/-- A finite unnormalised kernel sum samples exactly one coefficient at each
lattice point in its carrier. -/
theorem proposition59PoleKernel_sum_at_lattice
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    ∑ k ∈ S, v k * proposition59PoleKernel L k (proposition59Pole L j) =
      v j * ((L : ℂ) * (j.negOnePow : ℂ)) := by
  rw [Finset.sum_eq_single j]
  · rw [proposition59PoleKernel_at_lattice_sign hL]
    simp
  · intro k hk hkj
    rw [proposition59PoleKernel_at_lattice_sign hL, if_neg hkj]
    simp
  · simp [hj]

/-- At the central lattice point the unnormalised finite kernel sum is
`L * v 0`.  This deliberately does not include the raw transform's
`L^(-1/2)` normalisation. -/
theorem proposition59PoleKernel_sum_at_zero
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    ∑ k ∈ S, v k * proposition59PoleKernel L k 0 = (L : ℂ) * v 0 := by
  have hpole0 : proposition59Pole L 0 = 0 := by
    simp [proposition59Pole]
  rw [← hpole0, proposition59PoleKernel_sum_at_lattice hL S v h0]
  simp [mul_comm]

/-- At every lattice point the full pole row has squared `ℓ²` norm exactly
`L²`: its only nonzero entry is the removable diagonal value. -/
theorem proposition59PoleKernel_normSq_hasSum_at_lattice
    {L : ℝ} (hL : L ≠ 0) (j : ℤ) :
    HasSum
      (fun k : ℤ =>
        ‖proposition59PoleKernel L k (proposition59Pole L j)‖ ^ 2)
      (L ^ 2) := by
  have hrow :
      (fun k : ℤ =>
        ‖proposition59PoleKernel L k (proposition59Pole L j)‖ ^ 2) =
      fun k : ℤ => if k = j then L ^ 2 else 0 := by
    funext k
    rw [proposition59PoleKernel_at_lattice_sign hL]
    by_cases hkj : k = j
    · subst k
      simp [Int.cast_negOnePow, sq_abs]
    · simp [hkj]
  rw [hrow]
  exact hasSum_ite_eq j (L ^ 2)

/-- Each apparent-pole summand in Proposition 5.9 is globally entire after
the canonical removable extension. -/
theorem differentiable_proposition59PoleKernel (L : ℝ) (k : ℤ) :
    Differentiable ℂ (proposition59PoleKernel L k) := by
  have hnum : Differentiable ℂ (proposition59Numerator L) := by
    unfold proposition59Numerator
    fun_prop
  have hds : DifferentiableOn ℂ
      (dslope (proposition59Numerator L) (proposition59Pole L k)) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ)
      (c := proposition59Pole L k) univ_mem).2 hnum.differentiableOn
  exact differentiableOn_univ.mp hds

/-- The source-locked finite raw transform in Proposition 5.9.  The factor
`L^(-1/2)` is constant in the spectral variable and is kept exactly. -/
def proposition59RawTransform
    (L : ℝ) (S : Finset ℤ) (xi : ℤ → ℂ) (z : ℂ) : ℂ :=
  ((Real.sqrt L : ℂ)⁻¹) *
    ∑ k ∈ S, xi k * proposition59PoleKernel L k z

/-- The exact central value of the source-locked raw transform, retaining its
explicit `L^(-1/2)` normalisation. -/
theorem proposition59RawTransform_at_zero
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    proposition59RawTransform L S v 0 =
      (Real.sqrt L : ℂ)⁻¹ * ((L : ℂ) * v 0) := by
  unfold proposition59RawTransform
  rw [proposition59PoleKernel_sum_at_zero hL S v h0]

/-- For positive log length the normalised central value is `sqrt L * v 0`,
not the unnormalised value `L * v 0`. -/
theorem proposition59RawTransform_at_zero_eq_sqrt
    {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    proposition59RawTransform L S v 0 = (Real.sqrt L : ℂ) * v 0 := by
  rw [proposition59RawTransform_at_zero hL.ne' S v h0]
  have hsqrt : Real.sqrt L ≠ 0 := Real.sqrt_ne_zero'.mpr hL
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hsqC : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast hsq
  rw [← hsqC]
  field_simp

/-- Proposition 5.9's finite raw transform is entire, with no excluded lattice
points and no pole-cancellation assumption. -/
theorem differentiable_proposition59RawTransform
    (L : ℝ) (S : Finset ℤ) (xi : ℤ → ℂ) :
    Differentiable ℂ (proposition59RawTransform L S xi) := by
  unfold proposition59RawTransform
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro k hk
  exact (differentiable_proposition59PoleKernel L k).const_mul (xi k)

private theorem iteratedDeriv_dslope_second_at_zero (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    iteratedDeriv 2 (dslope f 0) 0 = iteratedDeriv 3 f 0 / 3 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ iteratedDeriv n f 0 / (n.factorial : ℂ))
  have hp : HasFPowerSeriesAt f p 0 := by
    simpa [p] using hf.hasFPowerSeriesAt
  obtain ⟨r, hq⟩ := hp.has_fpower_series_dslope_fslope
  have H := hq.factorial_smul (1 : ℂ) 2
  have H' : iteratedDeriv 2 (dslope f 0) 0 =
      2 * (iteratedDeriv 3 f 0 / 6) := by
    simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_fslope,
      FormalMultilinearSeries.coeff_ofScalars, p,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] using H.symm
  rw [H']
  ring

private theorem proposition59PoleKernel_secondDerivative_zero_of_ne
    {L : ℝ} {k : ℤ} (hL : 0 < L) (hk : k ≠ 0) :
    iteratedDeriv 2 (proposition59PoleKernel L k) 0 =
      -(2 * (L : ℂ)) / proposition59Pole L k ^ 2 := by
  have ha : proposition59Pole L k ≠ 0 := by
    unfold proposition59Pole
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hkC) hpi) hLC
  let q1 : ℂ → ℂ := fun z ↦
    (((L : ℂ) * Complex.cos (z * (L : ℂ) / 2)) *
      (z - proposition59Pole L k) - proposition59Numerator L z) /
        (z - proposition59Pole L k) ^ 2
  have hderiv : deriv (proposition59PoleKernel L k) =ᶠ[𝓝 0] q1 := by
    filter_upwards [eventually_ne_nhds ha.symm] with z hz
    have heq : proposition59PoleKernel L k =ᶠ[𝓝 z]
        (fun w ↦ proposition59Numerator L w /
          (w - proposition59Pole L k)) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact proposition59PoleKernel_eq_quotient hL.ne' k hw
    rw [heq.deriv_eq]
    simpa [q1, Function.id_def] using ((hasDerivAt_proposition59Numerator L z).div
      ((hasDerivAt_id z).sub_const (proposition59Pole L k))
      (sub_ne_zero.mpr hz)).deriv
  have hq1 : HasDerivAt q1 (-(2 * (L : ℂ)) / proposition59Pole L k ^ 2) 0 := by
    dsimp [q1]
    have harg : HasDerivAt (fun z : ℂ ↦ z * (L : ℂ) / 2) ((L : ℂ) / 2) 0 :=
      by simpa using ((hasDerivAt_id 0).mul_const (L : ℂ)).div_const 2
    have hcos : HasDerivAt
        (fun z : ℂ ↦ (L : ℂ) * Complex.cos (z * (L : ℂ) / 2)) 0 0 := by
      have hc := (Complex.hasDerivAt_cos
        (0 * (L : ℂ) / 2)).comp (0 : ℂ) harg
      simpa using hc.const_mul (L : ℂ)
    have hsub : HasDerivAt
        (fun z : ℂ ↦ z - proposition59Pole L k) 1 0 :=
      (hasDerivAt_id 0).sub_const _
    have hnum := (hcos.mul hsub).sub (hasDerivAt_proposition59Numerator L 0)
    have hden := hsub.pow 2
    convert hnum.div hden (by simpa using pow_ne_zero 2 (neg_ne_zero.mpr ha)) using 1 <;>
      simp [proposition59Numerator] <;> field_simp [ha]
  rw [show iteratedDeriv 2 (proposition59PoleKernel L k) 0 =
      deriv (deriv (proposition59PoleKernel L k)) 0 by
        simp [iteratedDeriv_succ]]
  rw [hderiv.deriv_eq, hq1.deriv]

private theorem proposition59PoleKernel_secondDerivative_zero_mode (L : ℝ) :
    iteratedDeriv 2 (proposition59PoleKernel L 0) 0 =
      -((L : ℂ) ^ 3) / 12 := by
  have hnum : AnalyticAt ℂ (proposition59Numerator L) 0 := by
    have hcd : ContDiffAt ℂ ⊤ (proposition59Numerator L) 0 := by
      unfold proposition59Numerator
      fun_prop
    exact hcd.analyticAt
  rw [show proposition59PoleKernel L 0 = dslope (proposition59Numerator L) 0 by
    simp [proposition59PoleKernel, proposition59Pole]]
  rw [iteratedDeriv_dslope_second_at_zero _ hnum]
  have hfun : proposition59Numerator L =
      fun z : ℂ ↦ 2 * Complex.sin (((L : ℂ) / 2) * z) := by
    funext z
    simp [proposition59Numerator]
    congr 2
    ring
  rw [hfun]
  have hf : ContDiffAt ℂ 3
      (fun z : ℂ ↦ Complex.sin (((L : ℂ) / 2) * z)) 0 := by
    fun_prop
  rw [iteratedDeriv_const_mul hf]
  rw [show iteratedDeriv 3 (fun z : ℂ ↦ Complex.sin (((L : ℂ) / 2) * z)) =
      fun z ↦ ((L : ℂ) / 2) ^ 3 *
        iteratedDeriv 3 Complex.sin (((L : ℂ) / 2) * z) by
          exact iteratedDeriv_comp_const_mul Complex.contDiff_sin ((L : ℂ) / 2)]
  rw [Complex.iteratedDeriv_odd_sin 1]
  simp
  ring

/-- The coefficient of a Proposition-5.9 mode in its normalized second jet at
the origin. -/
def proposition59SecondJetCoefficient (k : ℤ) : ℂ :=
  if k = 0 then 1 / 12
  else 1 / (2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2)

theorem proposition59PoleKernel_secondDerivative_zero
    {L : ℝ} (hL : 0 < L) (k : ℤ) :
    iteratedDeriv 2 (proposition59PoleKernel L k) 0 =
      -((L : ℂ) ^ 3) * proposition59SecondJetCoefficient k := by
  by_cases hk : k = 0
  · subst k
    rw [proposition59PoleKernel_secondDerivative_zero_mode]
    simp [proposition59SecondJetCoefficient]
    ring
  · rw [proposition59PoleKernel_secondDerivative_zero_of_ne hL hk]
    simp [proposition59SecondJetCoefficient, hk, proposition59Pole]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hkC, hLC, hpi]

private theorem iteratedDeriv_two_finset_sum
    {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, ContDiffAt ℂ 2 (f i) 0) :
    iteratedDeriv 2 (fun z ↦ ∑ i ∈ S, f i z) 0 =
      ∑ i ∈ S, iteratedDeriv 2 (f i) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
      simp only [Finset.mem_insert] at hf
      rw [show (fun z ↦ ∑ i ∈ insert a S, f i z) =
          (f a + fun z ↦ ∑ i ∈ S, f i z) by
            funext z
            simp [ha]]
      rw [iteratedDeriv_add (hf a (Or.inl rfl))
        (ContDiffAt.sum fun i hi ↦ hf i (Or.inr hi))]
      rw [ih (fun i hi ↦ hf i (Or.inr hi))]
      simp [ha]

private theorem proposition59RawTransform_secondDerivative_zero_as_sum
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) :
    iteratedDeriv 2 (proposition59RawTransform L S v) 0 =
      (Real.sqrt L : ℂ)⁻¹ *
        ∑ k ∈ S, v k *
          (-((L : ℂ) ^ 3) * proposition59SecondJetCoefficient k) := by
  unfold proposition59RawTransform
  rw [iteratedDeriv_const_mul]
  · congr 1
    rw [iteratedDeriv_two_finset_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [iteratedDeriv_const_mul]
      · rw [proposition59PoleKernel_secondDerivative_zero hL]
      · exact (differentiable_proposition59PoleKernel L k).contDiff.contDiffAt.of_le le_top
    · intro k hk
      have hker : ContDiffAt ℂ 2 (proposition59PoleKernel L k) 0 :=
        (differentiable_proposition59PoleKernel L k).contDiff.contDiffAt.of_le le_top
      simpa [smul_eq_mul] using hker.const_smul (v k)
  · apply ContDiffAt.sum
    intro k hk
    have hker : ContDiffAt ℂ 2 (proposition59PoleKernel L k) 0 :=
      (differentiable_proposition59PoleKernel L k).contDiff.contDiffAt.of_le le_top
    simpa [smul_eq_mul] using hker.const_smul (v k)

/-- The exact second jet at the origin of the finite Proposition-5.9 raw
transform on the symmetric lattice window. -/
theorem proposition59RawTransform_secondDerivative_zero
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) :
    iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0 =
      -((L : ℂ) ^ 2 * (Real.sqrt L : ℂ)) *
        (v 0 / 12 + (1 / (2 * (Real.pi : ℂ) ^ 2)) *
          ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
            v k / (k : ℂ) ^ 2) := by
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have h0 : (0 : ℤ) ∈ S := by simp [S]
  rw [proposition59RawTransform_secondDerivative_zero_as_sum hL]
  have hcoeff :
      ∑ k ∈ S, v k * proposition59SecondJetCoefficient k =
        v 0 / 12 + (1 / (2 * (Real.pi : ℂ) ^ 2)) *
          ∑ k ∈ S.erase 0, v k / (k : ℂ) ^ 2 := by
    rw [← Finset.add_sum_erase S _ h0]
    simp only [proposition59SecondJetCoefficient, if_pos]
    rw [show v 0 * (1 / 12) = v 0 / 12 by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      exact fun h ↦ by subst k; simpa using hk
    simp [hk0]
    field_simp
  rw [show (∑ k ∈ S, v k *
      (-((L : ℂ) ^ 3) * proposition59SecondJetCoefficient k)) =
      -((L : ℂ) ^ 3) *
        ∑ k ∈ S, v k * proposition59SecondJetCoefficient k by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring]
  rw [hcoeff]
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  have hsq : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hL.le
  have hscale : (Real.sqrt L : ℂ)⁻¹ * (-((L : ℂ) ^ 3)) =
      -((L : ℂ) ^ 2 * (Real.sqrt L : ℂ)) := by
    rw [← hsq]
    field_simp [hsqrt]
  rw [← mul_assoc, hscale]

private lemma sum_Icc_symmetric {M : Type*} [AddCommMonoid M]
    (N : ℕ) (g : ℤ → M) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g k =
      g 0 + ∑ k ∈ Finset.Icc 1 N, (g k + g (-k)) := by
  erw [show (Finset.Icc (-(N : ℤ)) N : Finset ℤ) =
      Finset.image (fun i : ℕ ↦ (i : ℤ)) (Finset.Icc 0 N) ∪
        Finset.image (fun i : ℕ ↦ -((i : ℤ))) (Finset.Icc 1 N) from ?_,
    Finset.sum_union]
  · norm_num [Finset.sum_add_distrib]
    erw [Finset.Icc_eq_cons_Ioc, Finset.sum_cons] <;> aesop
    rw [add_assoc, Nat.Icc_succ_left]
  · rw [Finset.disjoint_left]
    aesop
  · ext a
    aesop
    exact if h : a ≥ 0 then
      Or.inl ⟨Int.toNat a, by linarith [Int.toNat_of_nonneg h],
        by rw [Int.toNat_of_nonneg h]⟩
    else
      Or.inr ⟨Int.toNat (-a),
        ⟨by linarith [Int.toNat_of_nonneg (by linarith : 0 ≤ -a)],
          by linarith [Int.toNat_of_nonneg (by linarith : 0 ≤ -a)]⟩,
        by rw [Int.toNat_of_nonneg (by linarith : 0 ≤ -a)]; ring⟩

private theorem proposition59SecondJetCoefficient_norm_sq_nat
    (k : ℕ) (hk : 0 < k) :
    ‖proposition59SecondJetCoefficient (k : ℤ)‖ ^ 2 =
      1 / (4 * Real.pi ^ 4 * (k : ℝ) ^ 4) := by
  simp [proposition59SecondJetCoefficient, ne_of_gt hk]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp [hpi, hkR]
  ring

/-- The squared Euclidean norm of the normalized second-jet coefficient row on
any symmetric finite lattice window is at most `1 / 80`. -/
theorem proposition59SecondJetFunctional_norm_sq_le_one_div_eighty (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖proposition59SecondJetCoefficient k‖ ^ 2 ≤ (1 / 80 : ℝ) := by
  rw [sum_Icc_symmetric]
  have hzero : ‖proposition59SecondJetCoefficient 0‖ ^ 2 = (1 / 144 : ℝ) := by
    norm_num [proposition59SecondJetCoefficient, Complex.norm_def, Complex.normSq_apply]
  rw [hzero]
  have heven : ∀ k : ℕ, 0 < k →
      ‖proposition59SecondJetCoefficient (-(k : ℤ))‖ ^ 2 =
        ‖proposition59SecondJetCoefficient (k : ℤ)‖ ^ 2 := by
    intro k hk
    simp [proposition59SecondJetCoefficient, ne_of_gt hk]
  have hpairsum :
      (∑ k ∈ Finset.Icc 1 N,
        (‖proposition59SecondJetCoefficient (k : ℤ)‖ ^ 2 +
          ‖proposition59SecondJetCoefficient (-(k : ℤ))‖ ^ 2)) =
        ∑ k ∈ Finset.Icc 1 N,
          2 * (1 / (4 * Real.pi ^ 4 * (k : ℝ) ^ 4)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    rw [heven k hkpos, proposition59SecondJetCoefficient_norm_sq_nat k hkpos]
    ring
  rw [hpairsum]
  have hsum :
      ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ) ^ 4) ≤ Real.pi ^ 4 / 90 := by
    rw [← hasSum_zeta_four.tsum_eq]
    exact hasSum_zeta_four.summable.sum_le_tsum _ (fun k hk ↦ by positivity)
  have hpi : 0 < Real.pi ^ 4 := pow_pos Real.pi_pos 4
  calc
    1 / 144 + ∑ k ∈ Finset.Icc 1 N,
        2 * (1 / (4 * Real.pi ^ 4 * (k : ℝ) ^ 4))
        = 1 / 144 + (1 / (2 * Real.pi ^ 4)) *
            ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 4 := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              field_simp
              ring
    _ ≤ 1 / 144 + (1 / (2 * Real.pi ^ 4)) * (Real.pi ^ 4 / 90) := by
          gcongr
    _ = 1 / 80 := by
          field_simp [ne_of_gt hpi]
          ring

/-- The finite normalized second-jet coefficient functional. -/
def proposition59SecondJetFunctional (N : ℕ) (v : ℤ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    proposition59SecondJetCoefficient k * v k

theorem proposition59SecondJetFunctional_norm_le_one_div_sqrt_eighty
    (N : ℕ) (v : ℤ → ℂ) :
    ‖proposition59SecondJetFunctional N v‖ ≤
      (1 / Real.sqrt 80) *
        Real.sqrt (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖v k‖ ^ 2) := by
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have htri : ‖proposition59SecondJetFunctional N v‖ ≤
      ∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ * ‖v k‖ := by
    unfold proposition59SecondJetFunctional
    exact (norm_sum_le _ _).trans_eq
      (Finset.sum_congr rfl fun k hk ↦ norm_mul _ _)
  have hcs :
      ∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ * ‖v k‖ ≤
        Real.sqrt (∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ ^ 2) *
          Real.sqrt (∑ k ∈ S, ‖v k‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt S _ _
  have hnorm :
      ∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ ^ 2 ≤ (1 / 80 : ℝ) := by
    simpa [S] using proposition59SecondJetFunctional_norm_sq_le_one_div_eighty N
  have hsqrt :
      Real.sqrt (∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ ^ 2) ≤
        1 / Real.sqrt 80 := by
    calc
      Real.sqrt (∑ k ∈ S, ‖proposition59SecondJetCoefficient k‖ ^ 2) ≤
          Real.sqrt (1 / 80) := Real.sqrt_le_sqrt hnorm
      _ = 1 / Real.sqrt 80 := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
  exact htri.trans
    (hcs.trans (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)))

private theorem proposition59RawTransform_secondDerivative_zero_eq_functional
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℂ) :
    iteratedDeriv 2
        (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) v) 0 =
      -((L : ℂ) ^ 2 * (Real.sqrt L : ℂ)) *
        proposition59SecondJetFunctional N v := by
  rw [proposition59RawTransform_secondDerivative_zero hL]
  unfold proposition59SecondJetFunctional
  congr 1
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have h0 : (0 : ℤ) ∈ S := by simp [S]
  change v 0 / 12 + (1 / (2 * (Real.pi : ℂ) ^ 2)) *
      ∑ k ∈ S.erase 0, v k / (k : ℂ) ^ 2 =
    ∑ k ∈ S, proposition59SecondJetCoefficient k * v k
  rw [← Finset.add_sum_erase S _ h0]
  simp only [proposition59SecondJetCoefficient, if_pos]
  rw [show v 0 / 12 = (1 / 12) * v 0 by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by
    exact fun h ↦ by subst k; simpa using hk
  simp [hk0]
  field_simp

/-- Stability of the finite Proposition-5.9 second jet under an `ℓ²` change of
its coefficient row. -/
theorem proposition59RawTransform_secondDerivative_sub_norm_le
    {L : ℝ} (hL : 0 < L) (N : ℕ) (xi q : ℤ → ℂ) :
    ‖iteratedDeriv 2
          (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) xi) 0 -
        iteratedDeriv 2
          (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) q) 0‖ ≤
      (L ^ 2 * Real.sqrt L / Real.sqrt 80) *
        Real.sqrt (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ‖xi k - q k‖ ^ 2) := by
  rw [proposition59RawTransform_secondDerivative_zero_eq_functional hL,
    proposition59RawTransform_secondDerivative_zero_eq_functional hL]
  have hlin :
      proposition59SecondJetFunctional N xi - proposition59SecondJetFunctional N q =
        proposition59SecondJetFunctional N (fun k ↦ xi k - q k) := by
    unfold proposition59SecondJetFunctional
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← mul_sub, hlin, norm_mul]
  have hscale : ‖-((L : ℂ) ^ 2 * (Real.sqrt L : ℂ))‖ =
      L ^ 2 * Real.sqrt L := by
    rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real]
    simp [abs_of_pos hL, abs_of_nonneg (Real.sqrt_nonneg L)]
  rw [hscale]
  calc
    L ^ 2 * Real.sqrt L *
        ‖proposition59SecondJetFunctional N (fun k ↦ xi k - q k)‖ ≤
      L ^ 2 * Real.sqrt L *
        ((1 / Real.sqrt 80) *
          Real.sqrt (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ‖xi k - q k‖ ^ 2)) := by
              exact mul_le_mul_of_nonneg_left
                (proposition59SecondJetFunctional_norm_le_one_div_sqrt_eighty N
                  (fun k ↦ xi k - q k))
                (mul_nonneg (sq_nonneg L) (Real.sqrt_nonneg L))
    _ = (L ^ 2 * Real.sqrt L / Real.sqrt 80) *
          Real.sqrt (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ‖xi k - q k‖ ^ 2) := by ring

/-- On points avoiding the finite pole lattice, the removable definition is
definitionally the quotient formula from Proposition 5.9. -/
theorem proposition59RawTransform_eq_quotient_sum
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (xi : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    proposition59RawTransform L S xi z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ k ∈ S,
          xi k * (proposition59Numerator L z /
            (z - proposition59Pole L k)) := by
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [proposition59PoleKernel_eq_quotient hL k (hz k hk)]

/-- This is the printed Proposition-5.9 shape: one common sine numerator
times the finite Cauchy sum.  It is asserted only off the finite lattice;
`proposition59RawTransform` itself is defined and entire on all of `ℂ`. -/
theorem proposition59RawTransform_eq_paper_formula
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (xi : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    proposition59RawTransform L S xi z =
      ((Real.sqrt L : ℂ)⁻¹) * proposition59Numerator L z *
        ∑ k ∈ S, xi k / (z - proposition59Pole L k) := by
  rw [proposition59RawTransform_eq_quotient_sum hL S xi hz, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

#print axioms proposition59Numerator_at_pole
#print axioms proposition59Pole_ne
#print axioms proposition59PoleKernel_at_pole
#print axioms proposition59PoleKernel_eq_quotient
#print axioms proposition59PoleKernel_at_lattice
#print axioms proposition59PoleKernel_at_lattice_sign
#print axioms proposition59PoleKernel_sum_at_lattice
#print axioms proposition59PoleKernel_sum_at_zero
#print axioms proposition59PoleKernel_normSq_hasSum_at_lattice
#print axioms differentiable_proposition59PoleKernel
#print axioms proposition59RawTransform_at_zero
#print axioms proposition59RawTransform_at_zero_eq_sqrt
#print axioms differentiable_proposition59RawTransform
#print axioms proposition59PoleKernel_secondDerivative_zero
#print axioms proposition59RawTransform_secondDerivative_zero
#print axioms proposition59SecondJetFunctional_norm_sq_le_one_div_eighty
#print axioms proposition59RawTransform_secondDerivative_sub_norm_le
#print axioms proposition59RawTransform_eq_quotient_sum
#print axioms proposition59RawTransform_eq_paper_formula

end Q3.RouteB
