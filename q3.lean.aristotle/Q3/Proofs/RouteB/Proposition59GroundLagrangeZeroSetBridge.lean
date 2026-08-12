import Q3.Proofs.RouteB.Proposition59EntireTransform
import Q3.Proofs.RouteB.CCMFiniteWeilParity

set_option linter.mathlibStandardSet false

/-!
# Proposition 5.9 ground/Lagrange zero-set bridge

Knowledge preflight receipt (2026-08-12):

* `./orchestrator/kb.py ask proposition59RawTransform` returned the journal entry
  `Route B H1c2 raw-integral crosswalk (in progress)`;
* the exact normalized CCM supplier and the combined carrier/Lagrange query returned
  no knowledge-base hits.

The physical source contract is therefore the Route-058 G2b directive.  In particular,
the coordinate below is literally `-L*z/(2*pi)`, the CCM row is transported to the
integer carrier `Finset.Icc (-(N : ℤ)) N`, and the public wrapper ends in the locked
normalized supplier.  This file proves only a conditional finite zero-set transfer.
-/

noncomputable section

namespace Q3.RouteB

open Matrix Polynomial Set
open scoped BigOperators

/-- Exact carrier equivalence between CCM positions and their integer labels. -/
def ccmModeFiniteEquivIcc (N : ℕ) :
    CCMModeFinite N ≃ {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N} := by
  let toMode : CCMModeFinite N → {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N} :=
    fun i => ⟨ccmModeFinite N i, Finset.mem_Icc.mpr (ccmModeFinite_range N i)⟩
  refine Equiv.ofBijective toMode ?_
  constructor
  · intro i j hij
    apply Fin.ext
    have hval := congrArg Subtype.val hij
    change ccmModeFinite N i = ccmModeFinite N j at hval
    simp only [ccmModeFinite] at hval
    omega
  · intro k
    have hk := Finset.mem_Icc.mp k.2
    have hnonneg : 0 ≤ k.1 + (N : ℤ) := by omega
    have hlt : k.1 + (N : ℤ) < (2 * N + 1 : ℕ) := by omega
    have hltNat : (k.1 + (N : ℤ)).toNat < 2 * N + 1 := by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hlt
    let i : CCMModeFinite N := ⟨(k.1 + (N : ℤ)).toNat, hltNat⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    simp only [toMode, i, ccmModeFinite]
    rw [Int.toNat_of_nonneg hnonneg]
    omega

/-- Negation preserves the exact symmetric integer carrier. -/
theorem neg_mem_Icc_of_mem_Icc {N : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(N : ℤ)) N) :
    -k ∈ Finset.Icc (-(N : ℤ)) N := by
  simp only [Finset.mem_Icc] at hk ⊢
  omega

/-- The pole ordering: source mode `n` is attached to the P59 pole labelled `-n`. -/
def ccmPoleModeEquivIcc (N : ℕ) :
    CCMModeFinite N ≃ {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N} where
  toFun i := ⟨-ccmModeFinite N i,
    neg_mem_Icc_of_mem_Icc
      (Finset.mem_Icc.mpr (ccmModeFinite_range N i))⟩
  invFun k := (ccmModeFiniteEquivIcc N).symm
    ⟨-k.1, neg_mem_Icc_of_mem_Icc k.2⟩
  left_inv i := by
    let e := ccmModeFiniteEquivIcc N
    have hsub :
        (⟨-(-ccmModeFinite N i),
          neg_mem_Icc_of_mem_Icc
            (neg_mem_Icc_of_mem_Icc
              (Finset.mem_Icc.mpr (ccmModeFinite_range N i)))⟩ :
            {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N}) = e i := by
      apply Subtype.ext
      simp [e, ccmModeFiniteEquivIcc]
    change e.symm _ = i
    rw [hsub, e.symm_apply_apply]
  right_inv k := by
    let e := ccmModeFiniteEquivIcc N
    have happ := e.apply_symm_apply
      (⟨-k.1, neg_mem_Icc_of_mem_Icc k.2⟩ :
        {n : ℤ // n ∈ Finset.Icc (-(N : ℤ)) N})
    have hval := congrArg Subtype.val happ
    apply Subtype.ext
    change -ccmModeFinite N (e.symm ⟨-k.1, _⟩) = k.1
    change ccmModeFinite N (e.symm ⟨-k.1, _⟩) = -k.1 at hval
    omega

/-- The real CCM row, transported to the Proposition-5.9 pole coordinate.

The negation is intentional: a coefficient at source label `n` is attached to the
P59 pole labelled `-n`, which is exactly what produces the locked coordinate
`-L*z/(2*pi)` rather than its sign-flipped counterfeit.
-/
def proposition59CCMCoefficient
    (N : ℕ) (xi : CCMModeFinite N → ℝ) (k : ℤ) : ℂ :=
  if hk : k ∈ Finset.Icc (-(N : ℤ)) N then
    (xi ((ccmModeFiniteEquivIcc N).symm
      ⟨-k, neg_mem_Icc_of_mem_Icc hk⟩) : ℂ)
  else 0

@[simp] theorem proposition59CCMCoefficient_neg_mode
    (N : ℕ) (xi : CCMModeFinite N → ℝ) (i : CCMModeFinite N) :
    proposition59CCMCoefficient N xi (-ccmModeFinite N i) = (xi i : ℂ) := by
  have hi : -ccmModeFinite N i ∈ Finset.Icc (-(N : ℤ)) N :=
    neg_mem_Icc_of_mem_Icc
      (Finset.mem_Icc.mpr (ccmModeFinite_range N i))
  rw [proposition59CCMCoefficient, dif_pos hi]
  congr 1
  let e := ccmModeFiniteEquivIcc N
  have hsub :
      (⟨-(-ccmModeFinite N i),
        neg_mem_Icc_of_mem_Icc hi⟩ :
          {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N}) = e i := by
    apply Subtype.ext
    simp [e, ccmModeFiniteEquivIcc]
  change xi (e.symm _) = xi i
  rw [hsub, e.symm_apply_apply]

/-- The exact finite P59 transform of a real CCM row, on the literal integer carrier. -/
def proposition59CCMTransform
    (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) : ℂ → ℂ :=
  proposition59RawTransform L (Finset.Icc (-(N : ℤ)) N)
    (proposition59CCMCoefficient N xi)

theorem proposition59CCMTransform_eq_mode_sum
    (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) (z : ℂ) :
    proposition59CCMTransform L N xi z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ i, (xi i : ℂ) *
          proposition59PoleKernel L (-ccmModeFinite N i) z := by
  classical
  unfold proposition59CCMTransform proposition59RawTransform
  congr 1
  let e := ccmPoleModeEquivIcc N
  calc
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        proposition59CCMCoefficient N xi k * proposition59PoleKernel L k z) =
        ∑ k : {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N},
          proposition59CCMCoefficient N xi k.1 *
            proposition59PoleKernel L k.1 z := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (Finset.Icc (-(N : ℤ)) N)
          (fun k => proposition59CCMCoefficient N xi k *
            proposition59PoleKernel L k z)).symm
    _ = ∑ i : CCMModeFinite N,
          proposition59CCMCoefficient N xi (e i).1 *
            proposition59PoleKernel L (e i).1 z := by
      simpa using (e.sum_comp
        (fun k => proposition59CCMCoefficient N xi k.1 *
          proposition59PoleKernel L k.1 z)).symm
    _ = ∑ i, (xi i : ℂ) *
          proposition59PoleKernel L (-ccmModeFinite N i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [e, ccmPoleModeEquivIcc]

private theorem sourceLagrangePolynomial_map_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam xi : ι → ℝ) (s : ℂ) :
    ((sourceLagrangePolynomial lam xi).map (algebraMap ℝ ℂ)).eval s =
      ∑ i, (xi i : ℂ) *
        ∏ j ∈ Finset.univ.erase i, ((lam j : ℂ) - s) := by
  classical
  simp [sourceLagrangePolynomial]

private theorem cauchy_sum_zero_implies_lagrange_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam xi : ι → ℝ) (s : ℂ)
    (hdenom : ∀ i, (lam i : ℂ) - s ≠ 0)
    (hsum : ∑ i, (xi i : ℂ) / ((lam i : ℂ) - s) = 0) :
    ((sourceLagrangePolynomial lam xi).map (algebraMap ℝ ℂ)).eval s = 0 := by
  classical
  rw [sourceLagrangePolynomial_map_eval]
  let D : ℂ := ∏ j, ((lam j : ℂ) - s)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
    intro i hi
    exact hdenom i)
  have hterm (i : ι) :
      ((xi i : ℂ) / ((lam i : ℂ) - s)) * D =
        (xi i : ℂ) *
          ∏ j ∈ Finset.univ.erase i, ((lam j : ℂ) - s) := by
    have hprod :
        D = ((lam i : ℂ) - s) *
          ∏ j ∈ Finset.univ.erase i, ((lam j : ℂ) - s) := by
      exact (Finset.mul_prod_erase Finset.univ
        (fun j => (lam j : ℂ) - s) (Finset.mem_univ i)).symm
    rw [hprod]
    field_simp [hdenom i]
  have hmulk :
      (∑ i, (xi i : ℂ) / ((lam i : ℂ) - s)) * D = 0 := by
    rw [hsum, zero_mul]
  rw [Finset.sum_mul] at hmulk
  simpa only [hterm] using hmulk

/-- The exact P59 Cauchy denominator has the locked `-L*z/(2*pi)` coordinate. -/
private theorem proposition59_denominator_coordinate
    {L : ℝ} (hL : L ≠ 0) (n : ℤ) (z : ℂ) :
    z - proposition59Pole L (-n) =
      (2 * (Real.pi : ℂ) / (L : ℂ)) *
        ((n : ℂ) - (-(L : ℂ) * z / (2 * (Real.pi : ℂ)))) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold proposition59Pole
  field_simp [hLC, hpi]
  simp only [Int.cast_neg]
  ring

/-- A zero of the P59 sine numerator lies on the real lattice when `L ≠ 0`. -/
private theorem proposition59Numerator_zero_im
    {L : ℝ} (hL : L ≠ 0) {z : ℂ}
    (hz : proposition59Numerator L z = 0) : z.im = 0 := by
  have hsin : Complex.sin (z * (L : ℂ) / 2) = 0 := by
    simpa [proposition59Numerator] using hz
  rcases Complex.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  have harg_im := congrArg Complex.im hk
  have him : z.im * L / 2 = 0 := by
    simpa using harg_im
  have him' : z.im * L = 0 := by linarith
  exact (mul_eq_zero.mp him').resolve_right hL

/-- Generic finite transfer for the exact real CCM carrier.

The proof has the three source-required branches: an included removable pole,
an exterior zero of the sine numerator, and an off-lattice Lagrange zero.
-/
theorem proposition59CCMTransform_zerosRealOn_of_lagrange
    (L : ℝ) (hL : 0 < L) (N : ℕ) (xi : CCMModeFinite N → ℝ)
    (hreal : ZerosRealOn Set.univ
      (fun s =>
        ((sourceLagrangePolynomial
          (fun i => (ccmModeFinite N i : ℝ)) xi).map
            (algebraMap ℝ ℂ)).eval s)) :
    ZerosRealOn Set.univ (proposition59CCMTransform L N xi) := by
  classical
  intro z hzmem hzzero
  have hL0 : L ≠ 0 := ne_of_gt hL
  by_cases hpole : ∃ i : CCMModeFinite N,
      z = proposition59Pole L (-ccmModeFinite N i)
  · obtain ⟨i, rfl⟩ := hpole
    simp [proposition59Pole]
  · have hoff : ∀ i : CCMModeFinite N,
        z ≠ proposition59Pole L (-ccmModeFinite N i) := by
      intro i hi
      exact hpole ⟨i, hi⟩
    have hformula :
        proposition59CCMTransform L N xi z =
          ((Real.sqrt L : ℂ)⁻¹) * proposition59Numerator L z *
            ∑ i, (xi i : ℂ) /
              (z - proposition59Pole L (-ccmModeFinite N i)) := by
      rw [proposition59CCMTransform_eq_mode_sum]
      simp_rw [proposition59PoleKernel_eq_quotient hL0 _ (hoff _)]
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hformula] at hzzero
    have hsqrt : (Real.sqrt L : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
    have hzzero' :
        ((Real.sqrt L : ℂ)⁻¹) *
          (proposition59Numerator L z *
            (∑ i, (xi i : ℂ) /
              (z - proposition59Pole L (-ccmModeFinite N i)))) = 0 := by
      simpa only [mul_assoc] using hzzero
    have hfactor :
        proposition59Numerator L z *
          (∑ i, (xi i : ℂ) /
            (z - proposition59Pole L (-ccmModeFinite N i))) = 0 :=
      (mul_eq_zero.mp hzzero').resolve_left (inv_ne_zero hsqrt)
    rcases mul_eq_zero.mp hfactor with hnum | hcauchy
    · exact proposition59Numerator_zero_im hL0 hnum
    · let s : ℂ := -(L : ℂ) * z / (2 * (Real.pi : ℂ))
      let c : ℂ := 2 * (Real.pi : ℂ) / (L : ℂ)
      have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
      have hpiC : (Real.pi : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hc : c ≠ 0 := by
        exact div_ne_zero (mul_ne_zero (by norm_num) hpiC) hLC
      have hcoordinate (i : CCMModeFinite N) :
          z - proposition59Pole L (-ccmModeFinite N i) =
            c * ((ccmModeFinite N i : ℂ) - s) := by
        simpa [s, c] using
          proposition59_denominator_coordinate hL0 (ccmModeFinite N i) z
      have hdenom (i : CCMModeFinite N) :
          (ccmModeFinite N i : ℂ) - s ≠ 0 := by
        intro hzero
        apply hoff i
        apply sub_eq_zero.mp
        rw [hcoordinate i, hzero, mul_zero]
      have hcauchyScaled :
          ∑ i, (xi i : ℂ) /
            (c * ((ccmModeFinite N i : ℂ) - s)) = 0 := by
        simpa only [hcoordinate] using hcauchy
      have hcauchyLagrange :
          ∑ i, (xi i : ℂ) /
            ((ccmModeFinite N i : ℂ) - s) = 0 := by
        calc
          (∑ i, (xi i : ℂ) /
              ((ccmModeFinite N i : ℂ) - s)) =
              c * ∑ i, (xi i : ℂ) /
                (c * ((ccmModeFinite N i : ℂ) - s)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [hc, hdenom i]
          _ = 0 := by rw [hcauchyScaled, mul_zero]
      have hpoly :
          ((sourceLagrangePolynomial
            (fun i => (ccmModeFinite N i : ℝ)) xi).map
              (algebraMap ℝ ℂ)).eval s = 0 :=
        cauchy_sum_zero_implies_lagrange_zero
          (fun i => (ccmModeFinite N i : ℝ)) xi s hdenom hcauchyLagrange
      have hsreal : s.im = 0 := hreal s (Set.mem_univ s) hpoly
      have hsreal' : -(L * z.im) / (2 * Real.pi) = 0 := by
        simpa [s, Complex.div_im, Complex.mul_im, Complex.normSq] using hsreal
      have hLim : L * z.im = 0 := by
        field_simp [Real.pi_ne_zero] at hsreal'
        linarith
      exact (mul_eq_zero.mp hLim).resolve_left hL0

/-- The exact CCM P59 transform is entire independently of the spectral hypotheses. -/
theorem differentiable_proposition59CCMTransform
    (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) :
    Differentiable ℂ (proposition59CCMTransform L N xi) := by
  exact differentiable_proposition59RawTransform
    L (Finset.Icc (-(N : ℤ)) N) (proposition59CCMCoefficient N xi)

/-- Route-058 G2b: the exact Proposition-5.9 transform of the same normalized
simple bottom CCM row has only real zeros.

All spectral facts remain explicit hypotheses.  The final G1-to-G2 supplier is the
literal name-locked `_normalized` declaration; no adjacent wrapper is substituted.
-/
theorem Proposition59GroundLagrangeZeroSetBridge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi =
      epsilon • xi)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1)
    (hbottom : ∀ x : CCMModeFinite N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite mProject N) x)
    (hsimple : Module.finrank ℝ
      ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1)
    (b : Module.Basis ι ℝ
      ((CCMModeFinite N → ℝ) ⧸
        LinearMap.ker
          (Matrix.toBilin'
            (ccmShiftedWeilMatFinite mProject N epsilon)))) :
    ZerosRealOn Set.univ
      (proposition59CCMTransform (ccmL mProject) N xi) := by
  apply proposition59CCMTransform_zerosRealOn_of_lagrange
    (ccmL mProject) (ccmL_pos mProject hm) N xi
  exact
    Q3.RouteB.ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
      mProject N epsilon xi hm hN heig hnormalized hbottom hsimple b

#print axioms ccmModeFiniteEquivIcc
#print axioms proposition59CCMTransform_eq_mode_sum
#print axioms proposition59CCMTransform_zerosRealOn_of_lagrange
#print axioms differentiable_proposition59CCMTransform
#print axioms Proposition59GroundLagrangeZeroSetBridge

end Q3.RouteB
