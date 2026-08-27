import Q3.Proofs.RouteB.CCMFiniteWeilEtaNonzero
import Q3.Proofs.RouteB.SimpleEvenGroundSectorCriterion
import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementSpectral
import Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities
import Q3.Proofs.RouteB.LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Matrix Filter
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — selected Ferrers ground parity, realification, eta normalization

Verdict `REQ-2026-08-26-N`.  The odd-sector floor stays an explicit input;
odd strictness is DERIVED from it rather than minted as a new supplier.
Evenness is established BEFORE eta normalization, the real representative is
built from realness of the CCM matrix, and eta normalization is discharged by
the existing `CCMFiniteWeilEtaNonzero` suppliers.

No `heta` hypothesis, no trial-equals-ground assumption, no quotient basis
input, no numerics, no schedule change, no H2a/SlotS2/RH claim.
-/

/-! ## Step 0: local reconstructions (upstream copies are private) -/

private theorem gpr_hermitian_quadratic_real
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (x : ι → ℂ) :
    ((star x ⬝ᵥ (A *ᵥ x)).re : ℂ) = star x ⬝ᵥ (A *ᵥ x) := by
  have hconj : (starRingEnd ℂ) (star x ⬝ᵥ (A *ᵥ x)) =
      star x ⬝ᵥ (A *ᵥ x) := by
    calc (starRingEnd ℂ) (star x ⬝ᵥ (A *ᵥ x))
        = star (star x ⬝ᵥ (A *ᵥ x)) := rfl
      _ = star (A *ᵥ x) ⬝ᵥ star (star x) := by
          simp [dotProduct, map_sum, mul_comm]
      _ = star (A *ᵥ x) ⬝ᵥ x := by rw [star_star]
      _ = star x ⬝ᵥ (A *ᵥ x) := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hA.eq]
  exact (Complex.conj_eq_iff_re.mp hconj)

/-! ## Step 1: the selected ground extraction -/

/-- Ground extraction on the exact selected finite CCM cell: literal matrix,
literal unit trial row, exact Rayleigh shift and exact residual. -/
private theorem gpr_ground_extraction
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (beta : ℝ)
    (hfloor :
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
        beta) :
    ∃ (epsilon : ℝ) (xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ),
      complexHermitianGroundGapAtLeast
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0 ∧
      1 - Complex.normSq
          (star xi0 ⬝ᵥ selectedFerrersFiniteCCMRow P k) ≤
        (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
          selectedFerrersFiniteCCMResidual P k).re / beta ^ 2 := by
  classical
  haveI : Nonempty (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :=
    ⟨ccmCenterFinite _⟩
  refine hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
    (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
    (selectedFerrersFiniteCCMRow P k)
    (selectedFerrersFiniteCCMResidual P k)
    (selectedFerrersFiniteCCMRayleigh P k) beta
    (sourceCCMFiniteMatrix_isHermitian _)
    (selectedFerrersFiniteCCMRow_unit P k)
    ?_ rfl hfloor
  rw [selectedFerrersFiniteCCMRayleigh]
  exact gpr_hermitian_quadratic_real _
    (sourceCCMFiniteMatrix_isHermitian _) _

/-! ## Step 2: parity dichotomy of the ground line -/

/-- The ground eigenline is reflection-even or reflection-odd.  Only
commutation and the ground gap are used; no parity is assumed. -/
private theorem gpr_parity_dichotomy
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon beta : ℝ} (hbeta : 0 < beta)
    {xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hgap : complexHermitianGroundGapAtLeast
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0) :
    (ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ xi0 = xi0) ∨
    (ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ xi0 = -xi0) := by
  classical
  obtain ⟨hunit, heig, hbottom, hcomp⟩ := hgap
  set J := ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N with hJ
  set K := sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) with hK
  have hxi_ne : xi0 ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  -- reflected ground vector is again a ground eigenvector
  have hJeig : K *ᵥ (J *ᵥ xi0) = (epsilon : ℂ) • (J *ᵥ xi0) := by
    rw [Matrix.mulVec_mulVec, hJ, hK,
      sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul]
  set c : ℂ := star xi0 ⬝ᵥ (J *ᵥ xi0) with hcdef
  set w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ := J *ᵥ xi0 - c • xi0 with hw
  have hproj : star xi0 ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit, mul_one,
      ← hcdef, sub_self]
  have hweig : K *ᵥ w = (epsilon : ℂ) • w := by
    rw [hw, Matrix.mulVec_sub, hJeig, Matrix.mulVec_smul, heig,
      smul_comm, smul_sub]
  have hwzero : w = 0 := by
    by_contra hne
    have hpos : 0 < (star w ⬝ᵥ w).re := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hwj : w j ≠ 0 := by simpa using hj
      have hjpos : 0 < Complex.normSq (w j) := Complex.normSq_pos.mpr hwj
      simpa [Complex.normSq, dotProduct] using
        (show 0 < ∑ i, Complex.normSq (w i) from
          Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (w i))
            ⟨j, Finset.mem_univ j, hjpos⟩)
    have hgapw := hcomp w hproj
    have henergy : (star w ⬝ᵥ (K *ᵥ w)).re = epsilon * (star w ⬝ᵥ w).re := by
      rw [hweig, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [henergy] at hgapw
    nlinarith [hgapw, hpos, hbeta]
  have hc : J *ᵥ xi0 = c • xi0 := by
    have h0 : J *ᵥ xi0 - c • xi0 = 0 := by rw [← hw, hwzero]
    exact sub_eq_zero.mp h0
  have hcc : (c * c) • xi0 = xi0 := by
    calc (c * c) • xi0 = c • (c • xi0) := by
          rw [smul_smul]
      _ = c • (J *ᵥ xi0) := by rw [← hc]
      _ = J *ᵥ (c • xi0) := by rw [Matrix.mulVec_smul]
      _ = J *ᵥ (J *ᵥ xi0) := by rw [hc]
      _ = xi0 := by
          rw [Matrix.mulVec_mulVec, hJ, ccmComplexReflectionMatrix_sq,
            Matrix.one_mulVec]
  have hc2 : c * c = 1 := by
    have hsub : (c * c - 1) • xi0 = 0 := by
      rw [sub_smul, hcc, one_smul, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hxi_ne
  rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
  · left
    rw [hc, h1, one_smul]
  · right
    rw [hc, h1, neg_one_smul]

/-! ## Step 3: the odd branch dies against the odd-sector floor -/

/-- **Derived odd strictness.**  The retained odd-sector floor at the exact
Rayleigh shift, positivity of `beta0`, and `epsilon ≤ Rayleigh` make an odd
ground line impossible.  Odd strictness is derived cargo, not a new input. -/
private theorem gpr_ground_is_even
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon beta beta0 : ℝ} (hbeta : 0 < beta) (hbeta0 : 0 < beta0)
    {xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hgap : complexHermitianGroundGapAtLeast
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0)
    (hoddFloor :
      ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ,
        ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
        beta0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
                  (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) ℂ)) *ᵥ x)).re) :
    ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ xi0 = xi0 := by
  classical
  obtain ⟨hunit, heig, hbottom, hcomp⟩ := hgap
  rcases gpr_parity_dichotomy P k hbeta ⟨hunit, heig, hbottom, hcomp⟩ with
    heven | hodd
  · exact heven
  · exfalso
    -- the unit trial row realizes the Rayleigh value, so epsilon ≤ Rayleigh
    have hrow_unit := selectedFerrersFiniteCCMRow_unit P k
    have hbot := hbottom (selectedFerrersFiniteCCMRow P k)
    have hrow_re : (star (selectedFerrersFiniteCCMRow P k) ⬝ᵥ
        selectedFerrersFiniteCCMRow P k).re = 1 := by
      rw [hrow_unit]
      norm_num
    have heps_le : epsilon ≤ selectedFerrersFiniteCCMRayleigh P k := by
      rw [hrow_re, mul_one] at hbot
      rw [selectedFerrersFiniteCCMRayleigh]
      exact hbot
    -- the odd floor applied to the ground vector itself
    have hfl := hoddFloor xi0 hodd
    have hunit_re : (star xi0 ⬝ᵥ xi0).re = 1 := by
      rw [hunit]
      norm_num
    have henergy :
        (star xi0 ⬝ᵥ
          ((sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) -
            ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
              (1 : Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
                (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) ℂ)) *ᵥ xi0)).re =
        epsilon - selectedFerrersFiniteCCMRayleigh P k := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_sub, heig, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, hunit, mul_one, mul_one, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_re]
    rw [hunit_re, mul_one, henergy] at hfl
    linarith

/-! ## Step 4: realification of the ground line -/

/-- Real and imaginary parts of a complexified-real eigenvector are
themselves real eigenvectors at the same real eigenvalue. -/
private theorem gpr_re_im_eigen
    (mProject N : ℕ) (epsilon : ℝ)
    {xi : CCMModeFinite N → ℂ}
    (heig : (fun j l => ((ccmWeilMatFinite mProject N j l : ℝ) : ℂ)) *ᵥ xi =
      (epsilon : ℂ) • xi) :
    Matrix.mulVec (ccmWeilMatFinite mProject N) (fun j => (xi j).re) =
        epsilon • (fun j => (xi j).re) ∧
      Matrix.mulVec (ccmWeilMatFinite mProject N) (fun j => (xi j).im) =
        epsilon • (fun j => (xi j).im) := by
  classical
  have hcoord : ∀ j,
      ∑ l, ((ccmWeilMatFinite mProject N j l : ℝ) : ℂ) * xi l =
        (epsilon : ℂ) * xi j := by
    intro j
    have := congrFun heig j
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
  constructor
  · funext j
    have h := congrArg Complex.re (hcoord j)
    rw [Complex.re_sum] at h
    have hleft : ∑ l, (((ccmWeilMatFinite mProject N j l : ℝ) : ℂ) * xi l).re =
        ∑ l, ccmWeilMatFinite mProject N j l * (xi l).re := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hleft] at h
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at h
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using h
  · funext j
    have h := congrArg Complex.im (hcoord j)
    rw [Complex.im_sum] at h
    have hleft : ∑ l, (((ccmWeilMatFinite mProject N j l : ℝ) : ℂ) * xi l).im =
        ∑ l, ccmWeilMatFinite mProject N j l * (xi l).im := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hleft] at h
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using h

/-- A nonzero complex vector has a nonzero real or imaginary part. -/
private theorem gpr_re_or_im_ne_zero
    {N : ℕ} {xi : CCMModeFinite N → ℂ} (hne : xi ≠ 0) :
    (fun j => (xi j).re) ≠ 0 ∨ (fun j => (xi j).im) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  apply hne
  funext j
  have h1 : (xi j).re = 0 := congrFun hre j
  have h2 : (xi j).im = 0 := congrFun him j
  exact Complex.ext h1 h2

/-- Evenness of the complex ground vector transfers to both real parts. -/
private theorem gpr_parts_even
    {N : ℕ} {xi : CCMModeFinite N → ℂ}
    (heven : ccmComplexReflectionMatrix N *ᵥ xi = xi) :
    (∀ j, (xi (ccmNegFinite N j)).re = (xi j).re) ∧
      (∀ j, (xi (ccmNegFinite N j)).im = (xi j).im) := by
  have hpt : ∀ j, xi (ccmNegFinite N j) = xi j := by
    intro j
    have := congrFun heven j
    rwa [ccmComplexReflectionMatrix_mulVec] at this
  exact ⟨fun j => by rw [hpt j], fun j => by rw [hpt j]⟩

/-! ## Step 5: simplicity of the real eigenspace -/

/-- The positive ground gap forces every complex eigenvector at the ground
level onto the ground line. -/
private theorem gpr_complex_line
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon beta : ℝ} (hbeta : 0 < beta)
    {xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hgap : complexHermitianGroundGapAtLeast
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0)
    {y : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hy : sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ y = (epsilon : ℂ) • y) :
    y = (star xi0 ⬝ᵥ y) • xi0 := by
  classical
  obtain ⟨hunit, heig, hbottom, hcomp⟩ := hgap
  set K := sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) with hK
  set w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ := y - (star xi0 ⬝ᵥ y) • xi0 with hw
  have hproj : star xi0 ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit, mul_one,
      sub_self]
  have hweig : K *ᵥ w = (epsilon : ℂ) • w := by
    rw [hw, Matrix.mulVec_sub, hy, Matrix.mulVec_smul, heig, smul_comm,
      smul_sub]
  have hwzero : w = 0 := by
    by_contra hne
    have hpos : 0 < (star w ⬝ᵥ w).re := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hwj : w j ≠ 0 := by simpa using hj
      have hjpos : 0 < Complex.normSq (w j) := Complex.normSq_pos.mpr hwj
      simpa [Complex.normSq, dotProduct] using
        (show 0 < ∑ i, Complex.normSq (w i) from
          Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (w i))
            ⟨j, Finset.mem_univ j, hjpos⟩)
    have hgapw := hcomp w hproj
    have henergy : (star w ⬝ᵥ (K *ᵥ w)).re = epsilon * (star w ⬝ᵥ w).re := by
      rw [hweig, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [henergy] at hgapw
    nlinarith [hgapw, hpos, hbeta]
  have h0 : y - (star xi0 ⬝ᵥ y) • xi0 = 0 := by rw [← hw, hwzero]
  exact sub_eq_zero.mp h0

/-- Two real eigenvectors at the ground level are proportional over `ℝ`. -/
private theorem gpr_real_proportional
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon beta : ℝ} (hbeta : 0 < beta)
    {xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hgap : complexHermitianGroundGapAtLeast
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0)
    {u v : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ}
    (hu : Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) u =
      epsilon • u)
    (hv : Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) v =
      epsilon • v)
    (hu0 : u ≠ 0) :
    ∃ c : ℝ, v = c • u := by
  classical
  -- complexify both
  have hcomplexify : ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ,
      Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x = epsilon • x →
      sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ (fun j => ((x j : ℝ) : ℂ)) =
        (epsilon : ℂ) • (fun j => ((x j : ℝ) : ℂ)) := by
    intro x hx
    funext j
    have hj := congrFun hx j
    have hcast : ∑ l, ((ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N j l : ℝ) : ℂ) *
        ((x l : ℝ) : ℂ) =
        (((∑ l, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N j l * x l : ℝ)) : ℂ) := by
      push_cast
      rfl
    simp only [sourceCCMFiniteMatrix, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul]
    rw [hcast]
    have : ∑ l, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N j l * x l = epsilon * x j := by
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hj
    rw [this]
    push_cast
    ring
  have hUc := hcomplexify u hu
  have hVc := hcomplexify v hv
  have hU := gpr_complex_line P k hbeta hgap hUc
  have hV := gpr_complex_line P k hbeta hgap hVc
  -- the overlap of u is nonzero
  set a : ℂ := star xi0 ⬝ᵥ (fun j => ((u j : ℝ) : ℂ)) with ha
  set b : ℂ := star xi0 ⬝ᵥ (fun j => ((v j : ℝ) : ℂ)) with hb
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hu0
    funext j
    have hj := congrFun hU j
    rw [hzero] at hj
    simp only [Pi.smul_apply, smul_eq_mul, zero_mul] at hj
    exact_mod_cast hj
  -- v = (b/a) u coordinatewise, and the ratio is real because both are real
  have hpt : ∀ j, ((v j : ℝ) : ℂ) = (b / a) * ((u j : ℝ) : ℂ) := by
    intro j
    have hju := congrFun hU j
    have hjv := congrFun hV j
    simp only [Pi.smul_apply, smul_eq_mul] at hju hjv
    rw [hju, hjv]
    field_simp
  refine ⟨(b / a).re, ?_⟩
  funext j
  have hj := hpt j
  have him : ((v j : ℝ) : ℂ).im = 0 := by simp
  have hre := congrArg Complex.re hj
  rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at hre
  simpa [Pi.smul_apply, smul_eq_mul] using hre

/-! ## Step 6: the real eigenspace is one-dimensional -/

/-- Membership in the eigenspace is exactly the matrix eigenrelation. -/
private theorem gpr_mem_eigenspace_iff
    (mProject N : ℕ) (epsilon : ℝ) (x : CCMModeFinite N → ℝ) :
    x ∈ (ccmWeilOpFinite mProject N).eigenspace epsilon ↔
      Matrix.mulVec (ccmWeilMatFinite mProject N) x = epsilon • x := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    simpa [ccmWeilOpFinite, Matrix.mulVecLin_apply] using h
  · intro h
    simpa [ccmWeilOpFinite, Matrix.mulVecLin_apply] using h

set_option maxHeartbeats 8000000 in
/-- **Simplicity of the real ground eigenspace.**  Derived from the positive
complex ground gap; no simplicity is assumed. -/
private theorem gpr_real_eigenspace_finrank_one
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon beta : ℝ} (hbeta : 0 < beta)
    {xi0 : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ}
    (hgap : complexHermitianGroundGapAtLeast
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)) epsilon beta xi0)
    {u : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ}
    (hu : Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) u =
      epsilon • u)
    (hu0 : u ≠ 0) :
    Module.finrank ℝ
      ((ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon) = 1 := by
  classical
  have humem : u ∈ (ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon :=
    (gpr_mem_eigenspace_iff _ _ _ u).mpr hu
  set v0 : ((ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon) :=
    ⟨u, humem⟩ with hv0
  have hv0_ne : v0 ≠ 0 := by
    intro hzero
    apply hu0
    have := congrArg Subtype.val hzero
    simpa [hv0] using this
  rw [finrank_eq_one_iff_of_nonzero' v0 hv0_ne]
  intro w
  have hw : Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) (w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ) =
      epsilon • (w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ) :=
    (gpr_mem_eigenspace_iff _ _ _ _).mp w.2
  obtain ⟨c, hc⟩ := gpr_real_proportional P k hbeta hgap hu hw hu0
  refine ⟨c, ?_⟩
  apply Subtype.ext
  simpa [hv0] using hc.symm

/-! ## Step 7: the public ground parity/realification/normalization node -/

/-- Real bottom Rayleigh follows from the complex one by casting. -/
private theorem gpr_real_bottom
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) {epsilon : ℝ}
    (hbottom : ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ,
      epsilon * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ x)).re) :
    ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mulVec
          (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x := by
  intro x
  have h := hbottom (fun j => ((x j : ℝ) : ℂ))
  have hleft : (star (fun j => ((x j : ℝ) : ℂ)) ⬝ᵥ
      (fun j => ((x j : ℝ) : ℂ))).re = x ⬝ᵥ x := by
    simp [dotProduct, Complex.mul_re]
  have hright : (star (fun j => ((x j : ℝ) : ℂ)) ⬝ᵥ
      (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
        (fun j => ((x j : ℝ) : ℂ)))).re =
      x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x := by
    simp [dotProduct, sourceCCMFiniteMatrix, Matrix.mulVec, Complex.mul_re,
      Complex.re_sum, Finset.mul_sum]
  rw [hleft, hright] at h
  exact h

set_option maxHeartbeats 16000000 in
/-- **The selected-shell ground parity, realification and eta normalization**
(verdict `REQ-2026-08-26-N`).  From the retained odd-sector floor at the exact
Rayleigh shift and the literal complement floor, the selected finite CCM cell
has a real, reflection-even, eta-normalized simple bottom eigenvector, related
to the complex ground vector by one nonzero complex scalar.

Odd strictness is derived from the odd-sector floor; evenness is established
before eta normalization; realification uses realness of the CCM matrix; the
eta normalization is discharged by the existing supplier.  No `heta`
hypothesis, no trial-equals-ground identification, no quotient basis input. -/
theorem selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (beta0 beta : ℝ)
    (hbeta0 : 0 < beta0) (hbeta : 0 < beta)
    (hm : 2 ≤ ((selectedFerrersCofinalSourceData P).index k).m)
    (hN : 1 ≤ ((selectedFerrersCofinalSourceData P).index k).N)
    (hoddFloor :
      ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ,
        ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
        beta0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
                  (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) ℂ)) *ᵥ x)).re)
    (hfloor :
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
        beta) :
    ∃ (epsilon : ℝ)
      (xiC : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ)
      (xiR : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ)
      (c : ℂ),
        c ≠ 0 ∧
        (∀ j, ((xiR j : ℝ) : ℂ) = c * xiC j) ∧
        Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) xiR =
          epsilon • xiR ∧
        (∀ j, xiR (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j) = xiR j) ∧
        ccmEtaFinite ((selectedFerrersCofinalSourceData P).index k).N ⬝ᵥ xiR = 1 ∧
        (∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ,
          epsilon * (x ⬝ᵥ x) ≤
            x ⬝ᵥ Matrix.mulVec
              (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x) ∧
        Module.finrank ℝ
          ((ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon) = 1 := by
  classical
  obtain ⟨epsilon, xi0, hgap, -⟩ := gpr_ground_extraction P k beta hfloor
  have hgap' := hgap
  obtain ⟨hunit, heig, hbottom, hcomp⟩ := hgap
  have heven := gpr_ground_is_even P k hbeta hbeta0 hgap' hoddFloor
  have hxi_ne : xi0 ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  -- complexified real eigenrelation of the ground vector
  have heigCast : (fun j l => ((ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N j l : ℝ) : ℂ)) *ᵥ xi0 =
      (epsilon : ℂ) • xi0 := heig
  obtain ⟨hRe, hIm⟩ := gpr_re_im_eigen ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N epsilon heigCast
  obtain ⟨hevenRe, hevenIm⟩ := gpr_parts_even heven
  have hbottomR := gpr_real_bottom P k hbottom
  -- pick the nonzero part and run the same closing argument
  have hclose : ∀ (w : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ),
      Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) w = epsilon • w →
      (∀ j, w (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j) = w j) →
      w ≠ 0 →
      (∀ j, ((w j : ℝ) : ℂ) = (star xi0 ⬝ᵥ (fun l => ((w l : ℝ) : ℂ))) * xi0 j) →
      ∃ (epsilon' : ℝ) (xiC : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ)
        (xiR : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ) (c : ℂ),
        c ≠ 0 ∧
        (∀ j, ((xiR j : ℝ) : ℂ) = c * xiC j) ∧
        Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) xiR =
          epsilon' • xiR ∧
        (∀ j, xiR (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j) = xiR j) ∧
        ccmEtaFinite ((selectedFerrersCofinalSourceData P).index k).N ⬝ᵥ xiR = 1 ∧
        (∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ,
          epsilon' * (x ⬝ᵥ x) ≤
            x ⬝ᵥ Matrix.mulVec
              (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x) ∧
        Module.finrank ℝ
          ((ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon') = 1 := by
    intro w hw hwEven hw0 hwLine
    have hsimple := gpr_real_eigenspace_finrank_one P k hbeta hgap' hw hw0
    obtain ⟨xiR, hxiR0, hxiReig, hxiREven, hxiRnorm⟩ :=
      exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector
        ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N epsilon w hm hN hw0 hw hwEven hsimple
    -- xiR is a real multiple of w, hence a complex multiple of xi0
    obtain ⟨t, ht⟩ := gpr_real_proportional P k hbeta hgap' hw hxiReig hw0
    set ov : ℂ := star xi0 ⬝ᵥ (fun l => ((w l : ℝ) : ℂ)) with hov
    have hov_ne : ov ≠ 0 := by
      intro hzero
      apply hw0
      funext j
      have hj := hwLine j
      rw [hzero, zero_mul] at hj
      exact_mod_cast hj
    have ht_ne : t ≠ 0 := by
      intro hzero
      apply hxiR0
      rw [ht, hzero, zero_smul]
    refine ⟨epsilon, xi0, xiR, (t : ℂ) * ov, ?_, ?_, hxiReig, hxiREven,
      hxiRnorm, hbottomR, hsimple⟩
    · exact mul_ne_zero (by exact_mod_cast ht_ne) hov_ne
    · intro j
      have hj : xiR j = t * w j := by
        have := congrFun ht j
        simpa [Pi.smul_apply, smul_eq_mul] using this
      rw [hj]
      push_cast
      rw [hwLine j]
      ring
  -- the complex line identity for each part
  have hlineRe : ∀ j, (((fun l => (xi0 l).re) j : ℝ) : ℂ) =
      (star xi0 ⬝ᵥ (fun l => (((fun m => (xi0 m).re) l : ℝ) : ℂ))) * xi0 j := by
    intro j
    have hcast : (fun l => (((fun m => (xi0 m).re) l : ℝ) : ℂ)) =
        (fun l => (((xi0 l).re : ℝ) : ℂ)) := rfl
    have hEig : sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
        (fun l => (((xi0 l).re : ℝ) : ℂ)) =
        (epsilon : ℂ) • (fun l => (((xi0 l).re : ℝ) : ℂ)) := by
      funext l
      have hl := congrFun hRe l
      simp only [sourceCCMFiniteMatrix, Matrix.mulVec, dotProduct,
        Pi.smul_apply, smul_eq_mul]
      have hsum : ∑ m, ((ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m : ℝ) : ℂ) *
          (((xi0 m).re : ℝ) : ℂ) =
          (((∑ m, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m * (xi0 m).re : ℝ)) : ℂ) := by
        push_cast
        rfl
      rw [hsum]
      have : ∑ m, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m * (xi0 m).re =
          epsilon * (xi0 l).re := by
        simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hl
      rw [this]
      push_cast
      ring
    have := gpr_complex_line P k hbeta hgap' hEig
    have hj := congrFun this j
    simpa [Pi.smul_apply, smul_eq_mul] using hj
  have hlineIm : ∀ j, (((fun l => (xi0 l).im) j : ℝ) : ℂ) =
      (star xi0 ⬝ᵥ (fun l => (((fun m => (xi0 m).im) l : ℝ) : ℂ))) * xi0 j := by
    intro j
    have hEig : sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
        (fun l => (((xi0 l).im : ℝ) : ℂ)) =
        (epsilon : ℂ) • (fun l => (((xi0 l).im : ℝ) : ℂ)) := by
      funext l
      have hl := congrFun hIm l
      simp only [sourceCCMFiniteMatrix, Matrix.mulVec, dotProduct,
        Pi.smul_apply, smul_eq_mul]
      have hsum : ∑ m, ((ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m : ℝ) : ℂ) *
          (((xi0 m).im : ℝ) : ℂ) =
          (((∑ m, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m * (xi0 m).im : ℝ)) : ℂ) := by
        push_cast
        rfl
      rw [hsum]
      have : ∑ m, ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N l m * (xi0 m).im =
          epsilon * (xi0 l).im := by
        simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hl
      rw [this]
      push_cast
      ring
    have := gpr_complex_line P k hbeta hgap' hEig
    have hj := congrFun this j
    simpa [Pi.smul_apply, smul_eq_mul] using hj
  rcases gpr_re_or_im_ne_zero hxi_ne with hne | hne
  · exact hclose _ hRe hevenRe hne hlineRe
  · exact hclose _ hIm hevenIm hne hlineIm

#print axioms selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor

end Q3.RouteB.D0Pstar
