import Q3.Proofs.RouteB.G6N1SelectedFerrersGroundProposition59RealZeros
import Q3.Proofs.RouteB.LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail
import Q3.Proofs.RouteB.D0ZerosRealOnScalarTransfer

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Matrix
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — the tracked ground transform: real zeros AND pointwise tracking

Verdict `REQ-2026-08-26-N` closeout (same-witness lock).  One tracked ground
transform carries BOTH decisive finite properties: reality of its zero set and
the exact pointwise projective estimate against the selected shell's
`centeredPstar`.

The lock is genuine: the tracked complex ground vector and the real
eta-normalized representative are proved to lie on the same one-dimensional
ground line — no definitional equality is asserted, and no second ground row
is chosen for the two conclusions.

The reversed pole labels between `sourceOrderedCCMCoefficient` and
`proposition59CCMCoefficient` are handled by reflection parity of the real
representative; the production `-z` orientation stays explicit throughout.
-/

/-! ## Step 0: local extraction wrapper (the upstream copy is private) -/

private theorem gtt_hermitian_quadratic_real
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

private theorem gtt_ground_extraction
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
  exact gtt_hermitian_quadratic_real _
    (sourceCCMFiniteMatrix_isHermitian _) _

/-! ## Step 1: the tracked ground objects on the selected shell -/

/-- The tracked complex ground eigenvalue selected by the literal complement
floor on the exact selected cell. -/
def selectedFerrersTrackedGroundEigenvalue
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) : ℝ :=
  Classical.choose (gtt_ground_extraction P k beta (hfloor k))

/-- The tracked complex unit ground vector from the same choice. -/
def selectedFerrersTrackedGroundVector
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ :=
  Classical.choose
    (Classical.choose_spec (gtt_ground_extraction P k beta (hfloor k)))

/-- Both fields of the tracked choice: the full ground-gap package and the
exact projective residual/floor estimate. -/
theorem selectedFerrersTrackedGroundVector_spec
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) :
    complexHermitianGroundGapAtLeast
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersTrackedGroundEigenvalue P beta hfloor k) beta
        (selectedFerrersTrackedGroundVector P beta hfloor k) ∧
      1 - Complex.normSq
          (star (selectedFerrersTrackedGroundVector P beta hfloor k) ⬝ᵥ
            selectedFerrersFiniteCCMRow P k) ≤
        (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
          selectedFerrersFiniteCCMResidual P k).re / beta ^ 2 :=
  Classical.choose_spec
    (Classical.choose_spec (gtt_ground_extraction P k beta (hfloor k)))

/-- Exact projective overlap of the selected trial row on the tracked ground
line. -/
def selectedFerrersTrackedGroundOverlap
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) : ℂ :=
  star (selectedFerrersTrackedGroundVector P beta hfloor k) ⬝ᵥ
    selectedFerrersFiniteCCMRow P k

/-- Literal residual energy over the squared complement floor. -/
def selectedFerrersTrackedGroundResidualFloorRatio
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ) (k : ℕ) : ℝ :=
  (star (selectedFerrersFiniteCCMResidual P k) ⬝ᵥ
    selectedFerrersFiniteCCMResidual P k).re / beta ^ 2

/-- The exact nonzero scalar in front of the tracked ground transform. -/
def selectedFerrersTrackedGroundScale
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) : ℂ :=
  centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0 *
    selectedFerrersTrackedGroundOverlap P beta hfloor k

/-- **The tracked ground transform.**  One named function; both finite
conclusions below are proved for exactly this object. -/
def selectedFerrersTrackedGroundTransform
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta : ℝ)
    (hfloor : ∀ k,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) beta)
    (k : ℕ) (z : ℂ) : ℂ :=
  selectedFerrersTrackedGroundScale P beta hfloor k *
    sourceOrderedCCMRawTransform
      (logLength ((selectedFerrersCofinalSourceData P).index k))
      ((selectedFerrersCofinalSourceData P).index k).N
      (selectedFerrersTrackedGroundVector P beta hfloor k) z

/-! ## Step 2: the same-witness lock -/

/-- Two ground packages on the same matrix share the eigenvalue: each bottom
bound tests the other's vector. -/
private theorem gtt_eigenvalue_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℂ} {e1 e2 b1 b2 : ℝ} {x1 x2 : ι → ℂ}
    (h1 : complexHermitianGroundGapAtLeast K e1 b1 x1)
    (h2 : complexHermitianGroundGapAtLeast K e2 b2 x2) :
    e1 = e2 := by
  obtain ⟨hu1, he1, hb1, -⟩ := h1
  obtain ⟨hu2, he2, hb2, -⟩ := h2
  have hn1 : (star x1 ⬝ᵥ x1).re = 1 := by rw [hu1]; norm_num
  have hn2 : (star x2 ⬝ᵥ x2).re = 1 := by rw [hu2]; norm_num
  have hq1 : (star x1 ⬝ᵥ (K *ᵥ x1)).re = e1 := by
    rw [he1, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hu1]
    norm_num
  have hq2 : (star x2 ⬝ᵥ (K *ᵥ x2)).re = e2 := by
    rw [he2, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hu2]
    norm_num
  have hle1 := hb1 x2
  have hle2 := hb2 x1
  rw [hn2, mul_one, hq2] at hle1
  rw [hn1, mul_one, hq1] at hle2
  linarith

/-- The positive ground gap drives every eigenvector at the ground level onto
the ground line.  Local reconstruction: the upstream copy is private. -/
private theorem gtt_ground_line
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℂ} {epsilon beta : ℝ} (hbeta : 0 < beta)
    {xi0 : ι → ℂ}
    (hgap : complexHermitianGroundGapAtLeast K epsilon beta xi0)
    {y : ι → ℂ} (hy : K *ᵥ y = (epsilon : ℂ) • y) :
    y = (star xi0 ⬝ᵥ y) • xi0 := by
  classical
  obtain ⟨hunit, heig, hbottom, hcomp⟩ := hgap
  set w : ι → ℂ := y - (star xi0 ⬝ᵥ y) • xi0 with hw
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

/-! ## Step 3: the reversed-label crosswalk for an even real row -/

/-- For a reflection-even real row the source-ordered and Proposition-59
coefficient families agree on the whole carrier: the reversed pole label is
absorbed by parity. -/
private theorem gtt_coefficient_crosswalk
    (N : ℕ) (xiR : CCMModeFinite N → ℝ)
    (heven : ∀ j, xiR (ccmNegFinite N j) = xiR j)
    (n : ℤ) :
    sourceOrderedCCMCoefficient N (fun j => ((xiR j : ℝ) : ℂ)) n =
      proposition59CCMCoefficient N xiR n := by
  classical
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · rw [sourceOrderedCCMCoefficient, dif_pos hn,
      proposition59CCMCoefficient, dif_pos hn]
    have hcoe : ∀ i : CCMModeFinite N,
        (((ccmModeFiniteEquivIcc N) i : {m : ℤ // m ∈ Finset.Icc (-(N : ℤ)) N})
          : ℤ) = ccmModeFinite N i := fun i => rfl
    have hneg :
        (ccmModeFiniteEquivIcc N).symm ⟨-n, neg_mem_Icc_of_mem_Icc hn⟩ =
          ccmNegFinite N ((ccmModeFiniteEquivIcc N).symm ⟨n, hn⟩) := by
      apply (ccmModeFiniteEquivIcc N).injective
      apply Subtype.ext
      rw [Equiv.apply_symm_apply]
      rw [hcoe, ccmModeFinite_neg]
      have hback : ccmModeFinite N ((ccmModeFiniteEquivIcc N).symm ⟨n, hn⟩) = n := by
        have := congrArg Subtype.val
          ((ccmModeFiniteEquivIcc N).apply_symm_apply ⟨n, hn⟩)
        rw [hcoe] at this
        exact this
      rw [hback]
    rw [hneg, heven]
  · rw [sourceOrderedCCMCoefficient, dif_neg hn,
      proposition59CCMCoefficient, dif_neg hn]

/-- Hence the two transforms of an even real row agree up to the production
argument reflection. -/
private theorem gtt_transform_crosswalk
    (L : ℝ) (N : ℕ) (xiR : CCMModeFinite N → ℝ)
    (heven : ∀ j, xiR (ccmNegFinite N j) = xiR j)
    (z : ℂ) :
    sourceOrderedCCMRawTransform L N (fun j => ((xiR j : ℝ) : ℂ)) z =
      proposition59CCMTransform L N xiR (-z) := by
  unfold sourceOrderedCCMRawTransform proposition59CCMTransform
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [gtt_coefficient_crosswalk N xiR heven n]

/-! ## Step 4: auxiliary transfers -/

/-- Reality of the zero set is invariant under the production argument
reflection. -/
private theorem gtt_zerosRealOn_neg {f : ℂ → ℂ}
    (hf : ZerosRealOn Set.univ f) :
    ZerosRealOn Set.univ (fun z => f (-z)) := by
  intro z _ hz
  have h := hf (-z) (Set.mem_univ _) hz
  simpa using h

/-- Complexification of a real eigenvector of the real CCM matrix. -/
private theorem gtt_complexify_eigen
    (mProject N : ℕ) (epsilon : ℝ) (x : CCMModeFinite N → ℝ)
    (hx : Matrix.mulVec (ccmWeilMatFinite mProject N) x = epsilon • x) :
    (fun j l => ((ccmWeilMatFinite mProject N j l : ℝ) : ℂ)) *ᵥ
        (fun j => ((x j : ℝ) : ℂ)) =
      (epsilon : ℂ) • (fun j => ((x j : ℝ) : ℂ)) := by
  funext l
  have hl := congrFun hx l
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  have hsum : ∑ m, ((ccmWeilMatFinite mProject N l m : ℝ) : ℂ) *
      (((x m : ℝ)) : ℂ) =
      (((∑ m, ccmWeilMatFinite mProject N l m * x m : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hsum]
  have hval : ∑ m, ccmWeilMatFinite mProject N l m * x m = epsilon * x l := by
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hl
  rw [hval]
  push_cast
  ring

/-- Real and imaginary parts of a complexified-real eigenvector are real
eigenvectors at the same eigenvalue. -/
private theorem gtt_re_im_eigen
    (mProject N : ℕ) (epsilon : ℝ) {xi : CCMModeFinite N → ℂ}
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

/-- Real quadratic data of a complexified real vector. -/
private theorem gtt_real_quadratic
    (mProject N : ℕ) (x : CCMModeFinite N → ℝ) :
    (star (fun j => ((x j : ℝ) : ℂ)) ⬝ᵥ (fun j => ((x j : ℝ) : ℂ))).re =
        x ⬝ᵥ x ∧
      (star (fun j => ((x j : ℝ) : ℂ)) ⬝ᵥ
        ((fun j l => ((ccmWeilMatFinite mProject N j l : ℝ) : ℂ)) *ᵥ
          (fun j => ((x j : ℝ) : ℂ)))).re =
        x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite mProject N) x := by
  constructor
  · simp [dotProduct, Complex.mul_re]
  · simp [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.re_sum,
      Finset.mul_sum]

/-! ## Step 5: the public same-witness lock -/

set_option maxHeartbeats 16000000 in
/-- **The tracked ground transform carries both finite properties.**  One
named function has an entirely real zero set AND the exact pointwise
projective estimate against the selected shell's `centeredPstar`.

The tracked complex ground vector and the real eta-normalized representative
are proved to lie on the same one-dimensional ground line; no definitional
equality is asserted, and no second ground row is chosen. -/
theorem selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors
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
    (hfloor : ∀ j,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index j))
        (selectedFerrersFiniteCCMRow P j)
        ((selectedFerrersFiniteCCMRayleigh P j : ℝ) : ℂ) beta)
    (hratio : selectedFerrersTrackedGroundResidualFloorRatio P beta k < 1) :
    ZerosRealOn Set.univ
      (selectedFerrersTrackedGroundTransform P beta hfloor k) ∧
    ∀ z : ℂ,
      ‖selectedFerrersTrackedGroundTransform P beta hfloor k z -
          (selectedFerrersCofinalSourceData P).centeredPstar k z‖ ≤
        ‖centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0‖ *
          sourceOrderedCCMKernelL2
            (logLength ((selectedFerrersCofinalSourceData P).index k))
            ((selectedFerrersCofinalSourceData P).index k).N z *
          Real.sqrt
            (selectedFerrersTrackedGroundResidualFloorRatio P beta k) := by
  classical
  obtain ⟨htgap, htdefect⟩ :=
    selectedFerrersTrackedGroundVector_spec P beta hfloor k
  have hxunit := htgap.1
  have hxeig := htgap.2.1
  have hxbottom := htgap.2.2.1
  -- overlap nonvanishing from the strict ratio
  have hov_ne :
      selectedFerrersTrackedGroundOverlap P beta hfloor k ≠ 0 := by
    intro hzero
    rw [selectedFerrersTrackedGroundOverlap] at hzero
    rw [hzero] at htdefect
    simp only [map_zero, sub_zero] at htdefect
    rw [selectedFerrersTrackedGroundResidualFloorRatio] at hratio
    linarith
  -- the ratified real ground representative with real P59 zeros
  obtain ⟨eps2, xiC2, xiR, c2, hc2, hcast2, heig2, heven2, hnorm2, hbot2,
      hsimple2, hzeros⟩ :=
    selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors
      P k beta0 beta hbeta0 hbeta hm hN hoddFloor (hfloor k)
  have hxiRc := gtt_complexify_eigen ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N eps2 xiR heig2
  have hxiR_ne : (fun j => ((xiR j : ℝ) : ℂ)) ≠ 0 := by
    intro hzero
    have hall : ∀ j, xiR j = 0 := by
      intro j
      have h := congrFun hzero j
      simp only [Pi.zero_apply] at h
      exact_mod_cast h
    have hsum : ccmEtaFinite ((selectedFerrersCofinalSourceData P).index k).N ⬝ᵥ xiR = 0 := by
      rw [dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [hall j, mul_zero]
    rw [hnorm2] at hsum
    norm_num at hsum
  -- the two independent choices share the eigenvalue
  have heps : selectedFerrersTrackedGroundEigenvalue P beta hfloor k = eps2 := by
    obtain ⟨hq1, hq2⟩ := gtt_real_quadratic ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N xiR
    have hnormpos : 0 < xiR ⬝ᵥ xiR := by
      by_contra hcon
      push_neg at hcon
      have hnn : (0:ℝ) ≤ xiR ⬝ᵥ xiR := by
        rw [dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
      have hzero : xiR ⬝ᵥ xiR = 0 := le_antisymm hcon hnn
      have hall : ∀ j, xiR j = 0 := by
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_self_nonneg (xiR i))).mp (by rw [dotProduct] at hzero; exact hzero)
          j (Finset.mem_univ j)
        exact mul_self_eq_zero.mp this
      exact hxiR_ne (funext fun j => by rw [hall j]; norm_num)
    -- direction one: the tracked bottom tested on the real vector
    have hdir1 : selectedFerrersTrackedGroundEigenvalue P beta hfloor k ≤ eps2 := by
      have hb := hxbottom (fun j => ((xiR j : ℝ) : ℂ))
      have henergy :
          (star (fun j => ((xiR j : ℝ) : ℂ)) ⬝ᵥ
            (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
              (fun j => ((xiR j : ℝ) : ℂ)))).re = eps2 * (xiR ⬝ᵥ xiR) := by
        rw [show sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ
              (fun j => ((xiR j : ℝ) : ℂ)) =
            (eps2 : ℂ) • (fun j => ((xiR j : ℝ) : ℂ)) from hxiRc]
        rw [dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, hq1]
        ring
      rw [hq1, henergy] at hb
      exact le_of_mul_le_mul_right (by linarith) hnormpos
    -- direction two: the real bottom tested on a nonzero part of the tracked vector
    have hxeigCast :
        (fun j l => ((ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N j l : ℝ) : ℂ)) *ᵥ
          selectedFerrersTrackedGroundVector P beta hfloor k =
        ((selectedFerrersTrackedGroundEigenvalue P beta hfloor k : ℝ) : ℂ) •
          selectedFerrersTrackedGroundVector P beta hfloor k := hxeig
    obtain ⟨hRe, hIm⟩ := gtt_re_im_eigen ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N _ hxeigCast
    have hxi_ne : selectedFerrersTrackedGroundVector P beta hfloor k ≠ 0 := by
      intro hzero
      rw [hzero] at hxunit
      simp at hxunit
    have hpart : ∃ v : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ, v ≠ 0 ∧
        Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) v =
          selectedFerrersTrackedGroundEigenvalue P beta hfloor k • v := by
      by_cases hre :
        (fun j => (selectedFerrersTrackedGroundVector P beta hfloor k j).re) = 0
      · refine ⟨fun j =>
          (selectedFerrersTrackedGroundVector P beta hfloor k j).im, ?_, hIm⟩
        intro him
        apply hxi_ne
        funext j
        have h1 : (selectedFerrersTrackedGroundVector P beta hfloor k j).re = 0 :=
          congrFun hre j
        have h2 : (selectedFerrersTrackedGroundVector P beta hfloor k j).im = 0 :=
          congrFun him j
        exact Complex.ext h1 h2
      · exact ⟨_, hre, hRe⟩
    obtain ⟨v, hv_ne, hveig⟩ := hpart
    have hvnorm : 0 < v ⬝ᵥ v := by
      by_contra hcon
      push_neg at hcon
      have hnn : (0:ℝ) ≤ v ⬝ᵥ v := by
        rw [dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
      have hzero : v ⬝ᵥ v = 0 := le_antisymm hcon hnn
      apply hv_ne
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_self_nonneg (v i))).mp (by rw [dotProduct] at hzero; exact hzero)
        j (Finset.mem_univ j)
      exact mul_self_eq_zero.mp this
    have hb2 := hbot2 v
    have henergy2 : v ⬝ᵥ Matrix.mulVec
        (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) v =
        selectedFerrersTrackedGroundEigenvalue P beta hfloor k * (v ⬝ᵥ v) := by
      rw [hveig, dotProduct_smul, smul_eq_mul]
    rw [henergy2] at hb2
    have hdir2 : eps2 ≤ selectedFerrersTrackedGroundEigenvalue P beta hfloor k :=
      le_of_mul_le_mul_right (by linarith) hvnorm
    linarith
  -- the real representative lies on the tracked ground line
  have hline := gtt_ground_line hbeta htgap
    (by rw [heps]; exact hxiRc :
      sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) *ᵥ (fun j => ((xiR j : ℝ) : ℂ)) =
        ((selectedFerrersTrackedGroundEigenvalue P beta hfloor k : ℝ) : ℂ) •
          (fun j => ((xiR j : ℝ) : ℂ)))
  set alpha : ℂ := star (selectedFerrersTrackedGroundVector P beta hfloor k) ⬝ᵥ
    (fun j => ((xiR j : ℝ) : ℂ)) with halpha
  have halpha_ne : alpha ≠ 0 := by
    intro hzero
    apply hxiR_ne
    rw [hline, hzero, zero_smul]
  -- the tracked transform is a nonzero multiple of the real P59 transform
  have hrow_smul : ∀ z : ℂ,
      sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
          (fun j => ((xiR j : ℝ) : ℂ)) z =
        alpha * sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
          (selectedFerrersTrackedGroundVector P beta hfloor k) z := by
    intro z
    have hj : ∀ j, ((xiR j : ℝ) : ℂ) =
        alpha * selectedFerrersTrackedGroundVector P beta hfloor k j := by
      intro j
      have h := congrFun hline j
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hsum :
        (∑ j, ((xiR j : ℝ) : ℂ) *
            proposition59PoleKernel (logLength ((selectedFerrersCofinalSourceData P).index k))
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j) (-z)) =
          alpha * ∑ j, selectedFerrersTrackedGroundVector P beta hfloor k j *
            proposition59PoleKernel (logLength ((selectedFerrersCofinalSourceData P).index k))
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j) (-z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hj j]
      ring
    rw [sourceOrderedCCMRawTransform_eq_mode_sum,
      sourceOrderedCCMRawTransform_eq_mode_sum, hsum]
    ring
  have htracked_eq : ∀ z : ℂ,
      selectedFerrersTrackedGroundTransform P beta hfloor k z =
        ((centeredXi 0 /
            (selectedFerrersCofinalSourceData P).rawFplus k 0 *
          selectedFerrersTrackedGroundOverlap P beta hfloor k) * alpha⁻¹) *
          proposition59CCMTransform (ccmL ((selectedFerrersCofinalSourceData P).index k).m) ((selectedFerrersCofinalSourceData P).index k).N xiR (-z) := by
    intro z
    rw [selectedFerrersTrackedGroundTransform, selectedFerrersTrackedGroundScale]
    have hinv : sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
        (selectedFerrersTrackedGroundVector P beta hfloor k) z =
        alpha⁻¹ * sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
          (fun j => ((xiR j : ℝ) : ℂ)) z := by
      rw [hrow_smul z, ← mul_assoc, inv_mul_cancel₀ halpha_ne, one_mul]
    rw [hinv]
    have hcross : sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k))
        ((selectedFerrersCofinalSourceData P).index k).N (fun j => ((xiR j : ℝ) : ℂ)) z =
        proposition59CCMTransform (ccmL ((selectedFerrersCofinalSourceData P).index k).m) ((selectedFerrersCofinalSourceData P).index k).N xiR (-z) :=
      gtt_transform_crosswalk (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N xiR heven2 z
    rw [hcross]
    ring
  have hscale_ne :
      (centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0 *
        selectedFerrersTrackedGroundOverlap P beta hfloor k) * alpha⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact div_ne_zero centeredXi_zero_ne_zero
          ((selectedFerrersCofinalSourceData P).rawZeroNonzero k)
      · exact hov_ne
    · exact inv_ne_zero halpha_ne
  constructor
  · -- reality of the zero set
    refine Q3.RouteB.zerosRealOn_of_eq_smul hscale_ne (fun z _ => htracked_eq z) ?_
    exact gtt_zerosRealOn_neg hzeros
  · -- the pointwise projective estimate
    intro z
    have hproj := sourceOrderedCCMRawTransform_sub_projection_le
      (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
      (selectedFerrersTrackedGroundVector P beta hfloor k)
      (selectedFerrersFiniteCCMRow P k)
      hxunit (selectedFerrersFiniteCCMRow_unit P k) z
    have hsqrt_le :
        Real.sqrt (1 - Complex.normSq
            (selectedFerrersTrackedGroundOverlap P beta hfloor k)) ≤
          Real.sqrt (selectedFerrersTrackedGroundResidualFloorRatio P beta k) := by
      apply Real.sqrt_le_sqrt
      simpa [selectedFerrersTrackedGroundOverlap,
        selectedFerrersTrackedGroundResidualFloorRatio] using htdefect
    have hcenter :
        (selectedFerrersCofinalSourceData P).centeredPstar k z =
          centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0 *
            sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
              (selectedFerrersFiniteCCMRow P k) z := by
      rw [SelectedProlateCofinalSourceData.centeredPstar,
        sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus]
    rw [selectedFerrersTrackedGroundTransform, selectedFerrersTrackedGroundScale,
      hcenter, mul_assoc, ← mul_sub, norm_mul, norm_sub_rev]
    calc ‖centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0‖ *
        ‖sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
            (selectedFerrersFiniteCCMRow P k) z -
          selectedFerrersTrackedGroundOverlap P beta hfloor k *
            sourceOrderedCCMRawTransform (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N
              (selectedFerrersTrackedGroundVector P beta hfloor k) z‖ ≤
        ‖centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0‖ *
          (sourceOrderedCCMKernelL2 (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N z *
            Real.sqrt (1 - Complex.normSq
              (selectedFerrersTrackedGroundOverlap P beta hfloor k))) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa [selectedFerrersTrackedGroundOverlap] using hproj
      _ ≤ ‖centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0‖ *
          (sourceOrderedCCMKernelL2 (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N z *
            Real.sqrt
              (selectedFerrersTrackedGroundResidualFloorRatio P beta k)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left hsqrt_le
          exact sourceOrderedCCMKernelL2_nonneg _ _ _
      _ = ‖centeredXi 0 / (selectedFerrersCofinalSourceData P).rawFplus k 0‖ *
          sourceOrderedCCMKernelL2 (logLength ((selectedFerrersCofinalSourceData P).index k)) ((selectedFerrersCofinalSourceData P).index k).N z *
          Real.sqrt
            (selectedFerrersTrackedGroundResidualFloorRatio P beta k) := by
          ring

#print axioms selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors

end Q3.RouteB.D0Pstar
