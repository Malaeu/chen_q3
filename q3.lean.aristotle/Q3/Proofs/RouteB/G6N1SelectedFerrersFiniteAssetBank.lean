import Q3.Proofs.RouteB.Proposition59EntireTransform
import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

/-!
# G6N1: selected Ferrers finite asset bank (Track 2, verdict `071d3eb0`)

Finite-cell identities only, ratified paper assets from the 2026-08-27
adjudication chain.  Public surface carries NO `Tendsto`, NO `Filter.Eventually`,
NO rate hypothesis and NO cofinal conclusion.

Nodes: B1 (P59 diagonal resolvent on ALL of `ℂ`, lattice included),
A1-A3 (trial graph operator: positive definiteness, exact inverse-residual
identity), C1 (penalty lower envelopes, identity and Gram metric),
C2 (finite Schur minimal-slack criterion by exact completion of squares),
B2 (complexified rank-two commutator and the entire moved-action formula),
D1 (centering-factor bound from the exact central anchor).
-/

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators ComplexOrder

/-! ## Node B1: the Proposition-59 diagonal-resolvent identity, entire form -/

/-- The dimensionless spectral parameter of the reflected P59 kernel row. -/
def p59SpectralParameter (L : ℝ) (z : ℂ) : ℂ :=
  -(z * (L : ℂ)) / (2 * (Real.pi : ℂ))

/-- The common resolvent scalar `(√L/π)·sin(zL/2)`. -/
def p59ResolventScalar (L : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt L : ℂ) / (Real.pi : ℂ)) * Complex.sin (z * (L : ℂ) / 2)

/-- **Node B1.**  On ALL of `ℂ` — removable lattice points included — the
scaled reflected pole-kernel row satisfies the diagonal-mode resolvent
equation `(n − ζ(z))·h_n(z) = c(z)`.  At an included lattice pole both sides
vanish; off the lattice this is the exact Cauchy-quotient algebra. -/
theorem proposition59PoleKernel_diagonal_resolvent
    {L : ℝ} (hL : 0 < L) (n : ℤ) (z : ℂ) :
    ((n : ℂ) - p59SpectralParameter L z) *
        (((Real.sqrt L : ℂ))⁻¹ * proposition59PoleKernel L n (-z)) =
      p59ResolventScalar L z := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsL : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hL)
  have hsq : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    have := Real.mul_self_sqrt hL.le
    exact_mod_cast this
  by_cases hz : (-z) = proposition59Pole L n
  · -- included lattice pole: both sides vanish with the sine numerator
    have hzval : z = -((2 * (n : ℂ) * (Real.pi : ℂ)) / (L : ℂ)) := by
      have h2 := hz
      unfold proposition59Pole at h2
      linear_combination -h2
    have hsin : Complex.sin (z * (L : ℂ) / 2) = 0 := by
      have harg : z * (L : ℂ) / 2 = ((-n : ℤ) : ℂ) * (Real.pi : ℂ) := by
        rw [hzval]
        push_cast
        field_simp
      rw [harg, Complex.sin_int_mul_pi]
    have hzeta : p59SpectralParameter L z = (n : ℂ) := by
      unfold p59SpectralParameter
      rw [hzval]
      field_simp
    rw [hzeta, sub_self, zero_mul]
    unfold p59ResolventScalar
    rw [hsin, mul_zero]
  · -- off-lattice: exact quotient algebra with the shared sine numerator
    have hLne : L ≠ 0 := hL.ne'
    rw [proposition59PoleKernel_eq_quotient hLne n hz]
    have hne : (-z) - proposition59Pole L n ≠ 0 := sub_ne_zero.mpr hz
    unfold proposition59Numerator proposition59Pole p59SpectralParameter
      p59ResolventScalar at *
    have hsinneg : Complex.sin (-z * (L : ℂ) / 2) =
        -Complex.sin (z * (L : ℂ) / 2) := by
      rw [show -z * (L : ℂ) / 2 = -(z * (L : ℂ) / 2) by ring, Complex.sin_neg]
    rw [hsinneg]
    field_simp [hne]
    have hD : -((L : ℂ) * z) - (n : ℂ) * 2 * (Real.pi : ℂ) ≠ 0 := by
      have hprod := mul_ne_zero hLC hne
      intro hcontr
      apply hprod
      field_simp
      linear_combination hcontr
    field_simp [hD]
    linear_combination ((n : ℂ) * 2 * (Real.pi : ℂ) + (L : ℂ) * z) *
      Complex.sin ((L : ℂ) * z / 2) * hsq

/-! ## Nodes A1-A3: the trial-line graph operator -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trial-line graph operator `C = Q(K − ε)Q + P` with `P = q q*`,
`Q = 1 − P`, exactly as ratified in verdict `4a576dd5`. -/
def trialGraphOperator (K : Matrix ι ι ℂ) (q : ι → ℂ) (eps : ℝ) :
    Matrix ι ι ℂ :=
  (1 - Matrix.vecMulVec q (star q)) * (K - (eps : ℂ) • 1) *
      (1 - Matrix.vecMulVec q (star q)) +
    Matrix.vecMulVec q (star q)

/-- **Node A2.**  The exact inverse-residual identity in multiplied form:
`C · (ξ − d·q) = −d·r` for any eigenvector `ξ` of `K` at the ground value,
with `d = ⟨q,ξ⟩` and `r = Kq − ⟨q,Kq⟩·q`.  No Hermitian or floor hypothesis
enters this identity. -/
theorem trialGraphOperator_inverse_residual_identity
    (K : Matrix ι ι ℂ) (q ξ : ι → ℂ) (eps : ℝ)
    (hq : star q ⬝ᵥ q = 1)
    (hξ : K *ᵥ ξ = (eps : ℂ) • ξ) :
    trialGraphOperator K q eps *ᵥ (ξ - (star q ⬝ᵥ ξ) • q) =
      -((star q ⬝ᵥ ξ) •
        (K *ᵥ q - (star q ⬝ᵥ (K *ᵥ q)) • q)) := by
  classical
  set d : ℂ := star q ⬝ᵥ ξ with hd
  set a : ℂ := star q ⬝ᵥ (K *ᵥ q) with ha
  set w : ι → ℂ := ξ - d • q with hw
  have hqw : star q ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, hq, smul_eq_mul, mul_one, ← hd,
      sub_self]
  have hPw : Matrix.vecMulVec q (star q) *ᵥ w = 0 := by
    rw [Matrix.vecMulVec_mulVec, hqw]
    simp
  have hQw : (1 - Matrix.vecMulVec q (star q)) *ᵥ w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPw, sub_zero]
  have hKw : (K - (eps : ℂ) • 1) *ᵥ w =
      -(d • (K *ᵥ q - (eps : ℂ) • q)) := by
    rw [hw, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hξ,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have hPKq : Matrix.vecMulVec q (star q) *ᵥ (K *ᵥ q - (eps : ℂ) • q) =
      (a - eps) • q := by
    rw [Matrix.vecMulVec_mulVec, dotProduct_sub, dotProduct_smul, hq, ← ha]
    funext i
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hchain : trialGraphOperator K q eps *ᵥ w =
      (1 - Matrix.vecMulVec q (star q)) *ᵥ
        ((K - (eps : ℂ) • 1) *ᵥ
          ((1 - Matrix.vecMulVec q (star q)) *ᵥ w)) +
        Matrix.vecMulVec q (star q) *ᵥ w := by
    rw [trialGraphOperator, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  rw [hchain, hQw, hKw, hPw, add_zero, Matrix.mulVec_neg,
    Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, hPKq]
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem dot_star_self_re (w : ι → ℂ) :
    (star w ⬝ᵥ w).re = ∑ i, Complex.normSq (w i) := by
  simp only [dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

private theorem dot_star_swap (x y : ι → ℂ) :
    star x ⬝ᵥ y = starRingEnd ℂ (star y ⬝ᵥ x) := by
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul,
    Complex.conj_conj, RingHomCompTriple.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

omit [DecidableEq ι] in
private theorem herm_quad_conj_self {M : Matrix ι ι ℂ} (hM : Mᴴ = M)
    (v : ι → ℂ) :
    starRingEnd ℂ (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (M *ᵥ v) := by
  have h1 : star (star v ⬝ᵥ (M *ᵥ v)) = star (M *ᵥ v) ⬝ᵥ v := by
    rw [star_dotProduct]
    simp
  have h2 : star (M *ᵥ v) ⬝ᵥ v = (star v ᵥ* Mᴴ) ⬝ᵥ v := by
    rw [Matrix.star_mulVec]
  have h3 : (star v ᵥ* Mᴴ) ⬝ᵥ v = star v ⬝ᵥ (M *ᵥ v) := by
    rw [hM, ← Matrix.dotProduct_mulVec]
  calc starRingEnd ℂ (star v ⬝ᵥ (M *ᵥ v))
      = star (star v ⬝ᵥ (M *ᵥ v)) := rfl
    _ = star (M *ᵥ v) ⬝ᵥ v := h1
    _ = (star v ᵥ* Mᴴ) ⬝ᵥ v := h2
    _ = star v ⬝ᵥ (M *ᵥ v) := h3

omit [DecidableEq ι] in
private theorem herm_quad_im_zero {M : Matrix ι ι ℂ} (hM : Mᴴ = M)
    (v : ι → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).im = 0 := by
  have h := herm_quad_conj_self hM v
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

private theorem dot_star_self_re_pos {v : ι → ℂ} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ v).re := by
  rw [dot_star_self_re]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv (funext hall)
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, ?_, ?_⟩
  · exact Finset.mem_univ i
  · exact Complex.normSq_pos.mpr hi

/-- **Node A1.**  Positive definiteness of the trial graph operator from the
literal complement floor at the Rayleigh shift together with `ε ≤ a`. -/
theorem trialGraphOperator_posDef
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a eps beta : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (heps : eps ≤ a)
    (hfloor : ∀ w : ι → ℂ, star q ⬝ᵥ w = 0 →
      beta * (star w ⬝ᵥ w).re ≤
        (star w ⬝ᵥ ((K - (a : ℂ) • 1) *ᵥ w)).re) :
    (trialGraphOperator K q eps).PosDef := by
  classical
  set P : Matrix ι ι ℂ := Matrix.vecMulVec q (star q) with hPdef
  have hP_herm : Pᴴ = P := by
    ext i j
    simp [hPdef, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hQ_herm : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
  have hKe_herm : (K - (eps : ℂ) • 1)ᴴ = K - (eps : ℂ) • 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hK.eq,
      Matrix.conjTranspose_one]
    congr 1
    simp [Complex.conj_ofReal]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · show (trialGraphOperator K q eps)ᴴ = _
    rw [trialGraphOperator, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hP_herm, hQ_herm, hKe_herm]
    rw [mul_assoc]
  · intro x hx
    set dt : ℂ := star q ⬝ᵥ x with hdt
    set w : ι → ℂ := x - dt • q with hwdef
    have hQx : (1 - P) *ᵥ x = w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPdef,
        Matrix.vecMulVec_mulVec, hwdef, ← hdt]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
      ring
    have hqw : star q ⬝ᵥ w = 0 := by
      rw [hwdef, dotProduct_sub, dotProduct_smul, hq, smul_eq_mul, mul_one,
        ← hdt, sub_self]
    have hsplit : star x ⬝ᵥ (trialGraphOperator K q eps *ᵥ x) =
        star w ⬝ᵥ ((K - (eps : ℂ) • 1) *ᵥ w) + dt * starRingEnd ℂ dt := by
      rw [trialGraphOperator, ← hPdef, Matrix.add_mulVec, dotProduct_add]
      congr 1
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQx,
          Matrix.dotProduct_mulVec, ← hQ_herm, ← Matrix.star_mulVec, hQx]
      · rw [hPdef, Matrix.vecMulVec_mulVec, ← hdt]
        have hop : (MulOpposite.op dt) • q = dt • q := by
          funext i
          simp [MulOpposite.smul_eq_mul_unop, mul_comm]
        rw [hop, dotProduct_smul, smul_eq_mul, dot_star_swap x q, ← hdt]
    have hxw : (x : ι → ℂ) = w + dt • q := by
      rw [hwdef]
      funext i
      simp
    have hlen : star x ⬝ᵥ (x : ι → ℂ) =
        star w ⬝ᵥ w + ((Complex.normSq dt : ℝ) : ℂ) := by
      conv_lhs => rw [hxw]
      rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
      have h1 : star w ⬝ᵥ (dt • q) = 0 := by
        rw [dotProduct_smul, smul_eq_mul, dot_star_swap w q, hqw]
        simp
      have h2 : star (dt • q) ⬝ᵥ w = 0 := by
        rw [star_smul, smul_dotProduct, hqw]
        simp
      have h3 : star (dt • q) ⬝ᵥ (dt • q) =
          ((Complex.normSq dt : ℝ) : ℂ) := by
        rw [star_smul, smul_dotProduct, dotProduct_smul, hq]
        simp [Complex.normSq_eq_conj_mul_self, mul_comm]
      rw [h1, h2, h3]
      ring
    have hx0 : 0 < (star w ⬝ᵥ w).re + Complex.normSq dt := by
      have hpos := dot_star_self_re_pos hx
      rw [hlen, Complex.add_re, Complex.ofReal_re] at hpos
      exact hpos
    have hwre : 0 ≤ (star w ⬝ᵥ w).re := by
      rw [dot_star_self_re]
      exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hKesplit : star w ⬝ᵥ ((K - (eps : ℂ) • 1) *ᵥ w) =
        star w ⬝ᵥ ((K - (a : ℂ) • 1) *ᵥ w) +
          (((a - eps : ℝ)) : ℂ) * (star w ⬝ᵥ w) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_sub, dotProduct_smul, dotProduct_smul]
      push_cast
      simp only [smul_eq_mul]
      ring
    have hterm1 : beta * (star w ⬝ᵥ w).re ≤
        (star w ⬝ᵥ ((K - (eps : ℂ) • 1) *ᵥ w)).re := by
      have hfl := hfloor w hqw
      rw [hKesplit, Complex.add_re, Complex.re_ofReal_mul]
      nlinarith [hwre]
    have him1 : (star w ⬝ᵥ ((K - (eps : ℂ) • 1) *ᵥ w)).im = 0 :=
      herm_quad_im_zero hKe_herm w
    rw [hsplit, Complex.mul_conj]
    refine Complex.lt_def.mpr ⟨?_, ?_⟩
    · simp only [Complex.zero_re, Complex.add_re, Complex.ofReal_re]
      nlinarith [hterm1, hx0, hwre, Complex.normSq_nonneg dt,
        mul_nonneg hbeta.le hwre]
    · simp only [Complex.zero_im, Complex.add_im, Complex.ofReal_im,
        add_zero]
      exact him1.symm

private theorem posDef_mulVec_inj {M : Matrix ι ι ℂ} (hM : M.PosDef)
    {u v : ι → ℂ} (h : M *ᵥ u = M *ᵥ v) : u = v := by
  by_contra hne
  have hzero : M *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2
    (sub_ne_zero.mpr hne)
  rw [hzero] at hpos
  simp at hpos

/-- **Node A3, uniqueness form.**  Under the floor package the graph system
`C·y = −d·r` has the tracked eigen-decomposition as its unique solution;
combined with A2 this is exactly the ratified identity `C⁻¹r = q − d⁻¹ξ`. -/
theorem trialGraphOperator_inverse_residual_unique
    (K : Matrix ι ι ℂ) (q ξ y : ι → ℂ) (a eps beta : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (heps : eps ≤ a)
    (hfloor : ∀ w : ι → ℂ, star q ⬝ᵥ w = 0 →
      beta * (star w ⬝ᵥ w).re ≤
        (star w ⬝ᵥ ((K - (a : ℂ) • 1) *ᵥ w)).re)
    (hξ : K *ᵥ ξ = (eps : ℂ) • ξ)
    (hy : trialGraphOperator K q eps *ᵥ y =
      -((star q ⬝ᵥ ξ) • (K *ᵥ q - (star q ⬝ᵥ (K *ᵥ q)) • q))) :
    y = ξ - (star q ⬝ᵥ ξ) • q :=
  posDef_mulVec_inj
    (trialGraphOperator_posDef K q a eps beta hK hq hbeta heps hfloor)
    (hy.trans
      (trialGraphOperator_inverse_residual_identity K q ξ eps hq hξ).symm)

/-- **Node A3, inverse form.**  The literal ratified identity
`C⁻¹·(d·r) = d·q − ξ`, i.e. `C⁻¹ r = q − d⁻¹ ξ` after scaling. -/
theorem trialGraphOperator_inv_mulVec_residual
    (K : Matrix ι ι ℂ) (q ξ : ι → ℂ) (a eps beta : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (heps : eps ≤ a)
    (hfloor : ∀ w : ι → ℂ, star q ⬝ᵥ w = 0 →
      beta * (star w ⬝ᵥ w).re ≤
        (star w ⬝ᵥ ((K - (a : ℂ) • 1) *ᵥ w)).re)
    (hξ : K *ᵥ ξ = (eps : ℂ) • ξ) :
    (trialGraphOperator K q eps)⁻¹ *ᵥ
        ((star q ⬝ᵥ ξ) • (K *ᵥ q - (star q ⬝ᵥ (K *ᵥ q)) • q)) =
      (star q ⬝ᵥ ξ) • q - ξ := by
  have hC := trialGraphOperator_posDef K q a eps beta hK hq hbeta heps hfloor
  have hid := trialGraphOperator_inverse_residual_identity K q ξ eps hq hξ
  have hrew : (star q ⬝ᵥ ξ) • (K *ᵥ q - (star q ⬝ᵥ (K *ᵥ q)) • q) =
      trialGraphOperator K q eps *ᵥ
        ((star q ⬝ᵥ ξ) • q - ξ) := by
    have := congrArg Neg.neg hid
    rw [neg_neg] at this
    rw [← this, ← Matrix.mulVec_neg]
    congr 1
    funext i
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hrew, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hC.isUnit),
    Matrix.one_mulVec]

/-! ## Node C1: penalty lower envelopes -/

private theorem normSq_dot_le (q x : ι → ℂ) (hq : star q ⬝ᵥ q = 1) :
    Complex.normSq (star q ⬝ᵥ x) ≤ (star x ⬝ᵥ x).re := by
  classical
  set dt : ℂ := star q ⬝ᵥ x with hdt
  set w : ι → ℂ := x - dt • q with hwdef
  have hqw : star q ⬝ᵥ w = 0 := by
    rw [hwdef, dotProduct_sub, dotProduct_smul, hq, smul_eq_mul, mul_one,
      ← hdt, sub_self]
  have hxw : x = w + dt • q := by
    rw [hwdef]
    funext i
    simp
  have hlen : star x ⬝ᵥ x = star w ⬝ᵥ w + ((Complex.normSq dt : ℝ) : ℂ) := by
    conv_lhs => rw [hxw]
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
    have h1 : star w ⬝ᵥ (dt • q) = 0 := by
      rw [dotProduct_smul, smul_eq_mul, dot_star_swap w q, hqw]
      simp
    have h2 : star (dt • q) ⬝ᵥ w = 0 := by
      rw [star_smul, smul_dotProduct, hqw]
      simp
    have h3 : star (dt • q) ⬝ᵥ (dt • q) = ((Complex.normSq dt : ℝ) : ℂ) := by
      rw [star_smul, smul_dotProduct, dotProduct_smul, hq]
      simp [Complex.normSq_eq_conj_mul_self, mul_comm]
    rw [h1, h2, h3]
    ring
  have hw0 : 0 ≤ (star w ⬝ᵥ w).re := by
    rw [dot_star_self_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have := congrArg Complex.re hlen
  rw [Complex.add_re, Complex.ofReal_re] at this
  linarith

/-- **Node C1, identity metric.**  A rank-one penalty certificate yields the
exact lower envelope: `s := τ − (b − a) ≥ 0` and every unit-normalized
quadratic value sits above `b − τ = a − s`. -/
theorem penalty_lower_envelope
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a b tau : ℝ)
    (hq : star q ⬝ᵥ q = 1)
    (ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ))
    (htau : 0 ≤ tau)
    (hcert : (K - (b : ℂ) • 1 +
      (tau : ℂ) • Matrix.vecMulVec q (star q)).PosSemidef) :
    b - a ≤ tau ∧
      ∀ x : ι → ℂ,
        (b - tau) * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (K *ᵥ x)).re := by
  classical
  have hval : ∀ x : ι → ℂ,
      star x ⬝ᵥ ((K - (b : ℂ) • 1 +
        (tau : ℂ) • Matrix.vecMulVec q (star q)) *ᵥ x) =
      star x ⬝ᵥ (K *ᵥ x) - (b : ℂ) * (star x ⬝ᵥ x) +
        (tau : ℂ) * ((star q ⬝ᵥ x) * starRingEnd ℂ (star q ⬝ᵥ x)) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul]
    have hop : (MulOpposite.op (star q ⬝ᵥ x)) • q = (star q ⬝ᵥ x) • q := by
      funext i
      simp [MulOpposite.smul_eq_mul_unop, mul_comm]
    rw [hop, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      dot_star_swap x q]
  have hnn := Matrix.PosSemidef.dotProduct_mulVec_nonneg hcert
  constructor
  · have h0 := hnn q
    rw [hval q, hq, ha] at h0
    have h1 : ((0 : ℝ) : ℂ) ≤ ((a - b + tau : ℝ) : ℂ) := by
      convert h0 using 1 <;>
        · push_cast
          simp only [map_one]
          try ring
    have h2 := Complex.real_le_real.mp h1
    linarith
  · intro x
    have h0 := hnn x
    rw [hval x, Complex.mul_conj] at h0
    have hre := (Complex.le_def.mp h0).1
    simp only [Complex.zero_re, Complex.add_re, Complex.sub_re,
      Complex.re_ofReal_mul, Complex.ofReal_re] at hre
    have hcs := normSq_dot_le q x hq
    nlinarith [hcs, htau]

/-! ## Node C2: finite Schur minimal-slack criterion -/

private theorem trialGraphOperator_herm
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (b : ℝ) (hK : K.IsHermitian) :
    (trialGraphOperator K q b)ᴴ = trialGraphOperator K q b := by
  have hP_herm : (Matrix.vecMulVec q (star q))ᴴ = Matrix.vecMulVec q (star q) := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hQ_herm : (1 - Matrix.vecMulVec q (star q))ᴴ =
      1 - Matrix.vecMulVec q (star q) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
  have hKe_herm : (K - (b : ℂ) • 1)ᴴ = K - (b : ℂ) • 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hK.eq,
      Matrix.conjTranspose_one]
    congr 1
    simp [Complex.conj_ofReal]
  rw [trialGraphOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hP_herm, hQ_herm, hKe_herm]
  rw [mul_assoc]

private theorem dot_q_perp_sub (q w z : ι → ℂ) (hwq : star q ⬝ᵥ w = 0) :
    star w ⬝ᵥ ((1 - Matrix.vecMulVec q (star q)) *ᵥ z) = star w ⬝ᵥ z := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.vecMulVec_mulVec]
  have hop : (MulOpposite.op (star q ⬝ᵥ z)) • q = (star q ⬝ᵥ z) • q := by
    funext i
    simp [MulOpposite.smul_eq_mul_unop, mul_comm]
  rw [hop, dotProduct_smul, smul_eq_mul, dot_star_swap w q, hwq]
  simp

/-- **Node C2, exact quadratic split.**  With the Schur witness
`u = C_b⁻¹ r` (given through its defining equations), the penalty quadratic
splits exactly as a `C_b`-square plus the slack coefficient — the ratified
completion-of-squares identity behind `s_min = r*(B−bI)⁻¹r`. -/
theorem penalty_quadratic_split
    (K : Matrix ι ι ℂ) (q u x : ι → ℂ) (a b tau : ℝ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ))
    (hqu : star q ⬝ᵥ u = 0)
    (hu : trialGraphOperator K q b *ᵥ u = K *ᵥ q - (a : ℂ) • q) :
    star x ⬝ᵥ ((K - (b : ℂ) • 1 +
        (tau : ℂ) • Matrix.vecMulVec q (star q)) *ᵥ x) =
      star ((x - (star q ⬝ᵥ x) • q) + (star q ⬝ᵥ x) • u) ⬝ᵥ
          (trialGraphOperator K q b *ᵥ
            ((x - (star q ⬝ᵥ x) • q) + (star q ⬝ᵥ x) • u)) +
        ((star q ⬝ᵥ x) * starRingEnd ℂ (star q ⬝ᵥ x)) *
          (((a - b + tau : ℝ) : ℂ) -
            star u ⬝ᵥ (K *ᵥ q - (a : ℂ) • q)) := by
  classical
  set c : ℂ := star q ⬝ᵥ x with hc
  set w : ι → ℂ := x - c • q with hwdef
  set r : ι → ℂ := K *ᵥ q - (a : ℂ) • q with hrdef
  have hqw : star q ⬝ᵥ w = 0 := by
    rw [hwdef, dotProduct_sub, dotProduct_smul, hq, smul_eq_mul, mul_one,
      ← hc, sub_self]
  have hqr : star q ⬝ᵥ r = 0 := by
    rw [hrdef, dotProduct_sub, dotProduct_smul, hq, ha, smul_eq_mul, mul_one,
      sub_self]
  have hwq0 : star w ⬝ᵥ q = 0 := by
    rw [dot_star_swap w q, hqw]
    simp
  have huq0 : star u ⬝ᵥ q = 0 := by
    rw [dot_star_swap u q, hqu]
    simp
  -- C_b action on q-perp vectors, paired against q-perp vectors
  have hCpair : ∀ v z : ι → ℂ, star q ⬝ᵥ v = 0 → star q ⬝ᵥ z = 0 →
      star v ⬝ᵥ (trialGraphOperator K q b *ᵥ z) =
        star v ⬝ᵥ ((K - (b : ℂ) • 1) *ᵥ z) := by
    intro v z hv hz
    have hvq : star v ⬝ᵥ q = 0 := by
      rw [dot_star_swap v q, hv]
      simp
    have hPz : Matrix.vecMulVec q (star q) *ᵥ z = 0 := by
      rw [Matrix.vecMulVec_mulVec, hz]
      simp
    have hQz : (1 - Matrix.vecMulVec q (star q)) *ᵥ z = z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPz, sub_zero]
    rw [trialGraphOperator, Matrix.add_mulVec, dotProduct_add,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQz, hPz,
      dotProduct_zero, add_zero, dot_q_perp_sub q v _ hv]
  -- the Hermitian transfer for C_b
  have hCherm := trialGraphOperator_herm K q b hK
  have hCtransfer : ∀ v z : ι → ℂ,
      star v ⬝ᵥ (trialGraphOperator K q b *ᵥ z) =
        star (trialGraphOperator K q b *ᵥ v) ⬝ᵥ z := by
    intro v z
    rw [Matrix.dotProduct_mulVec, ← hCherm, ← Matrix.star_mulVec, hCherm]
  -- scalar atoms
  have hxw : x = w + c • q := by
    rw [hwdef]
    funext i
    simp
  -- expand both sides into atoms and close by ring
  have hru : star w ⬝ᵥ (trialGraphOperator K q b *ᵥ u) = star w ⬝ᵥ r := by
    rw [hu]
  have ht3 : star u ⬝ᵥ (trialGraphOperator K q b *ᵥ w) = star r ⬝ᵥ w := by
    rw [hCtransfer u w, hu]
  have ht4 : star u ⬝ᵥ (trialGraphOperator K q b *ᵥ u) = star u ⬝ᵥ r := by
    rw [hu]
  have ht1 : star w ⬝ᵥ (trialGraphOperator K q b *ᵥ w) =
      star w ⬝ᵥ ((K - (b : ℂ) • 1) *ᵥ w) := hCpair w w hqw hqw
  -- the C_b-square, fully expanded into atoms
  have hS : star (w + c • u) ⬝ᵥ (trialGraphOperator K q b *ᵥ (w + c • u)) =
      star w ⬝ᵥ ((K - (b : ℂ) • 1) *ᵥ w) + c * (star w ⬝ᵥ r) +
        starRingEnd ℂ c * (star r ⬝ᵥ w) +
        c * starRingEnd ℂ c * (star u ⬝ᵥ r) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul,
      add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, ht1, hru, ht3, ht4]
    simp only [smul_eq_mul, RCLike.star_def]
    ring
  -- the K-quadratic, expanded through the decomposition x = w + c·q
  have hwKq : star w ⬝ᵥ (K *ᵥ q) = star w ⬝ᵥ r := by
    rw [hrdef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hwq0, mul_zero,
      sub_zero]
  have hqKw : star q ⬝ᵥ (K *ᵥ w) = star r ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, ← hK.eq, ← Matrix.star_mulVec]
    have hKq : K *ᵥ q = r + ((a : ℝ) : ℂ) • q := by
      rw [hrdef]
      funext i
      simp
    rw [hKq, star_add, add_dotProduct, star_smul, smul_dotProduct]
    simp [RCLike.star_def, Complex.conj_ofReal, hqw]
  have hxKx : star x ⬝ᵥ (K *ᵥ x) =
      star w ⬝ᵥ (K *ᵥ w) + c * (star w ⬝ᵥ r) +
        starRingEnd ℂ c * (star r ⬝ᵥ w) +
        c * starRingEnd ℂ c * (a : ℂ) := by
    conv_lhs => rw [hxw]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul,
      add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hwKq, hqKw, ha]
    simp only [smul_eq_mul, RCLike.star_def]
    ring
  have hxx : star x ⬝ᵥ x = star w ⬝ᵥ w + c * starRingEnd ℂ c := by
    conv_lhs => rw [hxw]
    rw [star_add, star_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      hq, hwq0, hqw]
    simp only [smul_eq_mul, RCLike.star_def]
    ring
  have hwsub : star w ⬝ᵥ ((K - (b : ℂ) • 1) *ᵥ w) =
      star w ⬝ᵥ (K *ᵥ w) - (b : ℂ) * (star w ⬝ᵥ w) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
  -- the penalty quadratic in matrix-expanded form (as in Node C1)
  have hval : star x ⬝ᵥ ((K - (b : ℂ) • 1 +
      (tau : ℂ) • Matrix.vecMulVec q (star q)) *ᵥ x) =
      star x ⬝ᵥ (K *ᵥ x) - (b : ℂ) * (star x ⬝ᵥ x) +
        (tau : ℂ) * (c * starRingEnd ℂ c) := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul]
    have hop : (MulOpposite.op (star q ⬝ᵥ x)) • q = (star q ⬝ᵥ x) • q := by
      funext i
      simp [MulOpposite.smul_eq_mul_unop, mul_comm]
    rw [hop, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      dot_star_swap x q, ← hc]
  rw [hval, hS, hxKx, hxx, hwsub]
  push_cast
  ring

/-- **Node C1, Gram metric.**  The generalized-metric penalty envelope in the
exact `H2aPenalty` shape. -/
theorem penalty_lower_envelope_gram
    (K G : Matrix ι ι ℂ) (q : ι → ℂ) (a b tau : ℝ)
    (hG : G.PosSemidef)
    (hq : star q ⬝ᵥ (G *ᵥ q) = 1)
    (ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ))
    (htau : 0 ≤ tau)
    (hcert : (K - (b : ℂ) • G +
      (tau : ℂ) •
        Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef) :
    b - a ≤ tau ∧
      ∀ x : ι → ℂ, star x ⬝ᵥ (G *ᵥ x) = 1 →
        b - tau ≤ (star x ⬝ᵥ (K *ᵥ x)).re := by
  classical
  have hGherm := hG.1
  have hval : ∀ x : ι → ℂ,
      star x ⬝ᵥ ((K - (b : ℂ) • G +
        (tau : ℂ) •
          Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))) *ᵥ x) =
      star x ⬝ᵥ (K *ᵥ x) - (b : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) +
        (tau : ℂ) * ((star (G *ᵥ q) ⬝ᵥ x) *
          starRingEnd ℂ (star (G *ᵥ q) ⬝ᵥ x)) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_add,
      dotProduct_sub, dotProduct_smul, dotProduct_smul]
    have hop : (MulOpposite.op (star (G *ᵥ q) ⬝ᵥ x)) • (G *ᵥ q) =
        (star (G *ᵥ q) ⬝ᵥ x) • (G *ᵥ q) := by
      funext i
      simp [MulOpposite.smul_eq_mul_unop, mul_comm]
    rw [hop, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      dot_star_swap x (G *ᵥ q)]
  have hGq_q : star (G *ᵥ q) ⬝ᵥ q = 1 := by
    rw [dot_star_swap (G *ᵥ q) q, hq]
    simp
  have hnn := Matrix.PosSemidef.dotProduct_mulVec_nonneg hcert
  constructor
  · have h0 := hnn q
    rw [hval q, hq, ha, hGq_q] at h0
    have h1 : ((0 : ℝ) : ℂ) ≤ ((a - b + tau : ℝ) : ℂ) := by
      convert h0 using 1 <;>
        · push_cast
          simp only [map_one]
          try ring
    have h2 := Complex.real_le_real.mp h1
    linarith
  · intro x hxG
    -- Gram Cauchy-Schwarz through the G-orthogonal defect
    have hcs : Complex.normSq (star (G *ᵥ q) ⬝ᵥ x) ≤ 1 := by
      set tsc : ℂ := star (G *ᵥ q) ⬝ᵥ x with hts
      set y : ι → ℂ := x - tsc • q with hydef
      have htransfer : star q ⬝ᵥ (G *ᵥ x) = tsc := by
        rw [Matrix.dotProduct_mulVec, ← hGherm.eq, ← Matrix.star_mulVec]
      have hyG := Matrix.PosSemidef.dotProduct_mulVec_nonneg hG y
      have hyval : star y ⬝ᵥ (G *ᵥ y) =
          star x ⬝ᵥ (G *ᵥ x) - tsc * starRingEnd ℂ tsc := by
        rw [hydef, star_sub, sub_dotProduct, Matrix.mulVec_sub,
          Matrix.mulVec_smul, dotProduct_sub, dotProduct_sub]
        simp only [smul_dotProduct, dotProduct_smul, star_smul,
          smul_eq_mul, RCLike.star_def]
        rw [hq, htransfer, dot_star_swap x (G *ᵥ q), ← hts]
        ring
      rw [hyval, hxG] at hyG
      have hre := (Complex.le_def.mp hyG).1
      simp only [Complex.zero_re, Complex.sub_re, Complex.one_re] at hre
      have hnsq : (tsc * starRingEnd ℂ tsc).re = Complex.normSq tsc := by
        rw [Complex.mul_conj]
        simp
      rw [hnsq] at hre
      linarith
    have h0 := hnn x
    rw [hval x, hxG, Complex.mul_conj] at h0
    have hre := (Complex.le_def.mp h0).1
    simp only [mul_one, Complex.zero_re, Complex.add_re, Complex.sub_re,
      Complex.re_ofReal_mul, Complex.ofReal_re] at hre
    nlinarith [hcs, htau]

/-! ## Node B2: complexified commutator and the entire moved-action formula -/

private theorem vecMulVec_map (u v : ι → ℝ) :
    (Matrix.vecMulVec u v).map (Complex.ofRealHom) =
      Matrix.vecMulVec (fun i => ((u i : ℝ) : ℂ))
        (fun i => ((v i : ℝ) : ℂ)) := by
  ext i j
  simp [Matrix.map_apply, Matrix.vecMulVec_apply]

/-- **Node B2a.**  The rank-two commutator of the complete source matrix,
ported entrywise to the complex carrier. -/
theorem ccmWeilMatFinite_commutator_complex
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    (ccmModeDiagFinite N).map Complex.ofRealHom *
        (ccmWeilMatFinite mProject N).map Complex.ofRealHom -
      (ccmWeilMatFinite mProject N).map Complex.ofRealHom *
        (ccmModeDiagFinite N).map Complex.ofRealHom =
      Matrix.vecMulVec (fun i => ((ccmBetaFinite mProject N i : ℝ) : ℂ))
          (fun i => ((ccmEtaFinite N i : ℝ) : ℂ)) -
        Matrix.vecMulVec (fun i => ((ccmEtaFinite N i : ℝ) : ℂ))
          (fun i => ((ccmBetaFinite mProject N i : ℝ) : ℂ)) := by
  have h := ccmWeilMatFinite_commutator mProject N hm hN
  have hmap := congrArg (fun A => A.map Complex.ofRealHom) h
  simpa [Matrix.map_sub, Matrix.map_mul, vecMulVec_map] using hmap

/-- **Node B2b.**  The entire moved-action formula: given the rank-two
commutator and the diagonal resolvent row, the moved source action is an
exact finite-rank expression — valid on ALL of `ℂ` because no inverse
appears on either side. -/
theorem movedAction_entire_formula
    (D M : Matrix ι ι ℂ) (beta eta kappa : ι → ℂ) (w s aC : ℂ)
    (hcomm : D * M - M * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (hres : (D - w • 1) *ᵥ kappa = s • eta) :
    (D - w • 1) *ᵥ ((M - aC • 1) *ᵥ kappa) =
      s • (M *ᵥ eta - aC • eta) +
        ((eta ⬝ᵥ kappa) • beta - (beta ⬝ᵥ kappa) • eta) := by
  have hswap : (D - w • 1) * (M - aC • 1) =
      (M - aC • 1) * (D - w • 1) +
        (Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) := by
    rw [← hcomm]
    ext i j
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [Matrix.mulVec_mulVec, hswap, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hres, Matrix.mulVec_smul,
    Matrix.sub_mulVec (Matrix.vecMulVec beta eta),
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  rw [Matrix.sub_mulVec M, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/-! ## Node D1: the centering-factor bound -/

/-- **Node D1.**  The compact centering bound from the exact central anchor
`rawFplus(0) = √L · c₀` and the inverse-log center floor `c* ≤ L·|c₀|²`. -/
theorem centering_factor_bound
    (L cstar : ℝ) (y c0 Xi0 : ℂ)
    (hcpos : 0 < cstar)
    (hfloor : cstar ≤ L * Complex.normSq c0)
    (hanchor : y = (Real.sqrt L : ℂ) * c0)
    (hL : 0 ≤ L) :
    ‖Xi0 / y‖ ≤ ‖Xi0‖ / Real.sqrt cstar := by
  have hy2 : ‖y‖ ^ 2 = L * Complex.normSq c0 := by
    rw [hanchor, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg L), Real.sq_sqrt hL,
      Complex.sq_norm]
  have hylow : Real.sqrt cstar ≤ ‖y‖ := by
    have h1 : Real.sqrt cstar ≤ Real.sqrt (‖y‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [hy2]
      exact hfloor
    rwa [Real.sqrt_sq (norm_nonneg y)] at h1
  have hy0 : (0 : ℝ) < ‖y‖ := lt_of_lt_of_le (Real.sqrt_pos.mpr hcpos) hylow
  rw [norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg Xi0) (Real.sqrt_pos.mpr hcpos)
    hylow

/-! ## Node A4 mechanism: scalar transport of the P59 transform -/

/-- **Node A4.**  The finite Proposition-59 raw transform is homogeneous in
the coefficient row: the graph normalization `d⁻¹·ξ` transports to an exact
nonzero scalar multiple of the same ground transform. -/
theorem proposition59RawTransform_smul
    (L : ℝ) (S : Finset ℤ) (xi : ℤ → ℂ) (c z : ℂ) :
    proposition59RawTransform L S (fun k => c * xi k) z =
      c * proposition59RawTransform L S xi z := by
  unfold proposition59RawTransform
  rw [show (∑ k ∈ S, (c * xi k) * proposition59PoleKernel L k z) =
      c * ∑ k ∈ S, xi k * proposition59PoleKernel L k z by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring]
  ring

#print axioms proposition59PoleKernel_diagonal_resolvent
#print axioms trialGraphOperator_inverse_residual_identity
#print axioms trialGraphOperator_posDef
#print axioms trialGraphOperator_inverse_residual_unique
#print axioms trialGraphOperator_inv_mulVec_residual
#print axioms penalty_lower_envelope
#print axioms penalty_quadratic_split
#print axioms penalty_lower_envelope_gram
#print axioms ccmWeilMatFinite_commutator_complex
#print axioms movedAction_entire_formula
#print axioms centering_factor_bound
#print axioms proposition59RawTransform_smul

end Q3.RouteB
