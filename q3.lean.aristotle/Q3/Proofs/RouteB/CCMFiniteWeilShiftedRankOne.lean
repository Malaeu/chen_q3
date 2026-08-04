import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator
import Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1, Lemmas 5.1, 5.2, and 5.4
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- scope: exact shifted finite CCM source algebra under a conditional normalized
  even eigenvector
- no minimum-eigenvalue, positivity, simplicity, H2a, or H2b claim is made here
-/

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- The exact CCM metric matrix shifted by the conditional eigenvalue. -/
noncomputable def ccmShiftedWeilMatFinite
    (mProject N : ℕ) (epsilon : ℝ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  ccmWeilMatFinite mProject N -
    epsilon • (1 : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ)

/-- The finite operator represented by the shifted CCM metric matrix. -/
noncomputable def ccmShiftedWeilOpFinite
    (mProject N : ℕ) (epsilon : ℝ) :
    Module.End ℝ (CCMModeFinite N → ℝ) :=
  (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin

@[simp] theorem ccmNegFinite_center (N : ℕ) :
    ccmNegFinite N (ccmCenterFinite N) = ccmCenterFinite N := by
  apply Fin.ext
  simp only [ccmNegFinite, ccmCenterFinite]
  omega

@[simp] theorem ccmNegFinite_involutive
    (N : ℕ) (i : CCMModeFinite N) :
    ccmNegFinite N (ccmNegFinite N i) = i := by
  apply Fin.ext
  simp only [ccmNegFinite]
  omega

theorem ccmBetaFinite_neg
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (i : CCMModeFinite N) :
    ccmBetaFinite mProject N (ccmNegFinite N i) =
      -ccmBetaFinite mProject N i := by
  have hcentro :=
    ccmWeilMatFinite_centrosymmetric mProject N hm hN
      i (ccmCenterFinite N)
  rw [ccmNegFinite_center] at hcentro
  unfold ccmBetaFinite
  rw [ccmModeFinite_neg, hcentro]
  push_cast
  ring

theorem ccmBetaFinite_dotProduct_eq_zero_of_even
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (xi : CCMModeFinite N → ℝ)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i) :
    ccmBetaFinite mProject N ⬝ᵥ xi = 0 := by
  classical
  let negEquiv : CCMModeFinite N ≃ CCMModeFinite N :=
    { toFun := ccmNegFinite N
      invFun := ccmNegFinite N
      left_inv := ccmNegFinite_involutive N
      right_inv := ccmNegFinite_involutive N }
  have hsum := negEquiv.sum_comp
    (fun i => ccmBetaFinite mProject N i * xi i)
  dsimp [negEquiv] at hsum
  have hneg :
      (∑ i, ccmBetaFinite mProject N (ccmNegFinite N i) *
          xi (ccmNegFinite N i)) =
        -(∑ i, ccmBetaFinite mProject N i * xi i) := by
    calc
      (∑ i, ccmBetaFinite mProject N (ccmNegFinite N i) *
          xi (ccmNegFinite N i)) =
          ∑ i, -(ccmBetaFinite mProject N i * xi i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [ccmBetaFinite_neg mProject N hm hN, hxiEven]
            ring
      _ = -(∑ i, ccmBetaFinite mProject N i * xi i) := by
        rw [Finset.sum_neg_distrib]
  rw [hneg] at hsum
  unfold dotProduct
  linarith

theorem ccmShiftedWeilMatFinite_transpose_eq
    (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    (ccmShiftedWeilMatFinite mProject N epsilon).transpose =
      ccmShiftedWeilMatFinite mProject N epsilon := by
  unfold ccmShiftedWeilMatFinite
  rw [Matrix.transpose_sub, ccmWeilMatFinite_transpose_eq mProject N hm hN]
  simp

theorem ccmShiftedWeilMatFinite_commutator
    (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    ccmShiftedWeilMatFinite mProject N epsilon * ccmModeDiagFinite N -
        ccmModeDiagFinite N * ccmShiftedWeilMatFinite mProject N epsilon =
      -Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) +
        Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N) := by
  have hsource := ccmWeilMatFinite_commutator mProject N hm hN
  calc
    ccmShiftedWeilMatFinite mProject N epsilon * ccmModeDiagFinite N -
          ccmModeDiagFinite N * ccmShiftedWeilMatFinite mProject N epsilon =
        ccmWeilMatFinite mProject N * ccmModeDiagFinite N -
          ccmModeDiagFinite N * ccmWeilMatFinite mProject N := by
            simp [ccmShiftedWeilMatFinite, Matrix.sub_mul, Matrix.mul_sub]
    _ = -(ccmModeDiagFinite N * ccmWeilMatFinite mProject N -
          ccmWeilMatFinite mProject N * ccmModeDiagFinite N) := by
            abel
    _ = -(Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) -
          Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N)) := by
            rw [hsource]
    _ = -Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) +
          Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N) := by
            abel

theorem ccmShiftedWeilMatFinite_kills_eigenvector
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi) :
    Matrix.mulVec (ccmShiftedWeilMatFinite mProject N epsilon) xi = 0 := by
  unfold ccmShiftedWeilMatFinite
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig]
  exact sub_self _

theorem ccmShiftedWeilMatFinite_mulVec_modeDiag_eq_neg_beta
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1) :
    Matrix.mulVec (ccmShiftedWeilMatFinite mProject N epsilon)
        (Matrix.mulVec (ccmModeDiagFinite N) xi) =
      -ccmBetaFinite mProject N := by
  have hcomm :=
    ccmShiftedWeilMatFinite_commutator mProject N epsilon hm hN
  have hkill :=
    ccmShiftedWeilMatFinite_kills_eigenvector
      mProject N epsilon xi heig
  have horth :=
    ccmBetaFinite_dotProduct_eq_zero_of_even
      mProject N hm hN xi hxiEven
  have happ := congrArg (fun M => Matrix.mulVec M xi) hcomm
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec] at happ
  simpa [hkill, hnormalized, horth] using happ

theorem ccmShiftedWeil_rankOneCorrection_kernel_and_weightedSymmetric
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1) :
    Matrix.mulVec
          (rankOneCorrection
            (ccmModeDiagFinite N) xi (ccmEtaFinite N)) xi = 0 ∧
      ccmShiftedWeilMatFinite mProject N epsilon *
          rankOneCorrection
            (ccmModeDiagFinite N) xi (ccmEtaFinite N) =
        (rankOneCorrection
            (ccmModeDiagFinite N) xi (ccmEtaFinite N)).transpose *
          ccmShiftedWeilMatFinite mProject N epsilon := by
  have hD : (ccmModeDiagFinite N).transpose = ccmModeDiagFinite N := by
    simp [ccmModeDiagFinite]
  exact rankOneCorrection_kernel_and_weightedSymmetric
    (ccmShiftedWeilMatFinite mProject N epsilon)
    (ccmModeDiagFinite N)
    xi (ccmBetaFinite mProject N) (ccmEtaFinite N)
    (ccmShiftedWeilMatFinite_transpose_eq mProject N epsilon hm hN)
    hD
    (ccmShiftedWeilMatFinite_commutator mProject N epsilon hm hN)
    (ccmShiftedWeilMatFinite_mulVec_modeDiag_eq_neg_beta
      mProject N epsilon xi hm hN heig hxiEven hnormalized)
    hnormalized

#print axioms ccmBetaFinite_dotProduct_eq_zero_of_even
#print axioms ccmShiftedWeilMatFinite_commutator
#print axioms ccmShiftedWeilMatFinite_mulVec_modeDiag_eq_neg_beta
#print axioms ccmShiftedWeil_rankOneCorrection_kernel_and_weightedSymmetric

end Q3.RouteB
