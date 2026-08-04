import Q3.Proofs.RouteB.CCMFiniteWeilBottomSpectral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1, Lemma 5.2, Definition 5.3, and the
  normalization argument immediately before Lemma 5.4
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- scope: exact post-evenness nonvanishing of the finite CCM eta pairing
- evenness and one-dimensionality remain explicit inputs; this file does not
  bootstrap them from normalization and makes no H2a, H2b, route, or RH claim
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- The source-mode diagonal sends an even vector to an odd vector. -/
theorem ccmModeDiagFinite_mulVec_odd_of_even
    (N : ℕ)
    (xi : CCMModeFinite N → ℝ)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i) :
    ∀ i,
      Matrix.mulVec (ccmModeDiagFinite N) xi
          (ccmNegFinite N i) =
        -Matrix.mulVec (ccmModeDiagFinite N) xi i := by
  intro i
  simp only [ccmModeDiagFinite, Matrix.mulVec_diagonal,
    ccmModeFinite_neg, Int.cast_neg, hxiEven]
  ring

/-- A nonzero vector killed by the exact source-mode diagonal has nonzero
pairing with the all-ones source vector: only its central coordinate can
survive. -/
theorem ccmEtaFinite_dotProduct_ne_zero_of_modeDiag_mulVec_eq_zero
    (N : ℕ)
    (xi : CCMModeFinite N → ℝ)
    (hxi0 : xi ≠ 0)
    (hDxi : Matrix.mulVec (ccmModeDiagFinite N) xi = 0) :
    ccmEtaFinite N ⬝ᵥ xi ≠ 0 := by
  classical
  have houtside : ∀ i : CCMModeFinite N,
      i ≠ ccmCenterFinite N → xi i = 0 := by
    intro i hi
    have hmodeInt : ccmModeFinite N i ≠ 0 := by
      intro hmode
      apply hi
      apply ccmModeFinite_injective N
      simpa using hmode
    have hmodeReal : (ccmModeFinite N i : ℝ) ≠ 0 := by
      exact_mod_cast hmodeInt
    have hcoord := congrFun hDxi i
    simp only [ccmModeDiagFinite, Matrix.mulVec_diagonal] at hcoord
    exact (mul_eq_zero.mp hcoord).resolve_left hmodeReal
  intro heta
  apply hxi0
  have hsum : (∑ i : CCMModeFinite N, xi i) = 0 := by
    simpa [ccmEtaFinite, dotProduct] using heta
  have hsumCenter :
      (∑ i : CCMModeFinite N, xi i) = xi (ccmCenterFinite N) := by
    rw [Finset.sum_eq_single (ccmCenterFinite N)]
    · intro i _ hi
      exact houtside i hi
    · simp
  have hcenter : xi (ccmCenterFinite N) = 0 := by
    rw [hsumCenter] at hsum
    exact hsum
  funext i
  by_cases hi : i = ccmCenterFinite N
  · simpa [hi] using hcenter
  · exact houtside i hi

/-- Once evenness is supplied independently, the exact shifted CCM source
commutator and a simple shifted kernel force the eta pairing to be nonzero. -/
theorem ccmEtaFinite_dotProduct_ne_zero_of_even_simple_shifted_kernel
    (mProject N : ℕ)
    (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (hxi0 : xi ≠ 0)
    (hTxi :
      Matrix.mulVec
        (ccmShiftedWeilMatFinite mProject N epsilon) xi = 0)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hker1 :
      Module.finrank ℝ
        (LinearMap.ker
          (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin) = 1) :
    ccmEtaFinite N ⬝ᵥ xi ≠ 0 := by
  classical
  let T := ccmShiftedWeilMatFinite mProject N epsilon
  let Dxi := Matrix.mulVec (ccmModeDiagFinite N) xi
  have hker : LinearMap.ker T.mulVecLin = ℝ ∙ xi := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      rw [LinearMap.mem_ker]
      simpa [T] using hTxi
    · rw [finrank_span_singleton hxi0]
      simpa [T] using hker1.symm
  intro heta
  by_cases hDxi : Dxi = 0
  · exact
      (ccmEtaFinite_dotProduct_ne_zero_of_modeDiag_mulVec_eq_zero
        N xi hxi0 (by simpa [Dxi] using hDxi)) heta
  · have hDodd : ∀ i,
        Dxi (ccmNegFinite N i) = -Dxi i := by
      simpa [Dxi] using
        ccmModeDiagFinite_mulVec_odd_of_even N xi hxiEven
    have hDnotker : Dxi ∉ LinearMap.ker T.mulVecLin := by
      intro hmem
      have hspan : Dxi ∈ ℝ ∙ xi := by
        rw [← hker]
        exact hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
      have hDzero : Dxi = 0 := by
        funext i
        have hc_i := congrFun hc i
        have hc_neg := congrFun hc (ccmNegFinite N i)
        have hneg : Dxi i = -Dxi i := by
          calc
            Dxi i = c * xi i := by simpa using hc_i.symm
            _ = c * xi (ccmNegFinite N i) := by rw [hxiEven]
            _ = Dxi (ccmNegFinite N i) := by simpa using hc_neg
            _ = -Dxi i := hDodd i
        change Dxi i = 0
        linarith
      exact hDxi hDzero
    have hTDxi_ne : Matrix.mulVec T Dxi ≠ 0 := by
      intro hzero
      apply hDnotker
      rw [LinearMap.mem_ker]
      simpa using hzero
    have hbeta : ccmBetaFinite mProject N ⬝ᵥ xi = 0 :=
      ccmBetaFinite_dotProduct_eq_zero_of_even
        mProject N hm hN xi hxiEven
    have hcomm :=
      ccmShiftedWeilMatFinite_commutator
        mProject N epsilon hm hN
    have happ := congrArg (fun M => Matrix.mulVec M xi) hcomm
    have hTDxi_zero : Matrix.mulVec T Dxi = 0 := by
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec] at happ
      simpa [T, Dxi, hTxi, heta, hbeta] using happ
    exact hTDxi_ne hTDxi_zero

/-- Eigenspace simplicity is the unshifted roof-facing form of the exact
post-evenness eta-nonvanishing theorem. -/
theorem ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector
    (mProject N : ℕ)
    (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (hxi0 : xi ≠ 0)
    (heig :
      Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hsimple :
      Module.finrank ℝ
        ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1) :
    ccmEtaFinite N ⬝ᵥ xi ≠ 0 := by
  apply ccmEtaFinite_dotProduct_ne_zero_of_even_simple_shifted_kernel
    mProject N epsilon xi hm hN hxi0
  · exact ccmShiftedWeilMatFinite_kills_eigenvector
      mProject N epsilon xi heig
  · exact hxiEven
  · have hkerEq :
        LinearMap.ker
            (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin =
          (ccmWeilOpFinite mProject N).eigenspace epsilon := by
      simpa [ccmShiftedWeilOpFinite] using
        ccmShiftedWeilOpFinite_ker_eq_eigenspace
          mProject N epsilon
    rw [hkerEq]
    exact hsimple

/-- A nonzero simple even eigenvector therefore admits the legal CCM
normalization with eta pairing equal to one. -/
theorem exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector
    (mProject N : ℕ)
    (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (hxi0 : xi ≠ 0)
    (heig :
      Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hsimple :
      Module.finrank ℝ
        ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1) :
    ∃ xi' : CCMModeFinite N → ℝ,
      xi' ≠ 0 ∧
      Matrix.mulVec (ccmWeilMatFinite mProject N) xi' = epsilon • xi' ∧
      (∀ i, xi' (ccmNegFinite N i) = xi' i) ∧
      ccmEtaFinite N ⬝ᵥ xi' = 1 := by
  let a := ccmEtaFinite N ⬝ᵥ xi
  have ha : a ≠ 0 :=
    ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector
      mProject N epsilon xi hm hN hxi0 heig hxiEven hsimple
  refine ⟨a⁻¹ • xi, ?_, ?_, ?_, ?_⟩
  · exact smul_ne_zero (inv_ne_zero ha) hxi0
  · rw [Matrix.mulVec_smul, heig]
    simp only [smul_smul]
    rw [mul_comm]
  · intro i
    simp [hxiEven]
  · simp [dotProduct_smul, a, ha]

#print axioms
  ccmEtaFinite_dotProduct_ne_zero_of_modeDiag_mulVec_eq_zero
#print axioms
  ccmEtaFinite_dotProduct_ne_zero_of_even_simple_shifted_kernel
#print axioms
  ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector
#print axioms
  exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector

end Q3.RouteB
