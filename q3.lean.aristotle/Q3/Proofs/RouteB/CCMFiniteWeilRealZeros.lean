import Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne
import Q3.Proofs.RouteB.RankOneCorrectionLagrangeRealZeros

set_option linter.mathlibStandardSet false

/-
Source lock:
- Connes–Consani–Moscovici, Zeta Spectral Triples
- arXiv:2511.22755v1, Lemmas 5.1, 5.2, and 5.4
- e-print SHA-256:
  96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a
- scope: exact finite CCM source-object weld to the already proved quotient-by-
  radical real-zero consumer
- shifted nonnegativity, one-dimensional radical, the simple even bottom
  eigenpair, H2a, and H2b remain explicit external obligations
-/

noncomputable section

namespace Q3.RouteB

/-- The exact shifted finite CCM source object feeds the generic
quotient-by-radical real-zero consumer once nonnegativity and a
one-dimensional radical are supplied. -/
theorem ccmSourceLagrangePolynomial_complex_zerosRealOn_of_shifted_nonneg_finrank_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig :
      Matrix.mulVec (ccmWeilMatFinite mProject N) xi = epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1)
    (hpos : ∀ x,
      0 ≤ Matrix.toBilin'
        (ccmShiftedWeilMatFinite mProject N epsilon) x x)
    (hker1 :
      Module.finrank ℝ
          (LinearMap.ker
            (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin) = 1)
    (b : Module.Basis ι ℝ
      ((CCMModeFinite N → ℝ) ⧸
        LinearMap.ker
          (Matrix.toBilin'
            (ccmShiftedWeilMatFinite mProject N epsilon)))) :
    ZerosRealOn Set.univ
      (fun z =>
        ((sourceLagrangePolynomial
            (fun i => (ccmModeFinite N i : ℝ)) xi).map
          (algebraMap ℝ ℂ)).eval z) := by
  simpa [ccmModeDiagFinite, ccmEtaFinite] using
    (sourceLagrangePolynomial_complex_zerosRealOn_of_radical_nonneg
      (T := ccmShiftedWeilMatFinite mProject N epsilon)
      (lam := fun i => (ccmModeFinite N i : ℝ))
      (xi := xi)
      (beta := ccmBetaFinite mProject N)
      (hT :=
        ccmShiftedWeilMatFinite_transpose_eq
          mProject N epsilon hm hN)
      (hpos := hpos)
      (hcomm :=
        ccmShiftedWeilMatFinite_commutator
          mProject N epsilon hm hN)
      (hTDxi :=
        ccmShiftedWeilMatFinite_mulVec_modeDiag_eq_neg_beta
          mProject N epsilon xi hm hN heig hxiEven hnormalized)
      (hnormalized := hnormalized)
      (hTxi :=
        ccmShiftedWeilMatFinite_kills_eigenvector
          mProject N epsilon xi heig)
      (hker1 := hker1)
      b)

#print axioms
  ccmSourceLagrangePolynomial_complex_zerosRealOn_of_shifted_nonneg_finrank_one

end Q3.RouteB
