import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The exact finite Galerkin projection reconstructed in the literal
logarithmic Fourier modes indexed by `modeSet i`.

This is Goal 056 / Phase 4D.  It consumes the unconditional orthonormality of
`V_n_m`, keeps the coefficient orientation `inner V_n f`, and returns the
subtype-valued projection in the ambient `H_m i`.  It proves no raw/Gwin
coordinate identity, residual crosswalk, decay statement, or `SlotS2` claim.
-/
theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
    (i : PairIndex) (f : H_m i) :
    (P_m_N i f : H_m i) =
      ∑ n ∈ modeSet i,
        inner ℂ (V_n_m i n) f • V_n_m i n := by
  classical
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  let sourceCarrier : Submodule ℂ (H_m i) :=
    Submodule.span ℂ ((modeSet i).image (V_n_m i) : Set (H_m i))
  have hcarrier : sourceCarrier = E_m_N i := by
    change Submodule.span ℂ ((modeSet i).image (V_n_m i) : Set (H_m i)) =
      Submodule.span ℂ (V_n_m i '' (modeSet i : Set ℤ))
    rw [Finset.coe_image]
  let carrierEquiv : sourceCarrier ≃ₗᵢ[ℂ] E_m_N i :=
    LinearIsometryEquiv.ofEq sourceCarrier (E_m_N i) hcarrier
  let b : OrthonormalBasis (modeSet i) ℂ (E_m_N i) :=
    (OrthonormalBasis.span (V_n_m_orthonormal i) (modeSet i)).map carrierEquiv
  have hb (n : modeSet i) : (b n : H_m i) = V_n_m i n := by
    simp only [b, OrthonormalBasis.map_apply, carrierEquiv]
    exact OrthonormalBasis.span_apply (V_n_m_orthonormal i) (modeSet i) n
  have hprojection := b.orthogonalProjection_eq_sum f
  have hambient :=
    congrArg (fun x : E_m_N i => (x : H_m i)) hprojection
  rw [P_m_N]
  calc
    ((E_m_N i).orthogonalProjection f : H_m i) =
        (∑ n : modeSet i,
          inner ℂ (b n : H_m i) f • (b n : E_m_N i) : E_m_N i) := hambient
    _ = ∑ n : modeSet i,
          inner ℂ (b n : H_m i) f • (b n : H_m i) := by simp
    _ = ∑ n : modeSet i,
          inner ℂ (V_n_m i n) f • V_n_m i n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hb]
    _ = ∑ n ∈ modeSet i,
          inner ℂ (V_n_m i n) f • V_n_m i n :=
      by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach (modeSet i)
            (fun n => inner ℂ (V_n_m i n) f • V_n_m i n))

#print axioms coe_P_m_N_apply_eq_sum_inner_V_n_m_smul

end Q3.RouteB.D0Pstar
