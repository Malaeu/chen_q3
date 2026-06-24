import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Low-degree adapter for active-actual order-16 Horner rows.

The existing active-actual Horner segment container is fixed to degree `29`
with coefficients `Fin 30 -> Rat`.  This file proves that a proof-grade
low-degree active-actual segment row can be embedded into that container by
zero-extending its coefficient vector.  It does not produce any analytic row
source, interval certificate, or Step33A.1-A closure claim.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Zero-extend a low-degree active-actual coefficient row into the fixed
degree-29/`Fin 30` container used by the current Horner segment receiver. -/
def primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
    {d : Nat} (_hd : d <= 29) (coeff : Fin (d + 1) -> Rat) :
    Fin 30 -> Rat :=
  fun j =>
    if h : j.1 <= d then
      coeff ⟨j.1, Nat.lt_succ_iff.mpr h⟩
    else
      0

/-- The degree-29 polynomial of the zero-extended row is exactly the original
low-degree polynomial. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActualPoly_zeroExtend29_eq
    {d : Nat} (hd : d <= 29) (coeff : Fin (d + 1) -> Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
          hd coeff) eta =
      rawOmegaATaylorPolynomial d ((1 : Rat) / 20) coeff eta := by
  let term : Nat -> Real := fun k =>
    ((if h : k < d + 1 then coeff ⟨k, h⟩ else 0 : Rat) : Real) *
      (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ k
  have h29 :
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
          (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
            hd coeff) eta =
        ∑ k ∈ Finset.range 30, term k := by
    unfold rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
    change
      (∑ i : Fin 30,
        (((if h : i.1 <= d then
              coeff ⟨i.1, Nat.lt_succ_iff.mpr h⟩
            else
              0 : Rat) : Real) *
          (eta - ((((1 : Rat) / 20 : Rat) : Real))) ^ i.1)) =
        ∑ k ∈ Finset.range 30, term k
    rw [← Fin.sum_univ_eq_sum_range term 30]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    unfold term
    by_cases hle : i.1 <= d
    · have hlt : i.1 < d + 1 := Nat.lt_succ_iff.mpr hle
      simp [hle, hlt]
    · have hnotlt : ¬ i.1 < d + 1 := by
        simpa [Nat.lt_succ_iff] using hle
      simp [hle, hnotlt]
  have hdPoly :
      rawOmegaATaylorPolynomial d ((1 : Rat) / 20) coeff eta =
        ∑ k ∈ Finset.range (d + 1), term k := by
    unfold rawOmegaATaylorPolynomial
    rw [← Fin.sum_univ_eq_sum_range term (d + 1)]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    unfold term
    simp [i.2]
  have hsubset : Finset.range (d + 1) ⊆ Finset.range 30 := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have htail :
      ∀ k ∈ Finset.range 30, k ∉ Finset.range (d + 1) -> term k = 0 := by
    intro k _hk30 hknot
    have hkge : ¬ k < d + 1 := by
      simpa only [Finset.mem_range] using hknot
    unfold term
    simp [hkge]
  calc
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
          hd coeff) eta
        = ∑ k ∈ Finset.range 30, term k := h29
    _ = ∑ k ∈ Finset.range (d + 1), term k :=
        (Finset.sum_subset hsubset htail).symm
    _ = rawOmegaATaylorPolynomial d ((1 : Rat) / 20) coeff eta :=
        hdPoly.symm

/-- Transport a low-degree active-actual segment remainder row into the fixed
degree-29 Horner normalization consumed by the existing active-actual segment
receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree
    {d : Nat} (hd : d <= 29)
    {cellL cellU polyErrorAbs : Rat}
    (coeff : Fin (d + 1) -> Rat)
    (hLow :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            rawOmegaATaylorPolynomial d ((1 : Rat) / 20) coeff eta‖ <=
          (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29
              hd coeff) eta‖ <=
        (polyErrorAbs : Real) := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_activeActualPoly_zeroExtend29_eq
      hd coeff eta]
  exact hLow eta hEta

end Step33
end PSDpd
end Q3
