import Q3.Proofs.RouteB.D0PstarSourceEvenNonzeroLowBandAssembly
import Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Exact finite reflection-even CCM to source-Weil head crosswalk

This file identifies the reflection-even part of the literal finite CCM
carrier on modes `-N, ..., 0, ..., N` with the already constructed source-Weil
zero-plus-low-even head.  It is a carrier/synthesis bridge only.  It proves no
selected Rayleigh-shift floor, tail coercivity, Schur margin, complement floor,
G1, G3, or RH claim.
-/

/-- The positive CCM index with physical mode `r+1`. -/
def ccmEvenPositiveFinite (N : ℕ) (r : Fin N) : CCMModeFinite N :=
  ⟨N + r.1 + 1, by omega⟩

private theorem ccmEvenPositiveFinite_inj
    (N : ℕ) (r s : Fin N) :
    ccmEvenPositiveFinite N r = ccmEvenPositiveFinite N s ↔ r = s := by
  constructor
  · intro h
    apply Fin.ext
    simpa [ccmEvenPositiveFinite] using congrArg Fin.val h
  · intro h
    subst s
    rfl

private theorem ccmEvenPositiveFinite_ne_center
    (N : ℕ) (r : Fin N) :
    ccmEvenPositiveFinite N r ≠ ccmCenterFinite N := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ccmEvenPositiveFinite, ccmCenterFinite] at hv
  omega

private theorem ccmEvenPositiveFinite_ne_neg
    (N : ℕ) (r s : Fin N) :
    ccmEvenPositiveFinite N r ≠
      ccmNegFinite N (ccmEvenPositiveFinite N s) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ccmEvenPositiveFinite, ccmNegFinite] at hv
  omega

private theorem ccmEvenNegativeFinite_inj
    (N : ℕ) (r s : Fin N) :
    ccmNegFinite N (ccmEvenPositiveFinite N r) =
        ccmNegFinite N (ccmEvenPositiveFinite N s) ↔ r = s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [ccmEvenPositiveFinite, ccmNegFinite] at hv
    apply Fin.ext
    omega
  · intro h
    subst s
    rfl

private theorem ccmEvenNegativeFinite_ne_pos
    (N : ℕ) (r s : Fin N) :
    ccmNegFinite N (ccmEvenPositiveFinite N r) ≠
      ccmEvenPositiveFinite N s := by
  exact fun h => ccmEvenPositiveFinite_ne_neg N s r h.symm

private theorem ccmEvenNegativeFinite_ne_center
    (N : ℕ) (r : Fin N) :
    ccmNegFinite N (ccmEvenPositiveFinite N r) ≠ ccmCenterFinite N := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ccmEvenPositiveFinite, ccmNegFinite, ccmCenterFinite] at hv
  omega

private theorem ccmEvenNegFinite_involutive
    (N : ℕ) (j : CCMModeFinite N) :
    ccmNegFinite N (ccmNegFinite N j) = j := by
  apply Fin.ext
  simp only [ccmNegFinite]
  omega

/-- A normalized symmetric pair in the literal finite CCM carrier. -/
noncomputable def ccmEvenPairVector
    (N : ℕ) (r : Fin N) : CCMModeFinite N → ℂ :=
  fun j =>
    (if j = ccmEvenPositiveFinite N r then
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0) +
      (if j = ccmNegFinite N (ccmEvenPositiveFinite N r) then
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) else 0)

/-- Zero coefficient plus normalized symmetric-pair coefficients, embedded in
the exact finite CCM order. -/
noncomputable def ccmEvenCoefficientEmbedding
    (N : ℕ) (c0 : ℂ) (c : Fin N → ℂ) :
    CCMModeFinite N → ℂ :=
  fun j =>
    (if j = ccmCenterFinite N then c0 else 0) +
      ∑ r, c r * ccmEvenPairVector N r j

/-- The explicit even embedding is fixed by the literal CCM reflection. -/
theorem ccmEvenCoefficientEmbedding_reflection_even
    (N : ℕ) (c0 : ℂ) (c : Fin N → ℂ) :
    ∀ j, ccmEvenCoefficientEmbedding N c0 c (ccmNegFinite N j) =
      ccmEvenCoefficientEmbedding N c0 c j := by
  classical
  have hcenter (j : CCMModeFinite N) :
      (ccmNegFinite N j = ccmCenterFinite N) ↔
        (j = ccmCenterFinite N) := by
    constructor
    · intro h
      have hc :
          ccmNegFinite N (ccmCenterFinite N) = ccmCenterFinite N := by
        apply Fin.ext
        simp only [ccmNegFinite, ccmCenterFinite]
        omega
      exact (ccmEvenNegFinite_involutive N j).symm.trans
        ((congrArg (ccmNegFinite N) h).trans hc)
    · intro h
      subst j
      apply Fin.ext
      simp only [ccmNegFinite, ccmCenterFinite]
      omega
  have hpair (r : Fin N) (j : CCMModeFinite N) :
      ccmEvenPairVector N r (ccmNegFinite N j) =
        ccmEvenPairVector N r j := by
    have hpos :
        ccmNegFinite N j = ccmEvenPositiveFinite N r ↔
          j = ccmNegFinite N (ccmEvenPositiveFinite N r) := by
      constructor
      · intro h
        rw [← ccmEvenNegFinite_involutive N j]
        exact congrArg (ccmNegFinite N) h
      · intro h
        rw [h, ccmEvenNegFinite_involutive]
    have hneg :
        ccmNegFinite N j =
            ccmNegFinite N (ccmEvenPositiveFinite N r) ↔
          j = ccmEvenPositiveFinite N r := by
      constructor
      · intro h
        rw [← ccmEvenNegFinite_involutive N j]
        rw [← ccmEvenNegFinite_involutive N
          (ccmEvenPositiveFinite N r)]
        exact congrArg (ccmNegFinite N) h
      · intro h
        rw [h]
    simp only [ccmEvenPairVector, hpos, hneg]
    ac_rfl
  intro j
  simp only [ccmEvenCoefficientEmbedding, hcenter]
  apply congrArg (fun z : ℂ => (if j = ccmCenterFinite N then c0 else 0) + z)
  apply Finset.sum_congr rfl
  intro r _hr
  rw [hpair]

private theorem ccmEvenCoefficientEmbedding_center
    (N : ℕ) (c0 : ℂ) (c : Fin N → ℂ) :
    ccmEvenCoefficientEmbedding N c0 c (ccmCenterFinite N) = c0 := by
  classical
  unfold ccmEvenCoefficientEmbedding
  rw [if_pos rfl]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro r _hr
  have hp : ccmCenterFinite N ≠ ccmEvenPositiveFinite N r :=
    (ccmEvenPositiveFinite_ne_center N r).symm
  have hn :
      ccmCenterFinite N ≠
        ccmNegFinite N (ccmEvenPositiveFinite N r) :=
    (ccmEvenNegativeFinite_ne_center N r).symm
  simp [ccmEvenPairVector, hp, hn]

private theorem ccmEvenCoefficientEmbedding_positive
    (N : ℕ) (c0 : ℂ) (c : Fin N → ℂ) (r : Fin N) :
    ccmEvenCoefficientEmbedding N c0 c (ccmEvenPositiveFinite N r) =
      c r * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  classical
  simp [ccmEvenCoefficientEmbedding, ccmEvenPairVector,
    ccmEvenPositiveFinite_inj, ccmEvenPositiveFinite_ne_center,
    ccmEvenPositiveFinite_ne_neg]

private theorem ccmEvenCoefficientEmbedding_negative
    (N : ℕ) (c0 : ℂ) (c : Fin N → ℂ) (r : Fin N) :
    ccmEvenCoefficientEmbedding N c0 c
        (ccmNegFinite N (ccmEvenPositiveFinite N r)) =
      c r * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  rw [ccmEvenCoefficientEmbedding_reflection_even N c0 c
    (ccmEvenPositiveFinite N r)]
  exact ccmEvenCoefficientEmbedding_positive N c0 c r

/-- Every reflection-even finite CCM vector is reconstructed by its zero and
positive symmetric-pair coefficients. -/
theorem ccmEvenCoefficientEmbedding_reconstruct
    (N : ℕ) (x : CCMModeFinite N → ℂ)
    (hx : ∀ j, x (ccmNegFinite N j) = x j) :
    ccmEvenCoefficientEmbedding N
        (x (ccmCenterFinite N))
        (fun r => (((Real.sqrt 2 : ℝ) : ℂ)) *
          x (ccmEvenPositiveFinite N r)) = x := by
  funext j
  by_cases hjc : j = ccmCenterFinite N
  · subst j
    exact ccmEvenCoefficientEmbedding_center N _ _
  · by_cases hjpos : N < j.val
    · have hrlt : j.val - N - 1 < N := by omega
      let r : Fin N := ⟨j.val - N - 1, hrlt⟩
      have hj : ccmEvenPositiveFinite N r = j := by
        apply Fin.ext
        simp only [ccmEvenPositiveFinite, r]
        omega
      rw [← hj, ccmEvenCoefficientEmbedding_positive]
      have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2))
      field_simp [hsqrt]
    · have hjlt : j.val < N := by
        have hjle : j.val ≤ N := by omega
        have hjne : j.val ≠ N := by
          intro h
          apply hjc
          apply Fin.ext
          simpa [ccmCenterFinite] using h
        omega
      have hnegpos : N < (ccmNegFinite N j).val := by
        simp only [ccmNegFinite]
        omega
      have hrlt : (ccmNegFinite N j).val - N - 1 < N := by
        simp only [ccmNegFinite]
        omega
      let r : Fin N :=
        ⟨(ccmNegFinite N j).val - N - 1, hrlt⟩
      have hpos : ccmEvenPositiveFinite N r = ccmNegFinite N j := by
        apply Fin.ext
        simp only [ccmEvenPositiveFinite, ccmNegFinite, r]
        omega
      have hj : ccmNegFinite N (ccmEvenPositiveFinite N r) = j := by
        rw [hpos, ccmEvenNegFinite_involutive]
      rw [← hj, ccmEvenCoefficientEmbedding_negative]
      rw [hpos, hx]
      rw [ccmEvenNegFinite_involutive]
      have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2))
      field_simp [hsqrt]

/-- Finite synthesis of the explicit CCM even embedding is literally the
ambient image of the existing source-Weil zero-plus-low-even head. -/
theorem ccmFiniteSynthesis_evenCoefficientEmbedding
    (i : PairIndex) (c0 : ℂ) (c : Fin i.N → ℂ) :
    ccmFiniteSynthesis i (ccmEvenCoefficientEmbedding i.N c0 c) =
      sourceWeilGraphAmbient i
        (sourceWeilGraphEvenHeadSynthesis i c0 c) := by
  classical
  rw [sourceWeilGraphAmbient_evenHeadSynthesis]
  unfold ccmEvenCoefficientEmbedding
  unfold ccmFiniteSynthesis
  change
    (∑ j : CCMModeFinite i.N,
      ((if j = ccmCenterFinite i.N then c0 else 0) +
        ∑ r : Fin i.N, c r * ccmEvenPairVector i.N r j) •
          V_n_m i (ccmModeFinite i.N j)) = _
  simp only [add_smul]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hcenter :
      (∑ j : CCMModeFinite i.N,
        (if j = ccmCenterFinite i.N then c0 else 0) •
          V_n_m i (ccmModeFinite i.N j)) = c0 • V_n_m i 0 := by
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ (ccmCenterFinite i.N)]
    simp [ccmModeFinite, ccmCenterFinite]
  rw [hcenter]
  apply congrArg (fun z : H_m i => c0 • V_n_m i 0 + z)
  apply Finset.sum_congr rfl
  intro r _hr
  unfold ccmEvenPairVector
  simp_rw [mul_add, add_smul]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (ccmEvenPositiveFinite i.N r)]
  rw [Finset.sum_ite_eq' Finset.univ
    (ccmNegFinite i.N (ccmEvenPositiveFinite i.N r))]
  simp [ccmEvenPositiveFinite, ccmNegFinite, ccmModeFinite,
    smul_smul, mul_comm]
  congr 2 <;> congr 1 <;> omega

/-- Exact consumer-facing crosswalk: a reflection-even finite CCM vector is
the ambient synthesis of its source-Weil even head. -/
theorem ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_reflection
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ∀ j, x (ccmNegFinite i.N j) = x j) :
    ccmFiniteSynthesis i x =
      sourceWeilGraphAmbient i
        (sourceWeilGraphEvenHeadSynthesis i
          (x (ccmCenterFinite i.N))
          (fun r => (((Real.sqrt 2 : ℝ) : ℂ)) *
            x (ccmEvenPositiveFinite i.N r))) := by
  rw [← ccmFiniteSynthesis_evenCoefficientEmbedding]
  apply congrArg (ccmFiniteSynthesis i)
  exact (ccmEvenCoefficientEmbedding_reconstruct i.N x hx).symm

/-- Matrix-shaped adapter used by the selected finite CCM consumer. -/
theorem ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_mulVec_eq
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x) :
    ccmFiniteSynthesis i x =
      sourceWeilGraphAmbient i
        (sourceWeilGraphEvenHeadSynthesis i
          (x (ccmCenterFinite i.N))
          (fun r => (((Real.sqrt 2 : ℝ) : ℂ)) *
            x (ccmEvenPositiveFinite i.N r))) := by
  apply ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_reflection
  intro j
  calc
    x (ccmNegFinite i.N j) =
        (ccmComplexReflectionMatrix i.N *ᵥ x) j :=
      (ccmComplexReflectionMatrix_mulVec i.N x j).symm
    _ = x j := congrFun hx j

/-- The literal finite synthesis of every matrix-reflection-even CCM vector
is ambient-orthogonal to the exact closed nonzero-even tail after cutoff `N`.
This closes the finite-carrier/head/tail interface, not a graph coercivity or
selected-shift floor. -/
theorem ccmFiniteSynthesis_reflectionEven_orthogonal_evenNonzeroTail
    (i : PairIndex) (x : CCMModeFinite i.N → ℂ)
    (hx : ccmComplexReflectionMatrix i.N *ᵥ x = x)
    (y : SourceWeilGraphEvenNonzeroTailCarrier i i.N) :
    inner ℂ (ccmFiniteSynthesis i x)
      (sourceWeilGraphAmbient i (y : SourceWeilGraphCarrier i)) = 0 := by
  rw [ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_mulVec_eq
    i x hx]
  exact sourceWeilGraphEvenHeadSynthesis_orthogonal_tail i i.N
    (x (ccmCenterFinite i.N))
    (fun r => (((Real.sqrt 2 : ℝ) : ℂ)) *
      x (ccmEvenPositiveFinite i.N r)) y

#print axioms ccmEvenCoefficientEmbedding_reflection_even
#print axioms ccmEvenCoefficientEmbedding_reconstruct
#print axioms ccmFiniteSynthesis_evenCoefficientEmbedding
#print axioms ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_reflection
#print axioms ccmFiniteSynthesis_eq_sourceWeilGraphAmbient_evenHead_of_mulVec_eq
#print axioms ccmFiniteSynthesis_reflectionEven_orthogonal_evenNonzeroTail

end Q3.RouteB.D0Pstar
