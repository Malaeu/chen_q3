import Q3.Proofs.RouteB.CCMFiniteWeilBottomSpectral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.mathlibStandardSet false

/-
Source boundary:
- exact reflection action on the finite CCM source modes
- exact centrosymmetry plus a simple eigenspace and nonzero eta-normalization
  force the selected eigenvector to be even
- bottomness, simplicity, eigenvector selection, and normalization remain
  explicit conditional inputs
- no H2a, H2b, route-promotion, or RH claim is made here
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Reflection of source vectors across the central CCM mode. -/
def ccmReflectionEndFinite
    (N : ℕ) : Module.End ℝ (CCMModeFinite N → ℝ) where
  toFun := fun x i => x (ccmNegFinite N i)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

@[simp] theorem ccmReflectionEndFinite_apply
    (N : ℕ) (x : CCMModeFinite N → ℝ) (i : CCMModeFinite N) :
    ccmReflectionEndFinite N x i = x (ccmNegFinite N i) :=
  rfl

theorem ccmReflectionEndFinite_involutive
    (N : ℕ) :
    (ccmReflectionEndFinite N).comp (ccmReflectionEndFinite N) = 1 := by
  apply LinearMap.ext
  intro x
  funext i
  simp [LinearMap.comp_apply]

theorem ccmEtaFinite_reflection_invariant
    (N : ℕ) :
    ccmReflectionEndFinite N (ccmEtaFinite N) = ccmEtaFinite N := by
  ext i
  rfl

theorem ccmEtaFinite_dot_reflection
    (N : ℕ) (x : CCMModeFinite N → ℝ) :
    ccmEtaFinite N ⬝ᵥ ccmReflectionEndFinite N x =
      ccmEtaFinite N ⬝ᵥ x := by
  classical
  let negEquiv : CCMModeFinite N ≃ CCMModeFinite N :=
    { toFun := ccmNegFinite N
      invFun := ccmNegFinite N
      left_inv := ccmNegFinite_involutive N
      right_inv := ccmNegFinite_involutive N }
  have hsum := negEquiv.sum_comp
    (fun i => ccmEtaFinite N i * x i)
  simpa [negEquiv, ccmEtaFinite, dotProduct] using hsum

theorem ccmWeilOpFinite_commutes_reflection
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    (ccmReflectionEndFinite N).comp (ccmWeilOpFinite mProject N) =
      (ccmWeilOpFinite mProject N).comp (ccmReflectionEndFinite N) := by
  classical
  apply LinearMap.ext
  intro x
  funext i
  let negEquiv : CCMModeFinite N ≃ CCMModeFinite N :=
    { toFun := ccmNegFinite N
      invFun := ccmNegFinite N
      left_inv := ccmNegFinite_involutive N
      right_inv := ccmNegFinite_involutive N }
  have hsum := negEquiv.sum_comp
    (fun j => ccmWeilMatFinite mProject N i j *
      (ccmReflectionEndFinite N x) j)
  have hentry : ∀ j,
      ccmWeilMatFinite mProject N i (ccmNegFinite N j) =
        ccmWeilMatFinite mProject N (ccmNegFinite N i) j := by
    intro j
    have hcentro :=
      ccmWeilMatFinite_centrosymmetric mProject N hm hN
        i (ccmNegFinite N j)
    simpa using hcentro.symm
  have hsum' :
      (∑ j, ccmWeilMatFinite mProject N i (ccmNegFinite N j) * x j) =
        ∑ j, ccmWeilMatFinite mProject N i j *
          x (ccmNegFinite N j) := by
    change
      (∑ j, ccmWeilMatFinite mProject N i (ccmNegFinite N j) *
        x (ccmNegFinite N (ccmNegFinite N j))) =
          ∑ j, ccmWeilMatFinite mProject N i j *
            x (ccmNegFinite N j) at hsum
    simpa only [ccmNegFinite_involutive] using hsum
  simp_rw [hentry] at hsum'
  simpa [negEquiv, ccmWeilOpFinite, LinearMap.comp_apply,
    Matrix.mulVec, dotProduct] using hsum'

theorem ccmReflectionEndFinite_mem_eigenspace
    (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    {x : CCMModeFinite N → ℝ}
    (hx : x ∈ (ccmWeilOpFinite mProject N).eigenspace epsilon) :
    ccmReflectionEndFinite N x ∈
      (ccmWeilOpFinite mProject N).eigenspace epsilon := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hcomm :=
    LinearMap.congr_fun
      (ccmWeilOpFinite_commutes_reflection mProject N hm hN) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
  rw [← hcomm, hx, map_smul]

theorem ccmEigenvector_even_of_simple_eigenspace_and_normalized
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi =
      epsilon • xi)
    (hnormalized : ccmEtaFinite N ⬝ᵥ xi = 1)
    (hsimple : Module.finrank ℝ
      ((ccmWeilOpFinite mProject N).eigenspace epsilon) = 1) :
    ∀ i, xi (ccmNegFinite N i) = xi i := by
  have hxi0 : xi ≠ 0 := by
    intro hzero
    subst xi
    simp at hnormalized
  have hximem :
      xi ∈ (ccmWeilOpFinite mProject N).eigenspace epsilon := by
    rw [Module.End.mem_eigenspace_iff]
    simpa [ccmWeilOpFinite] using heig
  have hspanLe :
      ℝ ∙ xi ≤ (ccmWeilOpFinite mProject N).eigenspace epsilon :=
    (Submodule.span_singleton_le_iff_mem xi
      ((ccmWeilOpFinite mProject N).eigenspace epsilon)).mpr hximem
  have hspan :
      ℝ ∙ xi = (ccmWeilOpFinite mProject N).eigenspace epsilon := by
    apply Submodule.eq_of_le_of_finrank_eq hspanLe
    rw [finrank_span_singleton hxi0, hsimple]
  have hreflectMem :
      ccmReflectionEndFinite N xi ∈
        (ccmWeilOpFinite mProject N).eigenspace epsilon :=
    ccmReflectionEndFinite_mem_eigenspace
      mProject N epsilon hm hN hximem
  have hreflectSpan : ccmReflectionEndFinite N xi ∈ ℝ ∙ xi := by
    rw [hspan]
    exact hreflectMem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hreflectSpan
  have hcOne : c = 1 := by
    have hpair := ccmEtaFinite_dot_reflection N xi
    rw [← hc] at hpair
    simpa [hnormalized] using hpair
  intro i
  simpa [hcOne] using (congrFun hc i).symm

theorem ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
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
      (fun z =>
        ((sourceLagrangePolynomial
          (fun i => (ccmModeFinite N i : ℝ)) xi).map
            (algebraMap ℝ ℂ)).eval z) := by
  have hxiEven :=
    ccmEigenvector_even_of_simple_eigenspace_and_normalized
      mProject N epsilon xi hm hN heig hnormalized hsimple
  exact
    ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple
      mProject N epsilon xi hm hN heig hxiEven hnormalized hbottom hsimple b

#print axioms ccmWeilOpFinite_commutes_reflection
#print axioms ccmReflectionEndFinite_mem_eigenspace
#print axioms ccmEigenvector_even_of_simple_eigenspace_and_normalized
#print axioms ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized

end Q3.RouteB
