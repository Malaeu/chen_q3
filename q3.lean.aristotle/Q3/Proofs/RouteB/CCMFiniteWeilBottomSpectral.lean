import Q3.Proofs.RouteB.CCMFiniteWeilRealZeros
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.mathlibStandardSet false

/-
Source boundary:
- finite spectral adapter for the exact shifted CCM source matrix
- the bottom Rayleigh bound, simple eigenspace, even eigenvector, and
  normalization remain explicit conditional inputs
- no H2a, H2b, route-promotion, or RH claim is made here
-/

noncomputable section

namespace Q3.RouteB

open Matrix

/-- The shifted CCM matrix operator is the source operator minus the scalar
identity operator. -/
theorem ccmShiftedWeilOpFinite_eq_sub_smul_id
    (mProject N : ℕ) (epsilon : ℝ) :
    ccmShiftedWeilOpFinite mProject N epsilon =
      ccmWeilOpFinite mProject N -
        epsilon • (1 : Module.End ℝ (CCMModeFinite N → ℝ)) := by
  ext x i
  simp [ccmShiftedWeilOpFinite, ccmShiftedWeilMatFinite,
    ccmWeilOpFinite]

/-- The zero kernel of the shifted CCM operator is exactly the epsilon
eigenspace of the unshifted source operator. -/
theorem ccmShiftedWeilOpFinite_ker_eq_eigenspace
    (mProject N : ℕ) (epsilon : ℝ) :
    LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) =
      (ccmWeilOpFinite mProject N).eigenspace epsilon := by
  rw [ccmShiftedWeilOpFinite_eq_sub_smul_id, Module.End.eigenspace_def]

/-- A global Rayleigh lower bound at epsilon makes the exact epsilon-shifted
CCM source matrix positive semidefinite. -/
theorem ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh
    (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (hbottom : ∀ x : CCMModeFinite N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mulVec (ccmWeilMatFinite mProject N) x) :
    (ccmShiftedWeilMatFinite mProject N epsilon).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ccmShiftedWeilMatFinite_transpose_eq mProject N epsilon hm hN
  · intro x
    have hx := hbottom x
    simpa [ccmShiftedWeilMatFinite, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec] using sub_nonneg.mpr hx

/-- Bottom-Rayleigh and simple-eigenspace data supply exactly the shifted
nonnegativity and one-dimensional-kernel inputs consumed by the committed CCM
real-zero weld. -/
theorem ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) xi =
      epsilon • xi)
    (hxiEven : ∀ i, xi (ccmNegFinite N i) = xi i)
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
  have hpsd :=
    ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh
      mProject N epsilon hm hN hbottom
  have hpos : ∀ x,
      0 ≤ Matrix.toBilin'
        (ccmShiftedWeilMatFinite mProject N epsilon) x x := by
    intro x
    simpa [Matrix.toBilin'_apply'] using hpsd.dotProduct_mulVec_nonneg x
  have hker :
      LinearMap.ker
          (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin =
        (ccmWeilOpFinite mProject N).eigenspace epsilon := by
    simpa [ccmShiftedWeilOpFinite] using
      ccmShiftedWeilOpFinite_ker_eq_eigenspace mProject N epsilon
  have hker1 :
      Module.finrank ℝ
          (LinearMap.ker
            (ccmShiftedWeilMatFinite mProject N epsilon).mulVecLin) = 1 := by
    rw [hker]
    exact hsimple
  exact
    ccmSourceLagrangePolynomial_complex_zerosRealOn_of_shifted_nonneg_finrank_one
      mProject N epsilon xi hm hN heig hxiEven hnormalized hpos hker1 b

#print axioms ccmShiftedWeilOpFinite_eq_sub_smul_id
#print axioms ccmShiftedWeilOpFinite_ker_eq_eigenspace
#print axioms ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh
#print axioms ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple

end Q3.RouteB
