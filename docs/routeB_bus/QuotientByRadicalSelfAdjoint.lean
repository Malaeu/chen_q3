import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Real.Basic

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First descend the second argument of a symmetric bilinear form through its
left radical. -/
def quotientRadicalRight
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    V →ₗ[ℝ] ((V ⧸ LinearMap.ker B) →ₗ[ℝ] ℝ) where
  toFun x :=
    (LinearMap.ker B).liftQ (B x) (by
      intro k hk
      rw [LinearMap.mem_ker]
      rw [hB.eq x k]
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hk) x)
  map_add' := by
    intro x y
    ext z
    simp
  map_smul' := by
    intro c x
    ext z
    simp

/-- A symmetric bilinear form descends canonically to the quotient by its
radical. -/
def quotientByRadicalForm
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    LinearMap.BilinForm ℝ (V ⧸ LinearMap.ker B) :=
  (LinearMap.ker B).liftQ (quotientRadicalRight B hB) (by
    intro k hk
    rw [LinearMap.mem_ker]
    ext y
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hk) y)

@[simp] theorem quotientByRadicalForm_mk_mk
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (x y : V) :
    quotientByRadicalForm B hB
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := by
  rfl

theorem quotientByRadicalForm_nonneg
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hpos : ∀ x, 0 ≤ B x x) :
    ∀ q, 0 ≤ quotientByRadicalForm B hB q q := by
  intro q
  refine Submodule.Quotient.induction_on (LinearMap.ker B) q ?_
  intro x
  simpa using hpos x

theorem quotientByRadicalForm_definite
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hpos : ∀ x, 0 ≤ B x x) :
    ∀ q, quotientByRadicalForm B hB q q = 0 ↔ q = 0 := by
  intro q
  refine Submodule.Quotient.induction_on (LinearMap.ker B) q ?_
  intro x
  rw [quotientByRadicalForm_mk_mk, Submodule.Quotient.mk_eq_zero]
  exact B.apply_apply_same_eq_zero_iff hpos
    (LinearMap.BilinForm.isSymm_iff.mp hB)

/-- A map symmetric for `B` preserves the radical of `B`. -/
theorem maps_ker_of_bilinForm_selfAdjoint
    (B : LinearMap.BilinForm ℝ V) (A : Module.End ℝ V)
    (hself : LinearMap.IsSelfAdjoint B A) :
    LinearMap.ker B ≤ (LinearMap.ker B).comap A := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  change A x ∈ LinearMap.ker B
  rw [LinearMap.mem_ker]
  ext y
  rw [hself x y]
  exact LinearMap.congr_fun hx (A y)

/-- The induced endomorphism on the quotient by the radical. -/
def quotientByRadicalEnd
    (B : LinearMap.BilinForm ℝ V) (A : Module.End ℝ V)
    (hself : LinearMap.IsSelfAdjoint B A) :
    Module.End ℝ (V ⧸ LinearMap.ker B) :=
  (LinearMap.ker B).mapQ (LinearMap.ker B) A
    (maps_ker_of_bilinForm_selfAdjoint B A hself)

@[simp] theorem quotientByRadicalEnd_mk
    (B : LinearMap.BilinForm ℝ V) (A : Module.End ℝ V)
    (hself : LinearMap.IsSelfAdjoint B A) (x : V) :
    quotientByRadicalEnd B A hself (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A x) := by
  rfl

theorem quotientByRadicalEnd_isSelfAdjoint
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (A : Module.End ℝ V) (hself : LinearMap.IsSelfAdjoint B A) :
    LinearMap.IsSelfAdjoint (quotientByRadicalForm B hB)
      (quotientByRadicalEnd B A hself) := by
  intro q r
  refine Submodule.Quotient.induction_on (LinearMap.ker B) q ?_
  intro x
  refine Submodule.Quotient.induction_on (LinearMap.ker B) r ?_
  intro y
  simpa using hself x y

#print axioms quotientByRadicalForm_mk_mk
#print axioms quotientByRadicalForm_nonneg
#print axioms quotientByRadicalForm_definite
#print axioms maps_ker_of_bilinForm_selfAdjoint
#print axioms quotientByRadicalEnd_mk
#print axioms quotientByRadicalEnd_isSelfAdjoint

end Q3.RouteB
