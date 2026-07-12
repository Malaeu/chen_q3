import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- Residual in the ambient carrier. -/
def ambientResidual
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (v : E) (mu : 𝕜) : E :=
  A v - mu • v

/-- Residual visible after applying a projection/compression map. -/
def compressedResidual
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) (mu : 𝕜) : E :=
  P (A v) - mu • v

/-- Component of `A v` lost by the compression. -/
def projectionLeakage
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) : E :=
  A v - P (A v)

/-- The ambient residual is exactly the compressed residual plus the part of
`A v` lost by compression.  This is algebraic and does not identify any exact
Route B carrier. -/
theorem ambient_residual_eq_compressed_residual_add_leakage
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) (mu : 𝕜) :
    ambientResidual A v mu =
      compressedResidual A P v mu + projectionLeakage A P v := by
  simp only [ambientResidual, compressedResidual, projectionLeakage]
  abel

/-- A Ritz equation in the compressed carrier kills only the compressed
residual.  The true ambient residual is the leakage term. -/
theorem ambient_residual_eq_leakage_of_compressed_eigen
    {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {A P : E →ₗ[𝕜] E} {v : E} {mu : 𝕜}
    (hritz : P (A v) = mu • v) :
    ambientResidual A v mu = projectionLeakage A P v := by
  rw [ambient_residual_eq_compressed_residual_add_leakage A P v mu]
  simp [compressedResidual, hritz]

theorem ambient_residual_norm_eq_leakage_norm_of_compressed_eigen
    {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A P : E →ₗ[𝕜] E} {v : E} {mu : 𝕜}
    (hritz : P (A v) = mu • v) :
    ‖ambientResidual A v mu‖ = ‖projectionLeakage A P v‖ := by
  rw [ambient_residual_eq_leakage_of_compressed_eigen hritz]

/-- Coordinate projection `P(x,y)=(x,0)`. -/
def coordinateProjection2 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap 0

/-- Symmetric-coordinate swap model `A(x,y)=(y,x)`. -/
def swapOperator2 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateProjection2_apply (x : ℝ × ℝ) :
    coordinateProjection2 x = (x.1, 0) := by
  rfl

@[simp] theorem swapOperator2_apply (x : ℝ × ℝ) :
    swapOperator2 x = (x.2, x.1) := by
  rfl

theorem coordinateProjection2_idempotent (x : ℝ × ℝ) :
    coordinateProjection2 (coordinateProjection2 x) = coordinateProjection2 x := by
  ext <;> simp

/-- Executable anti-tautology guard: `v=(1,0)` lies in the projected carrier
and solves the compressed eigen-equation at zero, but its ambient residual is
the nonzero vector `(0,1)`. -/
theorem compressed_residual_zero_ambient_residual_nonzero :
    coordinateProjection2 (1, 0) = (1, 0) ∧
      compressedResidual swapOperator2 coordinateProjection2 (1, 0) 0 = 0 ∧
      ambientResidual swapOperator2 (1, 0) 0 = (0, 1) ∧
      projectionLeakage swapOperator2 coordinateProjection2 (1, 0) = (0, 1) ∧
      ambientResidual swapOperator2 (1, 0) 0 ≠ 0 := by
  norm_num [compressedResidual, ambientResidual, projectionLeakage]

#print axioms ambient_residual_eq_compressed_residual_add_leakage
#print axioms ambient_residual_eq_leakage_of_compressed_eigen
#print axioms ambient_residual_norm_eq_leakage_norm_of_compressed_eigen
#print axioms compressed_residual_zero_ambient_residual_nonzero

end Q3.RouteB
