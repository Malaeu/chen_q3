import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

set_option linter.mathlibStandardSet false

namespace Q3.Proofs

/-!
Finite penalty certificates for boundary-null PSD checks.

This is the Lean landing surface for Step 24 of the PSD-pd finite-certificate
route.  It deliberately avoids zeta, primes, Archimedean kernels, eigenvalues,
and interval arithmetic.  The only statement is the finite-dimensional algebra
used by the Step 18/22 penalty guard:

if `M + tau Q^T Q` is positive on the full coefficient space, then `M` is positive
on the boundary-null subspace `Qv = 0`.
-/

/-- Real quadratic form associated to a finite matrix.  We keep the explicit
double sum instead of depending on a heavier matrix quadratic-form API. -/
def quadForm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- Boundary-null predicate for a constraint matrix `Q`. -/
def BoundaryNull {ρ ι : Type*} [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ r, ∑ i, Q r i * v i = 0

/-- Squared boundary residual `||Qv||_2^2`, written as an explicit finite sum. -/
def boundaryEnergy {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ r, (∑ i, Q r i * v i) ^ 2

/-- Penalty form `v^T M v + tau ||Qv||^2`. -/
def penaltyForm {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (v : ι → ℝ) : ℝ :=
  quadForm M v + tau * boundaryEnergy Q v

/-- The boundary residual energy vanishes on the boundary-null subspace. -/
lemma boundaryEnergy_eq_zero_of_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (Q : Matrix ρ ι ℝ) (v : ι → ℝ)
    (hv : BoundaryNull Q v) :
    boundaryEnergy Q v = 0 := by
  unfold boundaryEnergy BoundaryNull at *
  simp [hv]

/-- On the boundary-null subspace, the penalty form equals the original
quadratic form. -/
lemma penaltyForm_eq_quadForm_of_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (v : ι → ℝ)
    (hv : BoundaryNull Q v) :
    penaltyForm M Q tau v = quadForm M v := by
  unfold penaltyForm
  rw [boundaryEnergy_eq_zero_of_boundaryNull Q v hv]
  simp

/-- Semidefinite penalty certificate.

If the penalized form is nonnegative on the full coefficient space, then the
unpenalized form is nonnegative on `ker Q`. -/
theorem quadForm_nonneg_on_boundaryNull_of_penalty_nonneg {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, 0 ≤ penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → 0 ≤ quadForm M v := by
  intro v hv
  simpa [penaltyForm_eq_quadForm_of_boundaryNull M Q tau v hv] using hpen v

/-- Strict positive penalty certificate.

If the penalized form is positive on every nonzero full-space vector, then the
unpenalized form is positive on every nonzero boundary-null vector. -/
theorem quadForm_pos_on_boundaryNull_of_penalty_pos {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm M v := by
  intro v hv hne
  simpa [penaltyForm_eq_quadForm_of_boundaryNull M Q tau v hv] using hpen v hne

/-- Strict full-space penalty positivity implies semidefinite positivity on
the boundary-null subspace.  This is the exact shape needed when a numerical
guard proves SPD for `M + tau Q^T Q`, but the downstream certificate only needs
PSD on `ker Q`. -/
theorem quadForm_nonneg_on_boundaryNull_of_penalty_pos {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (M : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) (tau : ℝ)
    (hpen : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm M Q tau v) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm M v := by
  intro v hv hne
  exact le_of_lt <| quadForm_pos_on_boundaryNull_of_penalty_pos
    (M := M) (Q := Q) (tau := tau) hpen v hv hne

/-- Two-form version matching Step 23: one penalty guard for `Dtheta`, one for
`Rkappa`, both restricted to the same boundary-null subspace. -/
theorem two_penalty_guards_on_boundaryNull {ρ ι : Type*}
    [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ)
    (tauD tauR : ℝ)
    (hD : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm D Q tauD v)
    (hR : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm R Q tauR v) :
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm D v) ∧
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm R v) := by
  constructor
  · exact quadForm_nonneg_on_boundaryNull_of_penalty_pos
      (M := D) (Q := Q) (tau := tauD) hD
  · exact quadForm_pos_on_boundaryNull_of_penalty_pos
      (M := R) (Q := Q) (tau := tauR) hR

end Q3.Proofs
