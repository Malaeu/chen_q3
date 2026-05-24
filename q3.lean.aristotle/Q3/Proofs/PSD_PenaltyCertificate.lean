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

/-- Squared Euclidean norm on a finite real coefficient space. -/
def euclideanEnergy {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- A nonzero finite real vector has positive squared Euclidean energy. -/
lemma euclideanEnergy_pos_of_ne_zero {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : v ≠ 0) :
    0 < euclideanEnergy v := by
  classical
  unfold euclideanEnergy
  have h_exists : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_not.mp (not_exists.mp h i)
  rcases h_exists with ⟨i, hi⟩
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (v j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

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

/-- A finite penalty certificate for the pair `(D, R)` relative to boundary
constraints `Q`.  In the PSD-pd kappa split, `D` is `Dtheta` and `R` is
`Rkappa`. -/
structure FinitePenaltyCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) where
  tauD : ℝ
  tauR : ℝ
  D_penalty_pos : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm D Q tauD v
  R_penalty_pos : ∀ v : ι → ℝ, v ≠ 0 → 0 < penaltyForm R Q tauR v

/-- Lower-bound landing surface for proof-generating interval/SPD checkers.

This is the certificate shape a future checked interval layer should produce:
the penalized forms dominate a positive multiple of the squared Euclidean
energy on the full finite coefficient space.  Such a lower bound immediately
implies the strict positivity fields required by `FinitePenaltyCert`. -/
structure FinitePenaltyLowerBoundCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (D R : Matrix ι ι ℝ) (Q : Matrix ρ ι ℝ) where
  tauD : ℝ
  tauR : ℝ
  dFloor : ℝ
  rFloor : ℝ
  dFloor_pos : 0 < dFloor
  rFloor_pos : 0 < rFloor
  D_penalty_lower : ∀ v : ι → ℝ,
    dFloor * euclideanEnergy v ≤ penaltyForm D Q tauD v
  R_penalty_lower : ∀ v : ι → ℝ,
    rFloor * euclideanEnergy v ≤ penaltyForm R Q tauR v

namespace FinitePenaltyLowerBoundCert

/-- A full-space positive Euclidean lower bound yields the standard finite
penalty certificate consumed by the matrix-identification layer. -/
def toFinitePenaltyCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ}
    (cert : FinitePenaltyLowerBoundCert D R Q) :
    FinitePenaltyCert D R Q where
  tauD := cert.tauD
  tauR := cert.tauR
  D_penalty_pos := by
    intro v hv
    exact lt_of_lt_of_le
      (mul_pos cert.dFloor_pos (euclideanEnergy_pos_of_ne_zero v hv))
      (cert.D_penalty_lower v)
  R_penalty_pos := by
    intro v hv
    exact lt_of_lt_of_le
      (mul_pos cert.rFloor_pos (euclideanEnergy_pos_of_ne_zero v hv))
      (cert.R_penalty_lower v)

end FinitePenaltyLowerBoundCert

namespace FinitePenaltyCert

/-- A finite penalty certificate gives `D >= 0` and `R > 0` on the
boundary-null subspace. -/
theorem boundaryNull_guards {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ}
    (cert : FinitePenaltyCert D R Q) :
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm D v) ∧
    (∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 < quadForm R v) := by
  exact two_penalty_guards_on_boundaryNull
    (D := D) (R := R) (Q := Q)
    (tauD := cert.tauD) (tauR := cert.tauR)
    cert.D_penalty_pos cert.R_penalty_pos

/-- If `C = D + theta R` as quadratic forms and `theta >= 0`, then the
certificate proves `C >= 0` on `ker Q`. -/
theorem C_nonneg_on_boundaryNull {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (cert : FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      quadForm C v = quadForm D v + theta * quadForm R v)
    (htheta : 0 ≤ theta) :
    ∀ v : ι → ℝ, BoundaryNull Q v → v ≠ 0 → 0 ≤ quadForm C v := by
  intro v hv hne
  have hD : 0 ≤ quadForm D v := (boundaryNull_guards cert).1 v hv hne
  have hR : 0 ≤ quadForm R v := le_of_lt <| (boundaryNull_guards cert).2 v hv hne
  rw [hC v]
  exact add_nonneg hD (mul_nonneg htheta hR)

/-- Strengthened form of the finite certificate:
`C >= theta R` on the boundary-null subspace. -/
theorem C_ge_theta_R_on_boundaryNull {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C D R : Matrix ι ι ℝ} {Q : Matrix ρ ι ℝ} {theta : ℝ}
    (cert : FinitePenaltyCert D R Q)
    (hC : ∀ v : ι → ℝ,
      quadForm C v = quadForm D v + theta * quadForm R v) :
    ∀ v : ι → ℝ,
      BoundaryNull Q v → v ≠ 0 →
        theta * quadForm R v ≤ quadForm C v := by
  intro v hv hne
  have hD : 0 ≤ quadForm D v := (boundaryNull_guards cert).1 v hv hne
  rw [hC v]
  simpa [zero_add] using add_le_add_right hD (theta * quadForm R v)

end FinitePenaltyCert

end Q3.Proofs
