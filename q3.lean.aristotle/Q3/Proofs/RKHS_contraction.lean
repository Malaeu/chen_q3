import Mathlib

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

/-- Aristotle-side logarithmic coordinate used by the bridge. -/
noncomputable def ξ (n : ℕ) : ℝ := Real.log n

/-- Aristotle-side RKHS weight (matches Q3 definition). -/
noncomputable def w_RKHS (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Arithmetic node set up to `exp K`, filtered by `log n ≤ K` and `n ≥ 1`. -/
def nodes (K : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (Real.exp K) + 1)).filter (fun n => 1 ≤ n ∧ Real.log n ≤ K)

/-- Subtype of active nodes for the Aristotle-side formulation. -/
abbrev Node (K : ℝ) := {x // x ∈ nodes K}

instance (K : ℝ) : Fintype (Node K) := inferInstance

/-- Aristotle-side heat-kernel matrix on `Node K`. -/
noncomputable def T_P_matrix (K : ℝ) (t : ℝ) : Matrix (Node K) (Node K) ℝ :=
  fun i j =>
    Real.sqrt (w_RKHS i.1) * Real.sqrt (w_RKHS j.1) *
      Real.exp (-((ξ i.1 - ξ j.1) ^ 2) / (4 * t))

/-- Operator norm of `T_P_matrix`. -/
noncomputable def T_P_norm (K : ℝ) (t : ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin (T_P_matrix K t)).toContinuousLinearMap‖

/-- Aristotle-side contraction statement consumed by `Q3/Proofs/Bridge.lean`. -/
axiom RKHS_contraction (K : ℝ) (hK : K ≥ 1) :
    ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧ T_P_norm K t ≤ ρ
