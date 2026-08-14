import Q3.Proofs.RouteB.D0Mode4FiniteBlockInertiaAdditivity

/-!
# Eventual finite-to-literal mode-four negative-count transport

This bounded leaf composes the exact finite block-inertia identity with the
fixed-carrier Schur convergence and nonsingular-limit stability theorem.  It
transports the negative count at one fixed nonsingular endpoint; it supplies
no numerical count or source-spectrum identification.

Knowledge preflight receipt: `./ask.sh "mode4 actual finite Jacobi truncation
negative count eventually hermitian Schur matrix"` exited `0` and returned only
broad Ferrers/Schur metadata; the exact `kb.py ask` query exited `1` with no
hits; `kb.py flags D0_MODE4_FINITE_TO_LITERAL_NEGATIVE_COUNT` exited `1`
because this territory had not previously been searched.  The initial
preflight, before this file was written, stopped at
`SEMANTIC_INDEX_CORPUS_STALE` and also reported the Route B cartographer
inventory stale.  The root executor then temporarily removed this owned file,
refreshed the semantic receipt and inventory, committed the authorized refresh,
and obtained clean-tree startup exit `0` with `P9_STRICT_PASS` at
`7e8848e7`; only then were these identical owned bytes restored.  This bounded
lane itself performed no index, inventory, or documentation refresh.
-/

open Filter Topology

noncomputable section

/-- At a fixed nonsingular literal Schur endpoint, the negative count of the
actual finite Jacobi truncations eventually equals the literal fixed-carrier
count. -/
theorem
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hdet :
      (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0) :
    ∀ᶠ d in Filter.atTop,
      mode4HermitianNegativeEigenvalueCount
          (mode4ActualFiniteJacobiTruncation
            mProject Λ K d)
          (mode4ActualFiniteJacobiTruncation_isHermitian
            mProject Λ K d)
        =
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian
            mProject K Λ) := by
  have hstable :=
    mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
      (fun d => mode4BackwardTailSchurApprox mProject Λ K d)
      (fun d => mode4BackwardTailSchurApprox_isHermitian mProject K d Λ)
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
      (mode4BackwardTailSchurApprox_tendsto_literal
        mProject K Λ hm hK hsep hΛ)
      hdet
  filter_upwards [hstable] with d hd
  exact
    (mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox
      mProject K d Λ hm hK hsep hΛ).trans hd

#print axioms
  mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix

end
