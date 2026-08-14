import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization

/-!
# Fixed-carrier convergence of the mode-four backward-tail Schur approximation

The matrix below is deliberately named `Approx`.  It is the literal fixed-size
Hermitian Schur matrix formula with the finite backward-tail approximant in the
single tail-dependent diagonal entry.  It is not identified here with the
Schur complement of a finite DLMF Jacobi matrix; that later finite-block
identity remains a separate Goal 058 G3 leaf.

Knowledge preflight on 2026-08-14 returned no hits for the exact target
`Mode4BackwardTailSchurApproxTendstoLiteral` or for the combined existing-object
query.  The proof therefore lifts the already kernel-checked scalar theorem
`mode4BackwardTail_tendsto_rightTailLimit` entrywise.
-/

open Filter Set Topology

noncomputable section

/-- The fixed-carrier exact-tail approximation obtained by replacing only the
right-tail limit in the newest diagonal entry by a finite backward tail with
terminal value zero.  This is not yet an actual finite Jacobi Schur complement. -/
noncomputable def mode4BackwardTailSchurApprox
    (mProject : ℕ) (Λ : ℝ) :
    (K d : ℕ) → Matrix (Fin K) (Fin K) ℝ
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, d => fun i j =>
      let G := mode4JacobiG mProject
      Fin.cases
        (Fin.cases
          (mode4JacobiCenter G Λ n -
            mode4JacobiUpper G n *
              mode4BackwardTail mProject Λ (n + 1) d 0)
          (fun j' =>
            if j'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
          j)
        (fun i' =>
          Fin.cases
            (if i'.val = 0 then -mode4JacobiSymmetricOff G (n - 1) else 0)
            (fun j' => mode4HermitianLeftContinuantMatrix G Λ n i' j')
            j)
        i

/-- Every finite backward-tail approximation is Hermitian on the same fixed
carrier as the literal exact-tail Schur matrix. -/
theorem mode4BackwardTailSchurApprox_isHermitian
    (mProject K d : ℕ) (Λ : ℝ) :
    (mode4BackwardTailSchurApprox mProject Λ K d).IsHermitian := by
  cases K with
  | zero =>
      apply Matrix.IsHermitian.ext
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply Matrix.IsHermitian.ext
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simp [mode4BackwardTailSchurApprox]
      · simp [mode4BackwardTailSchurApprox]
      · simp [mode4BackwardTailSchurApprox]
      · simpa [mode4BackwardTailSchurApprox] using
          (mode4HermitianLeftContinuantMatrix_isHermitian
            (mode4JacobiG mProject) Λ n).apply i' j'

/-- Under the existing production tail-separation hypotheses, the fixed-size
backward-tail approximation converges entrywise to the literal infinite-tail
Hermitian Schur matrix. -/
theorem mode4BackwardTailSchurApprox_tendsto_literal
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Tendsto
      (fun d => mode4BackwardTailSchurApprox mProject Λ K d)
      atTop
      (𝓝 (mode4HermitianSchurMatrix mProject Λ K)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  cases K with
  | zero => exact Fin.elim0 i
  | succ n =>
      have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
      have htail := mode4BackwardTail_tendsto_rightTailLimit
        mProject (n + 1) Λ 0 hm hK hsep hΛ hzero
      refine Fin.cases ?_ (fun i' => ?_) i <;>
        refine Fin.cases ?_ (fun j' => ?_) j
      · simpa [mode4BackwardTailSchurApprox, mode4HermitianSchurMatrix] using
          (tendsto_const_nhds.sub (tendsto_const_nhds.mul htail))
      · simp [mode4BackwardTailSchurApprox, mode4HermitianSchurMatrix]
      · simp [mode4BackwardTailSchurApprox, mode4HermitianSchurMatrix]
      · simp [mode4BackwardTailSchurApprox, mode4HermitianSchurMatrix]

#print axioms mode4BackwardTailSchurApprox_isHermitian
#print axioms mode4BackwardTailSchurApprox_tendsto_literal
