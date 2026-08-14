import Q3.Proofs.RouteB.D0Mode4JacobiRightTailLimit

/-!
# DLMF 30.3.5 even right-branch crosswalk

This file materializes only the right continued-fraction branch of DLMF
30.3.5 in the order-zero, even-degree convention.  The literal DLMF 30.3.7
coefficients define an independent right map, finite terminal-zero fractions,
and their `limUnder`.  Algebraic coefficient identities identify every finite
fraction with the existing project backward tail; contraction then identifies
the two limits in the current production domain.

The split convention is locked as `splitDegree = 2 * (K - 1)`, so the first
right coefficient degree is `splitDegree + 2 = 2 * K`.  No characteristic
solution set, endpoint count, mode selection, or route-level conclusion is
proved here.

Source lock: NIST DLMF version 1.2.7, equations
[`30.3.E5`](https://dlmf.nist.gov/30.3.E5.tex) and
[`30.3.E7a--c`](https://dlmf.nist.gov/30.3.E7a.tex).  The audited TeX hashes
are respectively
`f8cb8ef56617c5c4ecfa99749aaf1867b706825ab8162d414eb592b1dcce171a`,
`d9a5681e54bbd001a9a83cea0179fc2e85bf95982a65ebaf69e06441638962e8`,
`676f7b323938c236b4b80c97e9679535f9de6a963a7254ddeda570b1d21987f9`,
and `638b32eef5f601de7e3e694933f27273e39b16152adfa6c816f49c9770b7030c`.
The unit dictionary is `G = gamma^2` and project `Lambda =` DLMF `lambda`;
the shifted differential energy is not used in this right-ratio object.

Knowledge preflight receipt: strict startup at `74f87047` exited `0` with
`P9_STRICT_PASS` and no discrepancies.  The exact deep shelf query
`DLMF 30.3.5 even right ratio mode4RightTailLimit literal coefficients`
exited `0` and returned the source contract plus existing 30.8 and right-tail
candidates, but no declaration at this exact source interface.  Exact
`kb.py ask` and `kb.py flags DLMF3035_RIGHT_BRANCH_CROSSWALK` both exited `1`
with no prior exact hit or recorded search territory.
-/

open Filter Set Topology

noncomputable section

/-- DLMF 30.3.7 `alpha_k` at order zero and parameter square `G`. -/
noncomputable def mode4DLMF3037Alpha (G : ℝ) (k : ℕ) : ℝ :=
  let n := (k : ℝ)
  G * (n + 1) * (n + 2) / ((2 * n + 3) * (2 * n + 5))

/-- DLMF 30.3.7 `beta_k` at order zero and parameter square `G`. -/
noncomputable def mode4DLMF3037Beta (G : ℝ) (k : ℕ) : ℝ :=
  let n := (k : ℝ)
  n * (n + 1) -
    2 * G * (n * (n + 1) - 1) / ((2 * n - 1) * (2 * n + 3))

/-- DLMF 30.3.7 `gamma_k` at order zero and parameter square `G`. -/
noncomputable def mode4DLMF3037Gamma (G : ℝ) (k : ℕ) : ℝ :=
  let n := (k : ℝ)
  G * (n - 1) * n / ((2 * n - 3) * (2 * n - 1))

/-- The DLMF 30.3.5 even split immediately to the left of project ratio
index `K`. -/
def mode4DLMF3035EvenSplitDegree (K : ℕ) : ℕ :=
  2 * (K - 1)

/-- With a nonempty left side, the coefficient immediately right of the
DLMF split has degree `2*K`. -/
theorem mode4DLMF3035EvenSplitDegree_add_two
    (K : ℕ) (hK : 1 ≤ K) :
    mode4DLMF3035EvenSplitDegree K + 2 = 2 * K := by
  unfold mode4DLMF3035EvenSplitDegree
  omega

/-- At even degree `2*q`, DLMF `alpha` is the project upper coefficient. -/
theorem mode4DLMF3037Alpha_even_eq_mode4JacobiUpper
    (G : ℝ) (q : ℕ) :
    mode4DLMF3037Alpha G (2 * q) = mode4JacobiUpper G q := by
  simp [mode4DLMF3037Alpha, mode4JacobiUpper, mode4JacobiIndex]

/-- At even degree `2*q`, DLMF `beta - Lambda` is the project center. -/
theorem mode4DLMF3037Beta_even_sub_eq_mode4JacobiCenter
    (G Λ : ℝ) (q : ℕ) :
    mode4DLMF3037Beta G (2 * q) - Λ = mode4JacobiCenter G Λ q := by
  simp [mode4DLMF3037Beta, mode4JacobiCenter, mode4JacobiIndex]

/-- At even degree `2*q`, DLMF `gamma` is the project lower coefficient. -/
theorem mode4DLMF3037Gamma_even_eq_mode4JacobiLower
    (G : ℝ) (q : ℕ) :
    mode4DLMF3037Gamma G (2 * q) = mode4JacobiLower G q := by
  simp [mode4DLMF3037Gamma, mode4JacobiLower, mode4JacobiIndex]

/-- The literal order-zero even DLMF right-ratio map at coefficient index
`q`: `gamma_(2q) / (beta_(2q) - Lambda - alpha_(2q) * x)`. -/
noncomputable def mode4DLMF3035EvenRightMap
    (G Λ : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4DLMF3037Gamma G (2 * q) /
    (mode4DLMF3037Beta G (2 * q) - Λ -
      mode4DLMF3037Alpha G (2 * q) * x)

/-- The literal DLMF right map is algebraically the project tail map. -/
theorem mode4DLMF3035EvenRightMap_eq_mode4TailMap
    (G Λ : ℝ) (q : ℕ) (x : ℝ) :
    mode4DLMF3035EvenRightMap G Λ q x = mode4TailMap G Λ q x := by
  rw [mode4DLMF3035EvenRightMap, mode4TailMap,
    mode4DLMF3037Gamma_even_eq_mode4JacobiLower,
    mode4DLMF3037Beta_even_sub_eq_mode4JacobiCenter,
    mode4DLMF3037Alpha_even_eq_mode4JacobiUpper]

/-- The terminal-zero finite DLMF right fraction beginning at even degree
`2*K`. -/
def mode4DLMF3035EvenRightFiniteApprox
    (G Λ : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      mode4DLMF3035EvenRightMap G Λ K
        (mode4DLMF3035EvenRightFiniteApprox G Λ (K + 1) n)

/-- Every literal finite DLMF right fraction agrees term by term with the
project terminal-zero backward tail. -/
theorem mode4DLMF3035EvenRightFiniteApprox_eq_mode4BackwardTail
    (mProject K n : ℕ) (Λ : ℝ) :
    mode4DLMF3035EvenRightFiniteApprox
        (mode4JacobiG mProject) Λ K n =
      mode4BackwardTail mProject Λ K n 0 := by
  induction n generalizing K with
  | zero => rfl
  | succ n ih =>
      rw [mode4DLMF3035EvenRightFiniteApprox, mode4BackwardTail,
        mode4DLMF3035EvenRightMap_eq_mode4TailMap, ih]

/-- The independent source-side DLMF right ratio, defined as the limit of its
literal terminal-zero finite fractions. -/
noncomputable def mode4DLMF3035EvenRightRatio
    (G Λ : ℝ) (K : ℕ) : ℝ :=
  limUnder atTop
    (fun n => mode4DLMF3035EvenRightFiniteApprox G Λ K n)

/-- In the certified contraction domain, the literal DLMF 30.3.5 even right
ratio is exactly the existing project right-tail limit. -/
theorem mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenRightRatio
        (mode4JacobiG mProject) Λ K =
      mode4RightTailLimit mProject Λ K := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hprojectCauchy := mode4BackwardTail_cauchy
    mProject K Λ 0 hm hK hsep hΛ hzero
  have hsourceCauchy : CauchySeq
      (fun n => mode4DLMF3035EvenRightFiniteApprox
        (mode4JacobiG mProject) Λ K n) := by
    simpa only [mode4DLMF3035EvenRightFiniteApprox_eq_mode4BackwardTail] using
      hprojectCauchy
  have hsource : Tendsto
      (fun n => mode4DLMF3035EvenRightFiniteApprox
        (mode4JacobiG mProject) Λ K n)
      atTop
      (𝓝 (mode4DLMF3035EvenRightRatio
        (mode4JacobiG mProject) Λ K)) := by
    simpa [mode4DLMF3035EvenRightRatio] using hsourceCauchy.tendsto_limUnder
  have hproject := mode4BackwardTail_tendsto_rightTailLimit
    mProject K Λ 0 hm hK hsep hΛ hzero
  have hproject' : Tendsto
      (fun n => mode4DLMF3035EvenRightFiniteApprox
        (mode4JacobiG mProject) Λ K n)
      atTop
      (𝓝 (mode4RightTailLimit mProject Λ K)) := by
    simpa only [mode4DLMF3035EvenRightFiniteApprox_eq_mode4BackwardTail] using
      hproject
  exact tendsto_nhds_unique hsource hproject'

#print axioms mode4DLMF3035EvenSplitDegree_add_two
#print axioms mode4DLMF3035EvenRightMap_eq_mode4TailMap
#print axioms mode4DLMF3035EvenRightFiniteApprox_eq_mode4BackwardTail
#print axioms mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit

end
