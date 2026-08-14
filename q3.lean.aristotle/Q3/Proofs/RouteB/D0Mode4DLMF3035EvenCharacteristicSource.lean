import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenRightBranchCrosswalk
import Q3.Proofs.RouteB.D0Mode4JacobiRootFunction

/-!
# Pole-safe DLMF 30.3.5 even characteristic source object

This file adds the independent finite-left half of the order-zero even DLMF
30.3.5 equation.  Its recurrence is written only with the literal DLMF 30.3.7
coefficients from the right-branch source module.  The characteristic
predicate carries an explicit even-split guard, converts
`splitDegree` to the first right-ratio index by `splitDegree / 2 + 1`, and
matches the two branches by a division-free equality.

The local adapters prove that the literal finite-left pair is the existing
project left pair and, on the certified production domain with
`splitDegree = 2 * (K - 1)`, that this independent characteristic predicate is
equivalent to the existing division-free project residual vanishing.  No DLMF
solution-set theorem, classical carrier identification, endpoint count, or
mode selection is stated here.

Source lock and units are inherited from the directly imported
`D0Mode4DLMF3035EvenRightBranchCrosswalk`: NIST DLMF 30.3.5 and 30.3.7,
order zero, even degree `k = 2*q`, `G = gamma^2`, and project `Lambda =`
DLMF `lambda`.

Knowledge preflight receipt: the exact deep query `DLMF 30.3.5 even finite
left pair pole safe characteristic equation mode4LeftPair` exited `0` and
found the accepted source contract plus finite-DLMF candidates, but no exact
current declaration.  Exact `kb.py ask` and
`kb.py flags DLMF3035_EVEN_CHARACTERISTIC_SOURCE` both exited `1` with no
exact hit or prior recorded territory.  The immediately preceding clean-tree
startup at `74f87047` exited `0` with `P9_STRICT_PASS`; the imported untracked
right-branch file remained byte-locked at
`0822a3593ce11984bca31c2c619420af02868447a5a31c54db5697d8a3d1ab06`.
-/

noncomputable section

/-- The normalized even finite-left recurrence from DLMF 30.3.5 and 30.3.7.
In the parity-compressed project index, the pair at `q` is
`(a_(q-1), a_q)`, with boundary values `a_(-1)=0` and `a_0=1`; the
corresponding literal DLMF coefficient degrees are `2*(q-1)` and `2*q`. -/
noncomputable def mode4DLMF3035EvenLeftPair
    (G Λ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | q + 1 =>
      let y := mode4DLMF3035EvenLeftPair G Λ q
      (y.2,
        ((mode4DLMF3037Beta G (2 * q) - Λ) * y.2 -
          mode4DLMF3037Gamma G (2 * q) * y.1) /
          mode4DLMF3037Alpha G (2 * q))

/-- The literal DLMF finite-left recurrence agrees with the existing project
left continuant in the same units and even-index convention. -/
theorem mode4DLMF3035EvenLeftPair_eq_mode4LeftPair
    (G Λ : ℝ) (K : ℕ) :
    mode4DLMF3035EvenLeftPair G Λ K = mode4LeftPair G Λ K := by
  induction K with
  | zero => rfl
  | succ q ih =>
      simp only [mode4DLMF3035EvenLeftPair, mode4LeftPair, ih,
        mode4DLMF3037Beta_even_sub_eq_mode4JacobiCenter,
        mode4DLMF3037Gamma_even_eq_mode4JacobiLower,
        mode4DLMF3037Alpha_even_eq_mode4JacobiUpper]

/-- Pole-safe order-zero even DLMF 30.3.5 characteristic equation.  The
source object is defined independently from the project residual: it requires
an even split and cross-multiplies the literal finite-left pair against the
independent infinite right ratio. -/
noncomputable def mode4DLMF3035EvenCharacteristicEquation
    (G Λ : ℝ) (splitDegree : ℕ) : Prop :=
  Even splitDegree ∧
    let K := splitDegree / 2 + 1
    let y := mode4DLMF3035EvenLeftPair G Λ K
    y.2 = mode4DLMF3035EvenRightRatio G Λ K * y.1

/-- On the production contraction domain and at the source-locked split
`2*(K-1)`, the independent DLMF characteristic predicate is exactly the
existing project matching residual equation. -/
theorem mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenCharacteristicEquation
        (mode4JacobiG mProject) Λ (2 * (K - 1))
      ↔
    mode4RootFunction mProject K Λ = 0 := by
  have hEven : Even (2 * (K - 1)) := by
    exact ⟨K - 1, by omega⟩
  have hindex : 2 * (K - 1) / 2 + 1 = K := by omega
  simp only [mode4DLMF3035EvenCharacteristicEquation, hEven, true_and]
  rw [hindex, mode4DLMF3035EvenLeftPair_eq_mode4LeftPair,
    mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
      mProject K Λ hm hK hsep hΛ]
  exact (mode4RootFunction_eq_zero_iff_match mProject K Λ).symm

#print axioms mode4DLMF3035EvenLeftPair_eq_mode4LeftPair
#print axioms mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero

end
