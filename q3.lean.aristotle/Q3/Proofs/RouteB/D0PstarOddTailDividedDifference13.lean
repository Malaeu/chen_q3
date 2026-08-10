import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Exact odd source divided-difference identity at `m = 13`

The source commutator theorem already reconstructs every off-diagonal Weil
entry from the central-column beta scalar.  This file takes the exact odd
difference used by the G-LOWER tail and performs the cancellation before any
absolute-value or norm estimate:

`tau(k,n) - tau(k,-n) = 2 * (n * beta(k) - k * beta(n)) / (k^2 - n^2)`.

This is only the algebraic source identity.  It does not prove summability,
an infinite outer-block inverse, a graded resolvent estimate, odd-tail
coercivity, a constant floor, or an RH claim.
-/

/-- The central-column source beta scalar is odd in the mode index. -/
theorem ccmBetaScalar_neg
    (mProject : ℕ) (hm : 2 ≤ mProject) (n : ℤ) :
    Q3.RouteB.ccmBetaScalar mProject (-n) =
      -Q3.RouteB.ccmBetaScalar mProject n := by
  unfold Q3.RouteB.ccmBetaScalar
  have htau :
      Q3.RouteB.ccmWeilTauN1 mProject (-n) 0 =
        Q3.RouteB.ccmWeilTauN1 mProject n 0 := by
    simpa using Q3.RouteB.ccmWeilTauN1_neg_neg mProject hm n 0
  rw [htau]
  push_cast
  ring

/-- The exact odd off-diagonal entry before any tail estimate. -/
noncomputable def ccmWeilOddEntry
    (mProject : ℕ) (k n : ℤ) : ℝ :=
  Q3.RouteB.ccmWeilTauN1 mProject k n -
    Q3.RouteB.ccmWeilTauN1 mProject k (-n)

/-- Exact source-beta collapse of the odd off-diagonal entry.  The order
`0 < n < k` is the tail-versus-head regime and makes every denominator
nonzero without a totalized-division convention. -/
theorem ccmWeilOddEntry_eq_beta_dividedDifference
    (mProject : ℕ) (hm : 2 ≤ mProject)
    (k n : ℤ) (hnpos : 0 < n) (hnk : n < k) :
    ccmWeilOddEntry mProject k n =
      2 *
          ((n : ℝ) * Q3.RouteB.ccmBetaScalar mProject k -
            (k : ℝ) * Q3.RouteB.ccmBetaScalar mProject n) /
        ((k : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
  have hkn : k ≠ n := by omega
  have hkneg : k ≠ -n := by omega
  have hkmR : (k : ℝ) - (n : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hkn)
  have hkpR : (k : ℝ) - ((-n : ℤ) : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hkneg)
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnkR : (n : ℝ) < (k : ℝ) := by exact_mod_cast hnk
  have hkpnR : (k : ℝ) + (n : ℝ) ≠ 0 := by
    nlinarith
  have hsqR : (k : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    nlinarith
  unfold ccmWeilOddEntry
  rw [Q3.RouteB.ccmWeilTau_structured_offdiag mProject hm hkn,
    Q3.RouteB.ccmWeilTau_structured_offdiag mProject hm hkneg,
    ccmBetaScalar_neg mProject hm n]
  push_cast
  field_simp [hkmR, hkpR, hkpnR, hsqR]
  ring

/-- Finite odd residual rows inherit the same cancellation before a norm is
taken.  This identity is deliberately stated in an arbitrary real module so
that the corrected head rows can later be substituted without changing the
source algebra. -/
theorem sum_ccmWeilOddEntry_smul_eq_beta_cancellation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mProject : ℕ) (hm : 2 ≤ mProject)
    (k : ℤ) (s : Finset ℤ) (Z : ℤ → E)
    (hs : ∀ n ∈ s, 0 < n ∧ n < k) :
    (∑ n ∈ s, ccmWeilOddEntry mProject k n • Z n) =
      (2 * Q3.RouteB.ccmBetaScalar mProject k) •
          (∑ n ∈ s,
            ((n : ℝ) / ((k : ℝ) ^ 2 - (n : ℝ) ^ 2)) • Z n) -
        (2 * (k : ℝ)) •
          (∑ n ∈ s,
            (Q3.RouteB.ccmBetaScalar mProject n /
              ((k : ℝ) ^ 2 - (n : ℝ) ^ 2)) • Z n) := by
  classical
  calc
    (∑ n ∈ s, ccmWeilOddEntry mProject k n • Z n) =
        ∑ n ∈ s,
          (((2 * Q3.RouteB.ccmBetaScalar mProject k) *
                ((n : ℝ) / ((k : ℝ) ^ 2 - (n : ℝ) ^ 2))) -
              ((2 * (k : ℝ)) *
                (Q3.RouteB.ccmBetaScalar mProject n /
                  ((k : ℝ) ^ 2 - (n : ℝ) ^ 2)))) • Z n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccmWeilOddEntry_eq_beta_dividedDifference mProject hm k n
        (hs n hn).1 (hs n hn).2]
      congr 1
      ring
    _ = (∑ n ∈ s,
          ((2 * Q3.RouteB.ccmBetaScalar mProject k) *
            ((n : ℝ) / ((k : ℝ) ^ 2 - (n : ℝ) ^ 2))) • Z n) -
        (∑ n ∈ s,
          ((2 * (k : ℝ)) *
            (Q3.RouteB.ccmBetaScalar mProject n /
              ((k : ℝ) ^ 2 - (n : ℝ) ^ 2))) • Z n) := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    _ = (2 * Q3.RouteB.ccmBetaScalar mProject k) •
          (∑ n ∈ s,
            ((n : ℝ) / ((k : ℝ) ^ 2 - (n : ℝ) ^ 2)) • Z n) -
        (2 * (k : ℝ)) •
          (∑ n ∈ s,
            (Q3.RouteB.ccmBetaScalar mProject n /
              ((k : ℝ) ^ 2 - (n : ℝ) ^ 2)) • Z n) := by
      simp only [Finset.smul_sum, smul_smul]

/-- The exact odd source entry selected by the G-LOWER cell `m = 13`. -/
noncomputable def ccmWeilOddEntry13 (k n : ℤ) : ℝ :=
  ccmWeilOddEntry 13 k n

/-- Specialized `m = 13` source identity.  This is the Lean-facing algebraic
input for a future `OddTailGradedResolventBound13`; it is not that bound. -/
theorem ccmWeilOddEntry13_eq_beta_dividedDifference
    (k n : ℤ) (hnpos : 0 < n) (hnk : n < k) :
    ccmWeilOddEntry13 k n =
      2 *
          ((n : ℝ) * Q3.RouteB.ccmBetaScalar 13 k -
            (k : ℝ) * Q3.RouteB.ccmBetaScalar 13 n) /
        ((k : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
  exact ccmWeilOddEntry_eq_beta_dividedDifference 13 (by norm_num)
    k n hnpos hnk

#print axioms ccmBetaScalar_neg
#print axioms ccmWeilOddEntry_eq_beta_dividedDifference
#print axioms sum_ccmWeilOddEntry_smul_eq_beta_cancellation
#print axioms ccmWeilOddEntry13_eq_beta_dividedDifference

end Q3.RouteB.D0Pstar
