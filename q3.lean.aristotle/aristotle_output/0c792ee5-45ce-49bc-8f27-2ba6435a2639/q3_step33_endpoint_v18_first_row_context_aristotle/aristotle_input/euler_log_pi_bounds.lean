import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1600000

/-!
# Rigorous bounds on -γ - log π

We prove coarse (3-digit) bounds demonstrating the proof strategy for
bounding `-Real.eulerMascheroniConstant - Real.log Real.pi`.

## Approach

- **γ upper bound**: `eulerMascheroniConstant_lt_eulerMascheroniSeq' N` gives
  `γ < harmonic(N) - log(N)`. `harmonic(N)` is exact rational; `log(N)` is
  bounded via `exp` Taylor remainder + `native_decide` for large rational
  comparisons.

- **γ lower bound**: `eulerMascheroniSeq_lt_eulerMascheroniConstant N` gives
  `harmonic(N) - log(N+1) < γ`. Same tools.

- **log π bounds**: `Real.log_lt_iff_lt_exp` / `lt_log_iff_exp_lt` reduce to
  `exp` evaluation.  Taylor partial sums give lower bounds
  (`sum_le_exp_of_nonneg`), and Taylor remainder gives upper bounds
  (`exp_bound'`). π bounds from `pi_gt_d20` / `pi_lt_d20`.

## Precision gap

For the Omega endpoint anchor in `Step22OmegaClosedFormEndpointBoundsCert`,
the target interval width is ~2e-77, requiring ~77-digit precision on
`-γ - log π`.  Achieving this via `eulerMascheroniSeq` / `eulerMascheroniSeq'`
would require N ~ 10^77 (since the gap `eulerMascheroniSeq'(N) - eulerMascheroniSeq(N)
= log(1+1/N) ≈ 1/N`), which is computationally infeasible with `norm_num`.

**Resolution**: A code-generated high-precision certificate using a
fast-converging γ formula (e.g., Brent-McMillan) and multiprecision rational
arithmetic, compiled as Lean proof terms.
-/

/-- γ < 0.578.  Uses `eulerMascheroniSeq'(1000)` with `native_decide`
for harmonic sum and `exp` bounds for log(1000). -/
lemma euler_lt_0578 : Real.eulerMascheroniConstant < (578 : ℝ) / 1000 := by
  -- Use the exact Euler-Mascheroni inequality with $n = 1000$.
  have h_eulerMascheroni_ineq : Real.eulerMascheroniConstant < ∑ k ∈ Finset.Icc (1 : ℕ) 1000, (1 / (k : ℝ)) - Real.log 1000 := by
    convert Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1000 using 1;
    unfold Real.eulerMascheroniSeq';
    norm_num [ harmonic ];
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
  refine lt_of_lt_of_le h_eulerMascheroni_ineq ?_;
  rw [ show ( 1000 : ℝ ) = 10 ^ 3 by norm_num, Real.log_pow ] ; norm_num;
  -- We'll use that $Real.log 10 > 2.3025$ to conclude the proof.
  have h_log_10 : Real.log 10 > 2.3025 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 400 to get $e^{921} < 10^{400}$.
    have h_exp : Real.exp 921 < 10 ^ 400 := by
      have := Real.exp_one_lt_d9.le;
      -- We can raise both sides to the power of 921 to get $(2.7182818286)^{921} < 10^{400}$.
      have h_exp : (2.7182818286 : ℝ) ^ 921 < 10 ^ 400 := by
        norm_num;
        rw [ div_pow, div_lt_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;
      exact lt_of_le_of_lt ( by rw [ ← Real.exp_nat_mul ] ; norm_num ) ( h_exp.trans_le' ( pow_le_pow_left₀ ( by positivity ) this _ ) );
    contrapose! h_exp;
    exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 400 ) ( by norm_num [ ← Real.exp_nat_mul ] );
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num at * ; linarith

/-- 0.577 < γ.  Uses `eulerMascheroniSeq(10000)` with `native_decide`
for harmonic sum and `exp` bounds for log(10001). -/
lemma euler_gt_0577 : (577 : ℝ) / 1000 < Real.eulerMascheroniConstant := by
  refine' lt_of_lt_of_le _ ( le_of_lt ( Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 10000 ) );
  rw [ Real.eulerMascheroniSeq ];
  -- We'll use the fact that $\log(10001) \approx 9.2104$ to simplify the expression.
  have h_log_approx : Real.log 10001 < 9.2105 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 2000 to remove the fraction.
    suffices h_exp : (10001 : ℝ) ^ 2000 < Real.exp 18421 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 2000 );
    have := Real.exp_one_gt_d9.le;
    -- We can use the fact that $e^{18421} > (2.7182818283)^{18421}$ and compare this to $10001^{2000}$.
    have h_exp : (2.7182818283 : ℝ) ^ 18421 > 10001 ^ 2000 := by
      norm_num;
      rw [ div_pow, lt_div_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;
    exact h_exp.trans_le ( by simpa using pow_le_pow_left₀ ( by norm_num ) this 18421 );
  -- Now use the fact that $H_{10000} \approx 9.7876$ to conclude the proof.
  have h_harmonic : (harmonic 10000 : ℝ) > 9.7876 := by
    rw [ show ( 9.7876 : ℝ ) = 97876 / 10000 by norm_num, gt_iff_lt, div_lt_iff₀ ] <;> exact mod_cast by native_decide;
  linarith

/-- log(π) < 1.145.  Uses Taylor lower bound for exp(1.145) and π < 3.141593. -/
lemma log_pi_lt : Real.log Real.pi < (1145 : ℝ) / 1000 := by
  rw [Real.log_lt_iff_lt_exp (by exact Real.pi_pos)]
  have h_pi : Real.pi < 3.141593 := Real.pi_lt_d6
  refine lt_of_lt_of_le h_pi ?_;
  rw [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ] ; exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) ) ;

/-- 1.144 < log(π).  Uses Taylor upper bound for exp(1.144) and π > 3.14159265358979323846. -/
lemma log_pi_gt : (1144 : ℝ) / 1000 < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt (by exact Real.pi_pos)]
  have h_split : Real.exp (1144 / 1000) = Real.exp 1 * Real.exp (144 / 1000) := by
    rw [ ← Real.exp_add ] ; norm_num;
  have h_exp_bound : Real.exp (144 / 1000) ≤ (∑ i ∈ Finset.range 6, (144 / 1000 : ℝ)^i / Nat.factorial i) + (144 / 1000 : ℝ)^6 * (6 + 1) / (Nat.factorial 6 * 6) := by
    exact Real.exp_bound' ( by norm_num ) ( by norm_num ) ( by norm_num )
  norm_num at *; (
  exact h_split.symm ▸ lt_of_le_of_lt ( mul_le_mul_of_nonneg_left h_exp_bound <| Real.exp_nonneg _ ) ( by have := Real.exp_one_lt_d9; norm_num1 at *; linarith [ Real.pi_gt_d20 ] ) ;)

/-- Combined coarse bound: -1.723 ≤ -γ - log π ≤ -1.721. -/
theorem neg_euler_sub_log_pi_bounds :
    ((-1723 : ℝ) / 1000) ≤ -Real.eulerMascheroniConstant - Real.log Real.pi ∧
    -Real.eulerMascheroniConstant - Real.log Real.pi ≤ ((-1721 : ℝ) / 1000) := by
  exact ⟨by linarith [euler_lt_0578, log_pi_lt], by linarith [euler_gt_0577, log_pi_gt]⟩
