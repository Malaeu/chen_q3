import Q3.Proofs.RouteB.D0Mode4JacobiHermitianTailRow

/-!
# Square-summable uniqueness for the symmetric mode-four tail recurrence

Two square-summable solutions of the exact symmetric Jacobi recurrence are
proportional.  The proof is the discrete-Wronskian argument: the weighted
Wronskian is constant, while the off-diagonal weights are uniformly bounded
and both coefficient rows tend to zero.

This theorem is source-neutral.  It does not assert that either row is a
regular PSWF coefficient row, a Weyl solution, an operator eigenvector, or a
resolvent boundary value.
-/

open Filter Topology

noncomputable section

private theorem mode4SqSummable_tendsto_zero
    {a : ℕ → ℝ}
    (ha : Summable (fun n => (a n) ^ 2)) :
    Tendsto a atTop (𝓝 0) := by
  have hsquare : Tendsto (fun n => (a n) ^ 2) atTop (𝓝 0) :=
    ha.tendsto_atTop_zero
  have habs : Tendsto (fun n => |a n|) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero a).2
    (by simpa [Function.comp_def] using habs)

private theorem mode4JacobiSymmetricOff_pos
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 2 ≤ q) :
    0 < mode4JacobiSymmetricOff G q := by
  unfold mode4JacobiSymmetricOff
  apply Real.sqrt_pos.2
  exact mul_pos
    (mode4JacobiLower_pos G (q + 1) hG (by omega))
    (mode4JacobiUpper_pos G q hG)

private theorem mode4JacobiSymmetricOff_le_G
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 2 ≤ q) :
    mode4JacobiSymmetricOff G q ≤ G := by
  have hqSucc : 3 ≤ q + 1 := by omega
  have hL0 : 0 ≤ mode4JacobiLower G (q + 1) :=
    (mode4JacobiLower_pos G (q + 1) hG hqSucc).le
  have hU0 : 0 ≤ mode4JacobiUpper G q :=
    (mode4JacobiUpper_pos G q hG).le
  have hL := mode4JacobiLower_le_one_third_mul_G G (q + 1) hG hqSucc
  have hU := mode4JacobiUpper_le_one_quarter_mul_G G q hG
  have hprod :
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤ G ^ 2 := by
    calc
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤
          ((1 / 3 : ℝ) * G) * ((1 / 4 : ℝ) * G) :=
        mul_le_mul hL hU hU0 (by positivity)
      _ ≤ G ^ 2 := by nlinarith [sq_pos_of_pos hG]
  unfold mode4JacobiSymmetricOff
  exact (Real.sqrt_le_left hG.le).2 hprod

/-- Any two square-summable solutions of the exact symmetric mode-four tail
recurrence are proportional.  No source or operator interpretation is used. -/
theorem mode4HermitianTail_sqSummable_solution_unique_up_to_scale
    (G Λ : ℝ) (K : ℕ)
    (hG : 0 < G)
    (hK : 3 ≤ K)
    (a b : ℕ → ℝ)
    (ha0 : a 0 ≠ 0)
    (haRec : ∀ n,
      mode4JacobiSymmetricOff G (K - 1 + n) * a n -
        mode4JacobiCenter G Λ (K + n) * a (n + 1) +
        mode4JacobiSymmetricOff G (K + n) * a (n + 2) = 0)
    (hbRec : ∀ n,
      mode4JacobiSymmetricOff G (K - 1 + n) * b n -
        mode4JacobiCenter G Λ (K + n) * b (n + 1) +
        mode4JacobiSymmetricOff G (K + n) * b (n + 2) = 0)
    (haSq : Summable (fun n => (a n) ^ 2))
    (hbSq : Summable (fun n => (b n) ^ 2)) :
    ∃ c : ℝ, ∀ n, b n = c * a n := by
  let W : ℕ → ℝ := fun n => a n * b (n + 1) - a (n + 1) * b n
  let J : ℕ → ℝ := fun n => mode4JacobiSymmetricOff G (K - 1 + n) * W n
  have haLim : Tendsto a atTop (𝓝 0) := mode4SqSummable_tendsto_zero haSq
  have hbLim : Tendsto b atTop (𝓝 0) := mode4SqSummable_tendsto_zero hbSq
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have haSuccLim : Tendsto (fun n => a (n + 1)) atTop (𝓝 0) :=
    haLim.comp hshift
  have hbSuccLim : Tendsto (fun n => b (n + 1)) atTop (𝓝 0) :=
    hbLim.comp hshift
  have hWLim : Tendsto W atTop (𝓝 0) := by
    have h := (haLim.mul hbSuccLim).sub (haSuccLim.mul hbLim)
    simpa [W] using h
  have hWrec : ∀ n,
      mode4JacobiSymmetricOff G (K + n) * W (n + 1) =
        mode4JacobiSymmetricOff G (K - 1 + n) * W n := by
    intro n
    have ha := haRec n
    have hb := hbRec n
    change mode4JacobiSymmetricOff G (K + n) *
        (a (n + 1) * b (n + 2) - a (n + 2) * b (n + 1)) =
      mode4JacobiSymmetricOff G (K - 1 + n) *
        (a n * b (n + 1) - a (n + 1) * b n)
    linear_combination a (n + 1) * hb - b (n + 1) * ha
  have hJsucc : ∀ n, J (n + 1) = J n := by
    intro n
    have hidx : K - 1 + (n + 1) = K + n := by omega
    change mode4JacobiSymmetricOff G (K - 1 + (n + 1)) * W (n + 1) =
      mode4JacobiSymmetricOff G (K - 1 + n) * W n
    rw [hidx]
    exact hWrec n
  have hJconst : ∀ n, J n = J 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hJsucc n, ih]
  have hJbound : ∀ n, |J 0| ≤ G * |W n| := by
    intro n
    rw [← hJconst n]
    have hq : 2 ≤ K - 1 + n := by omega
    have hbeta0 : 0 ≤ mode4JacobiSymmetricOff G (K - 1 + n) :=
      (mode4JacobiSymmetricOff_pos G (K - 1 + n) hG hq).le
    have hbeta := mode4JacobiSymmetricOff_le_G G (K - 1 + n) hG hq
    unfold J
    rw [abs_mul, abs_of_nonneg hbeta0]
    exact mul_le_mul_of_nonneg_right hbeta (abs_nonneg _)
  have hboundLim : Tendsto (fun n => G * |W n|) atTop (𝓝 0) := by
    simpa using hWLim.abs.const_mul G
  have hJzero : J 0 = 0 := by
    have hle : |J 0| ≤ 0 :=
      ge_of_tendsto hboundLim (Filter.Eventually.of_forall hJbound)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hWallZero : ∀ n, W n = 0 := by
    intro n
    have hJn : J n = 0 := by rw [hJconst n, hJzero]
    have hq : 2 ≤ K - 1 + n := by omega
    have hbeta := mode4JacobiSymmetricOff_pos G (K - 1 + n) hG hq
    unfold J at hJn
    exact (mul_eq_zero.mp hJn).resolve_left (ne_of_gt hbeta)
  let c : ℝ := b 0 / a 0
  have hzero : b 0 = c * a 0 := by
    unfold c
    field_simp
  have hone : b 1 = c * a 1 := by
    have hw := hWallZero 0
    dsimp [W] at hw
    unfold c
    field_simp
    nlinarith
  refine ⟨c, fun n => Nat.twoStepInduction
    (P := fun j => b j = c * a j) hzero hone ?_ n⟩
  intro n hn hnSucc
  have ha := haRec n
  have hb := hbRec n
  have hq : 2 ≤ K + n := by omega
  have hbeta := mode4JacobiSymmetricOff_pos G (K + n) hG hq
  have hdiff :
      mode4JacobiSymmetricOff G (K + n) *
        (b (n + 2) - c * a (n + 2)) = 0 := by
    rw [hn, hnSucc] at hb
    linear_combination hb - c * ha
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_left (ne_of_gt hbeta))

#print axioms mode4HermitianTail_sqSummable_solution_unique_up_to_scale
