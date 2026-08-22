import Mathlib
import RequestProject.Defs
import RequestProject.Legendre

/-!
# Existence of infinitely many regular even spheroidal eigenvalues

The even regular eigenfunctions of

`L f = - d/dx ((1 - x^2) f'(x)) - G (1 - x^2) f(x)`

are expanded in the basis of even Legendre polynomials, `f = ∑ c_k P_{2k}`.  Since
`-((1-x²) P_n')' = n(n+1) P_n` and `(1 - x²) P_{2k}` is a combination of `P_{2k+2}`, `P_{2k}` and
`P_{2k-2}`, the eigenvalue equation becomes a Jacobi (tridiagonal) system for the coefficients,
with diagonal `2k(2k+1) - G b_k → ∞` and bounded off-diagonal entries.

For every large `n` a Banach fixed point argument in a weighted sup-norm produces a solution of
that system with `c_n = 1`, a coefficient decay `|c_k| ≤ ρ^{-|k-n|}/4` for `k ≠ n`, and an
eigenvalue parameter `Λ` close to `2n(2n+1)`.  The resulting series is then shown to be a genuine
regular even eigenfunction.  Since `2n(2n+1) → ∞`, the spectrum is unbounded, hence infinite.
-/

open Set Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-- The weight base used in the fixed point argument. -/
def specRho : ℝ := 1000

/-- The Legendre eigenvalue `2k(2k+1)`. -/
noncomputable def specLam (k : ℕ) : ℝ := (2 * (k : ℝ)) * (2 * (k : ℝ) + 1)

/-- The diagonal entry of the Jacobi matrix. -/
noncomputable def specD (G : ℝ) (k : ℕ) : ℝ := specLam k - G * jacB k

/-- The lower off-diagonal coefficient (vanishing at `k = 0`). -/
noncomputable def specJL (k : ℕ) : ℝ := if k = 0 then 0 else jacA (k - 1)

/-- The upper off-diagonal coefficient. -/
noncomputable def specJR (k : ℕ) : ℝ := jacC (k + 1)

@[simp] theorem specJL_zero : specJL 0 = 0 := by simp [specJL]

@[simp] theorem specJL_succ (k : ℕ) : specJL (k + 1) = jacA k := by simp [specJL]

theorem specJL_abs_le_one (k : ℕ) : |specJL k| ≤ 1 := by
  match k with
  | 0 => simp
  | (j + 1) => simpa using jacA_abs_le_one j

theorem specJR_abs_le_one (k : ℕ) : |specJR k| ≤ 1 := jacC_abs_le_one (k + 1)

/-- The function attached to a coefficient sequence. -/
noncomputable def specF (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, c k * lpv (2 * k) x

/-- The termwise derivative of `specF`. -/
noncomputable def specF1 (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, c k * lpd (2 * k) x

/-- The termwise second derivative of `specF`. -/
noncomputable def specF2 (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, c k * lpdd (2 * k) x

/-! ### Summability -/

theorem spec_summable_of_bound {A B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1) {v : ℕ → ℝ}
    (hv : ∀ k, |v k| ≤ A * B ^ k) : Summable v := by
  refine Summable.of_norm_bounded (g := fun k => A * B ^ k) ?_ (fun k => by simpa using hv k)
  exact (summable_geometric_of_lt_one hB0 hB1).mul_left A

section Coeffs

variable {c : ℕ → ℝ} {A : ℝ}

theorem spec_A_nonneg (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) : 0 ≤ A := by
  have h := hdecay 0
  simp at h
  exact le_trans (abs_nonneg _) h

theorem spec_summable_v (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k => c k * lpv (2 * k) x) := by
  have hA := spec_A_nonneg hdecay
  refine spec_summable_of_bound (A := A) (B := 9 / 1000) (by norm_num) (by norm_num) ?_
  intro k
  have h1 : |c k * lpv (2 * k) x| = |c k| * |lpv (2 * k) x| := abs_mul _ _
  have h2 : |lpv (2 * k) x| ≤ 3 ^ (2 * k) := lpv_abs_le _ hx
  have h3 : (3 : ℝ) ^ (2 * k) = 9 ^ k := by
    rw [pow_mul]; norm_num
  have h4 : A * (1 / specRho) ^ k * 9 ^ k = A * (9 / 1000 : ℝ) ^ k := by
    unfold specRho
    rw [mul_assoc, ← mul_pow]
    norm_num
  calc |c k * lpv (2 * k) x| = |c k| * |lpv (2 * k) x| := h1
    _ ≤ (A * (1 / specRho) ^ k) * 9 ^ k := by
        refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
        have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
        nlinarith
    _ = A * (9 / 1000 : ℝ) ^ k := h4

theorem spec_summable_d (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k => c k * lpd (2 * k) x) := by
  have hA := spec_A_nonneg hdecay
  refine spec_summable_of_bound (A := A) (B := 81 / 1000) (by norm_num) (by norm_num) ?_
  intro k
  have h2 : |lpd (2 * k) x| ≤ 9 ^ (2 * k) := lpd_abs_le _ hx
  have h3 : (9 : ℝ) ^ (2 * k) = 81 ^ k := by rw [pow_mul]; norm_num
  have h4 : A * (1 / specRho) ^ k * 81 ^ k = A * (81 / 1000 : ℝ) ^ k := by
    unfold specRho
    rw [mul_assoc, ← mul_pow]
    norm_num
  calc |c k * lpd (2 * k) x| = |c k| * |lpd (2 * k) x| := abs_mul _ _
    _ ≤ (A * (1 / specRho) ^ k) * 81 ^ k := by
        refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
        have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
        nlinarith
    _ = A * (81 / 1000 : ℝ) ^ k := h4

theorem spec_summable_dd (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k => c k * lpdd (2 * k) x) := by
  have hA := spec_A_nonneg hdecay
  refine spec_summable_of_bound (A := A) (B := 729 / 1000) (by norm_num) (by norm_num) ?_
  intro k
  have h2 : |lpdd (2 * k) x| ≤ 27 ^ (2 * k) := lpdd_abs_le _ hx
  have h3 : (27 : ℝ) ^ (2 * k) = 729 ^ k := by rw [pow_mul]; norm_num
  have h4 : A * (1 / specRho) ^ k * 729 ^ k = A * (729 / 1000 : ℝ) ^ k := by
    unfold specRho
    rw [mul_assoc, ← mul_pow]
    norm_num
  calc |c k * lpdd (2 * k) x| = |c k| * |lpdd (2 * k) x| := abs_mul _ _
    _ ≤ (A * (1 / specRho) ^ k) * 729 ^ k := by
        refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
        have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
        nlinarith
    _ = A * (729 / 1000 : ℝ) ^ k := h4

/-! ### Regularity of the sum -/

theorem spec_hasDerivAt_F (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (specF c) (specF1 c x) x := by
  have hA := spec_A_nonneg hdecay
  have hu : Summable (fun k : ℕ => A * (81 / 1000 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hmem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => A * (81 / 1000 : ℝ) ^ k) hu
    isOpen_Ioo (isPreconnected_Ioo) (fun k y _ => (hasDerivAt_lpv (2 * k) y).const_mul (c k))
    (fun k y hy => ?_) hmem ?_ hx
  · have hy1 : |y| ≤ 1 := by
      rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have h2 : |lpd (2 * k) y| ≤ 9 ^ (2 * k) := lpd_abs_le _ hy1
    have h3 : (9 : ℝ) ^ (2 * k) = 81 ^ k := by rw [pow_mul]; norm_num
    have h4 : A * (1 / specRho) ^ k * 81 ^ k = A * (81 / 1000 : ℝ) ^ k := by
      unfold specRho
      rw [mul_assoc, ← mul_pow]
      norm_num
    have : |c k * lpd (2 * k) y| ≤ A * (81 / 1000 : ℝ) ^ k := by
      calc |c k * lpd (2 * k) y| = |c k| * |lpd (2 * k) y| := abs_mul _ _
        _ ≤ (A * (1 / specRho) ^ k) * 81 ^ k := by
            refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
            have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
            nlinarith
        _ = A * (81 / 1000 : ℝ) ^ k := h4
    simpa using this
  · exact spec_summable_v hdecay (by norm_num)

theorem spec_hasDerivAt_F1 (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (specF1 c) (specF2 c x) x := by
  have hA := spec_A_nonneg hdecay
  have hu : Summable (fun k : ℕ => A * (729 / 1000 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hmem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => A * (729 / 1000 : ℝ) ^ k) hu
    isOpen_Ioo (isPreconnected_Ioo) (fun k y _ => (hasDerivAt_lpd (2 * k) y).const_mul (c k))
    (fun k y hy => ?_) hmem ?_ hx
  · have hy1 : |y| ≤ 1 := by
      rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have h2 : |lpdd (2 * k) y| ≤ 27 ^ (2 * k) := lpdd_abs_le _ hy1
    have h3 : (27 : ℝ) ^ (2 * k) = 729 ^ k := by rw [pow_mul]; norm_num
    have h4 : A * (1 / specRho) ^ k * 729 ^ k = A * (729 / 1000 : ℝ) ^ k := by
      unfold specRho
      rw [mul_assoc, ← mul_pow]
      norm_num
    have : |c k * lpdd (2 * k) y| ≤ A * (729 / 1000 : ℝ) ^ k := by
      calc |c k * lpdd (2 * k) y| = |c k| * |lpdd (2 * k) y| := abs_mul _ _
        _ ≤ (A * (1 / specRho) ^ k) * 729 ^ k := by
            refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
            have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
            nlinarith
        _ = A * (729 / 1000 : ℝ) ^ k := h4
    simpa using this
  · exact spec_summable_d hdecay (by norm_num)

theorem spec_continuousOn_F (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) :
    ContinuousOn (specF c) (Icc (-1 : ℝ) 1) := by
  have hA := spec_A_nonneg hdecay
  have hu : Summable (fun k : ℕ => A * (9 / 1000 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hbd : ∀ (k : ℕ), ∀ x ∈ Icc (-1 : ℝ) 1, ‖c k * lpv (2 * k) x‖ ≤ A * (9 / 1000 : ℝ) ^ k := by
    intro k x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have h2 : |lpv (2 * k) x| ≤ 3 ^ (2 * k) := lpv_abs_le _ hx1
    have h3 : (3 : ℝ) ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
    have h4 : A * (1 / specRho) ^ k * 9 ^ k = A * (9 / 1000 : ℝ) ^ k := by
      unfold specRho
      rw [mul_assoc, ← mul_pow]
      norm_num
    have : |c k * lpv (2 * k) x| ≤ A * (9 / 1000 : ℝ) ^ k := by
      calc |c k * lpv (2 * k) x| = |c k| * |lpv (2 * k) x| := abs_mul _ _
        _ ≤ (A * (1 / specRho) ^ k) * 9 ^ k := by
            refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
            have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
            nlinarith
        _ = A * (9 / 1000 : ℝ) ^ k := h4
    simpa using this
  have huc := tendstoUniformlyOn_tsum hu hbd
  refine huc.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards with t
  exact continuousOn_finset_sum t (fun k _ =>
    (Continuous.continuousOn (continuous_const.mul (continuous_lpv (2 * k)))))

theorem spec_continuousOn_F1 (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) :
    ContinuousOn (specF1 c) (Icc (-1 : ℝ) 1) := by
  have hA := spec_A_nonneg hdecay
  have hu : Summable (fun k : ℕ => A * (81 / 1000 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hbd : ∀ (k : ℕ), ∀ x ∈ Icc (-1 : ℝ) 1, ‖c k * lpd (2 * k) x‖ ≤ A * (81 / 1000 : ℝ) ^ k := by
    intro k x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have h2 : |lpd (2 * k) x| ≤ 9 ^ (2 * k) := lpd_abs_le _ hx1
    have h3 : (9 : ℝ) ^ (2 * k) = 81 ^ k := by rw [pow_mul]; norm_num
    have h4 : A * (1 / specRho) ^ k * 81 ^ k = A * (81 / 1000 : ℝ) ^ k := by
      unfold specRho
      rw [mul_assoc, ← mul_pow]
      norm_num
    have : |c k * lpd (2 * k) x| ≤ A * (81 / 1000 : ℝ) ^ k := by
      calc |c k * lpd (2 * k) x| = |c k| * |lpd (2 * k) x| := abs_mul _ _
        _ ≤ (A * (1 / specRho) ^ k) * 81 ^ k := by
            refine mul_le_mul (hdecay k) (by rw [← h3]; exact h2) (abs_nonneg _) ?_
            have : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
            nlinarith
        _ = A * (81 / 1000 : ℝ) ^ k := h4
    simpa using this
  have huc := tendstoUniformlyOn_tsum hu hbd
  refine huc.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards with t
  exact continuousOn_finset_sum t (fun k _ =>
    (Continuous.continuousOn (continuous_const.mul (continuous_lpd (2 * k)))))


/-! ### A general summability helper for shifted series -/

theorem spec_summable_shift {D : ℝ} {w : ℕ → ℝ} (hw : ∀ k, |w k| ≤ D * (1 / specRho) ^ k)
    {m : ℕ → ℕ} (hm : ∀ k, m k ≤ 2 * k + 4) {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k => w k * lpv (m k) x) := by
  have hD : 0 ≤ D := by
    have h := hw 0
    simp at h
    exact le_trans (abs_nonneg _) h
  refine spec_summable_of_bound (A := 81 * D) (B := 9 / 1000) (by norm_num) (by norm_num) ?_
  intro k
  have h2 : |lpv (m k) x| ≤ 3 ^ (m k) := lpv_abs_le _ hx
  have h3 : (3 : ℝ) ^ (m k) ≤ 3 ^ (2 * k + 4) := by
    refine pow_le_pow_right₀ (by norm_num) (hm k)
  have h5 : (3 : ℝ) ^ (2 * k + 4) = 81 * 9 ^ k := by
    rw [pow_add, pow_mul]; norm_num; ring
  have h6 : (0 : ℝ) ≤ (1 / specRho) ^ k := by unfold specRho; positivity
  have h7 : D * (1 / specRho) ^ k * (81 * 9 ^ k) = 81 * D * (9 / 1000 : ℝ) ^ k := by
    unfold specRho
    rw [show (9 / 1000 : ℝ) = (1 / 1000) * 9 by norm_num, mul_pow]
    ring
  calc |w k * lpv (m k) x| = |w k| * |lpv (m k) x| := abs_mul _ _
    _ ≤ (D * (1 / specRho) ^ k) * (81 * 9 ^ k) := by
        refine mul_le_mul (hw k) (le_trans h2 (by rw [← h5]; exact h3)) (abs_nonneg _) ?_
        positivity
    _ = 81 * D * (9 / 1000 : ℝ) ^ k := h7

/-! ### The differential equation -/

theorem spec_ode {G Λ : ℝ} (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k)
    (hrows : ∀ k, (specD G k - Λ) * c k = G * (specJL k * c (k - 1) + specJR k * c (k + 1)))
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -(1 - x ^ 2) * specF2 c x + 2 * x * specF1 c x + G * x ^ 2 * specF c x
      = (Λ + G) * specF c x := by
  have hA := spec_A_nonneg hdecay
  have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hrho : (0 : ℝ) < specRho := by unfold specRho; norm_num
  have sV := spec_summable_v hdecay hx1
  have sD := spec_summable_d hdecay hx1
  have sDD := spec_summable_dd hdecay hx1
  -- the shifted series
  have hrho1 : (1 : ℝ) ≤ specRho := by unfold specRho; norm_num
  have hpow : ∀ k : ℕ, (0 : ℝ) ≤ (1 / specRho) ^ k := by
    intro k; unfold specRho; positivity
  have hAp : ∀ k : ℕ, (0 : ℝ) ≤ A * (1 / specRho) ^ k := fun k => mul_nonneg hA (hpow k)
  have hbA : ∀ k, |c k * jacA k| ≤ A * (1 / specRho) ^ k := by
    intro k
    rw [abs_mul]
    calc |c k| * |jacA k| ≤ (A * (1 / specRho) ^ k) * 1 :=
          mul_le_mul (hdecay k) (jacA_abs_le_one k) (abs_nonneg _) (hAp k)
      _ = A * (1 / specRho) ^ k := mul_one _
  have hbC : ∀ k, |c k * jacC k| ≤ A * (1 / specRho) ^ k := by
    intro k
    rw [abs_mul]
    calc |c k| * |jacC k| ≤ (A * (1 / specRho) ^ k) * 1 :=
          mul_le_mul (hdecay k) (jacC_abs_le_one k) (abs_nonneg _) (hAp k)
      _ = A * (1 / specRho) ^ k := mul_one _
  have hbL : ∀ k, |specJL k * c (k - 1)| ≤ (specRho * A) * (1 / specRho) ^ k := by
    intro k
    rw [abs_mul]
    have hstep : A * (1 / specRho) ^ (k - 1) ≤ (specRho * A) * (1 / specRho) ^ k := by
      match k with
      | 0 =>
        simp only [Nat.zero_sub, pow_zero, mul_one]
        nlinarith [hA, hrho1]
      | (j + 1) =>
        have hne : (specRho : ℝ) ≠ 0 := by unfold specRho; norm_num
        have heq : (specRho * A) * (1 / specRho) ^ (j + 1) = A * (1 / specRho) ^ j := by
          calc (specRho * A) * (1 / specRho) ^ (j + 1)
              = (specRho * (1 / specRho)) * (A * (1 / specRho) ^ j) := by rw [pow_succ]; ring
            _ = A * (1 / specRho) ^ j := by rw [mul_one_div, div_self hne, one_mul]
        simp only [Nat.add_sub_cancel]
        rw [heq]
    have h1 : |c (k - 1)| ≤ (specRho * A) * (1 / specRho) ^ k := le_trans (hdecay (k - 1)) hstep
    calc |specJL k| * |c (k - 1)| ≤ 1 * ((specRho * A) * (1 / specRho) ^ k) :=
          mul_le_mul (specJL_abs_le_one k) h1 (abs_nonneg _) zero_le_one
      _ = (specRho * A) * (1 / specRho) ^ k := one_mul _
  have hbR : ∀ k, |specJR k * c (k + 1)| ≤ A * (1 / specRho) ^ k := by
    intro k
    rw [abs_mul]
    have hstep : A * (1 / specRho) ^ (k + 1) ≤ A * (1 / specRho) ^ k := by
      have h3 : (1 / specRho : ℝ) ^ (k + 1) = (1 / specRho) ^ k * (1 / specRho) := by ring
      have h5 : (1 / specRho : ℝ) ≤ 1 := by unfold specRho; norm_num
      rw [h3, ← mul_assoc]
      exact mul_le_of_le_one_right (hAp k) h5
    have h1 : |c (k + 1)| ≤ A * (1 / specRho) ^ k := le_trans (hdecay (k + 1)) hstep
    calc |specJR k| * |c (k + 1)| ≤ 1 * (A * (1 / specRho) ^ k) :=
          mul_le_mul (specJR_abs_le_one k) h1 (abs_nonneg _) zero_le_one
      _ = A * (1 / specRho) ^ k := one_mul _
  have hmA : ∀ k : ℕ, 2 * k + 2 ≤ 2 * k + 4 := fun k => by omega
  have hmC : ∀ k : ℕ, 2 * k - 2 ≤ 2 * k + 4 := fun k => by omega
  have hmI : ∀ k : ℕ, 2 * k ≤ 2 * k + 4 := fun k => by omega
  have sA : Summable (fun k => (c k * jacA k) * lpv (2 * k + 2) x) :=
    spec_summable_shift hbA hmA hx1
  have sC : Summable (fun k => (c k * jacC k) * lpv (2 * k - 2) x) :=
    spec_summable_shift hbC hmC hx1
  have sL : Summable (fun k => (specJL k * c (k - 1)) * lpv (2 * k) x) :=
    spec_summable_shift hbL hmI hx1
  have sR : Summable (fun k => (specJR k * c (k + 1)) * lpv (2 * k) x) :=
    spec_summable_shift hbR hmI hx1
  -- the termwise identity
  have hterm : ∀ k : ℕ,
      (-(1 - x ^ 2)) * (c k * lpdd (2 * k) x) + 2 * x * (c k * lpd (2 * k) x)
        + G * x ^ 2 * (c k * lpv (2 * k) x) - (Λ + G) * (c k * lpv (2 * k) x)
      = G * ((specJL k * c (k - 1)) * lpv (2 * k) x)
        + G * ((specJR k * c (k + 1)) * lpv (2 * k) x)
        - G * ((c k * jacA k) * lpv (2 * k + 2) x)
        - G * ((c k * jacC k) * lpv (2 * k - 2) x) := by
    intro k
    have hode := legendre_ode (2 * k) x
    have hexp := legendre_even_expansion k x
    have hrow := hrows k
    simp only [specD, specLam] at hrow
    push_cast at hode
    linear_combination (-(c k)) * hode + (-(G * c k)) * hexp + (lpv (2 * k) x) * hrow
  -- assemble
  have hs1 : Summable (fun k => (-(1 - x ^ 2)) * (c k * lpdd (2 * k) x)) := sDD.mul_left _
  have hs2 : Summable (fun k => 2 * x * (c k * lpd (2 * k) x)) := sD.mul_left _
  have hs3 : Summable (fun k => G * x ^ 2 * (c k * lpv (2 * k) x)) := sV.mul_left _
  have hs4 : Summable (fun k => (Λ + G) * (c k * lpv (2 * k) x)) := sV.mul_left _
  have expand : -(1 - x ^ 2) * specF2 c x + 2 * x * specF1 c x + G * x ^ 2 * specF c x
      - (Λ + G) * specF c x
      = ∑' k, ((-(1 - x ^ 2)) * (c k * lpdd (2 * k) x) + 2 * x * (c k * lpd (2 * k) x)
        + G * x ^ 2 * (c k * lpv (2 * k) x) - (Λ + G) * (c k * lpv (2 * k) x)) := by
    rw [Summable.tsum_sub ((hs1.add hs2).add hs3) hs4, Summable.tsum_add (hs1.add hs2) hs3,
      Summable.tsum_add hs1 hs2, tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    rfl
  have hshiftA : (∑' k, (specJL k * c (k - 1)) * lpv (2 * k) x)
      = ∑' k, (c k * jacA k) * lpv (2 * k + 2) x := by
    rw [sL.tsum_eq_zero_add]
    simp only [specJL_zero, zero_mul, Nat.zero_sub, specJL_succ]
    refine (add_eq_right.mpr rfl).trans (tsum_congr (fun k => ?_))
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega]
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
    ring
  have hshiftC : (∑' k, (c k * jacC k) * lpv (2 * k - 2) x)
      = ∑' k, (specJR k * c (k + 1)) * lpv (2 * k) x := by
    rw [sC.tsum_eq_zero_add]
    simp only [jacC_zero, mul_zero, zero_mul]
    refine (add_eq_right.mpr rfl).trans (tsum_congr (fun k => ?_))
    rw [show 2 * (k + 1) - 2 = 2 * k from by omega]
    unfold specJR
    ring
  have hzero : (∑' k, ((-(1 - x ^ 2)) * (c k * lpdd (2 * k) x) + 2 * x * (c k * lpd (2 * k) x)
      + G * x ^ 2 * (c k * lpv (2 * k) x) - (Λ + G) * (c k * lpv (2 * k) x))) = 0 := by
    rw [tsum_congr hterm]
    rw [Summable.tsum_sub (((sL.mul_left G).add (sR.mul_left G)).sub (sA.mul_left G))
        (sC.mul_left G),
      Summable.tsum_sub ((sL.mul_left G).add (sR.mul_left G)) (sA.mul_left G),
      Summable.tsum_add (sL.mul_left G) (sR.mul_left G),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left, hshiftA, hshiftC]
    ring
  have := expand.trans hzero
  linarith

theorem spec_even (x : ℝ) : specF c (-x) = specF c x := by
  unfold specF
  refine tsum_congr (fun k => ?_)
  rw [lpv_neg]
  have : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]; norm_num
  rw [this, one_mul]

theorem spec_at_one : specF c 1 = ∑' k, c k := by
  unfold specF
  refine tsum_congr (fun k => ?_)
  rw [lpv_at_one, mul_one]

end Coeffs

end
