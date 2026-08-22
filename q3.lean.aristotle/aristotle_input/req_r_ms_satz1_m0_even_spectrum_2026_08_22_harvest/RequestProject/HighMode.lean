import Mathlib
import RequestProject.Defs
import RequestProject.Legendre
import RequestProject.Spectrum

/-!
# High-mode preflight: uniform diagonal dominance and the decay crosswalk

First slice of `SPHEROIDAL_HIGH_MODE_JACOBI_WITNESS` (verdict `cab2b8c7`,
task `TASK_2026-08-22_spheroidal_high_mode_jacobi_witness.md`).

Two things are proved here, both consumed by the Banach fixed-point step that
remains open:

1. **Uniform diagonal dominance.** The Jacobi diagonal `specD G k` separates
   from `specD G n` linearly in `n`, uniformly over `k ≠ n`, and the bound
   survives shifting by any `Λ` within a fixed distance `C` of the `n`-th
   diagonal entry. Every constant sits outside the quantifier over the mode
   index; nothing is chosen after inspecting finitely many `n`.

2. **Decay crosswalk.** The fixed-point argument produces coefficients decaying
   from a moving centre `n`; the existing `Spectrum.lean` machinery consumes
   decay from the origin. A moving-centre bound implies the origin-centred
   bound with constant `ρ^n`, which is a constant for each fixed sequence, so
   all existing summability/regularity/ODE lemmas apply unchanged.

Not here: the fixed-point construction itself and the witness theorem. The
first exact missing lemma is stated at the bottom as the remaining obligation.
-/

open Set

noncomputable section

/-! ### Casts -/

theorem one_le_abs_cast_sub {k n : ℕ} (h : k ≠ n) : (1 : ℝ) ≤ |(k : ℝ) - n| := by
  rcases Nat.lt_or_lt_of_ne h with hlt | hgt
  · have hle : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have hle : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hgt
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ### The diagonal separates linearly in the centre index -/

theorem specLam_sub (k n : ℕ) :
    specLam k - specLam n = ((k : ℝ) - n) * (4 * ((k : ℝ) + n) + 2) := by
  unfold specLam; ring

/-- The bare Legendre diagonal gap: distinct indices are separated by at least
`4 n + 2`, uniformly over the other index. -/
theorem specLam_gap {k n : ℕ} (h : k ≠ n) :
    4 * (n : ℝ) + 2 ≤ |specLam k - specLam n| := by
  rw [specLam_sub, abs_mul]
  have hpos : (0 : ℝ) ≤ 4 * ((k : ℝ) + n) + 2 := by positivity
  rw [abs_of_nonneg hpos]
  have h1 := one_le_abs_cast_sub h
  have h2 : 4 * (n : ℝ) + 2 ≤ 4 * ((k : ℝ) + n) + 2 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  calc 4 * (n : ℝ) + 2 = 1 * (4 * (n : ℝ) + 2) := (one_mul _).symm
    _ ≤ |(k : ℝ) - n| * (4 * ((k : ℝ) + n) + 2) := by
        refine mul_le_mul h1 h2 (by positivity) (le_trans (by norm_num) h1)

/-- **Uniform diagonal dominance of `specD`.**  The `G`-perturbed diagonal
keeps a gap linear in `n`, losing at most `2 |G|` to the bounded `jacB`
perturbation. -/
theorem specD_gap (G : ℝ) {k n : ℕ} (h : k ≠ n) :
    4 * (n : ℝ) + 2 - 2 * |G| ≤ |specD G k - specD G n| := by
  have hlam := specLam_gap h
  have hjac : |G * jacB k - G * jacB n| ≤ 2 * |G| := by
    calc |G * jacB k - G * jacB n| ≤ |G * jacB k| + |G * jacB n| := abs_sub _ _
      _ = |G| * |jacB k| + |G| * |jacB n| := by rw [abs_mul, abs_mul]
      _ ≤ |G| * 1 + |G| * 1 := by
          refine add_le_add ?_ ?_ <;>
            exact mul_le_mul_of_nonneg_left (jacB_abs_le_one _) (abs_nonneg G)
      _ = 2 * |G| := by ring
  have hsplit :
      specD G k - specD G n =
        (specLam k - specLam n) - (G * jacB k - G * jacB n) := by
    unfold specD; ring
  calc 4 * (n : ℝ) + 2 - 2 * |G|
      ≤ |specLam k - specLam n| - |G * jacB k - G * jacB n| := by linarith
    _ ≤ |(specLam k - specLam n) - (G * jacB k - G * jacB n)| :=
        abs_sub_abs_le_abs_sub _ _
    _ = |specD G k - specD G n| := by rw [hsplit]

/-- **The row-shifted gap.**  Any `Λ` within `C` of the `n`-th diagonal entry
stays at least `4 n + 2 − 2 |G| − C` away from every other diagonal entry.

`C` and `G` are fixed before the quantifier over `k`; the lower bound grows
linearly in `n`, which is what makes the eventual choice of a uniform
threshold `N` possible without inspecting any finite list of modes. -/
theorem specD_row_gap (G C : ℝ) {Λ : ℝ} {n : ℕ}
    (hΛ : |Λ - specD G n| ≤ C) {k : ℕ} (h : k ≠ n) :
    4 * (n : ℝ) + 2 - 2 * |G| - C ≤ |specD G k - Λ| := by
  have hgap := specD_gap G h
  have hsplit : specD G k - specD G n = (specD G k - Λ) + (Λ - specD G n) := by
    ring
  have htri : |specD G k - specD G n| ≤ |specD G k - Λ| + |Λ - specD G n| := by
    rw [hsplit]; exact abs_add_le _ _
  linarith

/-! ### The decay crosswalk: moving centre to origin -/

/-- A moving-centre geometric bound implies the origin-centred bound the
existing `Spectrum.lean` machinery consumes, with the constant `ρ ^ n`.

The constant depends on the centre — which is fixed for each candidate
eigenfunction — and on nothing else. It is **not** uniform in `n` and is never
used as if it were: `spec_summable_v`, `spec_ode` and their consumers quantify
over a fixed coefficient row at a time. -/
theorem decay_center_to_origin {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℕ) {c : ℕ → ℝ}
    (h : ∀ k, |c k| ≤ (1 / ρ) ^ Nat.dist k n) :
    ∀ k, |c k| ≤ ρ ^ n * (1 / ρ) ^ k := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le one_pos hρ
  intro k
  refine le_trans (h k) ?_
  rcases le_total n k with hnk | hkn
  · -- right of the centre: exact equality of the two bounds
    have hdist : Nat.dist k n = k - n := by
      rw [Nat.dist_comm]; exact Nat.dist_eq_sub_of_le hnk
    have hsplit : (1 / ρ) ^ k = (1 / ρ) ^ n * (1 / ρ) ^ (k - n) := by
      rw [← pow_add]; congr 1; omega
    rw [hdist, hsplit, ← mul_assoc]
    have hone : ρ ^ n * (1 / ρ) ^ n = 1 := by
      rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hρ0.ne')]
    rw [hone, one_mul]
  · -- left of the centre: the moving bound is ≤ 1 ≤ the origin bound
    have hdist : Nat.dist k n = n - k := Nat.dist_eq_sub_of_le hkn
    have hle1 : (1 / ρ) ^ (n - k) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [div_le_one hρ0]; exact hρ
    have hone : ρ ^ k * (1 / ρ) ^ k = 1 := by
      rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero k hρ0.ne')]
    have hval : ρ ^ n * (1 / ρ) ^ k = ρ ^ (n - k) := by
      have hsplit : ρ ^ n = ρ ^ (n - k) * ρ ^ k := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, mul_assoc, hone, mul_one]
    have hge1 : (1 : ℝ) ≤ ρ ^ n * (1 / ρ) ^ k := by
      rw [hval]; exact one_le_pow₀ hρ
    rw [hdist]
    exact le_trans hle1 hge1

/-! ### The fixed-point data: coefficient realization, eigenvalue pin, map -/

section FixedPoint

variable (G : ℝ) (n : ℕ)

/-- The coefficient row realized from a bounded deviation `u`: the centre is
pinned to `1`, every other slot carries the moving-centre weight. -/
noncomputable def hmC (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = n then 1 else (1 / specRho) ^ Nat.dist k n * u k

/-- The eigenvalue pinned by the `n`-th row at `c n = 1`. -/
noncomputable def hmLam (u : ℕ → ℝ) : ℝ :=
  specD G n - G * (specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1))

/-- The off-row fixed-point map, in deviation coordinates. -/
noncomputable def hmT (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = n then 0
  else specRho ^ Nat.dist k n *
    (G * (specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1)) /
      (specD G k - hmLam G n u))

@[simp] theorem hmC_center (u : ℕ → ℝ) : hmC n u n = 1 := by simp [hmC]

@[simp] theorem hmT_center (u : ℕ → ℝ) : hmT G n u n = 0 := by simp [hmT]

theorem specRho_one_le : (1 : ℝ) ≤ specRho := by unfold specRho; norm_num

theorem specRho_pos : (0 : ℝ) < specRho := by unfold specRho; norm_num

theorem hmWeight_nonneg (d : ℕ) : (0 : ℝ) ≤ (1 / specRho) ^ d := by
  unfold specRho; positivity

theorem hmWeight_le_one (d : ℕ) : (1 / specRho) ^ d ≤ 1 := by
  refine pow_le_one₀ (hmWeight_nonneg 1 |>.trans (by unfold specRho; norm_num)) ?_
  rw [div_le_one specRho_pos]; exact specRho_one_le

/-! ### Weight geometry -/

/-- Antitone weight step: if the distance can drop by at most one, the weight
can grow by at most `ρ`. -/
theorem hmWeight_step {j k : ℕ} (h : Nat.dist k n ≤ Nat.dist j n + 1) :
    (1 / specRho) ^ Nat.dist j n ≤ specRho * (1 / specRho) ^ Nat.dist k n := by
  have hρ1 := specRho_one_le
  have hρ0 := specRho_pos
  have hbase0 : (0 : ℝ) ≤ 1 / specRho := by positivity
  have hbase1 : 1 / specRho ≤ 1 := by
    rw [div_le_one hρ0]; exact hρ1
  rcases Nat.eq_zero_or_pos (Nat.dist k n) with hz | hpos
  · rw [hz, pow_zero, mul_one]
    calc (1 / specRho) ^ Nat.dist j n ≤ 1 := pow_le_one₀ hbase0 hbase1
      _ ≤ specRho := hρ1
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hjm : m ≤ Nat.dist j n := by omega
    have hmono : (1 / specRho) ^ Nat.dist j n ≤ (1 / specRho) ^ m :=
      pow_le_pow_of_le_one hbase0 hbase1 hjm
    have hval : specRho * (1 / specRho) ^ Nat.dist k n = (1 / specRho) ^ m := by
      rw [hm, pow_succ]
      field_simp
    rw [hval]
    exact hmono

theorem hmWeight_pred (k : ℕ) :
    (1 / specRho) ^ Nat.dist (k - 1) n ≤ specRho * (1 / specRho) ^ Nat.dist k n := by
  refine hmWeight_step n ?_
  have h1 : Nat.dist k (k - 1) ≤ 1 := by
    simp [Nat.dist]; omega
  calc Nat.dist k n ≤ Nat.dist k (k - 1) + Nat.dist (k - 1) n :=
        Nat.dist.triangle_inequality _ _ _
    _ ≤ Nat.dist (k - 1) n + 1 := by omega

theorem hmWeight_succ (k : ℕ) :
    (1 / specRho) ^ Nat.dist (k + 1) n ≤ specRho * (1 / specRho) ^ Nat.dist k n := by
  refine hmWeight_step n ?_
  have h1 : Nat.dist k (k + 1) = 1 := by simp [Nat.dist]
  calc Nat.dist k n ≤ Nat.dist k (k + 1) + Nat.dist (k + 1) n :=
        Nat.dist.triangle_inequality _ _ _
    _ = Nat.dist (k + 1) n + 1 := by omega

theorem dist_succ_self (m : ℕ) : Nat.dist (m + 1) m = 1 := by simp [Nat.dist]

theorem dist_pred_self {m : ℕ} (hm : 1 ≤ m) : Nat.dist (m - 1) m = 1 := by
  simp [Nat.dist]; omega

/-! ### The four estimates -/

/-- The realized coefficient never exceeds its weight, on the half-ball. -/
theorem hmC_bound {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2) (k : ℕ) :
    |hmC n u k| ≤ (1 / specRho) ^ Nat.dist k n := by
  by_cases hk : k = n
  · subst hk; simp [hmC]
  · unfold hmC
    rw [if_neg hk, abs_mul, abs_of_nonneg (hmWeight_nonneg _)]
    calc (1 / specRho) ^ Nat.dist k n * |u k|
        ≤ (1 / specRho) ^ Nat.dist k n * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (hmWeight_nonneg _)
          exact le_trans (hu k) (by norm_num)
      _ = (1 / specRho) ^ Nat.dist k n := mul_one _

/-- The Lipschitz bound on the realized coefficient. -/
theorem hmC_lipschitz {u v : ℕ → ℝ} {δ : ℝ}
    (hd : ∀ j, |u j - v j| ≤ δ) (k : ℕ) :
    |hmC n u k - hmC n v k| ≤ (1 / specRho) ^ Nat.dist k n * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hd 0)
  by_cases hk : k = n
  · subst hk
    simp only [hmC_center, sub_self, abs_zero]
    exact mul_nonneg (hmWeight_nonneg _) hδ
  · unfold hmC
    rw [if_neg hk, if_neg hk, ← mul_sub, abs_mul,
      abs_of_nonneg (hmWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hd k) (hmWeight_nonneg _)

/-- The Lipschitz bound with the weight discarded. -/
theorem hmC_lipschitz' {u v : ℕ → ℝ} {δ : ℝ}
    (hd : ∀ j, |u j - v j| ≤ δ) (k : ℕ) :
    |hmC n u k - hmC n v k| ≤ δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hd 0)
  calc |hmC n u k - hmC n v k| ≤ (1 / specRho) ^ Nat.dist k n * δ :=
        hmC_lipschitz n hd k
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right (hmWeight_le_one _) hδ
    _ = δ := one_mul _

/-- The numerator bound: the neighbour sum costs one weight step. -/
theorem hmNum_bound {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2) (k : ℕ) :
    |specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1)| ≤
      2 * specRho * (1 / specRho) ^ Nat.dist k n := by
  have h1 : |specJL k * hmC n u (k - 1)| ≤ specRho * (1 / specRho) ^ Nat.dist k n := by
    rw [abs_mul]
    calc |specJL k| * |hmC n u (k - 1)|
        ≤ 1 * ((1 / specRho) ^ Nat.dist (k - 1) n) :=
          mul_le_mul (specJL_abs_le_one k) (hmC_bound n hu (k - 1))
            (abs_nonneg _) zero_le_one
      _ = (1 / specRho) ^ Nat.dist (k - 1) n := one_mul _
      _ ≤ specRho * (1 / specRho) ^ Nat.dist k n := hmWeight_pred n k
  have h2 : |specJR k * hmC n u (k + 1)| ≤ specRho * (1 / specRho) ^ Nat.dist k n := by
    rw [abs_mul]
    calc |specJR k| * |hmC n u (k + 1)|
        ≤ 1 * ((1 / specRho) ^ Nat.dist (k + 1) n) :=
          mul_le_mul (specJR_abs_le_one k) (hmC_bound n hu (k + 1))
            (abs_nonneg _) zero_le_one
      _ = (1 / specRho) ^ Nat.dist (k + 1) n := one_mul _
      _ ≤ specRho * (1 / specRho) ^ Nat.dist k n := hmWeight_succ n k
  calc |specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1)|
      ≤ |specJL k * hmC n u (k - 1)| + |specJR k * hmC n u (k + 1)| := abs_add_le _ _
    _ ≤ specRho * (1 / specRho) ^ Nat.dist k n + specRho * (1 / specRho) ^ Nat.dist k n :=
        add_le_add h1 h2
    _ = 2 * specRho * (1 / specRho) ^ Nat.dist k n := by ring

/-- The numerator Lipschitz bound. -/
theorem hmNum_lipschitz {u v : ℕ → ℝ} {δ : ℝ}
    (hd : ∀ j, |u j - v j| ≤ δ) (k : ℕ) :
    |(specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1)) -
      (specJL k * hmC n v (k - 1) + specJR k * hmC n v (k + 1))| ≤
      2 * specRho * (1 / specRho) ^ Nat.dist k n * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hd 0)
  have h1 : |specJL k * (hmC n u (k - 1) - hmC n v (k - 1))| ≤
      specRho * (1 / specRho) ^ Nat.dist k n * δ := by
    rw [abs_mul]
    calc |specJL k| * |hmC n u (k - 1) - hmC n v (k - 1)|
        ≤ 1 * ((1 / specRho) ^ Nat.dist (k - 1) n * δ) :=
          mul_le_mul (specJL_abs_le_one k) (hmC_lipschitz n hd (k - 1))
            (abs_nonneg _) zero_le_one
      _ = (1 / specRho) ^ Nat.dist (k - 1) n * δ := one_mul _
      _ ≤ (specRho * (1 / specRho) ^ Nat.dist k n) * δ :=
          mul_le_mul_of_nonneg_right (hmWeight_pred n k) hδ
      _ = specRho * (1 / specRho) ^ Nat.dist k n * δ := by ring
  have h2 : |specJR k * (hmC n u (k + 1) - hmC n v (k + 1))| ≤
      specRho * (1 / specRho) ^ Nat.dist k n * δ := by
    rw [abs_mul]
    calc |specJR k| * |hmC n u (k + 1) - hmC n v (k + 1)|
        ≤ 1 * ((1 / specRho) ^ Nat.dist (k + 1) n * δ) :=
          mul_le_mul (specJR_abs_le_one k) (hmC_lipschitz n hd (k + 1))
            (abs_nonneg _) zero_le_one
      _ = (1 / specRho) ^ Nat.dist (k + 1) n * δ := one_mul _
      _ ≤ (specRho * (1 / specRho) ^ Nat.dist k n) * δ :=
          mul_le_mul_of_nonneg_right (hmWeight_succ n k) hδ
      _ = specRho * (1 / specRho) ^ Nat.dist k n * δ := by ring
  have hsplit :
      (specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1)) -
        (specJL k * hmC n v (k - 1) + specJR k * hmC n v (k + 1)) =
      specJL k * (hmC n u (k - 1) - hmC n v (k - 1)) +
        specJR k * (hmC n u (k + 1) - hmC n v (k + 1)) := by ring
  rw [hsplit]
  calc |specJL k * (hmC n u (k - 1) - hmC n v (k - 1)) +
        specJR k * (hmC n u (k + 1) - hmC n v (k + 1))|
      ≤ |specJL k * (hmC n u (k - 1) - hmC n v (k - 1))| +
        |specJR k * (hmC n u (k + 1) - hmC n v (k + 1))| := abs_add_le _ _
    _ ≤ specRho * (1 / specRho) ^ Nat.dist k n * δ +
        specRho * (1 / specRho) ^ Nat.dist k n * δ := add_le_add h1 h2
    _ = 2 * specRho * (1 / specRho) ^ Nat.dist k n * δ := by ring

/-- The eigenvalue pin: `hmLam` stays within `2 |G| / ρ` of the diagonal.

The neighbours of the centre carry weight `1/ρ` — except at `n = 0`, where the
left neighbour collapses onto the centre and `specJL 0 = 0` kills the term. -/
theorem hmLam_bound {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2) :
    |hmLam G n u - specD G n| ≤ 2 * |G| / specRho := by
  have hρ0 := specRho_pos
  have h2 : |specJR n * hmC n u (n + 1)| ≤ 1 / specRho := by
    rw [abs_mul]
    calc |specJR n| * |hmC n u (n + 1)|
        ≤ 1 * ((1 / specRho) ^ Nat.dist (n + 1) n) :=
          mul_le_mul (specJR_abs_le_one n) (hmC_bound n hu (n + 1))
            (abs_nonneg _) zero_le_one
      _ = (1 / specRho) ^ 1 := by rw [one_mul, dist_succ_self]
      _ = 1 / specRho := pow_one _
  have h1 : |specJL n * hmC n u (n - 1)| ≤ 1 / specRho := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [specJL_zero, zero_mul, abs_zero]
      positivity
    · rw [abs_mul]
      calc |specJL n| * |hmC n u (n - 1)|
          ≤ 1 * ((1 / specRho) ^ Nat.dist (n - 1) n) :=
            mul_le_mul (specJL_abs_le_one n) (hmC_bound n hu (n - 1))
              (abs_nonneg _) zero_le_one
        _ = (1 / specRho) ^ 1 := by rw [one_mul, dist_pred_self hpos]
        _ = 1 / specRho := pow_one _
  have hnum : |specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)| ≤
      2 / specRho := by
    calc |specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)|
        ≤ |specJL n * hmC n u (n - 1)| + |specJR n * hmC n u (n + 1)| := abs_add_le _ _
      _ ≤ 1 / specRho + 1 / specRho := add_le_add h1 h2
      _ = 2 / specRho := by ring
  unfold hmLam
  rw [show specD G n - G * (specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
      specD G n = -(G * (specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)))
    from by ring, abs_neg, abs_mul]
  calc |G| * |specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)|
      ≤ |G| * (2 / specRho) :=
        mul_le_mul_of_nonneg_left hnum (abs_nonneg G)
    _ = 2 * |G| / specRho := by ring

/-- The eigenvalue Lipschitz bound: the centre neighbours are read at weight at
most one, so the pin moves by at most `2 |G|` times the deviation distance. -/
theorem hmLam_lipschitz {u v : ℕ → ℝ} {δ : ℝ}
    (hd : ∀ j, |u j - v j| ≤ δ) :
    |hmLam G n u - hmLam G n v| ≤ 2 * |G| * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hd 0)
  have hnum : |(specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
      (specJL n * hmC n v (n - 1) + specJR n * hmC n v (n + 1))| ≤ 2 * δ := by
    have h1 : |specJL n * (hmC n u (n - 1) - hmC n v (n - 1))| ≤ δ := by
      rw [abs_mul]
      calc |specJL n| * |hmC n u (n - 1) - hmC n v (n - 1)|
          ≤ 1 * δ :=
            mul_le_mul (specJL_abs_le_one n) (hmC_lipschitz' n hd (n - 1))
              (abs_nonneg _) zero_le_one
        _ = δ := one_mul _
    have h2 : |specJR n * (hmC n u (n + 1) - hmC n v (n + 1))| ≤ δ := by
      rw [abs_mul]
      calc |specJR n| * |hmC n u (n + 1) - hmC n v (n + 1)|
          ≤ 1 * δ :=
            mul_le_mul (specJR_abs_le_one n) (hmC_lipschitz' n hd (n + 1))
              (abs_nonneg _) zero_le_one
        _ = δ := one_mul _
    have hsplit :
        (specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
          (specJL n * hmC n v (n - 1) + specJR n * hmC n v (n + 1)) =
        specJL n * (hmC n u (n - 1) - hmC n v (n - 1)) +
          specJR n * (hmC n u (n + 1) - hmC n v (n + 1)) := by ring
    rw [hsplit]
    calc |specJL n * (hmC n u (n - 1) - hmC n v (n - 1)) +
          specJR n * (hmC n u (n + 1) - hmC n v (n + 1))|
        ≤ |specJL n * (hmC n u (n - 1) - hmC n v (n - 1))| +
          |specJR n * (hmC n u (n + 1) - hmC n v (n + 1))| := abs_add_le _ _
      _ ≤ δ + δ := add_le_add h1 h2
      _ = 2 * δ := by ring
  unfold hmLam
  rw [show specD G n - G * (specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
      (specD G n - G * (specJL n * hmC n v (n - 1) + specJR n * hmC n v (n + 1))) =
      -(G * ((specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
        (specJL n * hmC n v (n - 1) + specJR n * hmC n v (n + 1))))
    from by ring, abs_neg, abs_mul]
  calc |G| * |(specJL n * hmC n u (n - 1) + specJR n * hmC n u (n + 1)) -
        (specJL n * hmC n v (n - 1) + specJR n * hmC n v (n + 1))|
      ≤ |G| * (2 * δ) := mul_le_mul_of_nonneg_left hnum (abs_nonneg G)
    _ = 2 * |G| * δ := by ring

end FixedPoint

/-! ### The remaining obligation, named exactly

The Banach fixed-point step is the first exact missing lemma:

```text
FIRST_EXACT_MISSING_LEMMA (not proved here):
  For fixed G there exist N C with 0 ≤ C such that for every n ≥ N there
  exist Λ and c : ℕ → ℝ with
    c n = 1,
    ∀ k, |c k| ≤ (1/specRho) ^ Nat.dist k n,
    ∀ k, (specD G k - Λ) * c k
           = G * (specJL k * c (k - 1) + specJR k * c (k + 1)),
    |Λ - specD G n| ≤ C.
```

Given that lemma, `decay_center_to_origin` feeds the row into `spec_ode`,
`spec_continuousOn_F`, `spec_even` and `spec_at_one` unchanged, the centre
coefficient `c n = 1` gives nonvanishing, and `specD_row_gap` is what makes
the fixed-point map a contraction in the first place.
-/

end
