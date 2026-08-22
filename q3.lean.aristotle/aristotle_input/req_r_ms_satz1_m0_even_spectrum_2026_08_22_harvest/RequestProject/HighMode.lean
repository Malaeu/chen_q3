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
open scoped NNReal

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

theorem hmTail_summable : Summable (fun j : ℕ => (1 / specRho : ℝ) ^ (j + 1)) := by
  have hB0 : (0 : ℝ) ≤ 1 / specRho := by unfold specRho; positivity
  have hB1 : (1 / specRho : ℝ) < 1 := by unfold specRho; norm_num
  exact ((summable_geometric_of_lt_one hB0 hB1).mul_left (1 / specRho)).congr
    (fun j => by rw [pow_succ]; ring)

theorem hmTail_tsum : (∑' j : ℕ, (1 / specRho : ℝ) ^ (j + 1)) = 1 / 999 := by
  have hB0 : (0 : ℝ) ≤ 1 / specRho := by unfold specRho; positivity
  have hB1 : (1 / specRho : ℝ) < 1 := by unfold specRho; norm_num
  have hcongr : (∑' j : ℕ, (1 / specRho : ℝ) ^ (j + 1)) =
      ∑' j : ℕ, (1 / specRho : ℝ) * (1 / specRho) ^ j :=
    tsum_congr (fun j => by rw [pow_succ]; ring)
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one hB0 hB1]
  unfold specRho
  norm_num

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

/-! ### The contraction gates

Everything below runs under the explicit threshold

`hn : 8 * (|G| + 1) * specRho ≤ 4 * n + 2 - 4 * |G|`,

a single real inequality in `G` and `n`. For each fixed `G` it holds for all
large `n`, and no constant below is chosen after inspecting any finite list of
modes. -/

/-- Under the threshold, the shifted denominator keeps the full budget. -/
theorem hmGap {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|)
    {k : ℕ} (hk : k ≠ n) :
    8 * (|G| + 1) * specRho ≤ |specD G k - hmLam G n u| := by
  have hρ1 := specRho_one_le
  have hpin : |hmLam G n u - specD G n| ≤ 2 * |G| := by
    calc |hmLam G n u - specD G n| ≤ 2 * |G| / specRho := hmLam_bound G n hu
      _ ≤ 2 * |G| := by
          refine div_le_self (by positivity) hρ1
  have hrow := specD_row_gap G (2 * |G|) hpin hk
  linarith

/-- The denominator is nonzero and positive in absolute value. -/
theorem hmGap_pos {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|)
    {k : ℕ} (hk : k ≠ n) :
    0 < |specD G k - hmLam G n u| := by
  have hρ0 := specRho_pos
  have h := hmGap G n hu hn hk
  nlinarith [abs_nonneg G]

/-- The weights cancel exactly. -/
theorem hmWeight_cancel (d : ℕ) : specRho ^ d * (1 / specRho) ^ d = 1 := by
  rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ specRho_pos.ne')]
theorem hmWeight_cancel_comm (d : ℕ) : (1 / specRho) ^ d * specRho ^ d = 1 := by
  rw [mul_comm]; exact hmWeight_cancel d

/-- **Self-map.**  On the half-ball, under the threshold, the map lands in the
quarter-ball. -/
theorem hmT_selfmap {u : ℕ → ℝ} (hu : ∀ j, |u j| ≤ 1 / 2)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|) (k : ℕ) :
    |hmT G n u k| ≤ 1 / 4 := by
  by_cases hk : k = n
  · subst hk; simp
  · have hρ0 := specRho_pos
    have hρ1 := specRho_one_le
    set d := Nat.dist k n with hd
    set den := specD G k - hmLam G n u with hden
    set num := specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1) with hnum
    have hgap : 8 * (|G| + 1) * specRho ≤ |den| := hmGap G n hu hn hk
    have hdenpos : 0 < |den| := hmGap_pos G n hu hn hk
    have hnumb : |num| ≤ 2 * specRho * (1 / specRho) ^ d := hmNum_bound n hu k
    have hT : hmT G n u k = specRho ^ d * (G * num / den) := by
      unfold hmT; rw [if_neg hk]
    rw [hT, abs_mul, abs_div, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ specRho ^ d)]
    rw [mul_div_assoc', div_le_iff₀ hdenpos]
    have hlhs : specRho ^ d * (|G| * |num|) ≤ 2 * |G| * specRho := by
      calc specRho ^ d * (|G| * |num|)
          ≤ specRho ^ d * (|G| * (2 * specRho * (1 / specRho) ^ d)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hnumb (abs_nonneg G)
        _ = (specRho ^ d * (1 / specRho) ^ d) * (2 * |G| * specRho) := by ring
        _ = 2 * |G| * specRho := by rw [hmWeight_cancel]; ring
    have hrhs : 2 * |G| * specRho ≤ 1 / 4 * |den| := by
      calc 2 * |G| * specRho ≤ 1 / 4 * (8 * (|G| + 1) * specRho) := by nlinarith
        _ ≤ 1 / 4 * |den| := by linarith
    linarith

/-- **Contraction.**  Two deviations in the half-ball map to points at most
half their distance apart, under the threshold. -/
theorem hmT_contraction {u v : ℕ → ℝ} {δ : ℝ}
    (hu : ∀ j, |u j| ≤ 1 / 2) (hv : ∀ j, |v j| ≤ 1 / 2)
    (hd : ∀ j, |u j - v j| ≤ δ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|) (k : ℕ) :
    |hmT G n u k - hmT G n v k| ≤ 1 / 2 * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hd 0)
  by_cases hk : k = n
  · subst hk; simp; linarith
  · have hρ0 := specRho_pos
    have hρ1 := specRho_one_le
    set d := Nat.dist k n with hdd
    set du := specD G k - hmLam G n u with hdu
    set dv := specD G k - hmLam G n v with hdv
    set nu := specJL k * hmC n u (k - 1) + specJR k * hmC n u (k + 1) with hnu
    set nv := specJL k * hmC n v (k - 1) + specJR k * hmC n v (k + 1) with hnv
    have hgapu : 8 * (|G| + 1) * specRho ≤ |du| := hmGap G n hu hn hk
    have hgapv : 8 * (|G| + 1) * specRho ≤ |dv| := hmGap G n hv hn hk
    have hdupos : 0 < |du| := hmGap_pos G n hu hn hk
    have hdvpos : 0 < |dv| := hmGap_pos G n hv hn hk
    have hdune : du ≠ 0 := fun h => by simp [h] at hdupos
    have hdvne : dv ≠ 0 := fun h => by simp [h] at hdvpos
    have hnumd : |nu - nv| ≤ 2 * specRho * (1 / specRho) ^ d * δ :=
      hmNum_lipschitz n hd k
    have hnvb : |nv| ≤ 2 * specRho * (1 / specRho) ^ d := hmNum_bound n hv k
    have hlam : |hmLam G n u - hmLam G n v| ≤ 2 * |G| * δ :=
      hmLam_lipschitz G n hd
    have hTu : hmT G n u k = specRho ^ d * (G * nu / du) := by
      unfold hmT; rw [if_neg hk]
    have hTv : hmT G n v k = specRho ^ d * (G * nv / dv) := by
      unfold hmT; rw [if_neg hk]
    -- the two-term split: numerator difference over du, plus the pin shift
    have hsplit :
        specRho ^ d * (G * nu / du) - specRho ^ d * (G * nv / dv) =
          specRho ^ d * G * ((nu - nv) / du) +
            specRho ^ d * G * (nv * (hmLam G n u - hmLam G n v) / (du * dv)) := by
      have hswap : hmLam G n u - hmLam G n v = dv - du := by
        rw [hdu, hdv]; ring
      rw [hswap]
      field_simp
      ring
    rw [hTu, hTv, hsplit]
    have hterm1 : |specRho ^ d * G * ((nu - nv) / du)| ≤ 1 / 4 * δ := by
      rw [abs_mul, abs_mul, abs_div,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ specRho ^ d)]
      rw [mul_div_assoc', div_le_iff₀ hdupos]
      have hlhs : specRho ^ d * |G| * |nu - nv| ≤ 2 * |G| * specRho * δ := by
        calc specRho ^ d * |G| * |nu - nv|
            ≤ specRho ^ d * |G| * (2 * specRho * (1 / specRho) ^ d * δ) := by
              refine mul_le_mul_of_nonneg_left hnumd (by positivity)
          _ = (specRho ^ d * (1 / specRho) ^ d) * (2 * |G| * specRho * δ) := by
              ring
          _ = 2 * |G| * specRho * δ := by rw [hmWeight_cancel]; ring
      have hrhs : 2 * |G| * specRho * δ ≤ 1 / 4 * δ * |du| := by
        calc 2 * |G| * specRho * δ
            ≤ 1 / 4 * δ * (8 * (|G| + 1) * specRho) := by nlinarith
          _ ≤ 1 / 4 * δ * |du| := by nlinarith
      linarith
    have hterm2 :
        |specRho ^ d * G * (nv * (hmLam G n u - hmLam G n v) / (du * dv))| ≤
          1 / 4 * δ := by
      rw [abs_mul, abs_mul, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ specRho ^ d)]
      have hdupr : 0 < |du| * |dv| := mul_pos hdupos hdvpos
      rw [mul_div_assoc', div_le_iff₀ hdupr]
      have hlhs : specRho ^ d * |G| * (|nv| * |hmLam G n u - hmLam G n v|) ≤
          4 * |G| ^ 2 * specRho * δ := by
        calc specRho ^ d * |G| * (|nv| * |hmLam G n u - hmLam G n v|)
            ≤ specRho ^ d * |G| *
              ((2 * specRho * (1 / specRho) ^ d) * (2 * |G| * δ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul hnvb hlam (abs_nonneg _) (by positivity)
          _ = (specRho ^ d * (1 / specRho) ^ d) * (4 * |G| ^ 2 * specRho * δ) := by
              ring
          _ = 4 * |G| ^ 2 * specRho * δ := by rw [hmWeight_cancel]; ring
      have hgap2 : (8 * (|G| + 1) * specRho) * (8 * (|G| + 1) * specRho) ≤
          |du| * |dv| := by
        have h8 : (0 : ℝ) ≤ 8 * (|G| + 1) * specRho := by positivity
        exact mul_le_mul hgapu hgapv h8 (abs_nonneg _)
      have hrhs : 4 * |G| ^ 2 * specRho * δ ≤ 1 / 4 * δ * (|du| * |dv|) := by
        have hbig : 4 * |G| ^ 2 * specRho ≤
            1 / 4 * ((8 * (|G| + 1) * specRho) * (8 * (|G| + 1) * specRho)) := by
          have hg0 : (0 : ℝ) ≤ |G| := abs_nonneg G
          have e1 : 4 * |G| ^ 2 * specRho ≤ 4 * (|G| + 1) ^ 2 * specRho := by
            nlinarith [specRho_pos]
          have e3 : 4 * (|G| + 1) ^ 2 * specRho ≤
              16 * (|G| + 1) ^ 2 * specRho ^ 2 := by
            nlinarith [specRho_one_le, specRho_pos, sq_nonneg (|G| + 1)]
          have hexp : 1 / 4 * ((8 * (|G| + 1) * specRho) * (8 * (|G| + 1) * specRho)) =
              16 * (|G| + 1) ^ 2 * specRho ^ 2 := by ring
          linarith
        have h1 := mul_le_mul_of_nonneg_right hbig hδ
        have h2 := mul_le_mul_of_nonneg_right hgap2 hδ
        linarith
      linarith
    calc |specRho ^ d * G * ((nu - nv) / du) +
          specRho ^ d * G * (nv * (hmLam G n u - hmLam G n v) / (du * dv))|
        ≤ |specRho ^ d * G * ((nu - nv) / du)| +
          |specRho ^ d * G * (nv * (hmLam G n u - hmLam G n v) / (du * dv))| :=
          abs_add_le _ _
      _ ≤ 1 / 4 * δ + 1 / 4 * δ := add_le_add hterm1 hterm2
      _ = 1 / 2 * δ := by ring

/-! ### The Banach assembly

The half-ball of bounded deviations is a complete metric space, the map lands
back in it and contracts with constant one half, so it has a fixed point. The
fixed point realizes the row equations exactly. -/

/-- The half-ball of deviations as a set of bounded functions. -/
def hmBall : Set (BoundedContinuousFunction ℕ ℝ) :=
  Metric.closedBall 0 (1 / 2)

theorem hmBall_pointwise {w : BoundedContinuousFunction ℕ ℝ}
    (hw : w ∈ hmBall) (j : ℕ) : |w j| ≤ 1 / 2 := by
  have hnorm : ‖w‖ ≤ 1 / 2 := by
    have := Metric.mem_closedBall.mp hw
    rwa [dist_zero_right] at this
  calc |w j| = ‖w j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖w‖ := BoundedContinuousFunction.norm_coe_le_norm w j
    _ ≤ 1 / 2 := hnorm

/-- The map, packaged on the half-ball. -/
noncomputable def hmPhi (G : ℝ) (n : ℕ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|)
    (w : hmBall) : hmBall := by
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => hmT G n (⇑(w : BoundedContinuousFunction ℕ ℝ)) k) (1 / 4) ?_, ?_⟩
  · intro k
    rw [Real.norm_eq_abs]
    exact hmT_selfmap G n (hmBall_pointwise w.2) hn k
  · show _ ∈ Metric.closedBall (0 : BoundedContinuousFunction ℕ ℝ) (1 / 2)
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans ((BoundedContinuousFunction.norm_le (by norm_num)).mpr ?_)
      (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    intro k
    rw [BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
      Real.norm_eq_abs]
    exact hmT_selfmap G n (hmBall_pointwise w.2) hn k

theorem hmPhi_apply (G : ℝ) (n : ℕ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|)
    (w : hmBall) (k : ℕ) :
    ((hmPhi G n hn w : BoundedContinuousFunction ℕ ℝ)) k =
      hmT G n (⇑(w : BoundedContinuousFunction ℕ ℝ)) k := rfl

/-- The packaged map contracts with constant one half. -/
theorem hmPhi_contracting (G : ℝ) (n : ℕ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|) :
    ContractingWith (1 / 2 : ℝ≥0) (hmPhi G n hn) := by
  constructor
  · rw [← NNReal.coe_lt_coe]; norm_num
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    rw [Subtype.dist_eq]
    have hδ : (0 : ℝ) ≤ dist (u : BoundedContinuousFunction ℕ ℝ) v := dist_nonneg
    refine (BoundedContinuousFunction.dist_le (by positivity)).mpr ?_
    intro k
    rw [hmPhi_apply, hmPhi_apply, Real.dist_eq]
    have hd : ∀ j,
        |(u : BoundedContinuousFunction ℕ ℝ) j -
          (v : BoundedContinuousFunction ℕ ℝ) j| ≤
        dist (u : BoundedContinuousFunction ℕ ℝ) v := by
      intro j
      rw [← Real.dist_eq]
      exact BoundedContinuousFunction.dist_coe_le_dist j
    have hcontr := hmT_contraction G n (hmBall_pointwise u.2)
      (hmBall_pointwise v.2) hd hn k
    calc |hmT G n (⇑(u : BoundedContinuousFunction ℕ ℝ)) k -
          hmT G n (⇑(v : BoundedContinuousFunction ℕ ℝ)) k|
        ≤ 1 / 2 * dist (u : BoundedContinuousFunction ℕ ℝ) v := hcontr
      _ = (1 / 2 : ℝ≥0) * dist (u : BoundedContinuousFunction ℕ ℝ) v := by
          norm_num

/-- **The row witness.**  Under the threshold, the fixed point of the map
realizes a coefficient row with unit centre, moving-centre decay, the exact
Jacobi row equations, and the eigenvalue pinned to the diagonal within
`2 |G| / ρ`. -/
theorem hm_exists_row (G : ℝ) (n : ℕ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|) :
    ∃ (Λ : ℝ) (c : ℕ → ℝ),
      c n = 1 ∧
      (∀ k, |c k| ≤ (1 / specRho) ^ Nat.dist k n) ∧
      (∀ k, (specD G k - Λ) * c k =
        G * (specJL k * c (k - 1) + specJR k * c (k + 1))) ∧
      |Λ - specD G n| ≤ 2 * |G| / specRho := by
  haveI hcl : IsClosed hmBall := Metric.isClosed_closedBall
  haveI : Nonempty hmBall := by
    refine ⟨⟨0, ?_⟩⟩
    show _ ∈ Metric.closedBall (0 : BoundedContinuousFunction ℕ ℝ) (1 / 2)
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  set y := ContractingWith.fixedPoint (hmPhi G n hn) (hmPhi_contracting G n hn)
    with hy_def
  have hy : hmPhi G n hn y = y :=
    ContractingWith.fixedPoint_isFixedPt (hmPhi_contracting G n hn)
  set w : ℕ → ℝ := ⇑(y : BoundedContinuousFunction ℕ ℝ) with hw
  have hu : ∀ j, |w j| ≤ 1 / 2 := hmBall_pointwise y.2
  have hfix : ∀ k, hmT G n w k = w k := by
    intro k
    have hcoe : (hmPhi G n hn y : BoundedContinuousFunction ℕ ℝ) =
        (y : BoundedContinuousFunction ℕ ℝ) := congrArg Subtype.val hy
    calc hmT G n w k =
        (hmPhi G n hn y : BoundedContinuousFunction ℕ ℝ) k := rfl
      _ = (y : BoundedContinuousFunction ℕ ℝ) k := DFunLike.congr_fun hcoe k
  refine ⟨hmLam G n w, hmC n w, hmC_center n w, hmC_bound n hu, ?_,
    hmLam_bound G n hu⟩
  intro k
  by_cases hk : k = n
  · subst hk
    rw [hmC_center]
    unfold hmLam
    ring
  · have hden : specD G k - hmLam G n w ≠ 0 := by
      have hpos := hmGap_pos G n hu hn hk
      intro h
      rw [h, abs_zero] at hpos
      exact lt_irrefl 0 hpos
    have hfk := hfix k
    unfold hmT at hfk
    rw [if_neg hk] at hfk
    have hck : hmC n w k =
        G * (specJL k * hmC n w (k - 1) + specJR k * hmC n w (k + 1)) /
          (specD G k - hmLam G n w) := by
      conv_lhs => unfold hmC
      rw [if_neg hk, ← hfk, ← mul_assoc, hmWeight_cancel_comm, one_mul]
    rw [hck]
    field_simp

end FixedPoint

/-! ### From the row to a regular even eigenvalue -/

section Pipeline

variable {c : ℕ → ℝ}

/-- Endpoint flux at the right end: the derivative series is continuous up to
the closed endpoint, the degenerate factor vanishes there. -/
theorem spec_flux_right {A : ℝ} (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) :
    Filter.Tendsto (fun x : ℝ => (1 - x ^ 2) * specF1 c x)
      (nhdsWithin 1 (Iio 1)) (nhds 0) := by
  have hmem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hF1 : Filter.Tendsto (specF1 c) (nhdsWithin 1 (Ioo (-1 : ℝ) 1))
      (nhds (specF1 c 1)) :=
    ((spec_continuousOn_F1 hdecay 1 hmem).mono Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (-1 : ℝ) < 1)] at hF1
  have hfac : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) (nhdsWithin 1 (Iio 1))
      (nhds 0) := by
    have hcont : Continuous fun x : ℝ => 1 - x ^ 2 := by fun_prop
    have h0 : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) (nhds 1) (nhds 0) :=
      hcont.tendsto' 1 0 (by norm_num)
    exact h0.mono_left nhdsWithin_le_nhds
  have := hfac.mul hF1
  simpa using this

/-- Endpoint flux at the left end. -/
theorem spec_flux_left {A : ℝ} (hdecay : ∀ k, |c k| ≤ A * (1 / specRho) ^ k) :
    Filter.Tendsto (fun x : ℝ => (1 - x ^ 2) * specF1 c x)
      (nhdsWithin (-1) (Ioi (-1))) (nhds 0) := by
  have hmem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hF1 : Filter.Tendsto (specF1 c) (nhdsWithin (-1) (Ioo (-1 : ℝ) 1))
      (nhds (specF1 c (-1))) :=
    ((spec_continuousOn_F1 hdecay (-1) hmem).mono Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (-1 : ℝ) < 1)] at hF1
  have hfac : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) (nhdsWithin (-1) (Ioi (-1)))
      (nhds 0) := by
    have hcont : Continuous fun x : ℝ => 1 - x ^ 2 := by fun_prop
    have h0 : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) (nhds (-1)) (nhds 0) :=
      hcont.tendsto' (-1) 0 (by norm_num)
    exact h0.mono_left nhdsWithin_le_nhds
  have := hfac.mul hF1
  simpa using this

end Pipeline

/-- The centre value: a moving-centre row with unit centre sums to at least
`1 − 2/999` at the right endpoint, hence is nonzero there. -/
theorem hm_specF_one_ne_zero (n : ℕ) {c : ℕ → ℝ}
    (hc1 : c n = 1)
    (hdec : ∀ k, |c k| ≤ (1 / specRho) ^ Nat.dist k n) :
    specF c 1 ≠ 0 := by
  have hρ1 := specRho_one_le
  have hρ0 := specRho_pos
  have hdec0 : ∀ k, |c k| ≤ specRho ^ n * (1 / specRho) ^ k :=
    decay_center_to_origin hρ1 n hdec
  -- the deviation series and the majorant
  set e : ℕ → ℝ := fun k => if k = n then 0 else c k with he
  set w : ℕ → ℝ := fun k => if k = n then 0 else (1 / specRho) ^ Nat.dist k n
    with hwdef
  have hB0 : (0 : ℝ) ≤ 1 / specRho := by positivity
  have hB1 : 1 / specRho < 1 := by unfold specRho; norm_num
  have hebound : ∀ k, |e k| ≤ specRho ^ n * (1 / specRho) ^ k := by
    intro k
    by_cases hk : k = n
    · simp only [he, hk, if_pos rfl, abs_zero]
      positivity
    · simp only [he, if_neg hk]
      exact hdec0 k
  have hwbound : ∀ k, |w k| ≤ specRho ^ n * (1 / specRho) ^ k := by
    intro k
    by_cases hk : k = n
    · simp only [hwdef, hk, if_pos rfl, abs_zero]
      positivity
    · simp only [hwdef, if_neg hk, abs_of_nonneg (hmWeight_nonneg _)]
      exact le_trans (le_abs_self _)
        (decay_center_to_origin hρ1 n
          (c := fun j => (1 / specRho) ^ Nat.dist j n)
          (fun j => le_of_eq (abs_of_nonneg (hmWeight_nonneg _))) k)
  have hesum : Summable e := spec_summable_of_bound hB0 hB1 hebound
  have hwsum : Summable w := spec_summable_of_bound hB0 hB1 hwbound
  have hcsum : Summable c := spec_summable_of_bound hB0 hB1 hdec0
  -- split off the centre
  have hsplitfun : c = fun k => (if k = n then (1 : ℝ) else 0) + e k := by
    funext k
    by_cases hk : k = n
    · subst hk; simp [he, hc1]
    · simp [he, hk]
  have hsingle : Summable (fun k => if k = n then (1 : ℝ) else 0) :=
    (hasSum_ite_eq n (1 : ℝ)).summable
  have htsum_c : (∑' k, c k) = 1 + ∑' k, e k := by
    conv_lhs => rw [hsplitfun]
    rw [hsingle.tsum_add hesum, tsum_ite_eq]
  -- the tail bound: |∑ e| ≤ ∑ w ≤ 2/999
  have habs_le : |∑' k, e k| ≤ ∑' k, w k := by
    have h1 : |∑' k, e k| ≤ ∑' k, |e k| := by
      have := norm_tsum_le_tsum_norm (f := e) (by
        simpa [Real.norm_eq_abs] using hesum.abs)
      simpa [Real.norm_eq_abs] using this
    refine le_trans h1 (hesum.abs.tsum_le_tsum ?_ hwsum)
    intro k
    by_cases hk : k = n
    · simp [he, hwdef, hk]
    · simp only [he, hwdef, if_neg hk]
      exact hdec k
  have hwtail : (∑' k, w k) ≤ 2 / 999 := by
    -- split at n + 1
    have hsplit := (hwsum.sum_add_tsum_nat_add (n + 1)).symm
    have hfin : (∑ i ∈ Finset.range (n + 1), w i) ≤ 1 / 999 := by
      rw [Finset.sum_range_succ]
      have hwn : w n = 0 := by simp [hwdef]
      rw [hwn, add_zero]
      have hval : ∀ i ∈ Finset.range n, w i = (1 / specRho) ^ (n - i) := by
        intro i hi
        have hin : i ≠ n := by
          have := Finset.mem_range.mp hi; omega
        have hdist : Nat.dist i n = n - i := by
          have := Finset.mem_range.mp hi
          exact Nat.dist_eq_sub_of_le (by omega)
        simp [hwdef, hin, hdist]
      rw [Finset.sum_congr rfl hval]
      have hreflect :
          (∑ i ∈ Finset.range n, (1 / specRho) ^ (n - i)) =
            ∑ j ∈ Finset.range n, (1 / specRho) ^ (j + 1) := by
        have := Finset.sum_range_reflect
          (fun j => (1 / specRho : ℝ) ^ (j + 1)) n
        calc (∑ i ∈ Finset.range n, (1 / specRho) ^ (n - i))
            = ∑ i ∈ Finset.range n, (1 / specRho) ^ (n - 1 - i + 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have := Finset.mem_range.mp hi
              congr 1
              omega
          _ = ∑ j ∈ Finset.range n, (1 / specRho) ^ (j + 1) := this
      rw [hreflect]
      have hle := Summable.sum_le_tsum (Finset.range n)
        (fun j _ => hmWeight_nonneg (j + 1)) hmTail_summable
      rw [hmTail_tsum] at hle
      exact hle
    have htail : (∑' i : ℕ, w (i + (n + 1))) ≤ 1 / 999 := by
      have hval : ∀ i : ℕ, w (i + (n + 1)) = (1 / specRho) ^ (i + 1) := by
        intro i
        have hin : i + (n + 1) ≠ n := by omega
        have hdist : Nat.dist (i + (n + 1)) n = i + 1 := by
          rw [Nat.dist_comm]
          have : Nat.dist n (i + (n + 1)) = i + n + 1 - n := by
            exact Nat.dist_eq_sub_of_le (by omega)
          omega
        simp [hwdef, hin, hdist]
      rw [tsum_congr hval, hmTail_tsum]
    linarith [hsplit, hfin, htail]
  -- assemble
  have hone : specF c 1 = 1 + ∑' k, e k := by
    rw [spec_at_one, htsum_c]
  intro hzero
  rw [hone] at hzero
  have : |∑' k, e k| ≥ 1 := by
    have : (∑' k, e k) = -1 := by linarith
    rw [this]; norm_num
  linarith [habs_le, hwtail]

/-- **The witness, membership form.**  Under the threshold, the pinned
eigenvalue is a regular even spheroidal eigenvalue. -/
theorem hm_regularEven (G : ℝ) (n : ℕ)
    (hn : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G|) :
    ∃ Λ : ℝ, RegularEvenSpheroidalEigenvalue G Λ ∧
      |Λ - specD G n| ≤ 2 * |G| / specRho := by
  obtain ⟨Λ, c, hc1, hdec, hrows, hpin⟩ := hm_exists_row G n hn
  have hdec0 : ∀ k, |c k| ≤ specRho ^ n * (1 / specRho) ^ k :=
    decay_center_to_origin specRho_one_le n hdec
  refine ⟨Λ, ⟨specF c, specF1 c, specF2 c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpin⟩
  · exact ⟨1, by norm_num, hm_specF_one_ne_zero n hc1 hdec⟩
  · exact fun x => spec_even x
  · exact spec_continuousOn_F hdec0
  · exact fun x hx => ⟨spec_hasDerivAt_F hdec0 hx, spec_hasDerivAt_F1 hdec0 hx⟩
  · exact fun x hx => spec_ode hdec0 hrows hx
  · exact spec_flux_right hdec0
  · exact spec_flux_left hdec0

/-- **The final theorem in the verdict's N-form.**  For every parameter there
are a threshold and a constant, the constant outside the quantifier over the
mode, such that every large mode carries a regular even eigenvalue within the
constant of the Jacobi diagonal. -/
theorem spheroidal_highMode_eigenvalue_near_specD (G : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, N ≤ n →
        ∃ Λ : ℝ, RegularEvenSpheroidalEigenvalue G Λ ∧
          |Λ - specD G n| ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((8 * (|G| + 1) * specRho + 4 * |G| - 2) / 4)
  refine ⟨N, 2 * |G| / specRho,
    div_nonneg (by positivity) specRho_pos.le, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hmul := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hN
  have hthr : 8 * (|G| + 1) * specRho ≤ 4 * (n : ℝ) + 2 - 4 * |G| := by
    linarith
  exact hm_regularEven G n hthr

/-- **Infinitude, closed.**  The regular even spectrum is infinite: the
high-mode witnesses are unbounded above, and a finite set of reals is not. -/
theorem spheroidal_spectrum_infinite_of_highMode (G : ℝ) :
    {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨N, C, hC0, hwit⟩ := spheroidal_highMode_eigenvalue_near_specD G
  obtain ⟨M, hM⟩ := exists_nat_ge (b + C + |G| + 1)
  set n := max N M with hn_def
  have hnN : N ≤ n := le_max_left _ _
  have hnM : (M : ℝ) ≤ n := Nat.cast_le.mpr (le_max_right _ _)
  obtain ⟨Λ, hmem, hclose⟩ := hwit n hnN
  have hΛb : Λ ≤ b := hb hmem
  have hlam_lb : (n : ℝ) ≤ specLam n := by
    unfold specLam
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hjac : G * jacB n ≤ |G| := by
    calc G * jacB n ≤ |G * jacB n| := le_abs_self _
      _ = |G| * |jacB n| := abs_mul _ _
      _ ≤ |G| * 1 := mul_le_mul_of_nonneg_left (jacB_abs_le_one n) (abs_nonneg G)
      _ = |G| := mul_one _
  have hD_lb : (n : ℝ) - |G| ≤ specD G n := by
    unfold specD
    linarith
  have hΛ_lb : specD G n - C ≤ Λ := by
    have := abs_le.mp hclose
    linarith [this.1]
  linarith

/-! ### What stands, and what was the missing lemma

The obligation stated in earlier slices as the first exact missing lemma —
the Banach fixed point producing the row — is discharged by `hm_exists_row`,
and the full pipeline to `RegularEvenSpheroidalEigenvalue` is closed by
`hm_regularEven`. The verdict's N-form target is
`spheroidal_highMode_eigenvalue_near_specD`, and
`spheroidal_spectrum_infinite_of_highMode` closes, in this quarantined module
and without touching `Main.lean`, the statement whose `sorry` ended the paid
run.
-/

end
