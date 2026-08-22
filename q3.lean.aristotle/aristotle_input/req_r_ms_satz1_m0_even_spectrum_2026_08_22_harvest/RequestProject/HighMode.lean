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
