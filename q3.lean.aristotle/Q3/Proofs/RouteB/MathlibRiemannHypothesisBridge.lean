import Q3.Basic.Defs

/-!
# Bridge: project `Q3.RH` ⟷ Mathlib `RiemannHypothesis`

The project states RH on the open critical strip (`Q3.RH`, `Q3/Basic/Defs.lean`):
every zero of `riemannZeta` with `0 < Re s < 1` has `Re s = 1/2`.  Mathlib's
`RiemannHypothesis` (the Formal Conjectures / Clay reference statement) quantifies
over every zero that is neither trivial (`s = -2(n+1)`) nor the junk point `s = 1`.
The two statements are equivalent; the two classical inputs are

* `riemannZeta_ne_zero_of_one_le_re` (no zeros on `Re s ≥ 1`), and
* the functional equation `riemannZeta_one_sub`, which shows that every zero with
  `Re s ≤ 0` is a trivial zero (`riemannZeta_eq_zero_re_nonpos_trivial` below).

This file is the consumer-side bridge for a Comparator challenge whose trusted
statement is Mathlib's `RiemannHypothesis`.
-/

open Complex Real

namespace Q3

/-- A zero of `riemannZeta` with `Re s ≤ 0` is a trivial zero `s = -2(n+1)`. -/
theorem riemannZeta_eq_zero_re_nonpos_trivial {s : ℂ} (hs : s.re ≤ 0)
    (hz : riemannZeta s = 0) : ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  set t : ℂ := 1 - s with ht
  have htre : 1 ≤ t.re := by
    simp only [ht, sub_re, one_re]
    linarith
  have ht_ne : ∀ n : ℕ, t ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht1 : t ≠ 1 := by
    intro h
    apply hs0
    have : (1 : ℂ) - s = 1 := h
    linear_combination -this
  have hfe := riemannZeta_one_sub ht_ne ht1
  have h1t : (1 : ℂ) - t = s := by simp [ht]
  rw [h1t, hz] at hfe
  have hζ : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
  have hΓ : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero ht_ne
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (2 * (π : ℂ)) ^ (-t) ≠ 0 := by
    intro h
    obtain ⟨h2, -⟩ := (cpow_eq_zero_iff _ _).mp h
    exact absurd h2 (mul_ne_zero two_ne_zero hpi)
  have hprod := hfe.symm
  simp only [mul_eq_zero, hζ, hΓ, or_false, false_or, two_ne_zero] at hprod
  rcases hprod with hp | hcos
  · exact absurd hp hpow
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have htk : t = 2 * k + 1 := by
    have h2 : (π : ℂ) * t = (π : ℂ) * (2 * k + 1) := by linear_combination 2 * hk
    exact mul_left_cancel₀ hpi h2
  have hkre : (1 : ℝ) ≤ 2 * k + 1 := by
    have := htre
    rw [htk] at this
    simpa using this
  have hk0 : 0 ≤ k := by
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk1 : 1 ≤ k := by
    rcases lt_or_eq_of_le hk0 with h | h
    · omega
    · exfalso
      apply ht1
      rw [htk, ← h]
      simp
  refine ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    have : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hcast, ← h1t, htk]
  ring

/-- The project definition of RH is equivalent to Mathlib's `RiemannHypothesis`. -/
theorem rh_iff_mathlib : Q3.RH ↔ RiemannHypothesis := by
  constructor
  · intro h
    unfold RiemannHypothesis
    intro s hz htriv hs1
    rcases lt_or_ge 0 s.re with hpos | hnonpos
    · rcases lt_or_ge s.re 1 with hlt1 | hge1
      · exact h s hz hpos hlt1
      · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
    · exact absurd (riemannZeta_eq_zero_re_nonpos_trivial hnonpos hz) htriv
  · intro h
    unfold Q3.RH
    intro s hz h0 h1
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp at h0
      linarith
    · rintro rfl
      simp at h1

/-- Mathlib's `RiemannHypothesis` follows from the project statement. -/
theorem riemannHypothesis_of_rh (h : Q3.RH) : RiemannHypothesis := rh_iff_mathlib.mp h

end Q3

#print axioms Q3.rh_iff_mathlib
