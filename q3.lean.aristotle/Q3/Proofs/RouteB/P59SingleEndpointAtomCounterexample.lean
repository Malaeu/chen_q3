import Mathlib

/-!
# P59 single-endpoint atom — the kill plant

Judge verdict
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md`
(§Q1, `ENDPOINT_KILL_PLANT`) kills the *single-endpoint atom*: the claim that a
small relative error at the one real endpoint `R`,

  `e(R) = ‖F R - X R‖ / ‖X R‖ < 1`,

certifies equal zero counts of `F` and `X` inside the thin rectangle
`[-R, R] × [-h, h]`.

This file formalizes the explicit plant. Fix `R > 0` and `0 < a < R`, put
`b = √(R² - a²)` and

  `X z = 1`,   `F z = (1 - z²/a²) * (1 - z²/b²)`.

Then

* `F 0 = X 0 = 1` (anchor agreement),
* `F R = X R = 1`, hence `e(R) = 0 < 1` (endpoint agreement),
* `F` has the four distinct real zeros `±a, ±b`, all of absolute value `< R`,
  so all inside the rectangle for *every* height `h > 0`,
* `X` has no zeros at all.

Both functions are even, real on `ℝ`, real-rooted and normalized at the anchor,
so the plant lies inside the claimed class. The zero counts differ by four:
endpoint agreement does not control the zero count.

The refutation is packaged twice:

* `single_endpoint_atom_counterexample` — the existential exhibiting the plant;
* `endpoint_agreement_does_not_control_zero_count` — the negation of the
  implication the atom asserted.

Scope discipline of the verdict's `CODEX DIRECTIVE`: no general Rouché theorem,
no argument principle, no `centeredXi`, no numerics, no new axioms.

Success code: `P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_KERNEL_GREEN`.
-/

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB
namespace P59SingleEndpointAtom

/-- The plant `F z = (1 - z²/a²)(1 - z²/b²)`: even, real-rooted,
normalized at the anchor `0`, of exponential type zero. -/
def plant (a b : ℝ) : ℂ → ℂ :=
  fun z => (1 - z ^ 2 / (a : ℂ) ^ 2) * (1 - z ^ 2 / (b : ℂ) ^ 2)

/-- The target `X ≡ 1`: entire, zero-free, normalized at the anchor `0`. -/
def target : ℂ → ℂ := fun _ => 1

/-! ### Elementary properties of the two functions -/

@[simp] theorem target_apply (z : ℂ) : target z = 1 := rfl

theorem target_ne_zero (z : ℂ) : target z ≠ 0 := one_ne_zero

/-- The target has no zeros whatsoever. -/
theorem target_no_zeros : ∀ z : ℂ, target z ≠ 0 := fun z => target_ne_zero z

theorem plant_even (a b : ℝ) (z : ℂ) : plant a b (-z) = plant a b z := by
  simp only [plant]
  ring

/-- Anchor agreement: `F 0 = 1 = X 0`. -/
@[simp] theorem plant_zero (a b : ℝ) : plant a b 0 = 1 := by
  simp [plant]

theorem plant_anchor_eq_target (a b : ℝ) : plant a b 0 = target 0 := by
  simp

/-- `a` is a zero of the plant. -/
theorem plant_at_a {a : ℝ} (b : ℝ) (ha : a ≠ 0) : plant a b (a : ℂ) = 0 := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp [plant, div_self (pow_ne_zero 2 ha')]

/-- `b` is a zero of the plant. -/
theorem plant_at_b (a : ℝ) {b : ℝ} (hb : b ≠ 0) : plant a b (b : ℂ) = 0 := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  simp [plant, div_self (pow_ne_zero 2 hb')]

/-- `-a` is a zero of the plant. -/
theorem plant_at_neg_a {a : ℝ} (b : ℝ) (ha : a ≠ 0) : plant a b ((-a : ℝ) : ℂ) = 0 := by
  have h : ((-a : ℝ) : ℂ) = -((a : ℝ) : ℂ) := by push_cast; ring
  rw [h, plant_even, plant_at_a b ha]

/-- `-b` is a zero of the plant. -/
theorem plant_at_neg_b (a : ℝ) {b : ℝ} (hb : b ≠ 0) : plant a b ((-b : ℝ) : ℂ) = 0 := by
  have h : ((-b : ℝ) : ℂ) = -((b : ℝ) : ℂ) := by push_cast; ring
  rw [h, plant_even, plant_at_b a hb]

/-- **Endpoint agreement.** Whenever `a² + b² = R²`, the two factors of the
plant are reciprocal at `R`, so `F R = 1 = X R`. -/
theorem plant_at_endpoint {R a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 + b ^ 2 = R ^ 2) : plant a b (R : ℂ) = 1 := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have h : ((R : ℝ) : ℂ) ^ 2 = ((a : ℝ) : ℂ) ^ 2 + ((b : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hab.symm
  have ha2 : ((a : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 ha'
  have hb2 : ((b : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hb'
  simp only [plant, h]
  field_simp
  ring

/-- The endpoint error of the plant vanishes: `e(R) = 0`. -/
theorem plant_endpoint_error_eq_zero {R a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 + b ^ 2 = R ^ 2) :
    ‖plant a b (R : ℂ) - target (R : ℂ)‖ / ‖target (R : ℂ)‖ = 0 := by
  simp [plant_at_endpoint ha hb hab]

/-! ### The parameter `b = √(R² - a²)` of the verdict -/

/-- For `0 < a < R` the verdict's choice `b = √(R² - a²)` is positive, smaller
than `R`, and satisfies the Pythagorean relation `a² + b² = R²`. -/
theorem sqrt_leg_spec {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (haR : a < R) :
    0 < Real.sqrt (R ^ 2 - a ^ 2) ∧ Real.sqrt (R ^ 2 - a ^ 2) < R ∧
      a ^ 2 + Real.sqrt (R ^ 2 - a ^ 2) ^ 2 = R ^ 2 := by
  have hpos : 0 < R ^ 2 - a ^ 2 := by nlinarith
  have hsq : Real.sqrt (R ^ 2 - a ^ 2) ^ 2 = R ^ 2 - a ^ 2 := Real.sq_sqrt hpos.le
  have hb : 0 < Real.sqrt (R ^ 2 - a ^ 2) := Real.sqrt_pos.mpr hpos
  refine ⟨hb, ?_, by linarith⟩
  nlinarith

/-- For the concrete `3-4-5` choice the verdict's square root is explicit. -/
theorem sqrt_leg_pythagorean {R : ℝ} (hR : 0 < R) :
    Real.sqrt (R ^ 2 - (3 * R / 5) ^ 2) = 4 * R / 5 := by
  have h : R ^ 2 - (3 * R / 5) ^ 2 = (4 * R / 5) ^ 2 := by ring
  rw [h, Real.sqrt_sq (by linarith)]

/-! ### Four distinct real roots inside the rectangle -/

theorem card_four_roots {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ({a, -a, b, -b} : Finset ℝ).card = 4 := by
  have h1 : a ∉ ({-a, b, -b} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨by intro h; linarith, hab, by intro h; linarith⟩
  have h2 : (-a) ∉ ({b, -b} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨by intro h; linarith, by intro h; exact hab (by linarith)⟩
  have h3 : b ∉ ({-b} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    intro h; linarith
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- A real point of absolute value `< R` lies in the open thin rectangle
`(-R, R) × (-h, h)` for every height `h > 0`. -/
theorem real_mem_thin_rectangle {R h x : ℝ} (hx : |x| < R) (hh : 0 < h) :
    ((x : ℂ)).re ∈ Set.Ioo (-R) R ∧ ((x : ℂ)).im ∈ Set.Ioo (-h) h := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  refine ⟨?_, ?_⟩
  · simpa using ⟨h1, h2⟩
  · simp only [Complex.ofReal_im, Set.mem_Ioo]
    exact ⟨by linarith, hh⟩

/-! ### The counterexample -/

/-- **P59 single-endpoint atom counterexample.**

For every `R > 0` there are an approximant `F` and a target `X`, both entire,
even and real on `ℝ`, such that

* `F` and `X` agree at the anchor `0`;
* `F` and `X` agree at the real endpoint `R`, so the endpoint error
  `e(R) = ‖F R - X R‖ / ‖X R‖` is `0`, in particular `< 1`;
* `X` is zero-free;
* `F` has four distinct real zeros of absolute value `< R`, hence four zeros
  inside the thin rectangle `(-R, R) × (-h, h)` for every `h > 0`.

The zero counts therefore differ by four although the endpoint error vanishes:
the single-endpoint atom is not a rectangle count certificate. -/
theorem single_endpoint_atom_counterexample {R : ℝ} (hR : 0 < R) :
    ∃ (F X : ℂ → ℂ) (S : Finset ℝ),
      F 0 = X 0 ∧
      F (R : ℂ) = X (R : ℂ) ∧
      ‖F (R : ℂ) - X (R : ℂ)‖ / ‖X (R : ℂ)‖ = 0 ∧
      (∀ z : ℂ, X z ≠ 0) ∧
      4 ≤ S.card ∧
      (∀ x ∈ S, F (x : ℂ) = 0 ∧ |x| < R) := by
  have ha : (0 : ℝ) < 3 * R / 5 := by linarith
  have hb : (0 : ℝ) < 4 * R / 5 := by linarith
  have hab : (3 * R / 5 : ℝ) ≠ 4 * R / 5 := by intro h; linarith
  have hpyth : (3 * R / 5 : ℝ) ^ 2 + (4 * R / 5 : ℝ) ^ 2 = R ^ 2 := by ring
  refine ⟨plant (3 * R / 5) (4 * R / 5), target,
    ({3 * R / 5, -(3 * R / 5), 4 * R / 5, -(4 * R / 5)} : Finset ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [plant_at_endpoint ha.ne' hb.ne' hpyth]
  · exact plant_endpoint_error_eq_zero ha.ne' hb.ne' hpyth
  · exact target_no_zeros
  · exact le_of_eq (card_four_roots ha hb hab).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨plant_at_a _ ha.ne', ?_⟩
      rw [abs_of_pos ha]
      linarith
    · refine ⟨plant_at_neg_a _ ha.ne', ?_⟩
      rw [abs_neg, abs_of_pos ha]
      linarith
    · refine ⟨plant_at_b _ hb.ne', ?_⟩
      rw [abs_of_pos hb]
      linarith
    · refine ⟨plant_at_neg_b _ hb.ne', ?_⟩
      rw [abs_neg, abs_of_pos hb]
      linarith

/-- **The implication the atom asserted is false.**

There is no theorem deducing "the approximant is zero-free where the target is
zero-free" — a fortiori no equality of zero counts inside the rectangle — from
anchor agreement plus endpoint agreement at `R`. -/
theorem endpoint_agreement_does_not_control_zero_count {R : ℝ} (hR : 0 < R) :
    ¬ ∀ F X : ℂ → ℂ,
        F 0 = X 0 →
        F (R : ℂ) = X (R : ℂ) →
        (∀ z : ℂ, X z ≠ 0) →
        ∀ x : ℝ, |x| < R → F (x : ℂ) ≠ 0 := by
  intro hcontra
  obtain ⟨F, X, S, h0, hR', _he, hX, hcard, hroots⟩ := single_endpoint_atom_counterexample hR
  obtain ⟨x, hxS⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hcard)
  obtain ⟨hFx, hxR⟩ := hroots x hxS
  exact hcontra F X h0 hR' hX x hxR hFx

/-! ### Kernel audit -/

#print axioms plant_at_endpoint
#print axioms plant_endpoint_error_eq_zero
#print axioms sqrt_leg_spec
#print axioms card_four_roots
#print axioms single_endpoint_atom_counterexample
#print axioms endpoint_agreement_does_not_control_zero_count

end P59SingleEndpointAtom
end Q3.RouteB

end
