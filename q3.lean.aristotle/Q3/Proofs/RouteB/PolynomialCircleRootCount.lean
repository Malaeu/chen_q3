import Mathlib

/-!
# Polynomial circle argument principle

Judge verdict
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md`
(§Q4, `POLYNOMIAL_CIRCLE_ARGUMENT_PRINCIPLE`, candidate re-representation
`R2_POLYNOMIAL_CIRCLE_ROOT_COUNT`) states that a **circle-only** argument
principle for polynomials is derivable in the pinned Mathlib without first
formalizing a general winding number. This file carries that derivation out.

For `p : ℂ[X]` with `p ≠ 0` and no root on the circle `|z - c| = r` (`r > 0`):

  `∮ z in C(c, r), (derivative p).eval z / p.eval z
      = 2 π i * #{a ∈ p.roots | dist a c < r}`,

the roots being counted with multiplicity, since `p.roots` is a multiset.

The ingredients are exactly the ones named by the judge:

* `Polynomial.Splits.eval_eq_prod_roots` (over `ℂ` every polynomial splits,
  `IsAlgClosed.splits`) — the factorization into linear factors;
* `logDeriv_const_mul` and `logDeriv_mul` — the logarithmic derivative of the
  product of linear factors (the judge named `logDeriv_prod`, the `Finset`
  version; the root *multiset* is handled here by `Multiset.induction_on`
  through `logDeriv_mul`, which is what `logDeriv_prod` itself is built from);
* `circleIntegral.integral_sub_inv_of_mem_ball` — `∮ (z - a)⁻¹ = 2πi` for
  `a` inside the ball;
* `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` — the
  vanishing for `a` outside the closed ball;
* linearity of `circleIntegral` over the finite sum
  (`circleIntegral.integral_add` plus `CircleIntegrable`).

This is the `LEANABLE_WITH_NEW_LOCAL_THEOREM` layer only. It is *not* a
rectangle argument principle and *not* a Rouché theorem: the verdict classifies
those as `NEW_ANALYTIC`, and nothing here is used on `centeredXi`.
-/

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB
namespace PolynomialCircleRootCount

open Metric Polynomial

/-! ### The product of linear factors -/

/-- The product `∏_{a ∈ t} (z - a)` over a multiset of nodes is entire. -/
theorem differentiable_linear_prod (t : Multiset ℂ) :
    Differentiable ℂ fun z : ℂ => (t.map (fun a => z - a)).prod := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (differentiable_id.sub_const a).mul ih

/-- The product of linear factors is nonzero away from the nodes. -/
theorem linear_prod_ne_zero {t : Multiset ℂ} {z : ℂ} (h : ∀ a ∈ t, z - a ≠ 0) :
    (t.map (fun a => z - a)).prod ≠ 0 := by
  refine Multiset.prod_ne_zero ?_
  intro hmem
  obtain ⟨a, ha, hza⟩ := Multiset.mem_map.mp hmem
  exact h a ha hza

/-- **Logarithmic derivative of a product of linear factors.**
Away from the nodes, `(∏ (z - a))'/∏ (z - a) = ∑ (z - a)⁻¹`. -/
theorem logDeriv_linear_prod :
    ∀ (t : Multiset ℂ) (z : ℂ), (∀ a ∈ t, z - a ≠ 0) →
      logDeriv (fun w : ℂ => (t.map (fun a => w - a)).prod) z
        = (t.map (fun a => (z - a)⁻¹)).sum := by
  intro t
  induction t using Multiset.induction_on with
  | empty =>
      intro z _
      simp [logDeriv]
  | cons a t ih =>
      intro z hz
      have hza : z - a ≠ 0 := hz a (Multiset.mem_cons_self a t)
      have hzt : ∀ b ∈ t, z - b ≠ 0 := fun b hb => hz b (Multiset.mem_cons_of_mem hb)
      have hprod : (t.map (fun b => z - b)).prod ≠ 0 := linear_prod_ne_zero hzt
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - a) z := differentiableAt_id.sub_const a
      have hd2 : DifferentiableAt ℂ (fun w : ℂ => (t.map (fun b => w - b)).prod) z :=
        differentiable_linear_prod t z
      have hkey : logDeriv (fun w : ℂ => (w - a) * (t.map (fun b => w - b)).prod) z
          = logDeriv (fun w : ℂ => w - a) z
            + logDeriv (fun w : ℂ => (t.map (fun b => w - b)).prod) z :=
        logDeriv_mul z hza hprod hd1 hd2
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [hkey, ih z hzt]
      congr 1
      rw [logDeriv_apply]
      simp

/-- **Logarithmic derivative of a polynomial.** Over `ℂ`, away from the roots,
`p'/p` is the sum of `(z - a)⁻¹` over the root multiset. -/
theorem logDeriv_polynomial_eq_sum {p : Polynomial ℂ} (hp : p ≠ 0) {z : ℂ}
    (hz : p.eval z ≠ 0) :
    (Polynomial.derivative p).eval z / p.eval z
      = (p.roots.map (fun a => (z - a)⁻¹)).sum := by
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots : ∀ a ∈ p.roots, z - a ≠ 0 := by
    intro a ha hza
    have hza' : z = a := sub_eq_zero.mp hza
    rw [hza'] at hz
    exact hz (Polynomial.isRoot_of_mem_roots ha)
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hfun : (fun w : ℂ => p.eval w)
      = fun w : ℂ => p.leadingCoeff * (p.roots.map (fun a => w - a)).prod := by
    funext w
    exact hsplits.eval_eq_prod_roots w
  have h1 : logDeriv (fun w : ℂ => p.eval w) z
      = (Polynomial.derivative p).eval z / p.eval z := by
    rw [logDeriv_apply, Polynomial.deriv]
  rw [← h1, hfun, logDeriv_const_mul z p.leadingCoeff hlc,
    logDeriv_linear_prod p.roots z hroots]

/-! ### The circle integral of a single simple pole -/

/-- For a node outside the closed disk the Cauchy–Goursat theorem gives `0`. -/
theorem circleIntegral_inv_sub_of_outside {c a : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : r < dist a c) : (∮ z in C(c, r), (z - a)⁻¹) = 0 := by
  have hne : ∀ z ∈ closedBall c r, z - a ≠ 0 := by
    intro z hz h
    have hza : z = a := sub_eq_zero.mp h
    rw [hza] at hz
    exact absurd (Metric.mem_closedBall.mp hz) (not_le.mpr ha)
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty ?_ ?_
  · exact ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn hne
  · intro z hz
    exact (differentiableAt_id.sub_const a).inv
      (hne z (Metric.ball_subset_closedBall hz.1))

/-! ### Integrability and linearity over the root multiset -/

/-- A finite sum of simple poles off the circle is circle integrable. -/
theorem circleIntegrable_inv_sum (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∀ t : Multiset ℂ, (∀ a ∈ t, a ∉ sphere c r) →
      CircleIntegrable (fun z : ℂ => (t.map (fun a => (z - a)⁻¹)).sum) c r := by
  intro t
  induction t using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | cons a t ih =>
      intro ht
      have hza : a ∉ sphere c |r| := by
        rw [abs_of_pos hr]
        exact ht a (Multiset.mem_cons_self a t)
      have h1 : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) c r :=
        circleIntegrable_sub_inv_iff.mpr (Or.inr hza)
      have h2 : CircleIntegrable (fun z : ℂ => (t.map (fun b => (z - b)⁻¹)).sum) c r :=
        ih fun b hb => ht b (Multiset.mem_cons_of_mem hb)
      simpa only [Multiset.map_cons, Multiset.sum_cons] using h1.add h2

/-- **Circle integral of a finite sum of simple poles.** Each node inside the
ball contributes `2πi`, each node outside the closed ball contributes `0`. -/
theorem circleIntegral_inv_sum (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∀ t : Multiset ℂ, (∀ a ∈ t, a ∉ sphere c r) →
      (∮ z in C(c, r), (t.map (fun a => (z - a)⁻¹)).sum)
        = 2 * (Real.pi : ℂ) * Complex.I *
            ((t.filter (fun a => dist a c < r)).card : ℂ) := by
  intro t
  induction t using Multiset.induction_on with
  | empty =>
      intro _
      simp [circleIntegral]
  | cons a t ih =>
      intro ht
      have hasph : a ∉ sphere c r := ht a (Multiset.mem_cons_self a t)
      have htt : ∀ b ∈ t, b ∉ sphere c r := fun b hb => ht b (Multiset.mem_cons_of_mem hb)
      have h1 : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) c r :=
        circleIntegrable_sub_inv_iff.mpr (Or.inr (by rwa [abs_of_pos hr]))
      have h2 : CircleIntegrable (fun z : ℂ => (t.map (fun b => (z - b)⁻¹)).sum) c r :=
        circleIntegrable_inv_sum c r hr t htt
      have hsplit : (∮ z in C(c, r), ((a ::ₘ t).map (fun b => (z - b)⁻¹)).sum)
          = (∮ z in C(c, r), (z - a)⁻¹)
            + ∮ z in C(c, r), (t.map (fun b => (z - b)⁻¹)).sum := by
        simp only [Multiset.map_cons, Multiset.sum_cons]
        exact circleIntegral.integral_add h1 h2
      rw [hsplit, ih htt]
      by_cases hball : dist a c < r
      · have hmem : a ∈ ball c r := Metric.mem_ball.mpr hball
        rw [circleIntegral.integral_sub_inv_of_mem_ball hmem,
          Multiset.filter_cons_of_pos (p := fun x : ℂ => dist x c < r) t hball,
          Multiset.card_cons]
        push_cast
        ring
      · have hout : r < dist a c := by
          rcases lt_trichotomy (dist a c) r with h | h | h
          · exact absurd h hball
          · exact absurd (Metric.mem_sphere.mpr h) hasph
          · exact h
        rw [circleIntegral_inv_sub_of_outside hr hout,
          Multiset.filter_cons_of_neg (p := fun x : ℂ => dist x c < r) t hball]
        ring

/-! ### The circle argument principle for polynomials -/

/-- **Polynomial circle argument principle.**

Let `p : ℂ[X]` be nonzero, `c : ℂ`, `r > 0`, and suppose `p` has no zero on the
circle `|z - c| = r`. Then

  `∮ z in C(c, r), p'(z)/p(z) = 2 π i * #{a ∈ p.roots : dist a c < r}`,

the roots counted with multiplicity (`p.roots` is a multiset).

No general winding number and no rectangle theory is used. -/
theorem circleIntegral_logDeriv_eq_root_count {p : Polynomial ℂ} (hp : p ≠ 0) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hcirc : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), (Polynomial.derivative p).eval z / p.eval z)
      = 2 * (Real.pi : ℂ) * Complex.I *
          ((p.roots.filter (fun a => dist a c < r)).card : ℂ) := by
  have hEq : (∮ z in C(c, r), (Polynomial.derivative p).eval z / p.eval z)
      = ∮ z in C(c, r), (p.roots.map (fun a => (z - a)⁻¹)).sum := by
    refine circleIntegral.integral_congr hr.le ?_
    intro z hz
    exact logDeriv_polynomial_eq_sum hp (hcirc z hz)
  rw [hEq]
  refine circleIntegral_inv_sum c r hr p.roots ?_
  intro a ha hsph
  exact hcirc a hsph (Polynomial.isRoot_of_mem_roots ha)

/-- Corollary: a polynomial with no root in the closed disk has vanishing
`p'/p` circle integral. -/
theorem circleIntegral_logDeriv_eq_zero_of_no_root {p : Polynomial ℂ} (hp : p ≠ 0) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hno : ∀ a ∈ p.roots, r < dist a c) :
    (∮ z in C(c, r), (Polynomial.derivative p).eval z / p.eval z) = 0 := by
  have hcirc : ∀ z ∈ sphere c r, p.eval z ≠ 0 := by
    intro z hz hval
    have hmem : z ∈ p.roots := (Polynomial.mem_roots' ).mpr ⟨hp, hval⟩
    have := hno z hmem
    rw [Metric.mem_sphere.mp hz] at this
    exact lt_irrefl r this
  rw [circleIntegral_logDeriv_eq_root_count hp hr hcirc]
  have hfilter : p.roots.filter (fun a => dist a c < r) = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    exact not_lt.mpr (hno a ha).le
  rw [hfilter]
  simp

/-! ### Kernel audit -/

#print axioms logDeriv_linear_prod
#print axioms logDeriv_polynomial_eq_sum
#print axioms circleIntegral_inv_sub_of_outside
#print axioms circleIntegral_inv_sum
#print axioms circleIntegral_logDeriv_eq_root_count
#print axioms circleIntegral_logDeriv_eq_zero_of_no_root

end PolynomialCircleRootCount
end Q3.RouteB

end
