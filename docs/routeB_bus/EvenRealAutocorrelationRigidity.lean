import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- Typed transform-side model for full autocorrelation on the real-even,
compactly supported source class.

`A` is deliberately an abstract commutative transform domain with no zero
divisors.  The intended analytic instance is a ring of entire transforms; the
ring of all pointwise functions is not a legal instance because it has zero
divisors. -/
structure EvenRealFullAutocorrelationModel
    (Q A : Type*) [AddCommGroup Q] [CommRing A] where
  transform : Q →+ A
  autocorrelation : Q → A
  IsRealSource : Q → Prop
  IsEvenSource : Q → Prop
  HasCompactSupport : Q → Prop
  transform_injective : Function.Injective transform
  autocorrelation_eq_square :
    ∀ q, IsRealSource q → IsEvenSource q → HasCompactSupport q →
      autocorrelation q = transform q * transform q

/-- Difference of squares in any commutative ring without zero divisors. -/
theorem eq_or_eq_neg_of_mul_self_eq_mul_self
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    {x y : A} (h : x * x = y * y) :
    x = y ∨ x = -y := by
  have hfactor : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x * x - y * y := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hplus)

/-- `SOFT_L2_EvenRealFullAutocorrelationRigidity`.

On the typed real-even compact source class, equality of full
autocorrelations becomes equality of two squares in the entire-transform
domain.  Absence of zero divisors leaves exactly the global sign ambiguity. -/
theorem evenRealFullAutocorrelationRigidity
    {Q A : Type*} [AddCommGroup Q] [CommRing A] [NoZeroDivisors A]
    (M : EvenRealFullAutocorrelationModel Q A)
    {p q : Q}
    (hpReal : M.IsRealSource p) (hpEven : M.IsEvenSource p)
    (hpCompact : M.HasCompactSupport p)
    (hqReal : M.IsRealSource q) (hqEven : M.IsEvenSource q)
    (hqCompact : M.HasCompactSupport q)
    (hA : M.autocorrelation p = M.autocorrelation q) :
    p = q ∨ p = -q := by
  have hsquare : M.transform p * M.transform p =
      M.transform q * M.transform q := by
    rw [← M.autocorrelation_eq_square p hpReal hpEven hpCompact,
      ← M.autocorrelation_eq_square q hqReal hqEven hqCompact]
    exact hA
  rcases eq_or_eq_neg_of_mul_self_eq_mul_self hsquare with hsame | hneg
  · exact Or.inl (M.transform_injective hsame)
  · right
    apply M.transform_injective
    simpa using hneg

/-- A positive real linear anchor removes the remaining global sign. -/
theorem evenRealFullAutocorrelationRigidity_of_positive_anchor
    {Q A : Type*} [AddCommGroup Q] [CommRing A] [NoZeroDivisors A]
    (M : EvenRealFullAutocorrelationModel Q A)
    (anchor : Q →+ ℝ)
    {p q : Q}
    (hpReal : M.IsRealSource p) (hpEven : M.IsEvenSource p)
    (hpCompact : M.HasCompactSupport p)
    (hqReal : M.IsRealSource q) (hqEven : M.IsEvenSource q)
    (hqCompact : M.HasCompactSupport q)
    (hpAnchor : 0 < anchor p) (hqAnchor : 0 < anchor q)
    (hA : M.autocorrelation p = M.autocorrelation q) :
    p = q := by
  rcases evenRealFullAutocorrelationRigidity M
      hpReal hpEven hpCompact hqReal hqEven hqCompact hA with hsame | hneg
  · exact hsame
  · have hanchor : anchor p = -anchor q := by
      simpa using congrArg anchor hneg
    linarith

#print axioms eq_or_eq_neg_of_mul_self_eq_mul_self
#print axioms evenRealFullAutocorrelationRigidity
#print axioms evenRealFullAutocorrelationRigidity_of_positive_anchor

end Q3.RouteB
