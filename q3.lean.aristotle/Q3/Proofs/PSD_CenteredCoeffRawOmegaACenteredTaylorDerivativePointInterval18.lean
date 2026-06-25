import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
Signed point-interval assembly for order-18 centered Taylor derivative rows.

The existing `centeredTaylorDerivMajorant18` route is absolute-value based.
For the collapsed degree-0 point-slope audit we need the cheaper signed
version: keep the sign of `(x - center)^m` in the Taylor polynomial, and add
only the final symmetric Taylor remainder.

This file proves the algebraic assembly layer.  It does not provide the
analytic order-18 remainder row and it does not emit numeric point rows.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

/-- Lower endpoint for multiplying an interval by a scalar. -/
def scalarMulIntervalLower (c lower upper : Real) : Real :=
  if 0 <= c then c * lower else c * upper

/-- Upper endpoint for multiplying an interval by a scalar. -/
def scalarMulIntervalUpper (c lower upper : Real) : Real :=
  if 0 <= c then c * upper else c * lower

/-- Scalar multiplication preserves interval membership, reversing endpoints
when the scalar is negative. -/
theorem scalarMulInterval_mem
    {c x lower upper : Real}
    (h : lower <= x ∧ x <= upper) :
    scalarMulIntervalLower c lower upper <= c * x ∧
      c * x <= scalarMulIntervalUpper c lower upper := by
  by_cases hc : 0 <= c
  · constructor
    · dsimp [scalarMulIntervalLower]
      simp [hc]
      exact mul_le_mul_of_nonneg_left h.1 hc
    · dsimp [scalarMulIntervalUpper]
      simp [hc]
      exact mul_le_mul_of_nonneg_left h.2 hc
  · have hc' : c <= 0 := le_of_not_ge hc
    constructor
    · dsimp [scalarMulIntervalLower]
      simp [hc]
      exact mul_le_mul_of_nonpos_left h.2 hc'
    · dsimp [scalarMulIntervalUpper]
      simp [hc]
      exact mul_le_mul_of_nonpos_left h.1 hc'

/-- The signed coefficient multiplying the `(k + m)` normalized center jet in
the value of the `k`th derivative at `x`. -/
def centeredTaylorDerivPointCoeff18
    (center x : Real) (k : Fin 18) (m : Nat) : Real :=
  ((Nat.factorial (k.1 + m) : Real) / (Nat.factorial m : Real)) *
    (x - center) ^ m

def centeredTaylorDerivPointTermLower18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) (m : Nat) : Real :=
  if h : k.1 + m < 18 then
    scalarMulIntervalLower
      (centeredTaylorDerivPointCoeff18 center x k m)
      (jetLower ⟨k.1 + m, h⟩)
      (jetUpper ⟨k.1 + m, h⟩)
  else
    0

def centeredTaylorDerivPointTermUpper18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) (m : Nat) : Real :=
  if h : k.1 + m < 18 then
    scalarMulIntervalUpper
      (centeredTaylorDerivPointCoeff18 center x k m)
      (jetLower ⟨k.1 + m, h⟩)
      (jetUpper ⟨k.1 + m, h⟩)
  else
    0

def centeredTaylorDerivPointPolyLower18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) : Real :=
  ∑ m ∈ Finset.range (18 - k.1),
    centeredTaylorDerivPointTermLower18 jetLower jetUpper center x k m

def centeredTaylorDerivPointPolyUpper18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) : Real :=
  ∑ m ∈ Finset.range (18 - k.1),
    centeredTaylorDerivPointTermUpper18 jetLower jetUpper center x k m

def centeredTaylorDerivPointLower18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) (remainderAbs : Real) : Real :=
  centeredTaylorDerivPointPolyLower18 jetLower jetUpper center x k -
    remainderAbs

def centeredTaylorDerivPointUpper18
    (jetLower jetUpper : Fin 18 -> Real)
    (center x : Real) (k : Fin 18) (remainderAbs : Real) : Real :=
  centeredTaylorDerivPointPolyUpper18 jetLower jetUpper center x k +
    remainderAbs

theorem sum_interval_of_forall_mem
    {s : Finset Nat} {f lower upper : Nat -> Real}
    (h : ∀ m ∈ s, lower m <= f m ∧ f m <= upper m) :
    (∑ m ∈ s, lower m) <= (∑ m ∈ s, f m) ∧
      (∑ m ∈ s, f m) <= (∑ m ∈ s, upper m) := by
  constructor
  · exact Finset.sum_le_sum fun m hm => (h m hm).1
  · exact Finset.sum_le_sum fun m hm => (h m hm).2

theorem iteratedDeriv_centerJet_eq_shift18
    {f : Real -> Real} {center : Real} {k m : Nat} :
    iteratedDeriv m (iteratedDeriv k f) center /
        (Nat.factorial m : Real) =
      ((Nat.factorial (k + m) : Real) / (Nat.factorial m : Real)) *
        (iteratedDeriv (k + m) f center /
          (Nat.factorial (k + m) : Real)) := by
  have hCross :=
    congrFun (iteratedDeriv_iteratedDeriv_eq_add_comm (f := f) k m) center
  rw [hCross]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]

/--
Signed interval for the Taylor polynomial part of
`iteratedDeriv k f x`, using signed normalized center-jet intervals for `f`.
-/
theorem centerJetTaylorPolynomialN_deriv_point_interval18
    {f : Real -> Real} {center x : Real}
    {jetLower jetUpper : Fin 18 -> Real}
    (k : Fin 18)
    (hJet :
      ∀ j : Fin 18,
        jetLower j <=
            iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) ∧
          iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) <=
            jetUpper j) :
    centeredTaylorDerivPointPolyLower18 jetLower jetUpper center x k <=
        centerJetTaylorPolynomialN (18 - k.1) (iteratedDeriv k.1 f)
          center x ∧
      centerJetTaylorPolynomialN (18 - k.1) (iteratedDeriv k.1 f)
          center x <=
        centeredTaylorDerivPointPolyUpper18 jetLower jetUpper center x k := by
  unfold centeredTaylorDerivPointPolyLower18
  unfold centeredTaylorDerivPointPolyUpper18
  unfold centerJetTaylorPolynomialN
  refine sum_interval_of_forall_mem ?_
  intro m hm
  have hmLt : m < 18 - k.1 := Finset.mem_range.mp hm
  have hkm : k.1 + m < 18 := by
    omega
  have hTermInterval :=
    scalarMulInterval_mem
      (c := centeredTaylorDerivPointCoeff18 center x k m)
      (x :=
        iteratedDeriv (k.1 + m) f center /
          (Nat.factorial (k.1 + m) : Real))
      (lower := jetLower ⟨k.1 + m, hkm⟩)
      (upper := jetUpper ⟨k.1 + m, hkm⟩)
      (hJet ⟨k.1 + m, hkm⟩)
  have hEq :
      iteratedDeriv m (iteratedDeriv k.1 f) center /
          (Nat.factorial m : Real) * (x - center) ^ m =
        centeredTaylorDerivPointCoeff18 center x k m *
          (iteratedDeriv (k.1 + m) f center /
            (Nat.factorial (k.1 + m) : Real)) := by
    rw [iteratedDeriv_centerJet_eq_shift18 (f := f) (center := center)
      (k := k.1) (m := m)]
    unfold centeredTaylorDerivPointCoeff18
    ring
  constructor
  · simpa [
      centeredTaylorDerivPointTermLower18,
      centeredTaylorDerivPointCoeff18,
      hkm,
      hEq] using hTermInterval.1
  · simpa [
      centeredTaylorDerivPointTermUpper18,
      centeredTaylorDerivPointCoeff18,
      hkm,
      hEq] using hTermInterval.2

/--
Signed point interval once a Taylor-remainder bound for the same point is
available.  This is the reusable receiver for the collapsed degree-0
point-slope generator.
-/
theorem iteratedDeriv_mem_Icc_of_centerJet18_point_remainder
    {f : Real -> Real} {center x remainderAbs : Real}
    {jetLower jetUpper : Fin 18 -> Real}
    (k : Fin 18)
    (hJet :
      ∀ j : Fin 18,
        jetLower j <=
            iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) ∧
          iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) <=
            jetUpper j)
    (hRemainder :
      ‖iteratedDeriv k.1 f x -
          centerJetTaylorPolynomialN (18 - k.1) (iteratedDeriv k.1 f)
            center x‖ <=
        remainderAbs) :
    centeredTaylorDerivPointLower18 jetLower jetUpper center x k
        remainderAbs <=
        iteratedDeriv k.1 f x ∧
      iteratedDeriv k.1 f x <=
        centeredTaylorDerivPointUpper18 jetLower jetUpper center x k
          remainderAbs := by
  have hPoly :=
    centerJetTaylorPolynomialN_deriv_point_interval18
      (f := f) (center := center) (x := x)
      (jetLower := jetLower) (jetUpper := jetUpper) k hJet
  rw [Real.norm_eq_abs] at hRemainder
  have hRemBounds := abs_le.mp hRemainder
  constructor
  · unfold centeredTaylorDerivPointLower18
    linarith
  · unfold centeredTaylorDerivPointUpper18
    linarith

/-- Radius control on the right side of a center. -/
private theorem point_radius_right
    {center x y : Real} (hy : y ∈ Set.Icc center x) :
    ‖y - center‖ <= ‖x - center‖ := by
  have hyc_nonneg : 0 <= y - center := by linarith [hy.1]
  have hxc_nonneg : 0 <= x - center := by linarith [hy.1, hy.2]
  calc
    ‖y - center‖ = y - center := by
      rw [Real.norm_eq_abs, abs_of_nonneg hyc_nonneg]
    _ <= x - center := by
      linarith [hy.2]
    _ = ‖x - center‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hxc_nonneg]

/-- Radius control on the left side of a center. -/
private theorem point_radius_left
    {center x y : Real} (hy : y ∈ Set.Icc x center) :
    ‖y - center‖ <= ‖x - center‖ := by
  have hyc_nonpos : y - center <= 0 := by linarith [hy.2]
  have hxc_nonpos : x - center <= 0 := by linarith [hy.1, hy.2]
  calc
    ‖y - center‖ = -(y - center) := by
      rw [Real.norm_eq_abs, abs_of_nonpos hyc_nonpos]
    _ <= -(x - center) := by
      linarith [hy.1]
    _ = ‖x - center‖ := by
      rw [Real.norm_eq_abs, abs_of_nonpos hxc_nonpos]

/--
Signed point interval from proof-grade center jets and an order-18 bound on the
segment between the center and the point.

This is the generator-facing route selected for the collapsed degree-0
point-slope audit: signs are preserved in the Taylor polynomial, while the
only symmetric loss is the order-18 remainder on `Set.uIcc center x`.
-/
theorem iteratedDeriv_mem_Icc_of_centerJet18_point
    {f : Real -> Real} {center x order18Abs : Real}
    {jetLower jetUpper : Fin 18 -> Real}
    (k : Fin 18)
    (hSmooth : ContDiff Real 18 f)
    (hJet :
      ∀ j : Fin 18,
        jetLower j <=
            iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) ∧
          iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) <=
            jetUpper j)
    (hOrder18 :
      ∀ y ∈ Set.uIcc center x, ‖iteratedDeriv 18 f y‖ <= order18Abs) :
    centeredTaylorDerivPointLower18 jetLower jetUpper center x k
        (order18Abs * ‖x - center‖ ^ (18 - k.1) /
          (Nat.factorial (18 - k.1) : Real)) <=
        iteratedDeriv k.1 f x ∧
      iteratedDeriv k.1 f x <=
        centeredTaylorDerivPointUpper18 jetLower jetUpper center x k
          (order18Abs * ‖x - center‖ ^ (18 - k.1) /
            (Nat.factorial (18 - k.1) : Real)) := by
  have hklt : k.1 < 18 := k.2
  have hn_pos : 0 < 18 - k.1 := Nat.sub_pos_of_lt hklt
  have hkn : k.1 + (18 - k.1) = 18 :=
    Nat.add_sub_of_le (Nat.le_of_lt hklt)
  by_cases hcx : center <= x
  · have hCenterMem : center ∈ Set.Icc center x := ⟨le_rfl, hcx⟩
    have hxMem : x ∈ Set.Icc center x := ⟨hcx, le_rfl⟩
    have hOrder :
        ∀ y ∈ Set.Icc center x, ‖iteratedDeriv 18 f y‖ <= order18Abs := by
      intro y hy
      exact hOrder18 y (by
        simpa [Set.uIcc, min_eq_left hcx, max_eq_right hcx] using hy)
    have hRadius :
        ∀ y ∈ Set.Icc center x, ‖y - center‖ <= ‖x - center‖ := by
      intro y hy
      exact point_radius_right hy
    have hRemainder :=
      iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right18
        (f := f) (a := center) (b := x) (center := center)
        (radius := ‖x - center‖) (order18Abs := order18Abs)
        (eta := x) (k := k.1) (n := 18 - k.1)
        hn_pos hkn hCenterMem hSmooth hOrder hRadius hxMem hcx
    exact
      iteratedDeriv_mem_Icc_of_centerJet18_point_remainder
        (f := f) (center := center) (x := x)
        (remainderAbs :=
          order18Abs * ‖x - center‖ ^ (18 - k.1) /
            (Nat.factorial (18 - k.1) : Real))
        (jetLower := jetLower) (jetUpper := jetUpper)
        k hJet hRemainder
  · have hxc : x <= center := le_of_not_ge hcx
    have hOrder :
        ∀ y ∈ Set.Icc x center, ‖iteratedDeriv 18 f y‖ <= order18Abs := by
      intro y hy
      exact hOrder18 y (by
        simpa [Set.uIcc, min_eq_right hxc, max_eq_left hxc] using hy)
    have hRadius :
        ∀ y ∈ Set.Icc x center, ‖y - center‖ <= ‖x - center‖ := by
      intro y hy
      exact point_radius_left hy
    have hReflect :
        ∀ y ∈ Set.Icc center (2 * center - x),
          2 * center - y ∈ Set.Icc x center := by
      intro y hy
      constructor <;> linarith [hy.1, hy.2]
    have hRemainder :=
      iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left18
        (f := f) (a := x) (b := center) (center := center)
        (radius := ‖x - center‖) (order18Abs := order18Abs)
        (eta := x) (k := k.1) (n := 18 - k.1)
        hn_pos hkn hSmooth hOrder hRadius hxc hReflect
    exact
      iteratedDeriv_mem_Icc_of_centerJet18_point_remainder
        (f := f) (center := center) (x := x)
        (remainderAbs :=
          order18Abs * ‖x - center‖ ^ (18 - k.1) /
            (Nat.factorial (18 - k.1) : Real))
        (jetLower := jetLower) (jetUpper := jetUpper)
        k hJet hRemainder

end Step33
end PSDpd
end Q3
