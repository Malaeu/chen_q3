import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 300000

/-!
Order-18 derivative Taylor-model bridge for the Step33A.1-A local-factor route.

This file is a generic receiver only.  It does not contain generated rows and
does not close the direct signed segment0 source.  Its purpose is to turn
center-jet coefficient enclosures for a factor into a polynomial model and a
single derivative remainder bound before any Leibniz interval widening.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

/-- Polynomial model for the `k`th derivative built from normalized center
jets of the original function through order `17`. -/
def centeredTaylorDerivPolynomial18
    (coeff : Fin 18 -> Real) (k : Fin 18) (center eta : Real) : Real :=
  ∑ m ∈ Finset.range (18 - k.1),
    if h : k.1 + m < 18 then
      ((Nat.factorial (k.1 + m) : Real) / (Nat.factorial m : Real)) *
        coeff ⟨k.1 + m, h⟩ * (eta - center) ^ m
    else
      0

/-- Error budget for `centeredTaylorDerivPolynomial18`: coefficient errors
transported through the derivative polynomial plus the order-18 Taylor
remainder. -/
def centeredTaylorDerivError18
    (coeffErrorAbs : Fin 18 -> Real) (order18Abs radius : Real)
    (k : Fin 18) : Real :=
  (∑ m ∈ Finset.range (18 - k.1),
    if h : k.1 + m < 18 then
      ((Nat.factorial (k.1 + m) : Real) / (Nat.factorial m : Real)) *
        coeffErrorAbs ⟨k.1 + m, h⟩ * radius ^ m
    else
      0) +
    order18Abs * radius ^ (18 - k.1) /
      (Nat.factorial (18 - k.1) : Real)

/-- Absolute bound for a derivative Taylor polynomial from coefficient
absolute-value bounds and a radius bound. -/
theorem centeredTaylorDerivPolynomial18_abs_bound
    {coeff coeffAbs : Fin 18 -> Real} {center eta radius : Real}
    (k : Fin 18)
    (hCoeffAbsNonneg : ∀ j : Fin 18, 0 <= coeffAbs j)
    (hCoeffAbs : ∀ j : Fin 18, ‖coeff j‖ <= coeffAbs j)
    (hRadius : ‖eta - center‖ <= radius) :
    ‖centeredTaylorDerivPolynomial18 coeff k center eta‖ <=
      ∑ m ∈ Finset.range (18 - k.1),
        if h : k.1 + m < 18 then
          ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeffAbs ⟨k.1 + m, h⟩ * radius ^ m
        else
          0 := by
  unfold centeredTaylorDerivPolynomial18
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro m hm
  by_cases hkm : k.1 + m < 18
  · have hcoef_nonneg :
        0 <= (Nat.factorial (k.1 + m) : Real) /
          (Nat.factorial m : Real) := by
      positivity
    have hradius_nonneg : 0 <= radius :=
      (norm_nonneg _).trans hRadius
    have hpow_le : ‖(eta - center) ^ m‖ <= radius ^ m := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hRadius m
    have hright_nonneg :
        0 <= ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeffAbs ⟨k.1 + m, hkm⟩ := by
      exact mul_nonneg hcoef_nonneg (hCoeffAbsNonneg ⟨k.1 + m, hkm⟩)
    calc
      ‖if h : k.1 + m < 18 then
          ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeff ⟨k.1 + m, h⟩ * (eta - center) ^ m
        else
          0‖
          =
          ‖((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeff ⟨k.1 + m, hkm⟩ * (eta - center) ^ m‖ := by
            simp [hkm]
      _ =
          ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            ‖coeff ⟨k.1 + m, hkm⟩‖ * ‖(eta - center) ^ m‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs,
              abs_of_nonneg hcoef_nonneg]
      _ <=
          ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeffAbs ⟨k.1 + m, hkm⟩ * radius ^ m := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left
                (hCoeffAbs ⟨k.1 + m, hkm⟩) hcoef_nonneg)
              hpow_le
              (norm_nonneg _)
              hright_nonneg
      _ =
          if h : k.1 + m < 18 then
            ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              coeffAbs ⟨k.1 + m, h⟩ * radius ^ m
          else
            0 := by
            simp [hkm]
  · simp [hkm]

private theorem abs_sub_center_le_of_mem_center_radius
    {center radius eta : Real}
    (heta : eta ∈ Set.Icc (center - radius) (center + radius)) :
    ‖eta - center‖ <= radius := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [heta.1], by linarith [heta.2]⟩

/--
The Taylor polynomial assembled from approximate normalized center jets models
`iteratedDeriv k f` on a symmetric radius cell, with the explicit coefficient
and order-18 error budget.

This is the generic bridge needed before a generator can assemble the signed
Leibniz polynomial for the whole Step33A.1-A segment0 expression.
-/
theorem iteratedDeriv_sub_centeredTaylorDerivPolynomial18_norm_le
    {f : Real -> Real} {center radius order18Abs eta : Real}
    {coeff coeffErrorAbs : Fin 18 -> Real}
    (k : Fin 18)
    (hradius : 0 <= radius)
    (hSmooth : ContDiff Real 18 f)
    (hCoeffErrorNonneg : ∀ j : Fin 18, 0 <= coeffErrorAbs j)
    (hJet :
      ∀ j : Fin 18,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real) -
          coeff j‖ <= coeffErrorAbs j)
    (hOrder18 :
      ∀ x ∈ Set.Icc (center - radius) (center + radius),
        ‖iteratedDeriv 18 f x‖ <= order18Abs)
    (heta : eta ∈ Set.Icc (center - radius) (center + radius)) :
    ‖iteratedDeriv k.1 f eta -
        centeredTaylorDerivPolynomial18 coeff k center eta‖ <=
      centeredTaylorDerivError18 coeffErrorAbs order18Abs radius k := by
  let n : Nat := 18 - k.1
  let taylorPoly : Real :=
    centerJetTaylorPolynomialN n (iteratedDeriv k.1 f) center eta
  have hklt : k.1 < 18 := k.2
  have hn_pos : 0 < n := by
    dsimp [n]
    exact Nat.sub_pos_of_lt hklt
  have hkn : k.1 + n = 18 := by
    dsimp [n]
    exact Nat.add_sub_of_le (Nat.le_of_lt hklt)
  have hCenterMem :
      center ∈ Set.Icc (center - radius) (center + radius) := by
    constructor <;> linarith
  have hRadiusCell :
    ∀ x ∈ Set.Icc (center - radius) (center + radius),
        ‖x - center‖ <= radius := by
    intro x hx
    exact abs_sub_center_le_of_mem_center_radius hx
  have hReflectCell :
      ∀ y ∈ Set.Icc (center - radius) (center + radius), y <= center ->
        ∀ x ∈ Set.Icc center (2 * center - y),
          2 * center - x ∈ Set.Icc (center - radius) (center + radius) := by
    intro y hy hyle x hx
    constructor
    · linarith [hy.1, hx.2]
    · linarith [hradius, hx.1]
  have hRem :
      ‖iteratedDeriv k.1 f eta - taylorPoly‖ <=
        order18Abs * radius ^ n / (Nat.factorial n : Real) := by
    dsimp [taylorPoly, n]
    rcases le_total center eta with hCenterLe | hEtaLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right18
        (f := f) (a := center - radius) (b := center + radius)
        (center := center) (radius := radius) (order18Abs := order18Abs)
        (eta := eta) (k := k.1) (n := 18 - k.1)
        hn_pos hkn hCenterMem hSmooth hOrder18 hRadiusCell heta hCenterLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left18
        (f := f) (a := center - radius) (b := center + radius)
        (center := center) (radius := radius) (order18Abs := order18Abs)
        (eta := eta) (k := k.1) (n := 18 - k.1)
        hn_pos hkn hSmooth hOrder18 hRadiusCell hEtaLe
        (hReflectCell eta heta hEtaLe)
  have hEtaRadius : ‖eta - center‖ <= radius :=
    abs_sub_center_le_of_mem_center_radius heta
  have hPolyDiff :
      ‖taylorPoly - centeredTaylorDerivPolynomial18 coeff k center eta‖ <=
        ∑ m ∈ Finset.range n,
          if h : k.1 + m < 18 then
            ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              coeffErrorAbs ⟨k.1 + m, h⟩ * radius ^ m
          else
            0 := by
    dsimp [taylorPoly, n]
    unfold centerJetTaylorPolynomialN centeredTaylorDerivPolynomial18
    rw [← Finset.sum_sub_distrib]
    refine
      (norm_sum_le
        (s := Finset.range n)
        (f := fun m : Nat =>
          (iteratedDeriv m (iteratedDeriv k.1 f) center /
              (Nat.factorial m : Real)) *
              (eta - center) ^ m -
            (if h : k.1 + m < 18 then
              ((Nat.factorial (k.1 + m) : Real) /
                  (Nat.factorial m : Real)) *
                coeff ⟨k.1 + m, h⟩ * (eta - center) ^ m
            else
              0))).trans ?_
    refine Finset.sum_le_sum ?_
    intro m hm
    have hmLt : m < 18 - k.1 := Finset.mem_range.mp hm
    have hkm : k.1 + m < 18 := by omega
    have hcoef_nonneg :
        0 <= (Nat.factorial (k.1 + m) : Real) /
          (Nat.factorial m : Real) := by
      positivity
    have hpow_le : ‖(eta - center) ^ m‖ <= radius ^ m := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hEtaRadius m
    have herr_nonneg : 0 <= coeffErrorAbs ⟨k.1 + m, hkm⟩ :=
      hCoeffErrorNonneg ⟨k.1 + m, hkm⟩
    have hterm :
        ‖(iteratedDeriv m (iteratedDeriv k.1 f) center /
              (Nat.factorial m : Real)) *
              (eta - center) ^ m -
            ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              coeff ⟨k.1 + m, hkm⟩ * (eta - center) ^ m‖ <=
          ((Nat.factorial (k.1 + m) : Real) /
              (Nat.factorial m : Real)) *
            coeffErrorAbs ⟨k.1 + m, hkm⟩ * radius ^ m := by
      rw [iteratedDeriv_centerJet_eq_shift18 (f := f) (center := center)
        (k := k.1) (m := m)]
      have hfactor :
          ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              (iteratedDeriv (k.1 + m) f center /
                (Nat.factorial (k.1 + m) : Real)) *
              (eta - center) ^ m -
            ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              coeff ⟨k.1 + m, hkm⟩ * (eta - center) ^ m =
            (((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              (iteratedDeriv (k.1 + m) f center /
                (Nat.factorial (k.1 + m) : Real) -
                  coeff ⟨k.1 + m, hkm⟩)) *
              (eta - center) ^ m := by
        ring
      rw [hfactor]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
      have hleft :
          ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              ‖iteratedDeriv (k.1 + m) f center /
                (Nat.factorial (k.1 + m) : Real) -
                  coeff ⟨k.1 + m, hkm⟩‖ <=
            ((Nat.factorial (k.1 + m) : Real) /
                (Nat.factorial m : Real)) *
              coeffErrorAbs ⟨k.1 + m, hkm⟩ :=
        mul_le_mul_of_nonneg_left (hJet ⟨k.1 + m, hkm⟩) hcoef_nonneg
      exact mul_le_mul hleft hpow_le
        (norm_nonneg _) (mul_nonneg hcoef_nonneg herr_nonneg)
    simpa [hkm] using hterm
  calc
    ‖iteratedDeriv k.1 f eta -
        centeredTaylorDerivPolynomial18 coeff k center eta‖
        =
        ‖(iteratedDeriv k.1 f eta - taylorPoly) +
          (taylorPoly - centeredTaylorDerivPolynomial18 coeff k center eta)‖ := by
          congr 1
          ring
    _ <=
        ‖iteratedDeriv k.1 f eta - taylorPoly‖ +
          ‖taylorPoly - centeredTaylorDerivPolynomial18 coeff k center eta‖ :=
        norm_add_le _ _
    _ <=
        order18Abs * radius ^ n / (Nat.factorial n : Real) +
          ∑ m ∈ Finset.range n,
            if h : k.1 + m < 18 then
              ((Nat.factorial (k.1 + m) : Real) /
                  (Nat.factorial m : Real)) *
                coeffErrorAbs ⟨k.1 + m, h⟩ * radius ^ m
            else
              0 := add_le_add hRem hPolyDiff
    _ =
        centeredTaylorDerivError18 coeffErrorAbs order18Abs radius k := by
          unfold centeredTaylorDerivError18
          dsimp [n]
          ring

end Step33
end PSDpd
end Q3
