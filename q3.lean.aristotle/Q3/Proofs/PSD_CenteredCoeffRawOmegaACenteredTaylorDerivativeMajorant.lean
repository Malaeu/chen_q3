import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Taylor

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
Centered Taylor derivative majorant interface for the Step33A.1-A sub0 factor
derivative payload.

This file is intentionally isolated.  It records the normalization selected for
the next factor-derivative certificate layer.  It now contains the checked
variable-degree Taylor/remainder bridge for `g := iteratedDeriv k f`; the
remaining nontrivial step is assembling these local bounds into the exact
`centeredTaylorDerivMajorant16` statement and instantiating the actual factor
payload rows.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

/-- Exact centered Taylor polynomial with a variable number of center-jet
rows.  The Step33 derivative-majorant bridge uses this with
`n = 16 - k`, applied to `iteratedDeriv k f`. -/
def centerJetTaylorPolynomialN
    (n : Nat) (f : Real -> Real) (center eta : Real) : Real :=
  ∑ j ∈ Finset.range n,
    (iteratedDeriv j f center / (Nat.factorial j : Real)) *
      (eta - center) ^ j

/-- Bound the variable center-jet Taylor polynomial from coefficient bounds
and a radius bound. -/
theorem centerJetTaylorPolynomialN_norm_bound
    {f : Real -> Real} {center eta radius : Real} {n : Nat}
    {termAbs : Nat -> Real}
    (hTermNonneg : ∀ j ∈ Finset.range n, 0 <= termAbs j)
    (hJet :
      ∀ j ∈ Finset.range n,
        ‖iteratedDeriv j f center / (Nat.factorial j : Real)‖ <=
          termAbs j)
    (hRadius : ‖eta - center‖ <= radius) :
    ‖centerJetTaylorPolynomialN n f center eta‖ <=
      ∑ j ∈ Finset.range n, termAbs j * radius ^ j := by
  unfold centerJetTaylorPolynomialN
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro j hj
  rw [norm_mul, norm_pow]
  exact mul_le_mul (hJet j hj)
    (pow_le_pow_left₀ (norm_nonneg _) hRadius j)
    (pow_nonneg (norm_nonneg _) j) (hTermNonneg j hj)

/-- Mathlib's `taylorWithinEval` agrees with the local center-jet polynomial
for variable degree.  This is the API bridge needed before bounding the Taylor
remainder for `g := iteratedDeriv k f`. -/
theorem taylorWithinEval_eq_centerJetTaylorPolynomialN
    {f : Real -> Real} {s : Set Real} {center eta : Real} {n : Nat}
    (hn : 0 < n)
    (hs : UniqueDiffOn Real s)
    (hSmooth : ContDiff Real n f)
    (hCenter : center ∈ s) :
    taylorWithinEval f (n - 1) s center eta =
      centerJetTaylorPolynomialN n f center eta := by
  rw [taylor_within_apply]
  have hnRange : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
  rw [hnRange]
  unfold centerJetTaylorPolynomialN
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hjle : (j : WithTop ENat) <= (n : Nat) := by
    exact_mod_cast Nat.le_of_lt hjlt
  have hWithin :
      iteratedDerivWithin j f s center =
        iteratedDeriv j f center := by
    exact iteratedDerivWithin_eq_iteratedDeriv hs
      ((hSmooth.contDiffAt).of_le hjle) hCenter
  rw [hWithin]
  rw [smul_eq_mul]
  ring

/-- At the expansion center, the variable center-jet polynomial evaluates to
the original function. -/
theorem centerJetTaylorPolynomialN_center
    {f : Real -> Real} {center : Real} {n : Nat}
    (hn : 0 < n) (hSmooth : ContDiff Real n f) :
    centerJetTaylorPolynomialN n f center center = f center := by
  have hTaylor :=
    taylorWithinEval_eq_centerJetTaylorPolynomialN
      (f := f) (s := Set.univ) (center := center) (eta := center)
      (n := n) hn uniqueDiffOn_univ hSmooth (by simp)
  rw [← hTaylor]
  exact taylorWithinEval_self f (n - 1) Set.univ center

/-- Reflection formula for iterated derivatives around an arbitrary center. -/
theorem iteratedDeriv_reflect_two_center_sub
    (n : Nat) (f : Real -> Real) (center x : Real) :
    iteratedDeriv n (fun y : Real => f (2 * center - y)) x =
      (-1 : Real) ^ n * iteratedDeriv n f (2 * center - x) := by
  have hNeg :=
    iteratedDeriv_comp_neg (𝕜 := Real) (F := Real) n
      (fun y : Real => f (2 * center + y)) x
  have hShift :=
    congrFun
      (iteratedDeriv_comp_const_add (𝕜 := Real) (F := Real) n f
        (2 * center)) (-x)
  rw [hShift] at hNeg
  simpa [sub_eq_add_neg, smul_eq_mul] using hNeg

/-- The variable center-jet Taylor polynomial is invariant under reflection
around its center. -/
theorem centerJetTaylorPolynomialN_reflect_eq
    (n : Nat) (f : Real -> Real) (center eta : Real) :
    centerJetTaylorPolynomialN n
        (fun y : Real => f (2 * center - y)) center (2 * center - eta) =
      centerJetTaylorPolynomialN n f center eta := by
  unfold centerJetTaylorPolynomialN
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [iteratedDeriv_reflect_two_center_sub]
  have hCenter : 2 * center - center = center := by ring
  have hEta : 2 * center - eta - center = -(eta - center) := by ring
  rw [hCenter, hEta]
  let C : Real := iteratedDeriv j f center
  let F : Real := (Nat.factorial j : Real)
  let X : Real := (eta - center) ^ j
  change ((-1 : Real) ^ j * C / F) * (-(eta - center)) ^ j =
    C / F * X
  have hNegPow :
      (-(eta - center)) ^ j = (-1 : Real) ^ j * X := by
    dsimp [X]
    rw [neg_pow]
  have hsq : (-1 : Real) ^ j * (-1 : Real) ^ j = 1 := by
    rw [← pow_add]
    have hadd : j + j = j * 2 := by ring
    rw [hadd]
    exact Even.neg_one_pow ⟨j, by ring⟩
  calc
    ((-1 : Real) ^ j * C / F) * (-(eta - center)) ^ j
        = ((-1 : Real) ^ j * C / F) * ((-1 : Real) ^ j * X) := by
          rw [hNegPow]
    _ = ((-1 : Real) ^ j * (-1 : Real) ^ j) * (C / F * X) := by
          ring
    _ = C / F * X := by
          rw [hsq]
          ring

/-- Right-side Taylor remainder bound with variable degree.  This is the
`center <= eta` half of the bridge used for
`g := iteratedDeriv k f`, `n = 16 - k`. -/
theorem centerJetTaylorPolynomialN_remainder_bound_right
    {f : Real -> Real} {a b center radius orderAbs eta : Real} {n : Nat}
    (hn : 0 < n)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real n f)
    (hOrder :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ <= orderAbs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (heta : eta ∈ Set.Icc a b)
    (hCenterLe : center <= eta) :
    ‖f eta - centerJetTaylorPolynomialN n f center eta‖ <=
      orderAbs * radius ^ n / (Nat.factorial n : Real) := by
  have hOrderNonneg : 0 <= orderAbs := by
    exact (norm_nonneg _).trans (hOrder center hCenterMem)
  have hRadiusNonneg : 0 <= radius := by
    simpa using hRadius center hCenterMem
  by_cases hlt : center < eta
  · have hnRange : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
    have hSmoothPred : ContDiff Real (n - 1 + 1) f := by
      change ContDiff Real (((n - 1 + 1 : Nat) : WithTop ENat)) f
      rw [hnRange]
      exact hSmooth
    obtain ⟨xi, hxi, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := f)
        (x := eta)
        (x₀ := center)
        (n := n - 1)
        hlt
        (hSmoothPred.contDiffOn)
    have hTaylorPoly :
        taylorWithinEval f (n - 1) (Set.Icc center eta) center eta =
          centerJetTaylorPolynomialN n f center eta :=
      taylorWithinEval_eq_centerJetTaylorPolynomialN
        (f := f) (s := Set.Icc center eta)
        (center := center) (eta := eta) (n := n)
        hn (uniqueDiffOn_Icc hlt) hSmooth ⟨le_rfl, le_of_lt hlt⟩
    rw [hTaylorPoly] at hrem
    have hxiCell : xi ∈ Set.Icc a b := by
      rw [Set.mem_Ioo] at hxi
      rw [Set.mem_Icc] at hCenterMem heta ⊢
      constructor <;> linarith
    have hDer := hOrder xi hxiCell
    have hPow :
        ‖(eta - center) ^ n‖ <= radius ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hRadius eta heta) n
    calc
      ‖f eta - centerJetTaylorPolynomialN n f center eta‖
          =
          ‖iteratedDeriv n f xi *
              (eta - center) ^ n / (Nat.factorial n : Real)‖ := by
            rw [hrem, hnRange]
      _ =
          ‖iteratedDeriv n f xi‖ * ‖(eta - center) ^ n‖ /
            (Nat.factorial n : Real) := by
            rw [norm_div, norm_mul]
            simp
      _ <=
          orderAbs * radius ^ n / (Nat.factorial n : Real) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul hDer hPow (norm_nonneg _) hOrderNonneg
  · have heta_eq : eta = center := by
      exact (le_antisymm hCenterLe (le_of_not_gt hlt)).symm
    subst eta
    have hRhsNonneg :
        0 <= orderAbs * radius ^ n / (Nat.factorial n : Real) := by
      exact div_nonneg
        (mul_nonneg hOrderNonneg (pow_nonneg hRadiusNonneg n))
        (by positivity)
    simpa [centerJetTaylorPolynomialN_center hn hSmooth] using hRhsNonneg

/-- Left-side Taylor remainder bound with variable degree, reduced to the
right-side bound by reflecting around the expansion center.  The explicit
`hReflectCell` hypothesis records the only geometric requirement: the reflected
Taylor interval must remain inside the cell where the derivative/order and
radius bounds are valid. -/
theorem centerJetTaylorPolynomialN_remainder_bound_left
    {f : Real -> Real} {a b center radius orderAbs eta : Real} {n : Nat}
    (hn : 0 < n)
    (hSmooth : ContDiff Real n f)
    (hOrder :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ <= orderAbs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hEtaLe : eta <= center)
    (hReflectCell :
      ∀ x ∈ Set.Icc center (2 * center - eta),
        2 * center - x ∈ Set.Icc a b) :
    ‖f eta - centerJetTaylorPolynomialN n f center eta‖ <=
      orderAbs * radius ^ n / (Nat.factorial n : Real) := by
  let etaR : Real := 2 * center - eta
  have hCenterLeR : center <= etaR := by
    dsimp [etaR]
    linarith
  have hCenterMemR : center ∈ Set.Icc center etaR :=
    ⟨le_rfl, hCenterLeR⟩
  have hetaR : etaR ∈ Set.Icc center etaR :=
    ⟨hCenterLeR, le_rfl⟩
  have hReflectSmooth :
      ContDiff Real n (fun y : Real => f (2 * center - y)) := by
    exact hSmooth.comp (by fun_prop)
  have hOrderR :
      ∀ x ∈ Set.Icc center etaR,
        ‖iteratedDeriv n (fun y : Real => f (2 * center - y)) x‖ <=
          orderAbs := by
    intro x hx
    have hxBase : 2 * center - x ∈ Set.Icc a b := by
      simpa [etaR] using hReflectCell x hx
    have hBase := hOrder (2 * center - x) hxBase
    rw [iteratedDeriv_reflect_two_center_sub, norm_mul]
    have hNegNorm : ‖((-1 : Real) ^ n)‖ = 1 := by simp
    rw [hNegNorm, one_mul]
    exact hBase
  have hRadiusR :
      ∀ x ∈ Set.Icc center etaR, ‖x - center‖ <= radius := by
    intro x hx
    have hxBase : 2 * center - x ∈ Set.Icc a b := by
      simpa [etaR] using hReflectCell x hx
    have hBase := hRadius (2 * center - x) hxBase
    have hEq : 2 * center - x - center = -(x - center) := by ring
    have hNormEq : ‖x - center‖ = ‖2 * center - x - center‖ := by
      rw [hEq, norm_neg]
    exact hNormEq.trans_le hBase
  have hRight :=
    centerJetTaylorPolynomialN_remainder_bound_right
      (f := fun y : Real => f (2 * center - y))
      (a := center) (b := etaR) (center := center) (radius := radius)
      (orderAbs := orderAbs) (eta := etaR) (n := n)
      hn hCenterMemR hReflectSmooth hOrderR hRadiusR hetaR hCenterLeR
  have hEtaR : 2 * center - etaR = eta := by
    dsimp [etaR]
    ring
  simpa [etaR, hEtaR, centerJetTaylorPolynomialN_reflect_eq] using hRight

/-- Iterating `iteratedDeriv` is just addition of derivative orders.  This is
the local API bridge needed before applying a Taylor receiver to
`g := iteratedDeriv k f`. -/
theorem iteratedDeriv_iteratedDeriv_eq_add
    {f : Real -> Real} (k m : Nat) :
    iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate]
  exact (Function.iterate_add_apply deriv m k f).symm

/-- Same crosswalk in the `k + m` order used by the Step33 route notes. -/
theorem iteratedDeriv_iteratedDeriv_eq_add_comm
    {f : Real -> Real} (k m : Nat) :
    iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (k + m) f := by
  rw [Nat.add_comm k m]
  exact iteratedDeriv_iteratedDeriv_eq_add k m

/-- Smoothness transport for the variable-order Taylor step: after taking `k`
derivatives, there are still `n` derivatives available whenever `n + k <= 16`.
-/
theorem contDiff_iteratedDeriv_of_add_le_sixteen
    {f : Real -> Real} {k n : Nat}
    (hSmooth : ContDiff Real 16 f) (hkn : n + k <= 16) :
    ContDiff Real n (iteratedDeriv k f) := by
  have hSmooth' : ContDiff Real (n + k) f :=
    hSmooth.of_le (by exact_mod_cast hkn)
  simpa [iteratedDeriv_eq_iterate] using
    (ContDiff.iterate_deriv' (𝕜 := Real) (F := Real) n k hSmooth')

/-- Transport a uniform order-16 bound on `f` to the top derivative bound
needed by the Taylor theorem applied to `iteratedDeriv k f`. -/
theorem iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_sixteen
    {f : Real -> Real} {s : Set Real} {k n : Nat} {order16Abs : Real}
    (hkn : k + n = 16)
    (hOrder16 :
      ∀ eta ∈ s, ‖iteratedDeriv 16 f eta‖ <= order16Abs) :
    ∀ eta ∈ s,
      ‖iteratedDeriv n (iteratedDeriv k f) eta‖ <= order16Abs := by
  intro eta hEta
  have hCross :=
    congrFun (iteratedDeriv_iteratedDeriv_eq_add_comm (f := f) k n) eta
  rw [hCross, hkn]
  exact hOrder16 eta hEta

/-- Right-side Taylor remainder bound specialized to
`g := iteratedDeriv k f` with top derivative order normalized by
`k + n = 16`.  This is the first proof-grade half of the variable-order
Taylor bridge requested for the Step33 factor-derivative payload. -/
theorem iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right
    {f : Real -> Real} {a b center radius order16Abs eta : Real}
    {k n : Nat}
    (hn : 0 < n)
    (hkn : k + n = 16)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 16 f)
    (hOrder16 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 16 f x‖ <= order16Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (heta : eta ∈ Set.Icc a b)
    (hCenterLe : center <= eta) :
    ‖iteratedDeriv k f eta -
        centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
      order16Abs * radius ^ n / (Nat.factorial n : Real) := by
  have hnk : n + k <= 16 := by
    rw [Nat.add_comm]
    exact le_of_eq hkn
  have hSmoothG :
      ContDiff Real n (iteratedDeriv k f) :=
    contDiff_iteratedDeriv_of_add_le_sixteen
      (f := f) (k := k) (n := n) hSmooth hnk
  have hOrderG :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDeriv n (iteratedDeriv k f) x‖ <= order16Abs := by
    exact iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_sixteen
      (f := f) (s := Set.Icc a b) (k := k) (n := n)
      hkn hOrder16
  exact centerJetTaylorPolynomialN_remainder_bound_right
    (f := iteratedDeriv k f)
    (a := a) (b := b) (center := center) (radius := radius)
    (orderAbs := order16Abs) (eta := eta) (n := n)
    hn hCenterMem hSmoothG hOrderG hRadius heta hCenterLe

/-- Left-side version of
`iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right`, again with
the explicit reflected-cell geometry hypothesis left visible. -/
theorem iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left
    {f : Real -> Real} {a b center radius order16Abs eta : Real}
    {k n : Nat}
    (hn : 0 < n)
    (hkn : k + n = 16)
    (hSmooth : ContDiff Real 16 f)
    (hOrder16 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 16 f x‖ <= order16Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hEtaLe : eta <= center)
    (hReflectCell :
      ∀ x ∈ Set.Icc center (2 * center - eta),
        2 * center - x ∈ Set.Icc a b) :
    ‖iteratedDeriv k f eta -
        centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
      order16Abs * radius ^ n / (Nat.factorial n : Real) := by
  have hnk : n + k <= 16 := by
    rw [Nat.add_comm]
    exact le_of_eq hkn
  have hSmoothG :
      ContDiff Real n (iteratedDeriv k f) :=
    contDiff_iteratedDeriv_of_add_le_sixteen
      (f := f) (k := k) (n := n) hSmooth hnk
  have hOrderG :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDeriv n (iteratedDeriv k f) x‖ <= order16Abs := by
    exact iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_sixteen
      (f := f) (s := Set.Icc a b) (k := k) (n := n)
      hkn hOrder16
  exact centerJetTaylorPolynomialN_remainder_bound_left
    (f := iteratedDeriv k f)
    (a := a) (b := b) (center := center) (radius := radius)
    (orderAbs := order16Abs) (eta := eta) (n := n)
    hn hSmoothG hOrderG hRadius hEtaLe hReflectCell

/-- Coefficient normalization bridge for the Taylor theorem applied to
`iteratedDeriv k f`: the `m`th normalized center jet of `iteratedDeriv k f`
is controlled by the `(k + m)`th normalized center jet of `f`, with the exact
falling-factorial multiplier. -/
theorem iteratedDeriv_centerJet_bound_of_shift
    {f : Real -> Real} {center : Real} {jetAbs : Fin 16 -> Real}
    (hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    {k m : Nat} (hkm : k + m < 16) :
    ‖iteratedDeriv m (iteratedDeriv k f) center /
        (Nat.factorial m : Real)‖ <=
      ((Nat.factorial (k + m) : Real) / (Nat.factorial m : Real)) *
        jetAbs ⟨k + m, hkm⟩ := by
  have hCross :=
    congrFun (iteratedDeriv_iteratedDeriv_eq_add_comm (f := f) k m) center
  rw [hCross]
  have hRewrite :
      iteratedDeriv (k + m) f center / (Nat.factorial m : Real) =
        ((Nat.factorial (k + m) : Real) / (Nat.factorial m : Real)) *
          (iteratedDeriv (k + m) f center /
            (Nat.factorial (k + m) : Real)) := by
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]
  rw [hRewrite]
  rw [norm_mul, Real.norm_eq_abs]
  have hcoef_nonneg :
      0 <= (Nat.factorial (k + m) : Real) /
        (Nat.factorial m : Real) := by
    positivity
  rw [abs_of_nonneg hcoef_nonneg]
  exact mul_le_mul_of_nonneg_left (hJet ⟨k + m, hkm⟩) hcoef_nonneg

/--
Majorant for the `k`th derivative of a degree-15 centered Taylor model plus a
uniform order-16 remainder bound on a radius-`radius` cell.

For `k = 16` the finite Taylor sum is empty and the expression reduces to the
uniform order-16 bound.  For `k < 16`, the coefficient
`(k + m)! / m!` is the falling-factorial multiplier from differentiating the
centered monomial `(x - c)^(k + m)` exactly `k` times.
-/
def centeredTaylorDerivMajorant16
    (jetAbs : Fin 16 -> Real) (order16Abs radius : Real)
    (k : Fin 17) : Real :=
  (∑ j : Fin 16,
      if k.1 <= j.1 then
        ((Nat.factorial j.1 : Real) /
            (Nat.factorial (j.1 - k.1) : Real)) *
          jetAbs j *
          radius ^ (j.1 - k.1)
      else
        0) +
    order16Abs * radius ^ (16 - k.1) /
      (Nat.factorial (16 - k.1) : Real)

/-- Range-indexed version of `centeredTaylorDerivMajorant16`, used while the
variable-order Taylor bridge is stated with natural parameters `k` and `n`
such that `k + n = 16`. -/
def centeredTaylorDerivMajorant16Range
    (jetAbs : Fin 16 -> Real) (order16Abs radius : Real)
    (k n : Nat) : Real :=
  (∑ m ∈ Finset.range n,
      (if h : k + m < 16 then
        ((Nat.factorial (k + m) : Real) /
            (Nat.factorial m : Real)) *
          jetAbs ⟨k + m, h⟩
      else
        0) *
        radius ^ m) +
    order16Abs * radius ^ n / (Nat.factorial n : Real)

/-- Assemble the checked variable-order polynomial bound and the checked
right/left Taylor remainder bounds into a derivative majorant in range
normalization.  The remaining assembly step is to rewrite this range form into
the public `centeredTaylorDerivMajorant16` `Fin 17` normalization. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant16Range
    {f : Real -> Real} {a b center radius order16Abs eta : Real}
    {k n : Nat} {jetAbs : Fin 16 -> Real}
    (hn : 0 < n)
    (hkn : k + n = 16)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 16 f)
    (hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    (hOrder16 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 16 f x‖ <= order16Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hReflectCell :
      ∀ y ∈ Set.Icc a b, y <= center ->
        ∀ x ∈ Set.Icc center (2 * center - y),
          2 * center - x ∈ Set.Icc a b)
    (heta : eta ∈ Set.Icc a b) :
    ‖iteratedDeriv k f eta‖ <=
      centeredTaylorDerivMajorant16Range jetAbs order16Abs radius k n := by
  let termAbs : Nat -> Real := fun m =>
    if h : k + m < 16 then
      ((Nat.factorial (k + m) : Real) / (Nat.factorial m : Real)) *
        jetAbs ⟨k + m, h⟩
    else
      0
  have hTermNonneg :
      ∀ m ∈ Finset.range n, 0 <= termAbs m := by
    intro m hm
    dsimp [termAbs]
    by_cases h : k + m < 16
    · simp [h]
      have hJetNonneg : 0 <= jetAbs ⟨k + m, h⟩ :=
        (norm_nonneg _).trans (hJet ⟨k + m, h⟩)
      exact mul_nonneg (by positivity) hJetNonneg
    · simp [h]
  have hPolyJet :
      ∀ m ∈ Finset.range n,
        ‖iteratedDeriv m (iteratedDeriv k f) center /
            (Nat.factorial m : Real)‖ <=
          termAbs m := by
    intro m hm
    have hmLt : m < n := Finset.mem_range.mp hm
    have hkm : k + m < 16 := by
      rw [← hkn]
      exact Nat.add_lt_add_left hmLt k
    dsimp [termAbs]
    simp [hkm]
    exact iteratedDeriv_centerJet_bound_of_shift
      (f := f) (center := center) (jetAbs := jetAbs) hJet hkm
  have hPoly :
      ‖centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
        ∑ m ∈ Finset.range n, termAbs m * radius ^ m :=
    centerJetTaylorPolynomialN_norm_bound
      (f := iteratedDeriv k f) (center := center) (eta := eta)
      (radius := radius) (n := n) (termAbs := termAbs)
      hTermNonneg hPolyJet (hRadius eta heta)
  have hRem :
      ‖iteratedDeriv k f eta -
          centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
        order16Abs * radius ^ n / (Nat.factorial n : Real) := by
    rcases le_total center eta with hCenterLe | hEtaLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order16Abs := order16Abs)
        (eta := eta) (k := k) (n := n)
        hn hkn hCenterMem hSmooth hOrder16 hRadius heta hCenterLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order16Abs := order16Abs)
        (eta := eta) (k := k) (n := n)
        hn hkn hSmooth hOrder16 hRadius hEtaLe (hReflectCell eta heta hEtaLe)
  have hTriangle :
      ‖iteratedDeriv k f eta‖ <=
        ‖centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ +
          ‖iteratedDeriv k f eta -
            centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ := by
    calc
      ‖iteratedDeriv k f eta‖ =
          ‖(iteratedDeriv k f eta -
              centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta) +
            centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ := by
            congr 1
            ring
      _ <=
          ‖iteratedDeriv k f eta -
              centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ +
            ‖centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ :=
            norm_add_le _ _
      _ =
          ‖centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ +
            ‖iteratedDeriv k f eta -
              centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ := by
            rw [add_comm]
  unfold centeredTaylorDerivMajorant16Range
  dsimp [termAbs] at hPoly ⊢
  exact hTriangle.trans (add_le_add hPoly hRem)

/-- The range-indexed derivative majorant and the public `Fin 17` majorant
agree when the range length is `16 - k`. -/
theorem centeredTaylorDerivMajorant16Range_eq
    (jetAbs : Fin 16 -> Real) (order16Abs radius : Real)
    (k : Fin 17) :
    centeredTaylorDerivMajorant16Range jetAbs order16Abs radius
        k.1 (16 - k.1) =
      centeredTaylorDerivMajorant16 jetAbs order16Abs radius k := by
  classical
  unfold centeredTaylorDerivMajorant16Range centeredTaylorDerivMajorant16
  congr 1
  let K : Nat := k.1
  have hKle : K <= 16 := by
    dsimp [K]
    exact Nat.le_of_lt_succ k.2
  let T : Nat -> Real := fun j =>
    if hj : j < 16 then
      if K <= j then
        ((Nat.factorial j : Real) / (Nat.factorial (j - K) : Real)) *
          jetAbs ⟨j, hj⟩ * radius ^ (j - K)
      else
        0
    else
      0
  have hFinToRange :
      (∑ j : Fin 16,
          if K <= j.1 then
            ((Nat.factorial j.1 : Real) /
                (Nat.factorial (j.1 - K) : Real)) *
              jetAbs j *
              radius ^ (j.1 - K)
          else
            0) =
        ∑ j ∈ Finset.range 16, T j := by
    have h := Fin.sum_univ_eq_sum_range (f := T) (n := 16)
    rw [← h]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    dsimp [T]
    simp [j.2]
  have hsplit :
      (∑ j ∈ Finset.range 16, T j) =
        (∑ j ∈ Finset.range K, T j) +
          ∑ m ∈ Finset.range (16 - K), T (K + m) := by
    simpa [Nat.add_sub_of_le hKle] using
      (Finset.sum_range_add T K (16 - K))
  have hprefix :
      (∑ j ∈ Finset.range K, T j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjlt : j < K := Finset.mem_range.mp hj
    dsimp [T]
    by_cases h16 : j < 16
    · simp [h16, Nat.not_le.mpr hjlt]
    · simp [h16]
  have htail :
      (∑ m ∈ Finset.range (16 - K), T (K + m)) =
        ∑ m ∈ Finset.range (16 - K),
          (if h : K + m < 16 then
            ((Nat.factorial (K + m) : Real) /
                (Nat.factorial m : Real)) *
              jetAbs ⟨K + m, h⟩
          else
            0) *
            radius ^ m := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmlt : m < 16 - K := Finset.mem_range.mp hm
    have hlt : K + m < 16 := by omega
    have hKleKm : K <= K + m := by omega
    dsimp [T]
    simp [hlt, hKleKm]
  change
    (∑ m ∈ Finset.range (16 - K),
      (if h : K + m < 16 then
        ((Nat.factorial (K + m) : Real) /
            (Nat.factorial m : Real)) *
          jetAbs ⟨K + m, h⟩
      else
        0) *
        radius ^ m) =
      ∑ j : Fin 16,
        if K <= j.1 then
          ((Nat.factorial j.1 : Real) /
              (Nat.factorial (j.1 - K) : Real)) *
            jetAbs j *
            radius ^ (j.1 - K)
        else
          0
  rw [hFinToRange, hsplit, hprefix, zero_add, htail]

/-- Endpoint normalization check: the `k = 16` majorant is exactly the
order-16 absolute bound. -/
theorem centeredTaylorDerivMajorant16_last
    (jetAbs : Fin 16 -> Real) (order16Abs radius : Real) :
    centeredTaylorDerivMajorant16 jetAbs order16Abs radius
        ⟨16, by decide⟩ =
      order16Abs := by
  unfold centeredTaylorDerivMajorant16
  have hsum :
      (∑ j : Fin 16,
          if 16 <= j.1 then
            ((Nat.factorial j.1 : Real) /
                (Nat.factorial (j.1 - 16) : Real)) *
              jetAbs j *
              radius ^ (j.1 - 16)
          else
            0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _hj
    have hnot : ¬ 16 <= j.1 := Nat.not_le.mpr j.2
    simp [hnot]
  rw [hsum]
  simp

/-- The endpoint `k = 16` derivative bound feeds the majorant without any
Taylor crosswalk. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant16_last
    {f : Real -> Real} {a b order16Abs radius : Real}
    (jetAbs : Fin 16 -> Real)
    (hOrder16 :
      ∀ eta ∈ Set.Icc a b, ‖iteratedDeriv 16 f eta‖ <= order16Abs) :
    ∀ eta ∈ Set.Icc a b,
      ‖iteratedDeriv (⟨16, by decide⟩ : Fin 17).1 f eta‖ <=
        centeredTaylorDerivMajorant16 jetAbs order16Abs radius
          ⟨16, by decide⟩ := by
  intro eta hEta
  rw [centeredTaylorDerivMajorant16_last]
  exact hOrder16 eta hEta

/-- Public `Fin 17` derivative majorant.  This closes the normalization gap
between the checked variable-order Taylor bridge and the receiver-facing
`centeredTaylorDerivMajorant16` interface. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant16
    {f : Real -> Real} {a b center radius order16Abs eta : Real}
    {jetAbs : Fin 16 -> Real}
    (k : Fin 17)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 16 f)
    (hJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    (hOrder16 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 16 f x‖ <= order16Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hReflectCell :
      ∀ y ∈ Set.Icc a b, y <= center ->
        ∀ x ∈ Set.Icc center (2 * center - y),
          2 * center - x ∈ Set.Icc a b)
    (heta : eta ∈ Set.Icc a b) :
    ‖iteratedDeriv k.1 f eta‖ <=
      centeredTaylorDerivMajorant16 jetAbs order16Abs radius k := by
  by_cases hlast : k.1 = 16
  · have hk : k = ⟨16, by decide⟩ := Fin.ext hlast
    subst k
    exact iteratedDeriv_norm_le_centeredTaylorDerivMajorant16_last
      (f := f) (a := a) (b := b) (order16Abs := order16Abs)
      (radius := radius) jetAbs hOrder16 eta heta
  · have hklt : k.1 < 16 := by omega
    have hn : 0 < 16 - k.1 := Nat.sub_pos_of_lt hklt
    have hkn : k.1 + (16 - k.1) = 16 :=
      Nat.add_sub_of_le (Nat.le_of_lt hklt)
    have hRange :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant16Range
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order16Abs := order16Abs)
        (eta := eta) (k := k.1) (n := 16 - k.1)
        (jetAbs := jetAbs)
        hn hkn hCenterMem hSmooth hJet hOrder16 hRadius hReflectCell heta
    rw [centeredTaylorDerivMajorant16Range_eq] at hRange
    exact hRange

end Step33
end PSDpd
end Q3
