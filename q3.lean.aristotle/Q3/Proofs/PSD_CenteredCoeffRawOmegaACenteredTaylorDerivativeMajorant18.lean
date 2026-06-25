import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
Order-18 centered Taylor derivative majorant interface for the Step33A.1-A
two-segment raw-D17 factor-row route.

This file intentionally contains only the generic analytic bridge. It does not
assert any local two-segment numerical payload rows and it does not close
Step33A.1-A by itself.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

theorem contDiff_iteratedDeriv_of_add_le_eighteen
    {f : Real -> Real} {k n : Nat}
    (hSmooth : ContDiff Real 18 f) (hkn : n + k <= 18) :
    ContDiff Real n (iteratedDeriv k f) := by
  have hSmooth' : ContDiff Real (n + k) f :=
    hSmooth.of_le (by exact_mod_cast hkn)
  simpa [iteratedDeriv_eq_iterate] using
    (ContDiff.iterate_deriv' (𝕜 := Real) (F := Real) n k hSmooth')

/-- Transport a uniform order-18 bound on `f` to the top derivative bound
needed by the Taylor theorem applied to `iteratedDeriv k f`. -/
theorem iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_eighteen
    {f : Real -> Real} {s : Set Real} {k n : Nat} {order18Abs : Real}
    (hkn : k + n = 18)
    (hOrder18 :
      ∀ eta ∈ s, ‖iteratedDeriv 18 f eta‖ <= order18Abs) :
    ∀ eta ∈ s,
      ‖iteratedDeriv n (iteratedDeriv k f) eta‖ <= order18Abs := by
  intro eta hEta
  have hCross :=
    congrFun (iteratedDeriv_iteratedDeriv_eq_add_comm (f := f) k n) eta
  rw [hCross, hkn]
  exact hOrder18 eta hEta

/-- Right-side Taylor remainder bound specialized to
`g := iteratedDeriv k f` with top derivative order normalized by
`k + n = 18`.  This is the first proof-grade half of the variable-order
Taylor bridge requested for the Step33 factor-derivative payload. -/
theorem iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right18
    {f : Real -> Real} {a b center radius order18Abs eta : Real}
    {k n : Nat}
    (hn : 0 < n)
    (hkn : k + n = 18)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 18 f)
    (hOrder18 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 18 f x‖ <= order18Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (heta : eta ∈ Set.Icc a b)
    (hCenterLe : center <= eta) :
    ‖iteratedDeriv k f eta -
        centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
      order18Abs * radius ^ n / (Nat.factorial n : Real) := by
  have hnk : n + k <= 18 := by
    rw [Nat.add_comm]
    exact le_of_eq hkn
  have hSmoothG :
      ContDiff Real n (iteratedDeriv k f) :=
    contDiff_iteratedDeriv_of_add_le_eighteen
      (f := f) (k := k) (n := n) hSmooth hnk
  have hOrderG :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDeriv n (iteratedDeriv k f) x‖ <= order18Abs := by
    exact iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_eighteen
      (f := f) (s := Set.Icc a b) (k := k) (n := n)
      hkn hOrder18
  exact centerJetTaylorPolynomialN_remainder_bound_right
    (f := iteratedDeriv k f)
    (a := a) (b := b) (center := center) (radius := radius)
    (orderAbs := order18Abs) (eta := eta) (n := n)
    hn hCenterMem hSmoothG hOrderG hRadius heta hCenterLe

/-- Left-side version of
`iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right18`, again with
the explicit reflected-cell geometry hypothesis left visible. -/
theorem iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left18
    {f : Real -> Real} {a b center radius order18Abs eta : Real}
    {k n : Nat}
    (hn : 0 < n)
    (hkn : k + n = 18)
    (hSmooth : ContDiff Real 18 f)
    (hOrder18 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 18 f x‖ <= order18Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hEtaLe : eta <= center)
    (hReflectCell :
      ∀ x ∈ Set.Icc center (2 * center - eta),
        2 * center - x ∈ Set.Icc a b) :
    ‖iteratedDeriv k f eta -
        centerJetTaylorPolynomialN n (iteratedDeriv k f) center eta‖ <=
      order18Abs * radius ^ n / (Nat.factorial n : Real) := by
  have hnk : n + k <= 18 := by
    rw [Nat.add_comm]
    exact le_of_eq hkn
  have hSmoothG :
      ContDiff Real n (iteratedDeriv k f) :=
    contDiff_iteratedDeriv_of_add_le_eighteen
      (f := f) (k := k) (n := n) hSmooth hnk
  have hOrderG :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDeriv n (iteratedDeriv k f) x‖ <= order18Abs := by
    exact iteratedDeriv_iteratedDeriv_norm_bound_of_add_eq_eighteen
      (f := f) (s := Set.Icc a b) (k := k) (n := n)
      hkn hOrder18
  exact centerJetTaylorPolynomialN_remainder_bound_left
    (f := iteratedDeriv k f)
    (a := a) (b := b) (center := center) (radius := radius)
    (orderAbs := order18Abs) (eta := eta) (n := n)
    hn hSmoothG hOrderG hRadius hEtaLe hReflectCell

/-- Coefficient normalization bridge for the Taylor theorem applied to
`iteratedDeriv k f`: the `m`th normalized center jet of `iteratedDeriv k f`
is controlled by the `(k + m)`th normalized center jet of `f`, with the exact
falling-factorial multiplier. -/
theorem iteratedDeriv_centerJet_bound_of_shift18
    {f : Real -> Real} {center : Real} {jetAbs : Fin 18 -> Real}
    (hJet :
      ∀ j : Fin 18,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    {k m : Nat} (hkm : k + m < 18) :
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
uniform order-18 remainder bound on a radius-`radius` cell.

For `k = 18` the finite Taylor sum is empty and the expression reduces to the
uniform order-18 bound.  For `k < 18`, the coefficient
`(k + m)! / m!` is the falling-factorial multiplier from differentiating the
centered monomial `(x - c)^(k + m)` exactly `k` times.
-/
def centeredTaylorDerivMajorant18
    (jetAbs : Fin 18 -> Real) (order18Abs radius : Real)
    (k : Fin 19) : Real :=
  (∑ j : Fin 18,
      if k.1 <= j.1 then
        ((Nat.factorial j.1 : Real) /
            (Nat.factorial (j.1 - k.1) : Real)) *
          jetAbs j *
          radius ^ (j.1 - k.1)
      else
        0) +
    order18Abs * radius ^ (18 - k.1) /
      (Nat.factorial (18 - k.1) : Real)

/-- Range-indexed version of `centeredTaylorDerivMajorant18`, used while the
variable-order Taylor bridge is stated with natural parameters `k` and `n`
such that `k + n = 18`. -/
def centeredTaylorDerivMajorant18Range
    (jetAbs : Fin 18 -> Real) (order18Abs radius : Real)
    (k n : Nat) : Real :=
  (∑ m ∈ Finset.range n,
      (if h : k + m < 18 then
        ((Nat.factorial (k + m) : Real) /
            (Nat.factorial m : Real)) *
          jetAbs ⟨k + m, h⟩
      else
        0) *
        radius ^ m) +
    order18Abs * radius ^ n / (Nat.factorial n : Real)

/-- Assemble the checked variable-order polynomial bound and the checked
right/left Taylor remainder bounds into a derivative majorant in range
normalization.  The remaining assembly step is to rewrite this range form into
the public `centeredTaylorDerivMajorant18` `Fin 19` normalization. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant18Range
    {f : Real -> Real} {a b center radius order18Abs eta : Real}
    {k n : Nat} {jetAbs : Fin 18 -> Real}
    (hn : 0 < n)
    (hkn : k + n = 18)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 18 f)
    (hJet :
      ∀ j : Fin 18,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    (hOrder18 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 18 f x‖ <= order18Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hReflectCell :
      ∀ y ∈ Set.Icc a b, y <= center ->
        ∀ x ∈ Set.Icc center (2 * center - y),
          2 * center - x ∈ Set.Icc a b)
    (heta : eta ∈ Set.Icc a b) :
    ‖iteratedDeriv k f eta‖ <=
      centeredTaylorDerivMajorant18Range jetAbs order18Abs radius k n := by
  let termAbs : Nat -> Real := fun m =>
    if h : k + m < 18 then
      ((Nat.factorial (k + m) : Real) / (Nat.factorial m : Real)) *
        jetAbs ⟨k + m, h⟩
    else
      0
  have hTermNonneg :
      ∀ m ∈ Finset.range n, 0 <= termAbs m := by
    intro m hm
    dsimp [termAbs]
    by_cases h : k + m < 18
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
    have hkm : k + m < 18 := by
      rw [← hkn]
      exact Nat.add_lt_add_left hmLt k
    dsimp [termAbs]
    simp [hkm]
    exact iteratedDeriv_centerJet_bound_of_shift18
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
        order18Abs * radius ^ n / (Nat.factorial n : Real) := by
    rcases le_total center eta with hCenterLe | hEtaLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_right18
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order18Abs := order18Abs)
        (eta := eta) (k := k) (n := n)
        hn hkn hCenterMem hSmooth hOrder18 hRadius heta hCenterLe
    · exact iteratedDeriv_centerJetTaylorPolynomialN_remainder_bound_left18
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order18Abs := order18Abs)
        (eta := eta) (k := k) (n := n)
        hn hkn hSmooth hOrder18 hRadius hEtaLe (hReflectCell eta heta hEtaLe)
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
  unfold centeredTaylorDerivMajorant18Range
  dsimp [termAbs] at hPoly ⊢
  exact hTriangle.trans (add_le_add hPoly hRem)

/-- The range-indexed derivative majorant and the public `Fin 19` majorant
agree when the range length is `18 - k`. -/
theorem centeredTaylorDerivMajorant18Range_eq
    (jetAbs : Fin 18 -> Real) (order18Abs radius : Real)
    (k : Fin 19) :
    centeredTaylorDerivMajorant18Range jetAbs order18Abs radius
        k.1 (18 - k.1) =
      centeredTaylorDerivMajorant18 jetAbs order18Abs radius k := by
  classical
  unfold centeredTaylorDerivMajorant18Range centeredTaylorDerivMajorant18
  congr 1
  let K : Nat := k.1
  have hKle : K <= 18 := by
    dsimp [K]
    exact Nat.le_of_lt_succ k.2
  let T : Nat -> Real := fun j =>
    if hj : j < 18 then
      if K <= j then
        ((Nat.factorial j : Real) / (Nat.factorial (j - K) : Real)) *
          jetAbs ⟨j, hj⟩ * radius ^ (j - K)
      else
        0
    else
      0
  have hFinToRange :
      (∑ j : Fin 18,
          if K <= j.1 then
            ((Nat.factorial j.1 : Real) /
                (Nat.factorial (j.1 - K) : Real)) *
              jetAbs j *
              radius ^ (j.1 - K)
          else
            0) =
        ∑ j ∈ Finset.range 18, T j := by
    have h := Fin.sum_univ_eq_sum_range (f := T) (n := 18)
    rw [← h]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    dsimp [T]
    simp [j.2]
  have hsplit :
      (∑ j ∈ Finset.range 18, T j) =
        (∑ j ∈ Finset.range K, T j) +
          ∑ m ∈ Finset.range (18 - K), T (K + m) := by
    simpa [Nat.add_sub_of_le hKle] using
      (Finset.sum_range_add T K (18 - K))
  have hprefix :
      (∑ j ∈ Finset.range K, T j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjlt : j < K := Finset.mem_range.mp hj
    dsimp [T]
    by_cases h16 : j < 18
    · simp [h16, Nat.not_le.mpr hjlt]
    · simp [h16]
  have htail :
      (∑ m ∈ Finset.range (18 - K), T (K + m)) =
        ∑ m ∈ Finset.range (18 - K),
          (if h : K + m < 18 then
            ((Nat.factorial (K + m) : Real) /
                (Nat.factorial m : Real)) *
              jetAbs ⟨K + m, h⟩
          else
            0) *
            radius ^ m := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmlt : m < 18 - K := Finset.mem_range.mp hm
    have hlt : K + m < 18 := by omega
    have hKleKm : K <= K + m := by omega
    dsimp [T]
    simp [hlt, hKleKm]
  change
    (∑ m ∈ Finset.range (18 - K),
      (if h : K + m < 18 then
        ((Nat.factorial (K + m) : Real) /
            (Nat.factorial m : Real)) *
          jetAbs ⟨K + m, h⟩
      else
        0) *
        radius ^ m) =
      ∑ j : Fin 18,
        if K <= j.1 then
          ((Nat.factorial j.1 : Real) /
              (Nat.factorial (j.1 - K) : Real)) *
            jetAbs j *
            radius ^ (j.1 - K)
        else
          0
  rw [hFinToRange, hsplit, hprefix, zero_add, htail]

/-- Endpoint normalization check: the `k = 18` majorant is exactly the
order-18 absolute bound. -/
theorem centeredTaylorDerivMajorant18_last
    (jetAbs : Fin 18 -> Real) (order18Abs radius : Real) :
    centeredTaylorDerivMajorant18 jetAbs order18Abs radius
        ⟨18, by decide⟩ =
      order18Abs := by
  unfold centeredTaylorDerivMajorant18
  have hsum :
      (∑ j : Fin 18,
          if 18 <= j.1 then
            ((Nat.factorial j.1 : Real) /
                (Nat.factorial (j.1 - 18) : Real)) *
              jetAbs j *
              radius ^ (j.1 - 18)
          else
            0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _hj
    have hnot : ¬ 18 <= j.1 := Nat.not_le.mpr j.2
    simp [hnot]
  rw [hsum]
  simp

/-- The endpoint `k = 18` derivative bound feeds the majorant without any
Taylor crosswalk. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant18_last
    {f : Real -> Real} {a b order18Abs radius : Real}
    (jetAbs : Fin 18 -> Real)
    (hOrder18 :
      ∀ eta ∈ Set.Icc a b, ‖iteratedDeriv 18 f eta‖ <= order18Abs) :
    ∀ eta ∈ Set.Icc a b,
      ‖iteratedDeriv (⟨18, by decide⟩ : Fin 19).1 f eta‖ <=
        centeredTaylorDerivMajorant18 jetAbs order18Abs radius
          ⟨18, by decide⟩ := by
  intro eta hEta
  rw [centeredTaylorDerivMajorant18_last]
  exact hOrder18 eta hEta

/-- Public `Fin 19` derivative majorant.  This closes the normalization gap
between the checked variable-order Taylor bridge and the receiver-facing
`centeredTaylorDerivMajorant18` interface. -/
theorem iteratedDeriv_norm_le_centeredTaylorDerivMajorant18
    {f : Real -> Real} {a b center radius order18Abs eta : Real}
    {jetAbs : Fin 18 -> Real}
    (k : Fin 19)
    (hCenterMem : center ∈ Set.Icc a b)
    (hSmooth : ContDiff Real 18 f)
    (hJet :
      ∀ j : Fin 18,
        ‖iteratedDeriv j.1 f center / (Nat.factorial j.1 : Real)‖ <=
          jetAbs j)
    (hOrder18 :
      ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 18 f x‖ <= order18Abs)
    (hRadius :
      ∀ x ∈ Set.Icc a b, ‖x - center‖ <= radius)
    (hReflectCell :
      ∀ y ∈ Set.Icc a b, y <= center ->
        ∀ x ∈ Set.Icc center (2 * center - y),
          2 * center - x ∈ Set.Icc a b)
    (heta : eta ∈ Set.Icc a b) :
    ‖iteratedDeriv k.1 f eta‖ <=
      centeredTaylorDerivMajorant18 jetAbs order18Abs radius k := by
  by_cases hlast : k.1 = 18
  · have hk : k = ⟨18, by decide⟩ := Fin.ext hlast
    subst k
    exact iteratedDeriv_norm_le_centeredTaylorDerivMajorant18_last
      (f := f) (a := a) (b := b) (order18Abs := order18Abs)
      (radius := radius) jetAbs hOrder18 eta heta
  · have hklt : k.1 < 18 := by omega
    have hn : 0 < 18 - k.1 := Nat.sub_pos_of_lt hklt
    have hkn : k.1 + (18 - k.1) = 18 :=
      Nat.add_sub_of_le (Nat.le_of_lt hklt)
    have hRange :=
      iteratedDeriv_norm_le_centeredTaylorDerivMajorant18Range
        (f := f) (a := a) (b := b) (center := center)
        (radius := radius) (order18Abs := order18Abs)
        (eta := eta) (k := k.1) (n := 18 - k.1)
        (jetAbs := jetAbs)
        hn hkn hCenterMem hSmooth hJet hOrder18 hRadius hReflectCell heta
    rw [centeredTaylorDerivMajorant18Range_eq] at hRange
    exact hRange

end Step33
end PSDpd
end Q3
