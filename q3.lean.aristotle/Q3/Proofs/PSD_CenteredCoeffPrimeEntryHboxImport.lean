import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDictionaryBoundsImport
import Q3.Proofs.PSD_CenteredBSplineRBoundsImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 5000000

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeEntryHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffPrimeDictionaryBoundsImport

/-!
Step32 prime-side entry hbox surface.

This module exposes the analytic primary/control `P` entries as the finite
prime kernel profiles generated from the active dictionary.  The remaining
hbox certificates must prove scalar midpoint-radius enclosures for these
finite sums.
-/

/-- One primary `k=11` finite-prime summand at packet entry `(i,j)`. -/
def primaryK11FinitePrimeProfileTerm
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PrimeWeight n *
    (centeredBSplineR 11
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell) +
      centeredBSplineR 11
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell))

/-- One control `k=9` finite-prime summand at packet entry `(i,j)`. -/
def controlK9FinitePrimeProfileTerm
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  controlK9PrimeWeight n *
    (centeredBSplineR 9
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell) +
      centeredBSplineR 9
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell))

/-- Primary `k=11` finite-prime summand as a function of packet-center
difference.  This is the delta-compressed version of
`primaryK11FinitePrimeProfileTerm`. -/
def primaryK11FinitePrimeProfileTermOfDelta
    (δ : Real) (n : PrimeShiftIndexL3) : Real :=
  primaryK11PrimeWeight n *
    (centeredBSplineR 11
        ((δ - primaryK11PrimeShift n) / primaryK11Ell) +
      centeredBSplineR 11
        ((δ + primaryK11PrimeShift n) / primaryK11Ell))

/-- The entry-indexed primary summand is just the delta-compressed summand at
the packet-center difference. -/
theorem primaryK11FinitePrimeProfileTerm_eq_termOfDelta
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    primaryK11FinitePrimeProfileTerm i j n =
      primaryK11FinitePrimeProfileTermOfDelta
        (primaryK11Center j - primaryK11Center i) n := by
  rfl

/-- A primary prime shift is dead for a center difference `δ` if both normalized
`R11` arguments are outside the closed support window used by the current
support-zero lemmas. -/
def primaryK11PrimeShiftIsDead (δ : Real) (n : PrimeShiftIndexL3) : Prop :=
  (((δ - primaryK11PrimeShift n) / primaryK11Ell <= -2) ∨
      (2 <= (δ - primaryK11PrimeShift n) / primaryK11Ell)) ∧
    (((δ + primaryK11PrimeShift n) / primaryK11Ell <= -2) ∨
      (2 <= (δ + primaryK11PrimeShift n) / primaryK11Ell))

/-- Live primary shifts are exactly the complement of the support-zero dead
shifts.  Generated payloads should target this set, not all 98 shifts. -/
def primaryK11PrimeShiftIsLive (δ : Real) (n : PrimeShiftIndexL3) : Prop :=
  ¬ primaryK11PrimeShiftIsDead δ n

/-- Finite live-shift set for the primary direct-profile replay at center
difference `δ`. -/
noncomputable def primaryK11LivePrimeShiftSet (δ : Real) :
    Finset PrimeShiftIndexL3 := by
  classical
  exact Finset.univ.filter (fun n => primaryK11PrimeShiftIsLive δ n)

/-- Primary delta summands outside the live set vanish by compact support. -/
theorem primaryK11FinitePrimeProfileTermOfDelta_eq_zero_of_not_live
    {δ : Real} {n : PrimeShiftIndexL3}
    (hn : n ∉ primaryK11LivePrimeShiftSet δ) :
    primaryK11FinitePrimeProfileTermOfDelta δ n = 0 := by
  classical
  have hnotLive : ¬ primaryK11PrimeShiftIsLive δ n := by
    simpa [primaryK11LivePrimeShiftSet] using hn
  have hdead : primaryK11PrimeShiftIsDead δ n := by
    by_contra hnotDead
    exact hnotLive hnotDead
  rcases hdead with ⟨hminusDead, hplusDead⟩
  have hminusZero :
      centeredBSplineR 11
        ((δ - primaryK11PrimeShift n) / primaryK11Ell) = 0 := by
    rcases hminusDead with hleft | hright
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
          hleft
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
          hright
  have hplusZero :
      centeredBSplineR 11
        ((δ + primaryK11PrimeShift n) / primaryK11Ell) = 0 := by
    rcases hplusDead with hleft | hright
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
          hleft
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
          hright
  simp [primaryK11FinitePrimeProfileTermOfDelta, hminusZero, hplusZero]

/-- The primary finite-prime profile is the full sum of its delta-compressed
summands. -/
theorem primaryK11FinitePrimeProfile_eq_sumOfDelta (δ : Real) :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift δ =
      ∑ n : PrimeShiftIndexL3,
        primaryK11FinitePrimeProfileTermOfDelta δ n := by
  rfl

/-- Primary finite-prime profile reduced to the live prime-shift set.  This is
the first anti-swamp receiver: dead shifts are removed by support, so generated
hboxes only need to cover live shifts. -/
theorem primaryK11FinitePrimeProfile_eq_liveShiftSum (δ : Real) :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift δ =
      ∑ n ∈ (primaryK11LivePrimeShiftSet δ),
        primaryK11FinitePrimeProfileTermOfDelta δ n := by
  rw [primaryK11FinitePrimeProfile_eq_sumOfDelta]
  symm
  exact Finset.sum_subset
    (s₁ := primaryK11LivePrimeShiftSet δ)
    (s₂ := Finset.univ)
    (by intro n _; exact Finset.mem_univ n)
    (by
      intro n _ hn
      exact primaryK11FinitePrimeProfileTermOfDelta_eq_zero_of_not_live
        (δ := δ) hn)

/-- Entry form of the primary live-shift reduction. -/
theorem primaryK11FinitePrimeKernelProfile_entry_eq_liveShiftSum
    (i j : CoeffIndex23) :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) =
      ∑ n ∈ (primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i)),
        primaryK11FinitePrimeProfileTermOfDelta
          (primaryK11Center j - primaryK11Center i) n :=
  primaryK11FinitePrimeProfile_eq_liveShiftSum
    (primaryK11Center j - primaryK11Center i)

/-- Control `k=9` finite-prime summand as a function of packet-center
difference. -/
def controlK9FinitePrimeProfileTermOfDelta
    (δ : Real) (n : PrimeShiftIndexL3) : Real :=
  controlK9PrimeWeight n *
    (centeredBSplineR 9
        ((δ - controlK9PrimeShift n) / controlK9Ell) +
      centeredBSplineR 9
        ((δ + controlK9PrimeShift n) / controlK9Ell))

/-- The entry-indexed control summand is just the delta-compressed summand at
the packet-center difference. -/
theorem controlK9FinitePrimeProfileTerm_eq_termOfDelta
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    controlK9FinitePrimeProfileTerm i j n =
      controlK9FinitePrimeProfileTermOfDelta
        (controlK9Center j - controlK9Center i) n := by
  rfl

/-- A control prime shift is dead for a center difference `δ` if both normalized
`R9` arguments are outside the closed support window. -/
def controlK9PrimeShiftIsDead (δ : Real) (n : PrimeShiftIndexL3) : Prop :=
  (((δ - controlK9PrimeShift n) / controlK9Ell <= -2) ∨
      (2 <= (δ - controlK9PrimeShift n) / controlK9Ell)) ∧
    (((δ + controlK9PrimeShift n) / controlK9Ell <= -2) ∨
      (2 <= (δ + controlK9PrimeShift n) / controlK9Ell))

/-- Live control shifts are exactly the complement of the support-zero dead
shifts. -/
def controlK9PrimeShiftIsLive (δ : Real) (n : PrimeShiftIndexL3) : Prop :=
  ¬ controlK9PrimeShiftIsDead δ n

/-- Finite live-shift set for the control direct-profile replay at center
difference `δ`. -/
noncomputable def controlK9LivePrimeShiftSet (δ : Real) :
    Finset PrimeShiftIndexL3 := by
  classical
  exact Finset.univ.filter (fun n => controlK9PrimeShiftIsLive δ n)

/-- Control delta summands outside the live set vanish by compact support. -/
theorem controlK9FinitePrimeProfileTermOfDelta_eq_zero_of_not_live
    {δ : Real} {n : PrimeShiftIndexL3}
    (hn : n ∉ controlK9LivePrimeShiftSet δ) :
    controlK9FinitePrimeProfileTermOfDelta δ n = 0 := by
  classical
  have hnotLive : ¬ controlK9PrimeShiftIsLive δ n := by
    simpa [controlK9LivePrimeShiftSet] using hn
  have hdead : controlK9PrimeShiftIsDead δ n := by
    by_contra hnotDead
    exact hnotLive hnotDead
  rcases hdead with ⟨hminusDead, hplusDead⟩
  have hminusZero :
      centeredBSplineR 9
        ((δ - controlK9PrimeShift n) / controlK9Ell) = 0 := by
    rcases hminusDead with hleft | hright
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
          hleft
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
          hright
  have hplusZero :
      centeredBSplineR 9
        ((δ + controlK9PrimeShift n) / controlK9Ell) = 0 := by
    rcases hplusDead with hleft | hright
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
          hleft
    · exact
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
          hright
  simp [controlK9FinitePrimeProfileTermOfDelta, hminusZero, hplusZero]

/-- The control finite-prime profile is the full sum of its delta-compressed
summands. -/
theorem controlK9FinitePrimeProfile_eq_sumOfDelta (δ : Real) :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift δ =
      ∑ n : PrimeShiftIndexL3,
        controlK9FinitePrimeProfileTermOfDelta δ n := by
  rfl

/-- Control finite-prime profile reduced to the live prime-shift set. -/
theorem controlK9FinitePrimeProfile_eq_liveShiftSum (δ : Real) :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift δ =
      ∑ n ∈ (controlK9LivePrimeShiftSet δ),
        controlK9FinitePrimeProfileTermOfDelta δ n := by
  rw [controlK9FinitePrimeProfile_eq_sumOfDelta]
  symm
  exact Finset.sum_subset
    (s₁ := controlK9LivePrimeShiftSet δ)
    (s₂ := Finset.univ)
    (by intro n _; exact Finset.mem_univ n)
    (by
      intro n _ hn
      exact controlK9FinitePrimeProfileTermOfDelta_eq_zero_of_not_live
        (δ := δ) hn)

/-- Entry form of the control live-shift reduction. -/
theorem controlK9FinitePrimeKernelProfile_entry_eq_liveShiftSum
    (i j : CoeffIndex23) :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) =
      ∑ n ∈ (controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i)),
        controlK9FinitePrimeProfileTermOfDelta
          (controlK9Center j - controlK9Center i) n :=
  controlK9FinitePrimeProfile_eq_liveShiftSum
    (controlK9Center j - controlK9Center i)

/-- The primary finite-prime profile is the sum of its 98 dictionary terms. -/
theorem primaryK11FinitePrimeKernelProfile_entry_eq_sum
    (i j : CoeffIndex23) :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) =
      ∑ n : PrimeShiftIndexL3, primaryK11FinitePrimeProfileTerm i j n := by
  rfl

/-- The control finite-prime profile is the sum of its 98 dictionary terms. -/
theorem controlK9FinitePrimeKernelProfile_entry_eq_sum
    (i j : CoeffIndex23) :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) =
      ∑ n : PrimeShiftIndexL3, controlK9FinitePrimeProfileTerm i j n := by
  rfl

/-- Primary finite-prime profile entries are compressed by center difference. -/
theorem primaryK11FinitePrimeProfile_depends_on_center_sub
    {i j i' j' : CoeffIndex23}
    (h :
      primaryK11Center j - primaryK11Center i =
        primaryK11Center j' - primaryK11Center i') :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) =
      centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j' - primaryK11Center i') := by
  rw [h]

/-- Primary finite-prime profile entries are compressed by coefficient index delta. -/
theorem primaryK11FinitePrimeProfile_depends_on_index_delta
    {i j i' j' : CoeffIndex23}
    (h : (j.1 : Real) - (i.1 : Real) = (j'.1 : Real) - (i'.1 : Real)) :
    centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) =
      centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j' - primaryK11Center i') := by
  apply primaryK11FinitePrimeProfile_depends_on_center_sub
  rw [primaryK11Center_sub_eq_index_delta,
    primaryK11Center_sub_eq_index_delta]
  rw [h]

/-- Each primary finite-prime summand is compressed by center difference. -/
theorem primaryK11FinitePrimeProfileTerm_depends_on_center_sub
    {i j i' j' : CoeffIndex23} (n : PrimeShiftIndexL3)
    (h :
      primaryK11Center j - primaryK11Center i =
        primaryK11Center j' - primaryK11Center i') :
    primaryK11FinitePrimeProfileTerm i j n =
      primaryK11FinitePrimeProfileTerm i' j' n := by
  unfold primaryK11FinitePrimeProfileTerm
  rw [h]

/-- Control finite-prime profile entries are compressed by center difference. -/
theorem controlK9FinitePrimeProfile_depends_on_center_sub
    {i j i' j' : CoeffIndex23}
    (h :
      controlK9Center j - controlK9Center i =
        controlK9Center j' - controlK9Center i') :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) =
      centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j' - controlK9Center i') := by
  rw [h]

/-- Control finite-prime profile entries are compressed by coefficient index delta. -/
theorem controlK9FinitePrimeProfile_depends_on_index_delta
    {i j i' j' : CoeffIndex23}
    (h : (j.1 : Real) - (i.1 : Real) = (j'.1 : Real) - (i'.1 : Real)) :
    centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) =
      centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j' - controlK9Center i') := by
  apply controlK9FinitePrimeProfile_depends_on_center_sub
  rw [controlK9Center_sub_eq_index_delta,
    controlK9Center_sub_eq_index_delta]
  rw [h]

/-- Each control finite-prime summand is compressed by center difference. -/
theorem controlK9FinitePrimeProfileTerm_depends_on_center_sub
    {i j i' j' : CoeffIndex23} (n : PrimeShiftIndexL3)
    (h :
      controlK9Center j - controlK9Center i =
        controlK9Center j' - controlK9Center i') :
    controlK9FinitePrimeProfileTerm i j n =
      controlK9FinitePrimeProfileTerm i' j' n := by
  unfold controlK9FinitePrimeProfileTerm
  rw [h]

/-- Scalar interval multiplication for one prime-profile term.

If `w`, `x`, and `y` are enclosed by midpoint/radius data, then
`w * (x + y)` is enclosed by the standard product-of-balls radius used by the
generated prime-profile term certificates. -/
private theorem mul_sum_pair_abs_sub_le
    (w wm wr x xm xr y ym yr : Real)
    (hw : |w - wm| ≤ wr)
    (hx : |x - xm| ≤ xr)
    (hy : |y - ym| ≤ yr) :
    |w * (x + y) - wm * (xm + ym)| ≤
      (|wm| + wr) * (xr + yr) + wr * |xm + ym| := by
  have hwr_nonneg : 0 ≤ wr := le_trans (abs_nonneg _) hw
  have hxr_nonneg : 0 ≤ xr := le_trans (abs_nonneg _) hx
  have hyr_nonneg : 0 ≤ yr := le_trans (abs_nonneg _) hy
  have hsr_nonneg : 0 ≤ xr + yr := add_nonneg hxr_nonneg hyr_nonneg
  have hsum :
      |(x + y) - (xm + ym)| ≤ xr + yr := by
    calc
      |(x + y) - (xm + ym)| = |(x - xm) + (y - ym)| := by
        ring_nf
      _ ≤ |x - xm| + |y - ym| := abs_add_le _ _
      _ ≤ xr + yr := add_le_add hx hy
  have hdecomp :
      w * (x + y) - wm * (xm + ym) =
        (w - wm) * ((x + y) - (xm + ym)) +
          (w - wm) * (xm + ym) +
            wm * ((x + y) - (xm + ym)) := by
    ring
  have hprod :
      |w - wm| * |(x + y) - (xm + ym)| ≤ wr * (xr + yr) :=
    mul_le_mul hw hsum (abs_nonneg _) hwr_nonneg
  have hmid :
      |w - wm| * |xm + ym| ≤ wr * |xm + ym| :=
    mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have hcenter :
      |wm| * |(x + y) - (xm + ym)| ≤ |wm| * (xr + yr) :=
    mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  calc
    |w * (x + y) - wm * (xm + ym)| =
        |(w - wm) * ((x + y) - (xm + ym)) +
          (w - wm) * (xm + ym) +
            wm * ((x + y) - (xm + ym))| := by
          rw [hdecomp]
    _ ≤ |(w - wm) * ((x + y) - (xm + ym))| +
          |(w - wm) * (xm + ym)| +
            |wm * ((x + y) - (xm + ym))| := by
          calc
            |(w - wm) * ((x + y) - (xm + ym)) +
              (w - wm) * (xm + ym) +
                wm * ((x + y) - (xm + ym))| ≤
                |(w - wm) * ((x + y) - (xm + ym)) +
                  (w - wm) * (xm + ym)| +
                  |wm * ((x + y) - (xm + ym))| := by
                  exact abs_add_le _ _
            _ ≤ (|(w - wm) * ((x + y) - (xm + ym))| +
                  |(w - wm) * (xm + ym)|) +
                    |wm * ((x + y) - (xm + ym))| := by
                  have hAB :
                      |(w - wm) * ((x + y) - (xm + ym)) +
                        (w - wm) * (xm + ym)| ≤
                        |(w - wm) * ((x + y) - (xm + ym))| +
                          |(w - wm) * (xm + ym)| :=
                    abs_add_le
                      ((w - wm) * ((x + y) - (xm + ym)))
                      ((w - wm) * (xm + ym))
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hAB
                      (|wm * ((x + y) - (xm + ym))|)
            _ = |(w - wm) * ((x + y) - (xm + ym))| +
                  |(w - wm) * (xm + ym)| +
                    |wm * ((x + y) - (xm + ym))| := by
                  ring
    _ = |w - wm| * |(x + y) - (xm + ym)| +
          |w - wm| * |xm + ym| +
            |wm| * |(x + y) - (xm + ym)| := by
          simp [abs_mul]
    _ ≤ wr * (xr + yr) + wr * |xm + ym| + |wm| * (xr + yr) := by
          exact add_le_add (add_le_add hprod hmid) hcenter
    _ = (|wm| + wr) * (xr + yr) + wr * |xm + ym| := by
          ring

/-- Scalar interval multiplication for one product. -/
private theorem mul_abs_sub_le
    (a am ar b bm br : Real)
    (ha : |a - am| ≤ ar)
    (hb : |b - bm| ≤ br) :
    |a * b - am * bm| ≤ (|am| + ar) * br + ar * |bm| := by
  have hzero : |(0 : Real) - 0| ≤ (0 : Real) := by norm_num
  have h := mul_sum_pair_abs_sub_le
    a am ar b bm br 0 0 0 ha hb hzero
  simpa using h

/-- Generated log and exponential-factor hboxes imply an active prime-weight
hbox. -/
theorem activeL3PrimeWeight_hbox_of_log_exp_factor_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| ≤ logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| ≤ expRad n)
    (hmid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hrad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| ≤ weightRad n) :
    ∀ n,
      |activeL3PrimeWeight n - weightMid n| ≤ weightRad n := by
  intro n
  unfold activeL3PrimeWeight
  rw [hmid n]
  exact le_trans
    (mul_abs_sub_le
      (Real.log (activeL3PrimeBase n : Real)) (logMid n) (logRad n)
      (Real.exp (-(activeL3PrimeShift n) / 2)) (expMid n) (expRad n)
      (hlog n) (hexp n))
    (hrad n)

theorem primaryK11PrimeWeight_hbox_of_log_exp_factor_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| ≤ logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| ≤ expRad n)
    (hmid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hrad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| ≤ weightRad n) :
    ∀ n,
      |primaryK11PrimeWeight n - weightMid n| ≤ weightRad n := by
  intro n
  simpa [primaryK11PrimeWeight] using
    activeL3PrimeWeight_hbox_of_log_exp_factor_hboxes
      logMid logRad expMid expRad weightMid weightRad
      hlog hexp hmid hrad n

theorem controlK9PrimeWeight_hbox_of_log_exp_factor_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| ≤ logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| ≤ expRad n)
    (hmid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hrad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| ≤ weightRad n) :
    ∀ n,
      |controlK9PrimeWeight n - weightMid n| ≤ weightRad n := by
  intro n
  simpa [controlK9PrimeWeight] using
    activeL3PrimeWeight_hbox_of_log_exp_factor_hboxes
      logMid logRad expMid expRad weightMid weightRad
      hlog hexp hmid hrad n

/-- Generated cardinal B-spline hboxes imply the primary `centeredBSplineR 11`
minus/plus hboxes for all active prime shifts. -/
theorem primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusCard :
      ∀ i j n,
        |centeredCardinalBSpline (bsplineAutocorrDegree 11)
            (bsplineScale 11 *
              (((primaryK11Center j - primaryK11Center i) -
                primaryK11PrimeShift n) / primaryK11Ell)) -
          minusCardMid i j n| ≤ minusCardRad i j n)
    (hplusCard :
      ∀ i j n,
        |centeredCardinalBSpline (bsplineAutocorrDegree 11)
            (bsplineScale 11 *
              (((primaryK11Center j - primaryK11Center i) +
                primaryK11PrimeShift n) / primaryK11Ell)) -
          plusCardMid i j n| ≤ plusCardRad i j n)
    (hminusMid :
      ∀ i j n,
        minusMid i j n =
          minusCardMid i j n / bsplineAutocorrNorm 11)
    (hminusRad :
      ∀ i j n,
        minusCardRad i j n / bsplineAutocorrNorm 11 ≤ minusRad i j n)
    (hplusMid :
      ∀ i j n,
        plusMid i j n =
          plusCardMid i j n / bsplineAutocorrNorm 11)
    (hplusRad :
      ∀ i j n,
        plusCardRad i j n / bsplineAutocorrNorm 11 ≤ plusRad i j n) :
    (∀ i j n,
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) -
        minusMid i j n| ≤ minusRad i j n) ∧
    (∀ i j n,
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) -
        plusMid i j n| ≤ plusRad i j n) := by
  constructor
  · intro i j n
    rw [hminusMid i j n]
    exact le_trans
      (_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR_hbox_of_cardinal_hbox
        11
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell)
        (minusCardMid i j n) (minusCardRad i j n)
        (hminusCard i j n))
      (hminusRad i j n)
  · intro i j n
    rw [hplusMid i j n]
    exact le_trans
      (_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR_hbox_of_cardinal_hbox
        11
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell)
        (plusCardMid i j n) (plusCardRad i j n)
        (hplusCard i j n))
      (hplusRad i j n)

/-- Generated cardinal B-spline hboxes imply the control `centeredBSplineR 9`
minus/plus hboxes for all active prime shifts. -/
theorem controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_cardinal_hboxes
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusCard :
      ∀ i j n,
        |centeredCardinalBSpline (bsplineAutocorrDegree 9)
            (bsplineScale 9 *
              (((controlK9Center j - controlK9Center i) -
                controlK9PrimeShift n) / controlK9Ell)) -
          minusCardMid i j n| ≤ minusCardRad i j n)
    (hplusCard :
      ∀ i j n,
        |centeredCardinalBSpline (bsplineAutocorrDegree 9)
            (bsplineScale 9 *
              (((controlK9Center j - controlK9Center i) +
                controlK9PrimeShift n) / controlK9Ell)) -
          plusCardMid i j n| ≤ plusCardRad i j n)
    (hminusMid :
      ∀ i j n,
        minusMid i j n =
          minusCardMid i j n / bsplineAutocorrNorm 9)
    (hminusRad :
      ∀ i j n,
        minusCardRad i j n / bsplineAutocorrNorm 9 ≤ minusRad i j n)
    (hplusMid :
      ∀ i j n,
        plusMid i j n =
          plusCardMid i j n / bsplineAutocorrNorm 9)
    (hplusRad :
      ∀ i j n,
        plusCardRad i j n / bsplineAutocorrNorm 9 ≤ plusRad i j n) :
    (∀ i j n,
      |centeredBSplineR 9
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) -
        minusMid i j n| ≤ minusRad i j n) ∧
    (∀ i j n,
      |centeredBSplineR 9
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) -
        plusMid i j n| ≤ plusRad i j n) := by
  constructor
  · intro i j n
    rw [hminusMid i j n]
    exact le_trans
      (_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR_hbox_of_cardinal_hbox
        9
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell)
        (minusCardMid i j n) (minusCardRad i j n)
        (hminusCard i j n))
      (hminusRad i j n)
  · intro i j n
    rw [hplusMid i j n]
    exact le_trans
      (_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR_hbox_of_cardinal_hbox
        9
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell)
        (plusCardMid i j n) (plusCardRad i j n)
        (hplusCard i j n))
      (hplusRad i j n)

/-- Generated truncated-power summand hboxes imply the primary cardinal
B-spline numerator hboxes for all active prime shifts. -/
theorem primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_summand_hboxes
    (minusTermMid minusTermRad plusTermMid plusTermRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusTerm :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 11 + 2) ->
          |_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand
              (bsplineAutocorrDegree 11)
              (bsplineScale 11 *
                (((primaryK11Center j - primaryK11Center i) -
                  primaryK11PrimeShift n) / primaryK11Ell)) m -
            minusTermMid i j n m| ≤ minusTermRad i j n m)
    (hplusTerm :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 11 + 2) ->
          |_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand
              (bsplineAutocorrDegree 11)
              (bsplineScale 11 *
                (((primaryK11Center j - primaryK11Center i) +
                  primaryK11PrimeShift n) / primaryK11Ell)) m -
            plusTermMid i j n m| ≤ plusTermRad i j n m)
    (hminusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            minusTermMid i j n m) = minusCardMid i j n)
    (hminusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            minusTermRad i j n m) ≤ minusCardRad i j n)
    (hplusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            plusTermMid i j n m) = plusCardMid i j n)
    (hplusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            plusTermRad i j n m) ≤ plusCardRad i j n) :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell)) -
        minusCardMid i j n| ≤ minusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell)) -
        plusCardMid i j n| ≤ plusCardRad i j n) := by
  constructor
  · intro i j n
    exact
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSpline_hbox_of_summand_hboxes
        (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell))
        (minusCardMid i j n) (minusCardRad i j n)
        (minusTermMid i j n) (minusTermRad i j n)
        (hminusTerm i j n) (hminusMid i j n) (hminusRad i j n)
  · intro i j n
    exact
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSpline_hbox_of_summand_hboxes
        (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell))
        (plusCardMid i j n) (plusCardRad i j n)
        (plusTermMid i j n) (plusTermRad i j n)
        (hplusTerm i j n) (hplusMid i j n) (hplusRad i j n)

/-- Generated truncated-power summand hboxes imply the control cardinal
B-spline numerator hboxes for all active prime shifts. -/
theorem controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_summand_hboxes
    (minusTermMid minusTermRad plusTermMid plusTermRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusTerm :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 9 + 2) ->
          |_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand
              (bsplineAutocorrDegree 9)
              (bsplineScale 9 *
                (((controlK9Center j - controlK9Center i) -
                  controlK9PrimeShift n) / controlK9Ell)) m -
            minusTermMid i j n m| ≤ minusTermRad i j n m)
    (hplusTerm :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 9 + 2) ->
          |_root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand
              (bsplineAutocorrDegree 9)
              (bsplineScale 9 *
                (((controlK9Center j - controlK9Center i) +
                  controlK9PrimeShift n) / controlK9Ell)) m -
            plusTermMid i j n m| ≤ plusTermRad i j n m)
    (hminusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            minusTermMid i j n m) = minusCardMid i j n)
    (hminusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            minusTermRad i j n m) ≤ minusCardRad i j n)
    (hplusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            plusTermMid i j n m) = plusCardMid i j n)
    (hplusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            plusTermRad i j n m) ≤ plusCardRad i j n) :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell)) -
        minusCardMid i j n| ≤ minusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell)) -
        plusCardMid i j n| ≤ plusCardRad i j n) := by
  constructor
  · intro i j n
    exact
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSpline_hbox_of_summand_hboxes
        (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell))
        (minusCardMid i j n) (minusCardRad i j n)
        (minusTermMid i j n) (minusTermRad i j n)
        (hminusTerm i j n) (hminusMid i j n) (hminusRad i j n)
  · intro i j n
    exact
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSpline_hbox_of_summand_hboxes
        (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell))
        (plusCardMid i j n) (plusCardRad i j n)
        (plusTermMid i j n) (plusTermRad i j n)
        (hplusTerm i j n) (hplusMid i j n) (hplusRad i j n)

/-- Generated positive-part-power hboxes imply the primary cardinal
B-spline numerator hboxes for all active prime shifts.  This is the scalar
receiver that sits below the existing summand receiver. -/
theorem primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_positivePartPower_hboxes
    (minusPowerMid minusPowerRad plusPowerMid plusPowerRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusTermMid minusTermRad plusTermMid plusTermRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusPower :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 11 + 2) ->
          |positivePartPower (bsplineAutocorrDegree 11)
              (bsplineScale 11 *
                  (((primaryK11Center j - primaryK11Center i) -
                    primaryK11PrimeShift n) / primaryK11Ell) +
                (((bsplineAutocorrDegree 11 + 1 : ℕ) : Real) / 2) -
                (m : Real)) -
            minusPowerMid i j n m| ≤ minusPowerRad i j n m)
    (hplusPower :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 11 + 2) ->
          |positivePartPower (bsplineAutocorrDegree 11)
              (bsplineScale 11 *
                  (((primaryK11Center j - primaryK11Center i) +
                    primaryK11PrimeShift n) / primaryK11Ell) +
                (((bsplineAutocorrDegree 11 + 1 : ℕ) : Real) / 2) -
                (m : Real)) -
            plusPowerMid i j n m| ≤ plusPowerRad i j n m)
    (hminusTermMid :
      ∀ i j n m,
        (((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)) *
            minusPowerMid i j n m = minusTermMid i j n m)
    (hminusTermRad :
      ∀ i j n m,
        |((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)| *
            minusPowerRad i j n m ≤ minusTermRad i j n m)
    (hplusTermMid :
      ∀ i j n m,
        (((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)) *
            plusPowerMid i j n m = plusTermMid i j n m)
    (hplusTermRad :
      ∀ i j n m,
        |((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)| *
            plusPowerRad i j n m ≤ plusTermRad i j n m)
    (hminusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            minusTermMid i j n m) = minusCardMid i j n)
    (hminusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            minusTermRad i j n m) ≤ minusCardRad i j n)
    (hplusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            plusTermMid i j n m) = plusCardMid i j n)
    (hplusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
            plusTermRad i j n m) ≤ plusCardRad i j n) :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell)) -
        minusCardMid i j n| ≤ minusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell)) -
        plusCardMid i j n| ≤ plusCardRad i j n) := by
  exact
    primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_summand_hboxes
      minusTermMid minusTermRad plusTermMid plusTermRad
      minusCardMid minusCardRad plusCardMid plusCardRad
      (fun i j n m hm =>
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
          (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell))
          m
          (minusPowerMid i j n m) (minusPowerRad i j n m)
          (minusTermMid i j n m) (minusTermRad i j n m)
          (hminusPower i j n m hm)
          (hminusTermMid i j n m)
          (hminusTermRad i j n m))
      (fun i j n m hm =>
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
          (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell))
          m
          (plusPowerMid i j n m) (plusPowerRad i j n m)
          (plusTermMid i j n m) (plusTermRad i j n m)
          (hplusPower i j n m hm)
          (hplusTermMid i j n m)
          (hplusTermRad i j n m))
      hminusMid hminusRad hplusMid hplusRad

/-- Generated positive-part-power hboxes imply the control cardinal
B-spline numerator hboxes for all active prime shifts. -/
theorem controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_positivePartPower_hboxes
    (minusPowerMid minusPowerRad plusPowerMid plusPowerRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusTermMid minusTermRad plusTermMid plusTermRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> ℕ -> Real)
    (minusCardMid minusCardRad plusCardMid plusCardRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminusPower :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 9 + 2) ->
          |positivePartPower (bsplineAutocorrDegree 9)
              (bsplineScale 9 *
                  (((controlK9Center j - controlK9Center i) -
                    controlK9PrimeShift n) / controlK9Ell) +
                (((bsplineAutocorrDegree 9 + 1 : ℕ) : Real) / 2) -
                (m : Real)) -
            minusPowerMid i j n m| ≤ minusPowerRad i j n m)
    (hplusPower :
      ∀ i j n m,
        m ∈ Finset.range (bsplineAutocorrDegree 9 + 2) ->
          |positivePartPower (bsplineAutocorrDegree 9)
              (bsplineScale 9 *
                  (((controlK9Center j - controlK9Center i) +
                    controlK9PrimeShift n) / controlK9Ell) +
                (((bsplineAutocorrDegree 9 + 1 : ℕ) : Real) / 2) -
                (m : Real)) -
            plusPowerMid i j n m| ≤ plusPowerRad i j n m)
    (hminusTermMid :
      ∀ i j n m,
        (((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)) *
            minusPowerMid i j n m = minusTermMid i j n m)
    (hminusTermRad :
      ∀ i j n m,
        |((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)| *
            minusPowerRad i j n m ≤ minusTermRad i j n m)
    (hplusTermMid :
      ∀ i j n m,
        (((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)) *
            plusPowerMid i j n m = plusTermMid i j n m)
    (hplusTermRad :
      ∀ i j n m,
        |((-1 : Real) ^ m) *
          (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)| *
            plusPowerRad i j n m ≤ plusTermRad i j n m)
    (hminusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            minusTermMid i j n m) = minusCardMid i j n)
    (hminusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            minusTermRad i j n m) ≤ minusCardRad i j n)
    (hplusMid :
      ∀ i j n,
        ((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹) *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            plusTermMid i j n m) = plusCardMid i j n)
    (hplusRad :
      ∀ i j n,
        |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
          ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
            plusTermRad i j n m) ≤ plusCardRad i j n) :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell)) -
        minusCardMid i j n| ≤ minusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell)) -
        plusCardMid i j n| ≤ plusCardRad i j n) := by
  exact
    controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_summand_hboxes
      minusTermMid minusTermRad plusTermMid plusTermRad
      minusCardMid minusCardRad plusCardMid plusCardRad
      (fun i j n m hm =>
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
          (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell))
          m
          (minusPowerMid i j n m) (minusPowerRad i j n m)
          (minusTermMid i j n m) (minusTermRad i j n m)
          (hminusPower i j n m hm)
          (hminusTermMid i j n m)
          (hminusTermRad i j n m))
      (fun i j n m hm =>
        _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
          (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell))
          m
          (plusPowerMid i j n m) (plusPowerRad i j n m)
          (plusTermMid i j n m) (plusTermRad i j n m)
          (hplusPower i j n m hm)
          (hplusTermMid i j n m)
          (hplusTermRad i j n m))
      hminusMid hminusRad hplusMid hplusRad

private theorem activeL3PrimeBase_le_401 (n : PrimeShiftIndexL3) :
    activeL3PrimeBase n <= 401 := by
  native_decide +revert

private theorem activeL3PrimeExponent_le_8 (n : PrimeShiftIndexL3) :
    activeL3PrimeExponent n <= 8 := by
  native_decide +revert

private theorem activeL3PrimeShift_le_3208 (n : PrimeShiftIndexL3) :
    activeL3PrimeShift n <= (3208 : Real) := by
  have hlog_nonneg : 0 <= Real.log (activeL3PrimeBase n : Real) := by
    exact le_of_lt (activeL3PrimeLog_pos n)
  have hlog_self :
      Real.log (activeL3PrimeBase n : Real) <=
        (activeL3PrimeBase n : Real) := by
    exact Real.log_le_self (by positivity)
  have hbase : (activeL3PrimeBase n : Real) <= (401 : Real) := by
    exact_mod_cast activeL3PrimeBase_le_401 n
  have hexp : (activeL3PrimeExponent n : Real) <= (8 : Real) := by
    exact_mod_cast activeL3PrimeExponent_le_8 n
  calc
    activeL3PrimeShift n =
        (activeL3PrimeExponent n : Real) *
          Real.log (activeL3PrimeBase n : Real) := by
          rfl
    _ <= 8 * Real.log (activeL3PrimeBase n : Real) := by
          exact mul_le_mul_of_nonneg_right hexp hlog_nonneg
    _ <= 8 * 401 := by
          exact mul_le_mul_of_nonneg_left (hlog_self.trans hbase) (by norm_num)
    _ = 3208 := by norm_num

private theorem primaryK11Center_abs_le_three (i : CoeffIndex23) :
    |primaryK11Center i| <= (3 : Real) := by
  fin_cases i <;> norm_num [primaryK11Center, activeL3Ell030Delta025Center,
    activeL3Ell030Delta025CenterRatEntry]

private theorem primaryK11Center_sub_abs_le_six (i j : CoeffIndex23) :
    |primaryK11Center j - primaryK11Center i| <= (6 : Real) := by
  calc
    |primaryK11Center j - primaryK11Center i| <=
        |primaryK11Center j| + |primaryK11Center i| := abs_sub _ _
    _ <= 3 + 3 := add_le_add (primaryK11Center_abs_le_three j)
      (primaryK11Center_abs_le_three i)
    _ = 6 := by norm_num

private theorem primaryK11PrimeShift_abs_le_3208 (n : PrimeShiftIndexL3) :
    |primaryK11PrimeShift n| <= (3208 : Real) := by
  have hnonneg : 0 <= primaryK11PrimeShift n := by
    simpa [primaryK11PrimeShift] using activeL3PrimeShift_nonneg n
  rw [abs_of_nonneg hnonneg]
  simpa [primaryK11PrimeShift] using activeL3PrimeShift_le_3208 n

private theorem primaryK11MinusShift_abs_le_3214
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |(primaryK11Center j - primaryK11Center i) - primaryK11PrimeShift n| <=
      (3214 : Real) := by
  calc
    |(primaryK11Center j - primaryK11Center i) - primaryK11PrimeShift n| <=
        |primaryK11Center j - primaryK11Center i| +
          |primaryK11PrimeShift n| := abs_sub _ _
    _ <= 6 + 3208 := add_le_add (primaryK11Center_sub_abs_le_six i j)
      (primaryK11PrimeShift_abs_le_3208 n)
    _ = 3214 := by norm_num

private theorem primaryK11PlusShift_abs_le_3214
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |(primaryK11Center j - primaryK11Center i) + primaryK11PrimeShift n| <=
      (3214 : Real) := by
  have h :=
    abs_sub (primaryK11Center j - primaryK11Center i)
      (-(primaryK11PrimeShift n))
  calc
    |(primaryK11Center j - primaryK11Center i) + primaryK11PrimeShift n| =
        |(primaryK11Center j - primaryK11Center i) -
          (-(primaryK11PrimeShift n))| := by
          ring_nf
    _ <= |primaryK11Center j - primaryK11Center i| +
        |-(primaryK11PrimeShift n)| := h
    _ = |primaryK11Center j - primaryK11Center i| +
        |primaryK11PrimeShift n| := by
          rw [abs_neg]
    _ <= 6 + 3208 := add_le_add (primaryK11Center_sub_abs_le_six i j)
      (primaryK11PrimeShift_abs_le_3208 n)
    _ = 3214 := by norm_num

private theorem primaryK11ScaledMinusShift_abs_le_65000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell)| <= (65000 : Real) := by
  have hell_pos : 0 < primaryK11Ell := primaryK11_hell
  have hdiv :
      |((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell| <=
        (3214 : Real) / ((3 : Real) / 10) := by
    calc
      |((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell| =
          |(primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n| / primaryK11Ell := by
            rw [abs_div, abs_of_pos hell_pos]
      _ <= (3214 : Real) / primaryK11Ell := by
            exact div_le_div_of_nonneg_right
              (primaryK11MinusShift_abs_le_3214 i j n) (le_of_lt hell_pos)
      _ = (3214 : Real) / ((3 : Real) / 10) := by
            norm_num [primaryK11Ell, primaryK11EllRat]
  calc
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell)| =
        |bsplineScale 11| *
          |((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell| := by
          rw [abs_mul]
    _ <= 6 * ((3214 : Real) / ((3 : Real) / 10)) := by
          have hscale : |bsplineScale 11| = (6 : Real) := by
            norm_num [bsplineScale]
          rw [hscale]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ <= 65000 := by norm_num

private theorem primaryK11ScaledPlusShift_abs_le_65000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell)| <= (65000 : Real) := by
  have hell_pos : 0 < primaryK11Ell := primaryK11_hell
  have hdiv :
      |((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell| <=
        (3214 : Real) / ((3 : Real) / 10) := by
    calc
      |((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell| =
          |(primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n| / primaryK11Ell := by
            rw [abs_div, abs_of_pos hell_pos]
      _ <= (3214 : Real) / primaryK11Ell := by
            exact div_le_div_of_nonneg_right
              (primaryK11PlusShift_abs_le_3214 i j n) (le_of_lt hell_pos)
      _ = (3214 : Real) / ((3 : Real) / 10) := by
            norm_num [primaryK11Ell, primaryK11EllRat]
  calc
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell)| =
        |bsplineScale 11| *
          |((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell| := by
          rw [abs_mul]
    _ <= 6 * ((3214 : Real) / ((3 : Real) / 10)) := by
          have hscale : |bsplineScale 11| = (6 : Real) := by
            norm_num [bsplineScale]
          rw [hscale]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ <= 65000 := by norm_num

private theorem primaryK11MinusPowerArg_abs_le_70000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell) +
      (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
      (m : Real)| <= (70000 : Real) := by
  have hmain := primaryK11ScaledMinusShift_abs_le_65000 i j n
  have hm_nat : m < 25 := by
    simpa [bsplineAutocorrDegree] using Finset.mem_range.mp hm
  have hm_le : (m : Real) <= 24 := by
    have hm_le_nat : m <= 24 := Nat.le_of_lt_succ hm_nat
    exact_mod_cast hm_le_nat
  have hm_abs : |(m : Real)| <= 24 := by
    rw [abs_of_nonneg (by positivity : (0 : Real) <= (m : Real))]
    exact hm_le
  have hoff :
      |(((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2)| =
        (12 : Real) := by
    norm_num [bsplineAutocorrDegree]
  calc
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell) +
      (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
      (m : Real)| =
        |bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) +
          (-(m : Real))| := by
          ring_nf
    _ <= |bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell)| +
        |(((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2)| +
        |-(m : Real)| := abs_add_three _ _ _
    _ <= 65000 + 12 + 24 := by
          rw [hoff, abs_neg]
          exact add_le_add (add_le_add hmain le_rfl) hm_abs
    _ <= 70000 := by norm_num

private theorem primaryK11PlusPowerArg_abs_le_70000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell) +
      (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
      (m : Real)| <= (70000 : Real) := by
  have hmain := primaryK11ScaledPlusShift_abs_le_65000 i j n
  have hm_nat : m < 25 := by
    simpa [bsplineAutocorrDegree] using Finset.mem_range.mp hm
  have hm_le : (m : Real) <= 24 := by
    have hm_le_nat : m <= 24 := Nat.le_of_lt_succ hm_nat
    exact_mod_cast hm_le_nat
  have hm_abs : |(m : Real)| <= 24 := by
    rw [abs_of_nonneg (by positivity : (0 : Real) <= (m : Real))]
    exact hm_le
  have hoff :
      |(((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2)| =
        (12 : Real) := by
    norm_num [bsplineAutocorrDegree]
  calc
    |bsplineScale 11 *
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell) +
      (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
      (m : Real)| =
        |bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) +
          (-(m : Real))| := by
          ring_nf
    _ <= |bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell)| +
        |(((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2)| +
        |-(m : Real)| := abs_add_three _ _ _
    _ <= 65000 + 12 + 24 := by
          rw [hoff, abs_neg]
          exact add_le_add (add_le_add hmain le_rfl) hm_abs
    _ <= 70000 := by norm_num

private theorem positivePartPower23_abs_sub_zero_le_pow
    (x B : Real) (hB : 0 <= B) (hx : |x| <= B) :
    |positivePartPower 23 x - 0| <= B ^ 23 := by
  have hx_le : x <= B := (abs_le.mp hx).2
  have hmax_nonneg : 0 <= max x 0 := le_max_right x 0
  have hmax_le : max x 0 <= B := max_le hx_le hB
  have hpow : (max x 0) ^ 23 <= B ^ 23 :=
    pow_le_pow_left₀ hmax_nonneg hmax_le 23
  have hpp_nonneg : 0 <= positivePartPower 23 x := by
    rw [show 23 = 22 + 1 by norm_num, positivePartPower_succ_eq_max]
    exact pow_nonneg hmax_nonneg 23
  calc
    |positivePartPower 23 x - 0| = positivePartPower 23 x := by
      rw [sub_zero, abs_of_nonneg hpp_nonneg]
    _ = (max x 0) ^ 23 := by
      simpa using (positivePartPower_succ_eq_max 22 x)
    _ <= B ^ 23 := hpow

/-- Coarse certified primary scalar midpoint for the degree-23
`positivePartPower` payload.  This is a real enclosure payload, not the final
tight generated table needed for useful matrix radii. -/
def primaryK11PositivePartPowerCoarseMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real := 0

/-- Coarse certified primary scalar radius for the degree-23
`positivePartPower` payload. -/
def primaryK11PositivePartPowerCoarseRad
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real :=
  (70000 : Real) ^ 23

def primaryK11PositivePartPowerCoarseTermMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real := 0

def primaryK11PositivePartPowerCoarseTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 11 + 1) m : Real)| *
      primaryK11PositivePartPowerCoarseRad i j n m

def primaryK11PositivePartPowerCoarseCardMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) : Real := 0

def primaryK11PositivePartPowerCoarseCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 11) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 11 + 2)).sum fun m =>
      primaryK11PositivePartPowerCoarseTermRad i j n m)

private theorem primaryK11PositivePartPowerCoarse_minus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      primaryK11PositivePartPowerCoarseMid i j n m| <=
        primaryK11PositivePartPowerCoarseRad i j n m := by
  have h :=
    positivePartPower23_abs_sub_zero_le_pow
      (bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real))
      (70000 : Real) (by norm_num)
      (primaryK11MinusPowerArg_abs_le_70000 i j n m hm)
  simpa [bsplineAutocorrDegree, primaryK11PositivePartPowerCoarseMid,
    primaryK11PositivePartPowerCoarseRad] using h

private theorem primaryK11PositivePartPowerCoarse_plus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 11 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 11)
        (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) +
          (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      primaryK11PositivePartPowerCoarseMid i j n m| <=
        primaryK11PositivePartPowerCoarseRad i j n m := by
  have h :=
    positivePartPower23_abs_sub_zero_le_pow
      (bsplineScale 11 *
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) +
        (((bsplineAutocorrDegree 11 + 1 : Nat) : Real) / 2) -
        (m : Real))
      (70000 : Real) (by norm_num)
      (primaryK11PlusPowerArg_abs_le_70000 i j n m hm)
  simpa [bsplineAutocorrDegree, primaryK11PositivePartPowerCoarseMid,
    primaryK11PositivePartPowerCoarseRad] using h

/-- Concrete primary `k=11` cardinal numerator hbox produced from a coarse
certified `positivePartPower` payload.  The radius is deliberately coarse and
serves as a compiled Step33 payload-integration witness; the tight generated
payload remains the next numerical-data target. -/
theorem primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_coarse_positivePartPower_payload :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell)) -
        primaryK11PositivePartPowerCoarseCardMid i j n| <=
          primaryK11PositivePartPowerCoarseCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 11)
          (bsplineScale 11 *
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell)) -
        primaryK11PositivePartPowerCoarseCardMid i j n| <=
          primaryK11PositivePartPowerCoarseCardRad i j n) := by
  exact
    primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_positivePartPower_hboxes
      primaryK11PositivePartPowerCoarseMid
      primaryK11PositivePartPowerCoarseRad
      primaryK11PositivePartPowerCoarseMid
      primaryK11PositivePartPowerCoarseRad
      primaryK11PositivePartPowerCoarseTermMid
      primaryK11PositivePartPowerCoarseTermRad
      primaryK11PositivePartPowerCoarseTermMid
      primaryK11PositivePartPowerCoarseTermRad
      primaryK11PositivePartPowerCoarseCardMid
      primaryK11PositivePartPowerCoarseCardRad
      primaryK11PositivePartPowerCoarseCardMid
      primaryK11PositivePartPowerCoarseCardRad
      primaryK11PositivePartPowerCoarse_minus_hbox
      primaryK11PositivePartPowerCoarse_plus_hbox
      (fun i j n m => by
        simp [primaryK11PositivePartPowerCoarseMid,
          primaryK11PositivePartPowerCoarseTermMid])
      (fun i j n m => by
        rw [primaryK11PositivePartPowerCoarseTermRad]
      )
      (fun i j n m => by
        simp [primaryK11PositivePartPowerCoarseMid,
          primaryK11PositivePartPowerCoarseTermMid])
      (fun i j n m => by
        rw [primaryK11PositivePartPowerCoarseTermRad]
      )
      (fun i j n => by
        simp [primaryK11PositivePartPowerCoarseTermMid,
          primaryK11PositivePartPowerCoarseCardMid])
      (fun i j n => by
        rw [primaryK11PositivePartPowerCoarseCardRad])
      (fun i j n => by
        simp [primaryK11PositivePartPowerCoarseTermMid,
          primaryK11PositivePartPowerCoarseCardMid])
      (fun i j n => by
        rw [primaryK11PositivePartPowerCoarseCardRad])

private theorem controlK9Center_abs_le_three (i : CoeffIndex23) :
    |controlK9Center i| <= (3 : Real) := by
  simpa [controlK9Center, primaryK11Center] using
    primaryK11Center_abs_le_three i

private theorem controlK9Center_sub_abs_le_six (i j : CoeffIndex23) :
    |controlK9Center j - controlK9Center i| <= (6 : Real) := by
  calc
    |controlK9Center j - controlK9Center i| <=
        |controlK9Center j| + |controlK9Center i| := abs_sub _ _
    _ <= 3 + 3 := add_le_add (controlK9Center_abs_le_three j)
      (controlK9Center_abs_le_three i)
    _ = 6 := by norm_num

private theorem controlK9PrimeShift_abs_le_3208 (n : PrimeShiftIndexL3) :
    |controlK9PrimeShift n| <= (3208 : Real) := by
  simpa [controlK9PrimeShift, primaryK11PrimeShift] using
    primaryK11PrimeShift_abs_le_3208 n

private theorem controlK9MinusShift_abs_le_3214
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |(controlK9Center j - controlK9Center i) - controlK9PrimeShift n| <=
      (3214 : Real) := by
  calc
    |(controlK9Center j - controlK9Center i) - controlK9PrimeShift n| <=
        |controlK9Center j - controlK9Center i| +
          |controlK9PrimeShift n| := abs_sub _ _
    _ <= 6 + 3208 := add_le_add (controlK9Center_sub_abs_le_six i j)
      (controlK9PrimeShift_abs_le_3208 n)
    _ = 3214 := by norm_num

private theorem controlK9PlusShift_abs_le_3214
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |(controlK9Center j - controlK9Center i) + controlK9PrimeShift n| <=
      (3214 : Real) := by
  have h :=
    abs_sub (controlK9Center j - controlK9Center i)
      (-(controlK9PrimeShift n))
  calc
    |(controlK9Center j - controlK9Center i) + controlK9PrimeShift n| =
        |(controlK9Center j - controlK9Center i) -
          (-(controlK9PrimeShift n))| := by
          ring_nf
    _ <= |controlK9Center j - controlK9Center i| +
        |-(controlK9PrimeShift n)| := h
    _ = |controlK9Center j - controlK9Center i| +
        |controlK9PrimeShift n| := by
          rw [abs_neg]
    _ <= 6 + 3208 := add_le_add (controlK9Center_sub_abs_le_six i j)
      (controlK9PrimeShift_abs_le_3208 n)
    _ = 3214 := by norm_num

private theorem controlK9ScaledMinusShift_abs_le_65000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell)| <= (65000 : Real) := by
  have hell_pos : 0 < controlK9Ell := controlK9_hell
  have hdiv :
      |((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell| <=
        (3214 : Real) / ((3 : Real) / 10) := by
    calc
      |((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell| =
          |(controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n| / controlK9Ell := by
            rw [abs_div, abs_of_pos hell_pos]
      _ <= (3214 : Real) / controlK9Ell := by
            exact div_le_div_of_nonneg_right
              (controlK9MinusShift_abs_le_3214 i j n) (le_of_lt hell_pos)
      _ = (3214 : Real) / ((3 : Real) / 10) := by
            norm_num [controlK9Ell, controlK9EllRat]
  calc
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell)| =
        |bsplineScale 9| *
          |((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell| := by
          rw [abs_mul]
    _ <= 5 * ((3214 : Real) / ((3 : Real) / 10)) := by
          have hscale : |bsplineScale 9| = (5 : Real) := by
            norm_num [bsplineScale]
          rw [hscale]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ <= 65000 := by norm_num

private theorem controlK9ScaledPlusShift_abs_le_65000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell)| <= (65000 : Real) := by
  have hell_pos : 0 < controlK9Ell := controlK9_hell
  have hdiv :
      |((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell| <=
        (3214 : Real) / ((3 : Real) / 10) := by
    calc
      |((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell| =
          |(controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n| / controlK9Ell := by
            rw [abs_div, abs_of_pos hell_pos]
      _ <= (3214 : Real) / controlK9Ell := by
            exact div_le_div_of_nonneg_right
              (controlK9PlusShift_abs_le_3214 i j n) (le_of_lt hell_pos)
      _ = (3214 : Real) / ((3 : Real) / 10) := by
            norm_num [controlK9Ell, controlK9EllRat]
  calc
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell)| =
        |bsplineScale 9| *
          |((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell| := by
          rw [abs_mul]
    _ <= 5 * ((3214 : Real) / ((3 : Real) / 10)) := by
          have hscale : |bsplineScale 9| = (5 : Real) := by
            norm_num [bsplineScale]
          rw [hscale]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ <= 65000 := by norm_num

private theorem controlK9MinusPowerArg_abs_le_70000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell) +
      (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
      (m : Real)| <= (70000 : Real) := by
  have hmain := controlK9ScaledMinusShift_abs_le_65000 i j n
  have hm_nat : m < 21 := by
    simpa [bsplineAutocorrDegree] using Finset.mem_range.mp hm
  have hm_le : (m : Real) <= 20 := by
    have hm_le_nat : m <= 20 := Nat.le_of_lt_succ hm_nat
    exact_mod_cast hm_le_nat
  have hm_abs : |(m : Real)| <= 20 := by
    rw [abs_of_nonneg (by positivity : (0 : Real) <= (m : Real))]
    exact hm_le
  have hoff :
      |(((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2)| =
        (10 : Real) := by
    norm_num [bsplineAutocorrDegree]
  calc
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell) +
      (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
      (m : Real)| =
        |bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) +
          (-(m : Real))| := by
          ring_nf
    _ <= |bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell)| +
        |(((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2)| +
        |-(m : Real)| := abs_add_three _ _ _
    _ <= 65000 + 10 + 20 := by
          rw [hoff, abs_neg]
          exact add_le_add (add_le_add hmain le_rfl) hm_abs
    _ <= 70000 := by norm_num

private theorem controlK9PlusPowerArg_abs_le_70000
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell) +
      (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
      (m : Real)| <= (70000 : Real) := by
  have hmain := controlK9ScaledPlusShift_abs_le_65000 i j n
  have hm_nat : m < 21 := by
    simpa [bsplineAutocorrDegree] using Finset.mem_range.mp hm
  have hm_le : (m : Real) <= 20 := by
    have hm_le_nat : m <= 20 := Nat.le_of_lt_succ hm_nat
    exact_mod_cast hm_le_nat
  have hm_abs : |(m : Real)| <= 20 := by
    rw [abs_of_nonneg (by positivity : (0 : Real) <= (m : Real))]
    exact hm_le
  have hoff :
      |(((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2)| =
        (10 : Real) := by
    norm_num [bsplineAutocorrDegree]
  calc
    |bsplineScale 9 *
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell) +
      (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
      (m : Real)| =
        |bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) +
          (-(m : Real))| := by
          ring_nf
    _ <= |bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell)| +
        |(((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2)| +
        |-(m : Real)| := abs_add_three _ _ _
    _ <= 65000 + 10 + 20 := by
          rw [hoff, abs_neg]
          exact add_le_add (add_le_add hmain le_rfl) hm_abs
    _ <= 70000 := by norm_num

private theorem positivePartPower19_abs_sub_zero_le_pow
    (x B : Real) (hB : 0 <= B) (hx : |x| <= B) :
    |positivePartPower 19 x - 0| <= B ^ 19 := by
  have hx_le : x <= B := (abs_le.mp hx).2
  have hmax_nonneg : 0 <= max x 0 := le_max_right x 0
  have hmax_le : max x 0 <= B := max_le hx_le hB
  have hpow : (max x 0) ^ 19 <= B ^ 19 :=
    pow_le_pow_left₀ hmax_nonneg hmax_le 19
  have hpp_nonneg : 0 <= positivePartPower 19 x := by
    rw [show 19 = 18 + 1 by norm_num, positivePartPower_succ_eq_max]
    exact pow_nonneg hmax_nonneg 19
  calc
    |positivePartPower 19 x - 0| = positivePartPower 19 x := by
      rw [sub_zero, abs_of_nonneg hpp_nonneg]
    _ = (max x 0) ^ 19 := by
      simpa using (positivePartPower_succ_eq_max 18 x)
    _ <= B ^ 19 := hpow

def controlK9PositivePartPowerCoarseMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real := 0

def controlK9PositivePartPowerCoarseRad
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real :=
  (70000 : Real) ^ 19

def controlK9PositivePartPowerCoarseTermMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) (_m : Nat) : Real := 0

def controlK9PositivePartPowerCoarseTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree 9 + 1) m : Real)| *
      controlK9PositivePartPowerCoarseRad i j n m

def controlK9PositivePartPowerCoarseCardMid
    (_i _j : CoeffIndex23) (_n : PrimeShiftIndexL3) : Real := 0

def controlK9PositivePartPowerCoarseCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree 9) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree 9 + 2)).sum fun m =>
      controlK9PositivePartPowerCoarseTermRad i j n m)

private theorem controlK9PositivePartPowerCoarse_minus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      controlK9PositivePartPowerCoarseMid i j n m| <=
        controlK9PositivePartPowerCoarseRad i j n m := by
  have h :=
    positivePartPower19_abs_sub_zero_le_pow
      (bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real))
      (70000 : Real) (by norm_num)
      (controlK9MinusPowerArg_abs_le_70000 i j n m hm)
  simpa [bsplineAutocorrDegree, controlK9PositivePartPowerCoarseMid,
    controlK9PositivePartPowerCoarseRad] using h

private theorem controlK9PositivePartPowerCoarse_plus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (hm : m ∈ Finset.range (bsplineAutocorrDegree 9 + 2)) :
    |positivePartPower (bsplineAutocorrDegree 9)
        (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) +
          (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      controlK9PositivePartPowerCoarseMid i j n m| <=
        controlK9PositivePartPowerCoarseRad i j n m := by
  have h :=
    positivePartPower19_abs_sub_zero_le_pow
      (bsplineScale 9 *
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) +
        (((bsplineAutocorrDegree 9 + 1 : Nat) : Real) / 2) -
        (m : Real))
      (70000 : Real) (by norm_num)
      (controlK9PlusPowerArg_abs_le_70000 i j n m hm)
  simpa [bsplineAutocorrDegree, controlK9PositivePartPowerCoarseMid,
    controlK9PositivePartPowerCoarseRad] using h

/-- Concrete control `k=9` cardinal numerator hbox produced from the same
coarse certified `positivePartPower` payload shape as the primary block. -/
theorem controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_coarse_positivePartPower_payload :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell)) -
        controlK9PositivePartPowerCoarseCardMid i j n| <=
          controlK9PositivePartPowerCoarseCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree 9)
          (bsplineScale 9 *
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell)) -
        controlK9PositivePartPowerCoarseCardMid i j n| <=
          controlK9PositivePartPowerCoarseCardRad i j n) := by
  exact
    controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_positivePartPower_hboxes
      controlK9PositivePartPowerCoarseMid
      controlK9PositivePartPowerCoarseRad
      controlK9PositivePartPowerCoarseMid
      controlK9PositivePartPowerCoarseRad
      controlK9PositivePartPowerCoarseTermMid
      controlK9PositivePartPowerCoarseTermRad
      controlK9PositivePartPowerCoarseTermMid
      controlK9PositivePartPowerCoarseTermRad
      controlK9PositivePartPowerCoarseCardMid
      controlK9PositivePartPowerCoarseCardRad
      controlK9PositivePartPowerCoarseCardMid
      controlK9PositivePartPowerCoarseCardRad
      controlK9PositivePartPowerCoarse_minus_hbox
      controlK9PositivePartPowerCoarse_plus_hbox
      (fun i j n m => by
        simp [controlK9PositivePartPowerCoarseMid,
          controlK9PositivePartPowerCoarseTermMid])
      (fun i j n m => by
        rw [controlK9PositivePartPowerCoarseTermRad]
      )
      (fun i j n m => by
        simp [controlK9PositivePartPowerCoarseMid,
          controlK9PositivePartPowerCoarseTermMid])
      (fun i j n m => by
        rw [controlK9PositivePartPowerCoarseTermRad]
      )
      (fun i j n => by
        simp [controlK9PositivePartPowerCoarseTermMid,
          controlK9PositivePartPowerCoarseCardMid])
      (fun i j n => by
        rw [controlK9PositivePartPowerCoarseCardRad])
      (fun i j n => by
        simp [controlK9PositivePartPowerCoarseTermMid,
          controlK9PositivePartPowerCoarseCardMid])
      (fun i j n => by
        rw [controlK9PositivePartPowerCoarseCardRad])

/-- Termwise midpoint/radius certificates imply the primary finite-prime
profile hbox.  The generator still has to supply the term tables and the
termwise scalar proofs. -/
theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        |primaryK11FinitePrimeProfileTerm i j n - termMid i j n| ≤
          termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ primaryK11PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j := by
  intro i j
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
        ∑ n : PrimeShiftIndexL3,
          (primaryK11FinitePrimeProfileTerm i j n - termMid i j n) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
          (∑ n : PrimeShiftIndexL3, primaryK11FinitePrimeProfileTerm i j n) -
            ∑ n : PrimeShiftIndexL3, termMid i j n := by
            rw [primaryK11FinitePrimeKernelProfile_entry_eq_sum, hmid i j]
      _ = ∑ n : PrimeShiftIndexL3,
          (primaryK11FinitePrimeProfileTerm i j n - termMid i j n) := by
            rw [Finset.sum_sub_distrib]
  calc
    |centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) -
      primaryK11P i j| =
        |∑ n : PrimeShiftIndexL3,
          (primaryK11FinitePrimeProfileTerm i j n - termMid i j n)| := by
          rw [hdiff]
    _ ≤ ∑ n : PrimeShiftIndexL3,
        |primaryK11FinitePrimeProfileTerm i j n - termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n : PrimeShiftIndexL3, termRad i j n := by
          exact Finset.sum_le_sum (fun n _ => hterm i j n)
    _ ≤ primaryK11PRadius i j := hrad i j

/-- Primary term hboxes follow from generated weight hboxes and the two
`centeredBSplineR 11` hboxes for the minus/plus prime shifts. -/
theorem primaryK11FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |primaryK11PrimeWeight n - weightMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (hmid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (hrad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n) :
    ∀ i j n,
      |primaryK11FinitePrimeProfileTerm i j n - termMid i j n| ≤
        termRad i j n := by
  intro i j n
  unfold primaryK11FinitePrimeProfileTerm
  rw [hmid i j n]
  exact le_trans
    (mul_sum_pair_abs_sub_le
      (primaryK11PrimeWeight n) (weightMid n) (weightRad n)
      (centeredBSplineR 11
        (((primaryK11Center j - primaryK11Center i) -
          primaryK11PrimeShift n) / primaryK11Ell))
      (minusMid i j n) (minusRad i j n)
      (centeredBSplineR 11
        (((primaryK11Center j - primaryK11Center i) +
          primaryK11PrimeShift n) / primaryK11Ell))
      (plusMid i j n) (plusRad i j n)
      (hweight n) (hminus i j n) (hplus i j n))
    (hrad i j n)

/-- Primary `k=11` analytic prime entries are the finite prime kernel profile
on the active packet centers. -/
theorem primaryK11AnalyticP_entry (i j : CoeffIndex23) :
    primaryK11AnalyticP i j =
      centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) := by
  simp [primaryK11AnalyticP, primaryK11CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineFinitePrimePacketCoeffKernelData]

/-- Primary analytic `P` entries with the same center difference are equal. -/
theorem primaryK11AnalyticP_entry_depends_on_center_sub
    {i j i' j' : CoeffIndex23}
    (h :
      primaryK11Center j - primaryK11Center i =
        primaryK11Center j' - primaryK11Center i') :
    primaryK11AnalyticP i j = primaryK11AnalyticP i' j' := by
  rw [primaryK11AnalyticP_entry i j, primaryK11AnalyticP_entry i' j']
  exact primaryK11FinitePrimeProfile_depends_on_center_sub h

/-- Primary analytic `P` entries with the same coefficient index delta are equal. -/
theorem primaryK11AnalyticP_entry_depends_on_index_delta
    {i j i' j' : CoeffIndex23}
    (h : (j.1 : Real) - (i.1 : Real) = (j'.1 : Real) - (i'.1 : Real)) :
    primaryK11AnalyticP i j = primaryK11AnalyticP i' j' := by
  rw [primaryK11AnalyticP_entry i j, primaryK11AnalyticP_entry i' j']
  exact primaryK11FinitePrimeProfile_depends_on_index_delta h

/-- Once the finite prime profile has a scalar entry enclosure, it gives the
primary analytic `P` entry hbox required by the active Step32 certificate. -/
theorem primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (hprofile :
      ∀ i j : CoeffIndex23,
        |centeredBSplineFinitePrimeKernelProfile
            11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
            (primaryK11Center j - primaryK11Center i) -
          primaryK11P i j| ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  intro i j
  simpa [primaryK11AnalyticP_entry i j] using hprofile i j

/-- Live-shift midpoint/radius certificates imply the primary finite-prime
profile hbox.  This is the delta/live-support replacement for the full 98-term
termwise receiver. -/
theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
          |primaryK11FinitePrimeProfileTermOfDelta
              (primaryK11Center j - primaryK11Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termRad i j n) ≤ primaryK11PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j := by
  intro i j
  let live := primaryK11LivePrimeShiftSet
    (primaryK11Center j - primaryK11Center i)
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
        ∑ n ∈ live,
          (primaryK11FinitePrimeProfileTermOfDelta
            (primaryK11Center j - primaryK11Center i) n -
            termMid i j n) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
          (∑ n ∈ live,
            primaryK11FinitePrimeProfileTermOfDelta
              (primaryK11Center j - primaryK11Center i) n) -
            ∑ n ∈ live, termMid i j n := by
            rw [primaryK11FinitePrimeKernelProfile_entry_eq_liveShiftSum, hmid i j]
      _ = ∑ n ∈ live,
          (primaryK11FinitePrimeProfileTermOfDelta
            (primaryK11Center j - primaryK11Center i) n -
            termMid i j n) := by
            rw [Finset.sum_sub_distrib]
  calc
    |centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) -
      primaryK11P i j| =
        |∑ n ∈ live,
          (primaryK11FinitePrimeProfileTermOfDelta
            (primaryK11Center j - primaryK11Center i) n -
            termMid i j n)| := by
          rw [hdiff]
    _ ≤ ∑ n ∈ live,
        |primaryK11FinitePrimeProfileTermOfDelta
          (primaryK11Center j - primaryK11Center i) n -
          termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ live, termRad i j n := by
          exact Finset.sum_le_sum (fun n hn => hterm i j n hn)
    _ ≤ primaryK11PRadius i j := hrad i j

/-- Live-shift midpoint/radius certificates imply the final primary analytic
`P` hbox field. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
          |primaryK11FinitePrimeProfileTermOfDelta
              (primaryK11Center j - primaryK11Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termRad i j n) ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (primaryK11FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes
      termMid termRad hterm hmid hrad)

/-- Generated primary delta/live finite-profile payload obligation.  This is
the landing surface for the next replay generator: it must provide hboxes only
for live prime shifts, plus exact midpoint and radius sum checks. -/
def primaryK11DeltaLiveFinitePrimeProfilePayloadHbox : Prop :=
  ∃ termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real,
    (∀ i j n,
      n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
        |primaryK11FinitePrimeProfileTermOfDelta
            (primaryK11Center j - primaryK11Center i) n -
          termMid i j n| ≤ termRad i j n) ∧
    (∀ i j,
      (∑ n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i),
        termMid i j n) = primaryK11P i j) ∧
    (∀ i j,
      (∑ n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i),
        termRad i j n) ≤ primaryK11PRadius i j)

/-- A generated primary delta/live payload feeds the analytic `P` hbox. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_payload
    (hpayload : primaryK11DeltaLiveFinitePrimeProfilePayloadHbox) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  rcases hpayload with ⟨termMid, termRad, hterm, hmid, hrad⟩
  exact
    primaryK11AnalyticP_entry_hbox_of_delta_live_hboxes
      termMid termRad hterm hmid hrad

/-- Live-shift midpoint/radius certificates with center error imply the primary
finite-prime profile hbox.  This is the corrected 1024-bit audit contract:
the generated payload may have a small midpoint mismatch, provided that the
mismatch plus the live term-radius sum stays inside the imported `P` radius. -/
theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes_with_center_error
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
          |primaryK11FinitePrimeProfileTermOfDelta
              (primaryK11Center j - primaryK11Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termRad i j n) ≤ primaryK11PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j := by
  intro i j
  let live := primaryK11LivePrimeShiftSet
    (primaryK11Center j - primaryK11Center i)
  let actual := fun n =>
    primaryK11FinitePrimeProfileTermOfDelta
      (primaryK11Center j - primaryK11Center i) n
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
        ((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
          ((∑ n ∈ live, termMid i j n) - primaryK11P i j) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j =
          (∑ n ∈ live, actual n) - primaryK11P i j := by
            rw [primaryK11FinitePrimeKernelProfile_entry_eq_liveShiftSum]
      _ = ((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
            ((∑ n ∈ live, termMid i j n) - primaryK11P i j) := by
            ring
  have hsum :
      |(∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n| ≤
        ∑ n ∈ live, termRad i j n := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ n ∈ live, (actual n - termMid i j n)| ≤
          ∑ n ∈ live, |actual n - termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ live, termRad i j n := by
          exact Finset.sum_le_sum (fun n hn => hterm i j n hn)
  calc
    |centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) -
      primaryK11P i j| =
        |((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
          ((∑ n ∈ live, termMid i j n) - primaryK11P i j)| := by
          rw [hdiff]
    _ ≤ |(∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n| +
        |(∑ n ∈ live, termMid i j n) - primaryK11P i j| := by
          exact abs_add_le _ _
    _ ≤ (∑ n ∈ live, termRad i j n) +
        |(∑ n ∈ live, termMid i j n) - primaryK11P i j| := by
          exact add_le_add_left hsum _
    _ = |(∑ n ∈ live, termMid i j n) - primaryK11P i j| +
        (∑ n ∈ live, termRad i j n) := by
          ring
    _ ≤ primaryK11PRadius i j := by
          simpa [live] using hbound i j

/-- Live-shift midpoint/radius certificates with center error imply the final
primary analytic `P` hbox field. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_hboxes_with_center_error
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
          |primaryK11FinitePrimeProfileTermOfDelta
              (primaryK11Center j - primaryK11Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          termRad i j n) ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (primaryK11FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes_with_center_error
      termMid termRad hterm hbound)

/-- Generated primary delta/live finite-profile payload obligation using the
corrected center-error containment contract from the 1024-bit audit. -/
def primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError : Prop :=
  ∃ termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real,
    (∀ i j n,
      n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
        |primaryK11FinitePrimeProfileTermOfDelta
            (primaryK11Center j - primaryK11Center i) n -
          termMid i j n| ≤ termRad i j n) ∧
    (∀ i j,
      |(∑ n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i),
        termMid i j n) - primaryK11P i j| +
        (∑ n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i),
        termRad i j n) ≤ primaryK11PRadius i j)

/-- A generated primary delta/live center-error payload feeds the analytic `P`
hbox. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
    (hpayload : primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  rcases hpayload with ⟨termMid, termRad, hterm, hbound⟩
  exact
    primaryK11AnalyticP_entry_hbox_of_delta_live_hboxes_with_center_error
      termMid termRad hterm hbound

/-- Direct finite-profile midpoint/radius payloads imply the primary profile
hbox against the imported `P/PRadius` matrix.  This is the receiver shape for
the direct Arb profile replay route; unlike the termwise receiver, it does not
sum independent term radii. -/
theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
    (profileMid profileRad : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hprofile :
      ∀ i j,
        |centeredBSplineFinitePrimeKernelProfile
            11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
            (primaryK11Center j - primaryK11Center i) -
          profileMid i j| ≤ profileRad i j)
    (hmid :
      ∀ i j, profileMid i j = primaryK11P i j)
    (hrad :
      ∀ i j, profileRad i j ≤ primaryK11PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j := by
  intro i j
  calc
    |centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) -
      primaryK11P i j| =
        |centeredBSplineFinitePrimeKernelProfile
            11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
            (primaryK11Center j - primaryK11Center i) -
          profileMid i j| := by
          rw [← hmid i j]
    _ ≤ profileRad i j := hprofile i j
    _ ≤ primaryK11PRadius i j := hrad i j

/-- Direct finite-profile midpoint/radius payloads imply the final primary
analytic `P` hbox field. -/
theorem primaryK11AnalyticP_entry_hbox_of_direct_profile_hboxes
    (profileMid profileRad : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hprofile :
      ∀ i j,
        |centeredBSplineFinitePrimeKernelProfile
            11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
            (primaryK11Center j - primaryK11Center i) -
          profileMid i j| ≤ profileRad i j)
    (hmid :
      ∀ i j, profileMid i j = primaryK11P i j)
    (hrad :
      ∀ i j, profileRad i j ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (primaryK11FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
      profileMid profileRad hprofile hmid hrad)

/-- Packaged direct finite-profile certificate for the primary prime-side
`P` hbox.  This is the exact landing surface expected from the generated
profile-level replay engine. -/
structure PrimaryK11DirectFinitePrimeProfileHboxCert where
  profileMid : CoeffIndex23 -> CoeffIndex23 -> Real
  profileRad : CoeffIndex23 -> CoeffIndex23 -> Real
  hprofile :
    ∀ i j,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        profileMid i j| ≤ profileRad i j
  hmid :
    ∀ i j, profileMid i j = primaryK11P i j
  hrad :
    ∀ i j, profileRad i j ≤ primaryK11PRadius i j

/-- The synchronized direct-profile midpoint payload is the imported primary
`P` midpoint matrix. -/
def primaryK11DirectFinitePrimeProfileMid :
    CoeffIndex23 -> CoeffIndex23 -> Real :=
  fun i j => primaryK11P i j

/-- The synchronized direct-profile radius payload is the imported primary
`P` radius matrix. -/
def primaryK11DirectFinitePrimeProfileRad :
    CoeffIndex23 -> CoeffIndex23 -> Real :=
  fun i j => primaryK11PRadius i j

/-- The single generated primary direct-profile payload obligation left after
the imported midpoint/radius fields have been synchronized. -/
def primaryK11DirectFinitePrimeProfilePayloadHbox : Prop :=
  ∀ i j,
    |centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) -
      primaryK11DirectFinitePrimeProfileMid i j| ≤
        primaryK11DirectFinitePrimeProfileRad i j

theorem primaryK11DirectFinitePrimeProfile_mid_eq_imported :
    ∀ i j, primaryK11DirectFinitePrimeProfileMid i j = primaryK11P i j := by
  intro i j
  rfl

theorem primaryK11DirectFinitePrimeProfile_rad_le_imported :
    ∀ i j, primaryK11DirectFinitePrimeProfileRad i j ≤ primaryK11PRadius i j := by
  intro i j
  exact le_rfl

def primaryK11DirectFinitePrimeProfileHboxCert_of_payload_hbox
    (hprofile : primaryK11DirectFinitePrimeProfilePayloadHbox) :
    PrimaryK11DirectFinitePrimeProfileHboxCert where
  profileMid := primaryK11DirectFinitePrimeProfileMid
  profileRad := primaryK11DirectFinitePrimeProfileRad
  hprofile := hprofile
  hmid := primaryK11DirectFinitePrimeProfile_mid_eq_imported
  hrad := primaryK11DirectFinitePrimeProfile_rad_le_imported

theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_direct_profile_cert
    (cert : PrimaryK11DirectFinitePrimeProfileHboxCert) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j :=
  primaryK11FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
    cert.profileMid cert.profileRad cert.hprofile cert.hmid cert.hrad

theorem primaryK11AnalyticP_entry_hbox_of_direct_profile_cert
    (cert : PrimaryK11DirectFinitePrimeProfileHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (primaryK11FinitePrimeKernelProfile_entry_hbox_of_direct_profile_cert cert)

theorem primaryK11AnalyticP_entry_hbox_of_direct_profile_payload_hbox
    (hprofile : primaryK11DirectFinitePrimeProfilePayloadHbox) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_direct_profile_cert
    (primaryK11DirectFinitePrimeProfileHboxCert_of_payload_hbox hprofile)

/-- Termwise midpoint/radius certificates imply the final primary analytic
`P` hbox field. -/
theorem primaryK11AnalyticP_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        |primaryK11FinitePrimeProfileTerm i j n - termMid i j n| ≤
          termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (primaryK11FinitePrimeKernelProfile_entry_hbox_of_term_hboxes
      termMid termRad hterm hmid hrad)

/-- Generated weight and `centeredBSplineR 11` pair hboxes imply the final
primary analytic `P` hbox field once the generator also supplies the term
midpoint/radius sums. -/
theorem primaryK11AnalyticP_entry_hbox_of_weight_and_R_pair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |primaryK11PrimeWeight n - weightMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (htermMid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (htermRad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_term_hboxes termMid termRad
    (primaryK11FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
      weightMid weightRad minusMid minusRad plusMid plusRad termMid termRad
      hweight hminus hplus htermMid htermRad)
    hmid hrad

/-- Generated log, exponential-factor, and `centeredBSplineR 11` pair hboxes
imply the final primary analytic `P` hbox field once the generator supplies
the rational term-sum checks. -/
theorem primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| ≤ logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| ≤ expRad n)
    (hweightMid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hweightRad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (htermMid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (htermRad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_weight_and_R_pair_hboxes
    weightMid weightRad minusMid minusRad plusMid plusRad termMid termRad
    (primaryK11PrimeWeight_hbox_of_log_exp_factor_hboxes
      logMid logRad expMid expRad weightMid weightRad
      hlog hexp hweightMid hweightRad)
    hminus hplus htermMid htermRad hmid hrad

/-- Control `k=9` analytic prime entries are the finite prime kernel profile
on the active packet centers. -/
theorem controlK9AnalyticP_entry (i j : CoeffIndex23) :
    controlK9AnalyticP i j =
      centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) := by
  simp [controlK9AnalyticP, controlK9CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineFinitePrimePacketCoeffKernelData]

/-- Control analytic `P` entries with the same center difference are equal. -/
theorem controlK9AnalyticP_entry_depends_on_center_sub
    {i j i' j' : CoeffIndex23}
    (h :
      controlK9Center j - controlK9Center i =
        controlK9Center j' - controlK9Center i') :
    controlK9AnalyticP i j = controlK9AnalyticP i' j' := by
  rw [controlK9AnalyticP_entry i j, controlK9AnalyticP_entry i' j']
  exact controlK9FinitePrimeProfile_depends_on_center_sub h

/-- Control analytic `P` entries with the same coefficient index delta are equal. -/
theorem controlK9AnalyticP_entry_depends_on_index_delta
    {i j i' j' : CoeffIndex23}
    (h : (j.1 : Real) - (i.1 : Real) = (j'.1 : Real) - (i'.1 : Real)) :
    controlK9AnalyticP i j = controlK9AnalyticP i' j' := by
  rw [controlK9AnalyticP_entry i j, controlK9AnalyticP_entry i' j']
  exact controlK9FinitePrimeProfile_depends_on_index_delta h

/-- Once the finite prime profile has a scalar entry enclosure, it gives the
control analytic `P` entry hbox required by the active Step32 certificate. -/
theorem controlK9AnalyticP_entry_hbox_of_profile_hbox
    (hprofile :
      ∀ i j : CoeffIndex23,
        |centeredBSplineFinitePrimeKernelProfile
            9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
            (controlK9Center j - controlK9Center i) -
          controlK9P i j| ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  intro i j
  simpa [controlK9AnalyticP_entry i j] using hprofile i j

/-- Live-shift midpoint/radius certificates imply the control finite-prime
profile hbox. -/
theorem controlK9FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
          |controlK9FinitePrimeProfileTermOfDelta
              (controlK9Center j - controlK9Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termRad i j n) ≤ controlK9PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j| ≤ controlK9PRadius i j := by
  intro i j
  let live := controlK9LivePrimeShiftSet
    (controlK9Center j - controlK9Center i)
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
        ∑ n ∈ live,
          (controlK9FinitePrimeProfileTermOfDelta
            (controlK9Center j - controlK9Center i) n -
            termMid i j n) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
          (∑ n ∈ live,
            controlK9FinitePrimeProfileTermOfDelta
              (controlK9Center j - controlK9Center i) n) -
            ∑ n ∈ live, termMid i j n := by
            rw [controlK9FinitePrimeKernelProfile_entry_eq_liveShiftSum, hmid i j]
      _ = ∑ n ∈ live,
          (controlK9FinitePrimeProfileTermOfDelta
            (controlK9Center j - controlK9Center i) n -
            termMid i j n) := by
            rw [Finset.sum_sub_distrib]
  calc
    |centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) -
      controlK9P i j| =
        |∑ n ∈ live,
          (controlK9FinitePrimeProfileTermOfDelta
            (controlK9Center j - controlK9Center i) n -
            termMid i j n)| := by
          rw [hdiff]
    _ ≤ ∑ n ∈ live,
        |controlK9FinitePrimeProfileTermOfDelta
          (controlK9Center j - controlK9Center i) n -
          termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ live, termRad i j n := by
          exact Finset.sum_le_sum (fun n hn => hterm i j n hn)
    _ ≤ controlK9PRadius i j := hrad i j

/-- Live-shift midpoint/radius certificates imply the final control analytic
`P` hbox field. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
          |controlK9FinitePrimeProfileTermOfDelta
              (controlK9Center j - controlK9Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termRad i j n) ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_profile_hbox
    (controlK9FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes
      termMid termRad hterm hmid hrad)

/-- Generated control delta/live finite-profile payload obligation. -/
def controlK9DeltaLiveFinitePrimeProfilePayloadHbox : Prop :=
  ∃ termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real,
    (∀ i j n,
      n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
        |controlK9FinitePrimeProfileTermOfDelta
            (controlK9Center j - controlK9Center i) n -
          termMid i j n| ≤ termRad i j n) ∧
    (∀ i j,
      (∑ n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i),
        termMid i j n) = controlK9P i j) ∧
    (∀ i j,
      (∑ n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i),
        termRad i j n) ≤ controlK9PRadius i j)

/-- A generated control delta/live payload feeds the analytic `P` hbox. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_payload
    (hpayload : controlK9DeltaLiveFinitePrimeProfilePayloadHbox) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  rcases hpayload with ⟨termMid, termRad, hterm, hmid, hrad⟩
  exact
    controlK9AnalyticP_entry_hbox_of_delta_live_hboxes
      termMid termRad hterm hmid hrad

/-- Live-shift midpoint/radius certificates with center error imply the control
finite-prime profile hbox. -/
theorem controlK9FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes_with_center_error
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
          |controlK9FinitePrimeProfileTermOfDelta
              (controlK9Center j - controlK9Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termRad i j n) ≤ controlK9PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j| ≤ controlK9PRadius i j := by
  intro i j
  let live := controlK9LivePrimeShiftSet
    (controlK9Center j - controlK9Center i)
  let actual := fun n =>
    controlK9FinitePrimeProfileTermOfDelta
      (controlK9Center j - controlK9Center i) n
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
        ((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
          ((∑ n ∈ live, termMid i j n) - controlK9P i j) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
          (∑ n ∈ live, actual n) - controlK9P i j := by
            rw [controlK9FinitePrimeKernelProfile_entry_eq_liveShiftSum]
      _ = ((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
            ((∑ n ∈ live, termMid i j n) - controlK9P i j) := by
            ring
  have hsum :
      |(∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n| ≤
        ∑ n ∈ live, termRad i j n := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ n ∈ live, (actual n - termMid i j n)| ≤
          ∑ n ∈ live, |actual n - termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ live, termRad i j n := by
          exact Finset.sum_le_sum (fun n hn => hterm i j n hn)
  calc
    |centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) -
      controlK9P i j| =
        |((∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n) +
          ((∑ n ∈ live, termMid i j n) - controlK9P i j)| := by
          rw [hdiff]
    _ ≤ |(∑ n ∈ live, actual n) - ∑ n ∈ live, termMid i j n| +
        |(∑ n ∈ live, termMid i j n) - controlK9P i j| := by
          exact abs_add_le _ _
    _ ≤ (∑ n ∈ live, termRad i j n) +
        |(∑ n ∈ live, termMid i j n) - controlK9P i j| := by
          exact add_le_add_left hsum _
    _ = |(∑ n ∈ live, termMid i j n) - controlK9P i j| +
        (∑ n ∈ live, termRad i j n) := by
          ring
    _ ≤ controlK9PRadius i j := by
          simpa [live] using hbound i j

/-- Live-shift midpoint/radius certificates with center error imply the final
control analytic `P` hbox field. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_hboxes_with_center_error
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
          |controlK9FinitePrimeProfileTermOfDelta
              (controlK9Center j - controlK9Center i) n -
            termMid i j n| ≤ termRad i j n)
    (hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          termRad i j n) ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_profile_hbox
    (controlK9FinitePrimeKernelProfile_entry_hbox_of_delta_live_hboxes_with_center_error
      termMid termRad hterm hbound)

/-- Generated control delta/live finite-profile payload obligation using the
corrected center-error containment contract from the 1024-bit audit. -/
def controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError : Prop :=
  ∃ termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real,
    (∀ i j n,
      n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
        |controlK9FinitePrimeProfileTermOfDelta
            (controlK9Center j - controlK9Center i) n -
          termMid i j n| ≤ termRad i j n) ∧
    (∀ i j,
      |(∑ n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i),
        termMid i j n) - controlK9P i j| +
        (∑ n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i),
        termRad i j n) ≤ controlK9PRadius i j)

/-- A generated control delta/live center-error payload feeds the analytic `P`
hbox. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
    (hpayload : controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  rcases hpayload with ⟨termMid, termRad, hterm, hbound⟩
  exact
    controlK9AnalyticP_entry_hbox_of_delta_live_hboxes_with_center_error
      termMid termRad hterm hbound

/-- Direct finite-profile midpoint/radius payloads imply the control profile
hbox against the imported `P/PRadius` matrix. -/
theorem controlK9FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
    (profileMid profileRad : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hprofile :
      ∀ i j,
        |centeredBSplineFinitePrimeKernelProfile
            9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
            (controlK9Center j - controlK9Center i) -
          profileMid i j| ≤ profileRad i j)
    (hmid :
      ∀ i j, profileMid i j = controlK9P i j)
    (hrad :
      ∀ i j, profileRad i j ≤ controlK9PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j| ≤ controlK9PRadius i j := by
  intro i j
  calc
    |centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) -
      controlK9P i j| =
        |centeredBSplineFinitePrimeKernelProfile
            9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
            (controlK9Center j - controlK9Center i) -
          profileMid i j| := by
          rw [← hmid i j]
    _ ≤ profileRad i j := hprofile i j
    _ ≤ controlK9PRadius i j := hrad i j

/-- Direct finite-profile midpoint/radius payloads imply the final control
analytic `P` hbox field. -/
theorem controlK9AnalyticP_entry_hbox_of_direct_profile_hboxes
    (profileMid profileRad : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hprofile :
      ∀ i j,
        |centeredBSplineFinitePrimeKernelProfile
            9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
            (controlK9Center j - controlK9Center i) -
          profileMid i j| ≤ profileRad i j)
    (hmid :
      ∀ i j, profileMid i j = controlK9P i j)
    (hrad :
      ∀ i j, profileRad i j ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_profile_hbox
    (controlK9FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
      profileMid profileRad hprofile hmid hrad)

/-- Packaged direct finite-profile certificate for the control prime-side
`P` hbox. -/
structure ControlK9DirectFinitePrimeProfileHboxCert where
  profileMid : CoeffIndex23 -> CoeffIndex23 -> Real
  profileRad : CoeffIndex23 -> CoeffIndex23 -> Real
  hprofile :
    ∀ i j,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        profileMid i j| ≤ profileRad i j
  hmid :
    ∀ i j, profileMid i j = controlK9P i j
  hrad :
    ∀ i j, profileRad i j ≤ controlK9PRadius i j

/-- The synchronized direct-profile midpoint payload is the imported control
`P` midpoint matrix. -/
def controlK9DirectFinitePrimeProfileMid :
    CoeffIndex23 -> CoeffIndex23 -> Real :=
  fun i j => controlK9P i j

/-- The synchronized direct-profile radius payload is the imported control
`P` radius matrix. -/
def controlK9DirectFinitePrimeProfileRad :
    CoeffIndex23 -> CoeffIndex23 -> Real :=
  fun i j => controlK9PRadius i j

/-- The single generated control direct-profile payload obligation left after
the imported midpoint/radius fields have been synchronized. -/
def controlK9DirectFinitePrimeProfilePayloadHbox : Prop :=
  ∀ i j,
    |centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) -
      controlK9DirectFinitePrimeProfileMid i j| ≤
        controlK9DirectFinitePrimeProfileRad i j

theorem controlK9DirectFinitePrimeProfile_mid_eq_imported :
    ∀ i j, controlK9DirectFinitePrimeProfileMid i j = controlK9P i j := by
  intro i j
  rfl

theorem controlK9DirectFinitePrimeProfile_rad_le_imported :
    ∀ i j, controlK9DirectFinitePrimeProfileRad i j ≤ controlK9PRadius i j := by
  intro i j
  exact le_rfl

def controlK9DirectFinitePrimeProfileHboxCert_of_payload_hbox
    (hprofile : controlK9DirectFinitePrimeProfilePayloadHbox) :
    ControlK9DirectFinitePrimeProfileHboxCert where
  profileMid := controlK9DirectFinitePrimeProfileMid
  profileRad := controlK9DirectFinitePrimeProfileRad
  hprofile := hprofile
  hmid := controlK9DirectFinitePrimeProfile_mid_eq_imported
  hrad := controlK9DirectFinitePrimeProfile_rad_le_imported

theorem controlK9FinitePrimeKernelProfile_entry_hbox_of_direct_profile_cert
    (cert : ControlK9DirectFinitePrimeProfileHboxCert) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j| ≤ controlK9PRadius i j :=
  controlK9FinitePrimeKernelProfile_entry_hbox_of_direct_profile_hboxes
    cert.profileMid cert.profileRad cert.hprofile cert.hmid cert.hrad

theorem controlK9AnalyticP_entry_hbox_of_direct_profile_cert
    (cert : ControlK9DirectFinitePrimeProfileHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_profile_hbox
    (controlK9FinitePrimeKernelProfile_entry_hbox_of_direct_profile_cert cert)

theorem controlK9AnalyticP_entry_hbox_of_direct_profile_payload_hbox
    (hprofile : controlK9DirectFinitePrimeProfilePayloadHbox) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_direct_profile_cert
    (controlK9DirectFinitePrimeProfileHboxCert_of_payload_hbox hprofile)

/-- Control term hboxes follow from generated weight hboxes and the two
`centeredBSplineR 9` hboxes for the minus/plus prime shifts. -/
theorem controlK9FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |controlK9PrimeWeight n - weightMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (hmid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (hrad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n) :
    ∀ i j n,
      |controlK9FinitePrimeProfileTerm i j n - termMid i j n| ≤
        termRad i j n := by
  intro i j n
  unfold controlK9FinitePrimeProfileTerm
  rw [hmid i j n]
  exact le_trans
    (mul_sum_pair_abs_sub_le
      (controlK9PrimeWeight n) (weightMid n) (weightRad n)
      (centeredBSplineR 9
        (((controlK9Center j - controlK9Center i) -
          controlK9PrimeShift n) / controlK9Ell))
      (minusMid i j n) (minusRad i j n)
      (centeredBSplineR 9
        (((controlK9Center j - controlK9Center i) +
          controlK9PrimeShift n) / controlK9Ell))
      (plusMid i j n) (plusRad i j n)
      (hweight n) (hminus i j n) (hplus i j n))
    (hrad i j n)

/-- Control termwise midpoint/radius certificates imply the control
finite-prime profile hbox. -/
theorem controlK9FinitePrimeKernelProfile_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        |controlK9FinitePrimeProfileTerm i j n - termMid i j n| ≤
          termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ controlK9PRadius i j) :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j| ≤ controlK9PRadius i j := by
  intro i j
  have hdiff :
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
        ∑ n : PrimeShiftIndexL3,
          (controlK9FinitePrimeProfileTerm i j n - termMid i j n) := by
    calc
      centeredBSplineFinitePrimeKernelProfile
          9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
          (controlK9Center j - controlK9Center i) -
        controlK9P i j =
          (∑ n : PrimeShiftIndexL3, controlK9FinitePrimeProfileTerm i j n) -
            ∑ n : PrimeShiftIndexL3, termMid i j n := by
            rw [controlK9FinitePrimeKernelProfile_entry_eq_sum, hmid i j]
      _ = ∑ n : PrimeShiftIndexL3,
          (controlK9FinitePrimeProfileTerm i j n - termMid i j n) := by
            rw [Finset.sum_sub_distrib]
  calc
    |centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) -
      controlK9P i j| =
        |∑ n : PrimeShiftIndexL3,
          (controlK9FinitePrimeProfileTerm i j n - termMid i j n)| := by
          rw [hdiff]
    _ ≤ ∑ n : PrimeShiftIndexL3,
        |controlK9FinitePrimeProfileTerm i j n - termMid i j n| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n : PrimeShiftIndexL3, termRad i j n := by
          exact Finset.sum_le_sum (fun n _ => hterm i j n)
    _ ≤ controlK9PRadius i j := hrad i j

/-- Control termwise midpoint/radius certificates imply the final control
analytic `P` hbox field. -/
theorem controlK9AnalyticP_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hterm :
      ∀ i j n,
        |controlK9FinitePrimeProfileTerm i j n - termMid i j n| ≤
          termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_profile_hbox
    (controlK9FinitePrimeKernelProfile_entry_hbox_of_term_hboxes
      termMid termRad hterm hmid hrad)

/-- Generated weight and `centeredBSplineR 9` pair hboxes imply the final
control analytic `P` hbox field once the generator also supplies the term
midpoint/radius sums. -/
theorem controlK9AnalyticP_entry_hbox_of_weight_and_R_pair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |controlK9PrimeWeight n - weightMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (htermMid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (htermRad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_term_hboxes termMid termRad
    (controlK9FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes
      weightMid weightRad minusMid minusRad plusMid plusRad termMid termRad
      hweight hminus hplus htermMid htermRad)
    hmid hrad

/-- Generated log, exponential-factor, and `centeredBSplineR 9` pair hboxes
imply the final control analytic `P` hbox field once the generator supplies
the rational term-sum checks. -/
theorem controlK9AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| ≤ logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| ≤ expRad n)
    (hweightMid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hweightRad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| ≤ weightRad n)
    (hminus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (htermMid :
      ∀ i j n,
        termMid i j n =
          weightMid n * (minusMid i j n + plusMid i j n))
    (htermRad :
      ∀ i j n,
        (|weightMid n| + weightRad n) *
            (minusRad i j n + plusRad i j n) +
          weightRad n * |minusMid i j n + plusMid i j n| ≤
            termRad i j n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3, termRad i j n) ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius :=
  controlK9AnalyticP_entry_hbox_of_weight_and_R_pair_hboxes
    weightMid weightRad minusMid minusRad plusMid plusRad termMid termRad
    (controlK9PrimeWeight_hbox_of_log_exp_factor_hboxes
      logMid logRad expMid expRad weightMid weightRad
      hlog hexp hweightMid hweightRad)
    hminus hplus htermMid htermRad hmid hrad

end CenteredCoeffPrimeEntryHboxImport
end PSDpd
end Q3
