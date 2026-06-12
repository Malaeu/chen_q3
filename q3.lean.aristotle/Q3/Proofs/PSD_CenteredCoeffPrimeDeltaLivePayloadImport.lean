import Q3.Proofs.PSD_CenteredCoeffEntryHboxImport
import Q3.Proofs.PSD_CenteredCoeffPrimePositivePartTightImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 5000000

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLivePayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

/-!
Step33A.1 delta/live payload adapter.

The tight positive-part-power module already proves the scalar term hboxes
through the cardinal, `R`, and prime-weight receiver chain.  This file isolates
the remaining generated obligation for the live-shift route: exact live
midpoint sums and live radius-sum containment against the imported `P` boxes.
-/

/-- Primary class-A generated fact for the active Step33A contract.

This is the whole primary generated live-sum check in the corrected
center-error form:

`abs(live_mid_sum - imported_P_mid) + live_rad_sum <= imported_P_radius`.
-/
def primaryK11TightLiveCenterErrorSumCheck : Prop :=
  ∀ i j,
    |(∑ n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i),
      primaryK11PositivePartPowerTightPrimeTermMid
        activeL3PrimeWeightMid i j n) - primaryK11P i j| +
      (∑ n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i),
      primaryK11PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
        primaryK11PRadius i j

/-- Control class-A generated fact for the active Step33A contract.

This is the whole control generated live-sum check in the corrected
center-error form:

`abs(live_mid_sum - imported_P_mid) + live_rad_sum <= imported_P_radius`.
-/
def controlK9TightLiveCenterErrorSumCheck : Prop :=
  ∀ i j,
    |(∑ n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i),
      controlK9PositivePartPowerTightPrimeTermMid
        activeL3PrimeWeightMid i j n) - controlK9P i j| +
      (∑ n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i),
      controlK9PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
        controlK9PRadius i j

private theorem center_error_budget_of_sum_interval
    {sumMid importedMid sumRad centerRad radCap importedRad : Real}
    (hlo : importedMid - centerRad ≤ sumMid)
    (hhi : sumMid ≤ importedMid + centerRad)
    (hrad : sumRad ≤ radCap)
    (hbudget : centerRad + radCap ≤ importedRad) :
    |sumMid - importedMid| + sumRad ≤ importedRad := by
  have habs : |sumMid - importedMid| ≤ centerRad := by
    rw [abs_le]
    constructor <;> linarith
  exact (add_le_add habs hrad).trans hbudget

/-- Generated entrywise interval bounds imply the primary named center-error
check.  The generator only has to prove interval endpoints for the live
midpoint sum and live radius sum; this receiver performs the absolute-value
budget algebra once. -/
theorem primaryK11TightLiveCenterErrorSumCheck_of_entry_interval_bounds
    (centerRad radCap : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hlo :
      ∀ i j,
        primaryK11P i j - centerRad i j ≤
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
            primaryK11PositivePartPowerTightPrimeTermMid
              activeL3PrimeWeightMid i j n))
    (hhi :
      ∀ i j,
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
            primaryK11PositivePartPowerTightPrimeTermMid
              activeL3PrimeWeightMid i j n) ≤
            primaryK11P i j + centerRad i j)
    (hrad :
      ∀ i j,
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
            primaryK11PositivePartPowerTightPrimeTermRad
              activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            radCap i j)
    (hbudget :
      ∀ i j, centerRad i j + radCap i j ≤ primaryK11PRadius i j) :
    primaryK11TightLiveCenterErrorSumCheck := by
  intro i j
  exact
    center_error_budget_of_sum_interval
      (hlo i j) (hhi i j) (hrad i j) (hbudget i j)

/-- Generated entrywise interval bounds imply the control named center-error
check. -/
theorem controlK9TightLiveCenterErrorSumCheck_of_entry_interval_bounds
    (centerRad radCap : CoeffIndex23 -> CoeffIndex23 -> Real)
    (hlo :
      ∀ i j,
        controlK9P i j - centerRad i j ≤
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
            controlK9PositivePartPowerTightPrimeTermMid
              activeL3PrimeWeightMid i j n))
    (hhi :
      ∀ i j,
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
            controlK9PositivePartPowerTightPrimeTermMid
              activeL3PrimeWeightMid i j n) ≤
            controlK9P i j + centerRad i j)
    (hrad :
      ∀ i j,
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
            controlK9PositivePartPowerTightPrimeTermRad
              activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            radCap i j)
    (hbudget :
      ∀ i j, centerRad i j + radCap i j ≤ controlK9PRadius i j) :
    controlK9TightLiveCenterErrorSumCheck := by
  intro i j
  exact
    center_error_budget_of_sum_interval
      (hlo i j) (hhi i j) (hrad i j) (hbudget i j)

/-- Primary support classifier from generated shift bounds. -/
theorem primaryK11PrimeShiftIsDead_of_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ primaryK11PrimeShift n)
    (hhi : primaryK11PrimeShift n ≤ hi)
    (hminus :
      ((δ - lo) / primaryK11Ell ≤ -2) ∨
        (2 ≤ (δ - hi) / primaryK11Ell))
    (hplus :
      ((δ + hi) / primaryK11Ell ≤ -2) ∨
        (2 ≤ (δ + lo) / primaryK11Ell)) :
    primaryK11PrimeShiftIsDead δ n := by
  have hell : 0 < primaryK11Ell := by
    norm_num [primaryK11Ell, primaryK11EllRat]
  constructor
  · rcases hminus with hleft | hright
    · left
      have hsub : δ - primaryK11PrimeShift n ≤ δ - lo := by
        linarith
      have hdiv :
          (δ - primaryK11PrimeShift n) / primaryK11Ell ≤
            (δ - lo) / primaryK11Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hdiv.trans hleft
    · right
      have hsub : δ - hi ≤ δ - primaryK11PrimeShift n := by
        linarith
      have hdiv :
          (δ - hi) / primaryK11Ell ≤
            (δ - primaryK11PrimeShift n) / primaryK11Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hright.trans hdiv
  · rcases hplus with hleft | hright
    · left
      have hsub : δ + primaryK11PrimeShift n ≤ δ + hi := by
        linarith
      have hdiv :
          (δ + primaryK11PrimeShift n) / primaryK11Ell ≤
            (δ + hi) / primaryK11Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hdiv.trans hleft
    · right
      have hsub : δ + lo ≤ δ + primaryK11PrimeShift n := by
        linarith
      have hdiv :
          (δ + lo) / primaryK11Ell ≤
            (δ + primaryK11PrimeShift n) / primaryK11Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hright.trans hdiv

/-- Primary live classifier from a certified inside-support minus argument. -/
theorem primaryK11PrimeShiftIsLive_of_minus_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ primaryK11PrimeShift n)
    (hhi : primaryK11PrimeShift n ≤ hi)
    (hleft : -2 < (δ - hi) / primaryK11Ell)
    (hright : (δ - lo) / primaryK11Ell < 2) :
    primaryK11PrimeShiftIsLive δ n := by
  have hell : 0 < primaryK11Ell := by
    norm_num [primaryK11Ell, primaryK11EllRat]
  intro hdead
  rcases hdead with ⟨hminus, _hplus⟩
  have hlow :
      (δ - hi) / primaryK11Ell ≤
        (δ - primaryK11PrimeShift n) / primaryK11Ell := by
    have hsub : δ - hi ≤ δ - primaryK11PrimeShift n := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hhigh :
      (δ - primaryK11PrimeShift n) / primaryK11Ell ≤
        (δ - lo) / primaryK11Ell := by
    have hsub : δ - primaryK11PrimeShift n ≤ δ - lo := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  rcases hminus with hminusLeft | hminusRight
  · linarith
  · linarith

/-- Primary live classifier from a certified inside-support plus argument. -/
theorem primaryK11PrimeShiftIsLive_of_plus_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ primaryK11PrimeShift n)
    (hhi : primaryK11PrimeShift n ≤ hi)
    (hleft : -2 < (δ + lo) / primaryK11Ell)
    (hright : (δ + hi) / primaryK11Ell < 2) :
    primaryK11PrimeShiftIsLive δ n := by
  have hell : 0 < primaryK11Ell := by
    norm_num [primaryK11Ell, primaryK11EllRat]
  intro hdead
  rcases hdead with ⟨_hminus, hplus⟩
  have hlow :
      (δ + lo) / primaryK11Ell ≤
        (δ + primaryK11PrimeShift n) / primaryK11Ell := by
    have hsub : δ + lo ≤ δ + primaryK11PrimeShift n := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hhigh :
      (δ + primaryK11PrimeShift n) / primaryK11Ell ≤
        (δ + hi) / primaryK11Ell := by
    have hsub : δ + primaryK11PrimeShift n ≤ δ + hi := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  rcases hplus with hplusLeft | hplusRight
  · linarith
  · linarith

/-- Control support classifier from generated shift bounds. -/
theorem controlK9PrimeShiftIsDead_of_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ controlK9PrimeShift n)
    (hhi : controlK9PrimeShift n ≤ hi)
    (hminus :
      ((δ - lo) / controlK9Ell ≤ -2) ∨
        (2 ≤ (δ - hi) / controlK9Ell))
    (hplus :
      ((δ + hi) / controlK9Ell ≤ -2) ∨
        (2 ≤ (δ + lo) / controlK9Ell)) :
    controlK9PrimeShiftIsDead δ n := by
  have hell : 0 < controlK9Ell := by
    norm_num [controlK9Ell, controlK9EllRat]
  constructor
  · rcases hminus with hleft | hright
    · left
      have hsub : δ - controlK9PrimeShift n ≤ δ - lo := by
        linarith
      have hdiv :
          (δ - controlK9PrimeShift n) / controlK9Ell ≤
            (δ - lo) / controlK9Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hdiv.trans hleft
    · right
      have hsub : δ - hi ≤ δ - controlK9PrimeShift n := by
        linarith
      have hdiv :
          (δ - hi) / controlK9Ell ≤
            (δ - controlK9PrimeShift n) / controlK9Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hright.trans hdiv
  · rcases hplus with hleft | hright
    · left
      have hsub : δ + controlK9PrimeShift n ≤ δ + hi := by
        linarith
      have hdiv :
          (δ + controlK9PrimeShift n) / controlK9Ell ≤
            (δ + hi) / controlK9Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hdiv.trans hleft
    · right
      have hsub : δ + lo ≤ δ + controlK9PrimeShift n := by
        linarith
      have hdiv :
          (δ + lo) / controlK9Ell ≤
            (δ + controlK9PrimeShift n) / controlK9Ell :=
        div_le_div_of_nonneg_right hsub (le_of_lt hell)
      exact hright.trans hdiv

/-- Control live classifier from a certified inside-support minus argument. -/
theorem controlK9PrimeShiftIsLive_of_minus_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ controlK9PrimeShift n)
    (hhi : controlK9PrimeShift n ≤ hi)
    (hleft : -2 < (δ - hi) / controlK9Ell)
    (hright : (δ - lo) / controlK9Ell < 2) :
    controlK9PrimeShiftIsLive δ n := by
  have hell : 0 < controlK9Ell := by
    norm_num [controlK9Ell, controlK9EllRat]
  intro hdead
  rcases hdead with ⟨hminus, _hplus⟩
  have hlow :
      (δ - hi) / controlK9Ell ≤
        (δ - controlK9PrimeShift n) / controlK9Ell := by
    have hsub : δ - hi ≤ δ - controlK9PrimeShift n := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hhigh :
      (δ - controlK9PrimeShift n) / controlK9Ell ≤
        (δ - lo) / controlK9Ell := by
    have hsub : δ - controlK9PrimeShift n ≤ δ - lo := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  rcases hminus with hminusLeft | hminusRight
  · linarith
  · linarith

/-- Control live classifier from a certified inside-support plus argument. -/
theorem controlK9PrimeShiftIsLive_of_plus_shift_bounds
    {δ lo hi : Real} (n : PrimeShiftIndexL3)
    (hlo : lo ≤ controlK9PrimeShift n)
    (hhi : controlK9PrimeShift n ≤ hi)
    (hleft : -2 < (δ + lo) / controlK9Ell)
    (hright : (δ + hi) / controlK9Ell < 2) :
    controlK9PrimeShiftIsLive δ n := by
  have hell : 0 < controlK9Ell := by
    norm_num [controlK9Ell, controlK9EllRat]
  intro hdead
  rcases hdead with ⟨_hminus, hplus⟩
  have hlow :
      (δ + lo) / controlK9Ell ≤
        (δ + controlK9PrimeShift n) / controlK9Ell := by
    have hsub : δ + lo ≤ δ + controlK9PrimeShift n := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hhigh :
      (δ + controlK9PrimeShift n) / controlK9Ell ≤
        (δ + hi) / controlK9Ell := by
    have hsub : δ + controlK9PrimeShift n ≤ δ + hi := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  rcases hplus with hplusLeft | hplusRight
  · linarith
  · linarith

/-- Strict exact-midpoint compatibility obstruction: the imported primary
diagonal `P` midpoint is not exactly zero.  The active center-error contract
absorbs this tiny diagonal residual into the imported radius. -/
theorem primaryK11PEntryRat_0_0_ne_zero :
    primaryK11PEntryRat 0 0 ≠ 0 := by
  native_decide

/-- Strict exact-midpoint compatibility obstruction: the imported control
diagonal `P` midpoint is not exactly zero.  The active center-error contract
absorbs this tiny diagonal residual into the imported radius. -/
theorem controlK9PEntryRat_0_0_ne_zero :
    controlK9PEntryRat 0 0 ≠ 0 := by
  native_decide

/-- Primary live-shift sum checks package the existing tight term hboxes into
the delta/live finite prime-profile payload. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
    (hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHbox := by
  refine ⟨
    primaryK11PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid,
    primaryK11PositivePartPowerTightPrimeTermRad
      activeL3PrimeWeightMid activeL3PrimeWeightRad,
    ?_, hmid, hrad⟩
  have hweight :
      ∀ n,
        |primaryK11PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      primaryK11PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have hterm :=
    primaryK11PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n _hn
  simpa [← primaryK11FinitePrimeProfileTerm_eq_termOfDelta i j n] using
    hterm i j n

/-- Primary live-shift sum checks feed the analytic `P` hbox through the
delta/live payload adapter. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_tight_sum_checks
    (hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = primaryK11P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  exact
    primaryK11AnalyticP_entry_hbox_of_delta_live_payload
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
        hmid hrad)

/-- Primary corrected live-shift sum check packages the existing tight term
hboxes into the center-error delta/live finite prime-profile payload. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
    (hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  refine ⟨
    primaryK11PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid,
    primaryK11PositivePartPowerTightPrimeTermRad
      activeL3PrimeWeightMid activeL3PrimeWeightRad,
    ?_, hbound⟩
  have hweight :
      ∀ n,
        |primaryK11PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      primaryK11PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have hterm :=
    primaryK11PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n _hn
  simpa [← primaryK11FinitePrimeProfileTerm_eq_termOfDelta i j n] using
    hterm i j n

/-- Primary corrected live-shift sum check feeds the analytic `P` hbox through
the center-error delta/live payload adapter. -/
theorem primaryK11AnalyticP_entry_hbox_of_delta_live_tight_sum_check_with_center_error
    (hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  exact
    primaryK11AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
        hbound)

/-- Named primary class-A generated check feeds the center-error payload. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_named_tight_live_sum_check
    (hbound : primaryK11TightLiveCenterErrorSumCheck) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
      hbound

/-- Control live-shift sum checks package the existing tight term hboxes into
the delta/live finite prime-profile payload. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
    (hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHbox := by
  refine ⟨
    controlK9PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid,
    controlK9PositivePartPowerTightPrimeTermRad
      activeL3PrimeWeightMid activeL3PrimeWeightRad,
    ?_, hmid, hrad⟩
  have hweight :
      ∀ n,
        |controlK9PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      controlK9PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have hterm :=
    controlK9PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n _hn
  simpa [← controlK9FinitePrimeProfileTerm_eq_termOfDelta i j n] using
    hterm i j n

/-- Control live-shift sum checks feed the analytic `P` hbox through the
delta/live payload adapter. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_tight_sum_checks
    (hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = controlK9P i j)
    (hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  exact
    controlK9AnalyticP_entry_hbox_of_delta_live_payload
      (controlK9DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
        hmid hrad)

/-- Control corrected live-shift sum check packages the existing tight term
hboxes into the center-error delta/live finite prime-profile payload. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
    (hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  refine ⟨
    controlK9PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid,
    controlK9PositivePartPowerTightPrimeTermRad
      activeL3PrimeWeightMid activeL3PrimeWeightRad,
    ?_, hbound⟩
  have hweight :
      ∀ n,
        |controlK9PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      controlK9PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have hterm :=
    controlK9PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n _hn
  simpa [← controlK9FinitePrimeProfileTerm_eq_termOfDelta i j n] using
    hterm i j n

/-- Control corrected live-shift sum check feeds the analytic `P` hbox through
the center-error delta/live payload adapter. -/
theorem controlK9AnalyticP_entry_hbox_of_delta_live_tight_sum_check_with_center_error
    (hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  exact
    controlK9AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
        hbound)

/-- Named control class-A generated check feeds the center-error payload. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_named_tight_live_sum_check
    (hbound : controlK9TightLiveCenterErrorSumCheck) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_tight_live_sum_check
      hbound

/-- Generated primary/control live-shift sum checks feed the active Step33
entry-hbox certificate bundle. -/
theorem activeCenteredCoeffEntryHboxCert_of_deltaLiveTightSumChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = primaryK11P i j)
    (primary_hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = controlK9P i j)
    (control_hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_deltaLivePrimeProfilePayloadHboxes
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
        primary_hmid primary_hrad)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHbox_of_tight_live_sum_checks
        control_hmid control_hrad)
      control_hP0

/-- Corrected generated primary/control live-shift sum checks feed the active
Step33 entry-hbox certificate bundle.  This is the adapter matching the
1024-bit/36-decimal audit contract. -/
theorem activeCenteredCoeffEntryHboxCert_of_deltaLiveTightSumChecksWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact ActiveCenteredCoeffEntryHboxCert.mk
    (PrimaryK11BaseEntryHboxCert.mk
      primary_hA
      (primaryK11AnalyticP_entry_hbox_of_delta_live_tight_sum_check_with_center_error
        primary_hbound)
      primary_hP0)
    (ControlK9BaseEntryHboxCert.mk
      control_hA
      (controlK9AnalyticP_entry_hbox_of_delta_live_tight_sum_check_with_center_error
        control_hbound)
      control_hP0)

/-- Named class-A generated checks feed the active Step33 entry-hbox
certificate bundle. -/
theorem activeCenteredCoeffEntryHboxCert_of_namedDeltaLiveTightSumChecksWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hbound : primaryK11TightLiveCenterErrorSumCheck)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hbound : controlK9TightLiveCenterErrorSumCheck)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact activeCenteredCoeffEntryHboxCert_of_deltaLiveTightSumChecksWithCenterError
    primary_hA primary_hbound primary_hP0
    control_hA control_hbound control_hP0

/-- Option-B landing surface for Step33A.1.

The old named tight-sum checks are kept as compatibility wrappers, but the
active generated route should land here: a generator provides rational
delta/live term midpoints and radii, Lean checks the term hboxes plus the
center-error budget inside the generic payload propositions, and this theorem
only composes the existing entry-hbox receivers. -/
theorem activeCenteredCoeffEntryHboxCert_of_rationalDeltaLivePayloadHboxesWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hpayload : primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hpayload : controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact ActiveCenteredCoeffEntryHboxCert.mk
    (PrimaryK11BaseEntryHboxCert.mk
      primary_hA
      (primaryK11AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
        primary_hpayload)
      primary_hP0)
    (ControlK9BaseEntryHboxCert.mk
      control_hA
      (controlK9AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
        control_hpayload)
      control_hP0)

/-!
Step33 closure aggregators.

These theorems intentionally do not introduce new scalar replay.  They record
the mathematical Step33 gates above the generated payload layer:

* 33A: construct `ActiveCenteredCoeffEntryHboxCert`;
* 33B: expose finite analytic Weil positivity from the certified blocks;
* 33C: expose the singleton `DirectedCertFamily` handoff.
-/

/-- Gate 33A: generated delta/live tight-sum checks construct the active
entry-hbox certificate. -/
theorem psd_step33_active_entry_hbox_cert_from_deltaLiveTightSumChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = primaryK11P i j)
    (primary_hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = controlK9P i j)
    (control_hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact activeCenteredCoeffEntryHboxCert_of_deltaLiveTightSumChecks
    primary_hA primary_hmid primary_hrad primary_hP0
    control_hA control_hmid control_hrad control_hP0

/-- Gate 33A, corrected contract: generated delta/live center-error checks
construct the active entry-hbox certificate. -/
theorem psd_step33_active_entry_hbox_cert_from_deltaLiveTightSumChecksWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact activeCenteredCoeffEntryHboxCert_of_deltaLiveTightSumChecksWithCenterError
    primary_hA primary_hbound primary_hP0
    control_hA control_hbound control_hP0

/-- Gate 33A, option-B contract: generated rational delta/live payload hboxes
construct the active entry-hbox certificate without asking Lean to prove the
old symbolic tight-sum surface. -/
theorem psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hpayload : primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hpayload : controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primary_hpayload primary_hP0
      control_hA control_hpayload control_hP0

/-- Gate 33B target: finite analytic Weil positivity for both active blocks. -/
def PsdStep33FiniteAnalyticPositivity
    (cert : ActiveCenteredCoeffEntryHboxCert) : Prop :=
  (∀ v : CoeffIndex23 -> Real,
    (primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.boundary.evalPlus
        ((primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v) = 0 ->
    (primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.boundary.evalMinus
        ((primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v) = 0 ->
      0 ≤ (primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.weilForm
        ((primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v)) ∧
  (∀ v : CoeffIndex23 -> Real,
    (controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.boundary.evalPlus
        ((controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v) = 0 ->
    (controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.boundary.evalMinus
        ((controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v) = 0 ->
      0 ≤ (controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.weilForm
        ((controlK9CertifiedCoeffBlock_of_activeEntryHboxCert cert).finiteWeilMatrixModel.synth v))

/-- Gate 33C target: singleton directed-family handoff for primary and
control active blocks. -/
def PsdStep33SingletonDirectedFamilyHandoff
    (cert : ActiveCenteredCoeffEntryHboxCert) : Prop :=
  ∃ primaryFamily controlFamily : DirectedCertFamily,
    primaryFamily = primaryK11SingletonDirectedCertFamily_of_activeEntryHboxCert cert ∧
    controlFamily = controlK9SingletonDirectedCertFamily_of_activeEntryHboxCert cert

/-- Gate 33B: an active entry-hbox certificate exposes finite analytic Weil
positivity through the already-compiled certified-block receivers. -/
theorem psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
    (cert : ActiveCenteredCoeffEntryHboxCert) :
    PsdStep33FiniteAnalyticPositivity cert := by
  exact ⟨
    primaryK11_weil_nonneg_on_analyticBoundary_of_activeEntryHboxCert cert,
    controlK9_weil_nonneg_on_analyticBoundary_of_activeEntryHboxCert cert⟩

/-- Gate 33C: an active entry-hbox certificate exposes the singleton
`DirectedCertFamily` handoff objects for Step34. -/
theorem psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
    (cert : ActiveCenteredCoeffEntryHboxCert) :
    PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact ⟨
    primaryK11SingletonDirectedCertFamily_of_activeEntryHboxCert cert,
    controlK9SingletonDirectedCertFamily_of_activeEntryHboxCert cert,
    rfl, rfl⟩

/-- Thin Step33 aggregator: generated delta/live tight-sum checks feed 33A,
then the existing receivers expose 33B finite analytic positivity and 33C
singleton directed-family handoff. -/
theorem psd_step33_closed_from_deltaLiveTightSumChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hmid :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = primaryK11P i j)
    (primary_hrad :
      ∀ i j,
        (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hmid :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) = controlK9P i j)
    (control_hrad :
      ∀ i j,
        (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_deltaLiveTightSumChecks
      primary_hA primary_hmid primary_hrad primary_hP0
      control_hA control_hmid control_hrad control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  dsimp
  exact ⟨
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert _,
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert _⟩

/-- Thin Step33 aggregator, corrected contract: generated delta/live
center-error checks feed 33A, then the existing receivers expose 33B finite
analytic positivity and 33C singleton directed-family handoff. -/
theorem psd_step33_closed_from_deltaLiveTightSumChecksWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hbound :
      ∀ i j,
        |(∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - primaryK11P i j| +
          (∑ n ∈ primaryK11LivePrimeShiftSet
            (primaryK11Center j - primaryK11Center i),
          primaryK11PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            primaryK11PRadius i j)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hbound :
      ∀ i j,
        |(∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n) - controlK9P i j| +
          (∑ n ∈ controlK9LivePrimeShiftSet
            (controlK9Center j - controlK9Center i),
          controlK9PositivePartPowerTightPrimeTermRad
            activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) ≤
            controlK9PRadius i j)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_deltaLiveTightSumChecksWithCenterError
      primary_hA primary_hbound primary_hP0
      control_hA control_hbound control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  dsimp
  exact ⟨
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert _,
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert _⟩

/-- Thin Step33 aggregator, option-B contract: rational generated delta/live
payload hboxes feed 33A, then the existing receivers expose 33B finite analytic
positivity and 33C singleton directed-family handoff. -/
theorem psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hpayload : primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hpayload : controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primary_hpayload primary_hP0
      control_hA control_hpayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  dsimp
  exact ⟨
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert _,
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert _⟩

/-- Thin Step33 aggregator with named class-A payload checks.  This is the
clearest current Step33 closure surface: once the two generated center-error
checks plus the existing `A/P0` entry hboxes are available, the three Step33
mathematical gates compose immediately. -/
theorem psd_step33_closed_from_namedDeltaLiveTightSumChecksWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hbound : primaryK11TightLiveCenterErrorSumCheck)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hbound : controlK9TightLiveCenterErrorSumCheck)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := activeCenteredCoeffEntryHboxCert_of_namedDeltaLiveTightSumChecksWithCenterError
      primary_hA primary_hbound primary_hP0
      control_hA control_hbound control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  dsimp
  exact ⟨
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert _,
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert _⟩

end CenteredCoeffPrimeDeltaLivePayloadImport
end PSDpd
end Q3
