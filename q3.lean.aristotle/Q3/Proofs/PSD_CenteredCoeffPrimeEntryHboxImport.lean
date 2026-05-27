import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDictionaryBoundsImport
import Q3.Proofs.PSD_CenteredBSplineRBoundsImport

set_option linter.mathlibStandardSet false

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
