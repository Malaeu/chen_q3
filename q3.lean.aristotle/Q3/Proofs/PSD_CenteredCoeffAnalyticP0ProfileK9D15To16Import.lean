import Q3.Proofs.PSD_P0Piecewise
import Q3.Proofs.PSD_CenteredBSplineRBoundsImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory

namespace Q3
namespace PSDpd

def p0PieceK9D15PlusWindowSeg0Coeff : Nat -> Real
  | 0 => ((10000000000000000 : Real) / (37307713155613 : Real))
  | 1 => ((95000000000000000 : Real) / (37307713155613 : Real))
  | 2 => ((427500000000000000 : Real) / (37307713155613 : Real))
  | 3 => ((1211250000000000000 : Real) / (37307713155613 : Real))
  | 4 => ((2422500000000000000 : Real) / (37307713155613 : Real))
  | 5 => ((3633750000000000000 : Real) / (37307713155613 : Real))
  | 6 => ((4239375000000000000 : Real) / (37307713155613 : Real))
  | 7 => ((3936562500000000000 : Real) / (37307713155613 : Real))
  | 8 => ((2952421875000000000 : Real) / (37307713155613 : Real))
  | 9 => ((1804257812500000000 : Real) / (37307713155613 : Real))
  | 10 => ((902128906250000000 : Real) / (37307713155613 : Real))
  | 11 => ((369052734375000000 : Real) / (37307713155613 : Real))
  | 12 => ((123017578125000000 : Real) / (37307713155613 : Real))
  | 13 => ((33120117187500000 : Real) / (37307713155613 : Real))
  | 14 => ((7097167968750000 : Real) / (37307713155613 : Real))
  | 15 => ((1182861328125000 : Real) / (37307713155613 : Real))
  | 16 => ((147857666015625 : Real) / (37307713155613 : Real))
  | 17 => ((26092529296875 : Real) / (74615426311226 : Real))
  | 18 => ((2899169921875 : Real) / (149230852622452 : Real))
  | 19 => ((152587890625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg0_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real)) < x) (hxhi : x < ((-9 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg0Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 1 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (1 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 1 := by simpa using hj
    have hj_le_nat : j <= 0 := by omega
    have hj_le_real : (j : Real) <= (0 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (0 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg0Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg0_expPolyIntegral :
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg0Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg0Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-2 : Real))
    ((-9 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg0_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg0Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-9 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-9 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-9 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg0_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg0_expPolyIntegral

def p0PieceK9D15PlusWindowSeg1Coeff : Nat -> Real
  | 0 => ((-850851717672992089 : Real) / (1865385657780650 : Real))
  | 1 => ((-1901798070642983299 : Real) / (373077131556130 : Real))
  | 2 => ((-1996798070642983299 : Real) / (74615426311226 : Real))
  | 3 => ((-6555382814987169645 : Real) / (74615426311226 : Real))
  | 4 => ((-7552925349985744050 : Real) / (37307713155613 : Real))
  | 5 => ((-12991958916642906750 : Real) / (37307713155613 : Real))
  | 6 => ((-17312469891944508750 : Real) / (37307713155613 : Real))
  | 7 => ((-18299467944069731250 : Real) / (37307713155613 : Real))
  | 8 => ((-15577603495058109375 : Real) / (37307713155613 : Real))
  | 9 => ((-10777858179514765625 : Real) / (37307713155613 : Real))
  | 10 => ((-6087935533758203125 : Real) / (37307713155613 : Real))
  | 11 => ((-2808249283810546875 : Real) / (37307713155613 : Real))
  | 12 => ((-1053760947128906250 : Real) / (37307713155613 : Real))
  | 13 => ((-318907646777343750 : Real) / (37307713155613 : Real))
  | 14 => ((-76718966308593750 : Real) / (37307713155613 : Real))
  | 15 => ((-14338645019531250 : Real) / (37307713155613 : Real))
  | 16 => ((-4015814208984375 : Real) / (74615426311226 : Real))
  | 17 => ((-198303222656250 : Real) / (37307713155613 : Real))
  | 18 => ((-49285888671875 : Real) / (149230852622452 : Real))
  | 19 => ((-2899169921875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg1_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-9 : Real) / (5 : Real)) < x) (hxhi : x < ((-8 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg1Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 2 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (2 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 2 := by simpa using hj
    have hj_le_nat : j <= 1 := by omega
    have hj_le_real : (j : Real) <= (1 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (1 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg1Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg1_expPolyIntegral :
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg1Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg1Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-9 : Real) / (5 : Real))
    ((-8 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg1_centeredBSplineR_expIntegral :
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg1Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-8 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-9 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-8 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-8 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg1_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg1_expPolyIntegral

def p0PieceK9D15PlusWindowSeg2Coeff : Nat -> Real
  | 0 => ((103648513809527739 : Real) / (373077131556130 : Real))
  | 1 => ((43541963236081123 : Real) / (12034746179230 : Real))
  | 2 => ((1661250726688702077 : Real) / (74615426311226 : Real))
  | 3 => ((6400206675562549395 : Real) / (74615426311226 : Real))
  | 4 => ((8641561513201404750 : Real) / (37307713155613 : Real))
  | 5 => ((17372703951832997250 : Real) / (37307713155613 : Real))
  | 6 => ((26969330124582851250 : Real) / (37307713155613 : Real))
  | 7 => ((33099049932256668750 : Real) / (37307713155613 : Real))
  | 8 => ((32608507013997890625 : Real) / (37307713155613 : Real))
  | 9 => ((26030976237125234375 : Real) / (37307713155613 : Real))
  | 10 => ((16917585976641796875 : Real) / (37307713155613 : Real))
  | 11 => ((8955937852189453125 : Real) / (37307713155613 : Real))
  | 12 => ((3847983692871093750 : Real) / (37307713155613 : Real))
  | 13 => ((1330717953222656250 : Real) / (37307713155613 : Real))
  | 14 => ((365145033691406250 : Real) / (37307713155613 : Real))
  | 15 => ((77716354980468750 : Real) / (37307713155613 : Real))
  | 16 => ((798431396484375 : Real) / (2406949235846 : Real))
  | 17 => ((1388122558593750 : Real) / (37307713155613 : Real))
  | 18 => ((391387939453125 : Real) / (149230852622452 : Real))
  | 19 => ((26092529296875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg2_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-8 : Real) / (5 : Real)) < x) (hxhi : x < ((-7 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg2Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 3 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (3 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 3 := by simpa using hj
    have hj_le_nat : j <= 2 := by omega
    have hj_le_real : (j : Real) <= (2 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (2 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg2Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg2_expPolyIntegral :
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg2Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg2Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-8 : Real) / (5 : Real))
    ((-7 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg2_centeredBSplineR_expIntegral :
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg2Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-7 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-8 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-7 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-7 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg2_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg2_expPolyIntegral

def p0PieceK9D15PlusWindowSeg3Coeff : Nat -> Real
  | 0 => ((-65747228259315228 : Real) / (932692828890325 : Real))
  | 1 => ((-206885533109250727 : Real) / (186538565778065 : Real))
  | 2 => ((-303099446572302276 : Real) / (37307713155613 : Real))
  | 3 => ((-1388782797595655385 : Real) / (37307713155613 : Real))
  | 4 => ((-4469541730732681200 : Real) / (37307713155613 : Real))
  | 5 => ((-10722517285168615500 : Real) / (37307713155613 : Real))
  | 6 => ((-19856038603753170000 : Real) / (37307713155613 : Real))
  | 7 => ((-29016235115536012500 : Real) / (37307713155613 : Real))
  | 8 => ((-33943584108637125000 : Real) / (37307713155613 : Real))
  | 9 => ((-32070055695333906250 : Real) / (37307713155613 : Real))
  | 10 => ((-24583151117971875000 : Real) / (37307713155613 : Real))
  | 11 => ((-15297739670636718750 : Real) / (37307713155613 : Real))
  | 12 => ((-7701386556093750000 : Real) / (37307713155613 : Real))
  | 13 => ((-3111347527148437500 : Real) / (37307713155613 : Real))
  | 14 => ((-994670929687500000 : Real) / (37307713155613 : Real))
  | 15 => ((-246049350585937500 : Real) / (37307713155613 : Real))
  | 16 => ((-45439617919921875 : Real) / (37307713155613 : Real))
  | 17 => ((-11799041748046875 : Real) / (74615426311226 : Real))
  | 18 => ((-1922149658203125 : Real) / (149230852622452 : Real))
  | 19 => ((-147857666015625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg3_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-7 : Real) / (5 : Real)) < x) (hxhi : x < ((-6 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg3Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 4 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (4 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 4 := by simpa using hj
    have hj_le_nat : j <= 3 := by omega
    have hj_le_real : (j : Real) <= (3 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (3 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg3Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg3_expPolyIntegral :
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg3Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg3Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-7 : Real) / (5 : Real))
    ((-6 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg3_centeredBSplineR_expIntegral :
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg3Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-6 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-7 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-6 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-6 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg3_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg3_expPolyIntegral

def p0PieceK9D15PlusWindowSeg4Coeff : Nat -> Real
  | 0 => ((322458809978244 : Real) / (37307713155613 : Real))
  | 1 => ((5368402433705029 : Real) / (37307713155613 : Real))
  | 2 => ((47491871344361532 : Real) / (37307713155613 : Real))
  | 3 => ((266787314788590375 : Real) / (37307713155613 : Real))
  | 4 => ((1049025310548138000 : Real) / (37307713155613 : Real))
  | 5 => ((3073900318033432500 : Real) / (37307713155613 : Real))
  | 6 => ((6970328958028590000 : Real) / (37307713155613 : Real))
  | 7 => ((403250396822812500 : Real) / (1203474617923 : Real))
  | 8 => ((17952662662666875000 : Real) / (37307713155613 : Real))
  | 9 => ((20787232682846093750 : Real) / (37307713155613 : Real))
  | 10 => ((19464589197178125000 : Real) / (37307713155613 : Real))
  | 11 => ((14734810544238281250 : Real) / (37307713155613 : Real))
  | 12 => ((8983363563281250000 : Real) / (37307713155613 : Real))
  | 13 => ((4375399321289062500 : Real) / (37307713155613 : Real))
  | 14 => ((1679167230468750000 : Real) / (37307713155613 : Real))
  | 15 => ((496683471679687500 : Real) / (37307713155613 : Real))
  | 16 => ((109296386718750000 : Real) / (37307713155613 : Real))
  | 17 => ((16855773925781250 : Real) / (37307713155613 : Real))
  | 18 => ((1626434326171875 : Real) / (37307713155613 : Real))
  | 19 => ((147857666015625 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg4_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-6 : Real) / (5 : Real)) < x) (hxhi : x < ((-1 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg4Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 5 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (5 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 5 := by simpa using hj
    have hj_le_nat : j <= 4 := by omega
    have hj_le_real : (j : Real) <= (4 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (4 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg4Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg4_expPolyIntegral :
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg4Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg4Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-6 : Real) / (5 : Real))
    ((-1 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg4_centeredBSplineR_expIntegral :
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
  calc
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg4Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-6 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg4_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg4_expPolyIntegral

def p0PieceK9D15PlusWindowSeg5Coeff : Nat -> Real
  | 0 => ((26743477946994 : Real) / (37307713155613 : Real))
  | 1 => ((-250188874888721 : Real) / (37307713155613 : Real))
  | 2 => ((-3075450432982218 : Real) / (37307713155613 : Real))
  | 3 => ((-19760841949690875 : Real) / (37307713155613 : Real))
  | 4 => ((-97167316404987000 : Real) / (37307713155613 : Real))
  | 5 => ((-364677562825942500 : Real) / (37307713155613 : Real))
  | 6 => ((-1053019430643285000 : Real) / (37307713155613 : Real))
  | 7 => ((-2399741848883437500 : Real) / (37307713155613 : Real))
  | 8 => ((-4398093562919062500 : Real) / (37307713155613 : Real))
  | 9 => ((-6530358259536718750 : Real) / (37307713155613 : Real))
  | 10 => ((-7853001745204687500 : Real) / (37307713155613 : Real))
  | 11 => ((-7615945681347656250 : Real) / (37307713155613 : Real))
  | 12 => ((-5917140587109375000 : Real) / (37307713155613 : Real))
  | 13 => ((-117675776367187500 : Real) / (1203474617923 : Real))
  | 14 => ((-1759410650390625000 : Real) / (37307713155613 : Real))
  | 15 => ((-649509155273437500 : Real) / (37307713155613 : Real))
  | 16 => ((-177251770019531250 : Real) / (37307713155613 : Real))
  | 17 => ((-33711547851562500 : Real) / (37307713155613 : Real))
  | 18 => ((-3992156982421875 : Real) / (37307713155613 : Real))
  | 19 => ((-443572998046875 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg5_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real)) < x) (hxhi : x < ((-4 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg5Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 6 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (6 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 6 := by simpa using hj
    have hj_le_nat : j <= 5 := by omega
    have hj_le_real : (j : Real) <= (5 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (5 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg5Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg5_expPolyIntegral :
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg5Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg5Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-1 : Real))
    ((-4 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg5_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg5Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-4 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-4 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-4 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg5_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg5_expPolyIntegral

def p0PieceK9D15PlusWindowSeg6Coeff : Nat -> Real
  | 0 => ((934943640503586 : Real) / (932692828890325 : Real))
  | 1 => ((14249911742891 : Real) / (186538565778065 : Real))
  | 2 => ((-228763289062602 : Real) / (37307713155613 : Real))
  | 3 => ((403191986406405 : Real) / (37307713155613 : Real))
  | 4 => ((3652853275499400 : Real) / (37307713155613 : Real))
  | 5 => ((13398073475881500 : Real) / (37307713155613 : Real))
  | 6 => ((49701175237035000 : Real) / (37307713155613 : Real))
  | 7 => ((160145271910162500 : Real) / (37307713155613 : Real))
  | 8 => ((401694788568937500 : Real) / (37307713155613 : Real))
  | 9 => ((802651721903281250 : Real) / (37307713155613 : Real))
  | 10 => ((1313260731595312500 : Real) / (37307713155613 : Real))
  | 11 => ((1758640942652343750 : Real) / (37307713155613 : Real))
  | 12 => ((1895014932890625000 : Real) / (37307713155613 : Real))
  | 13 => ((1610232532617187500 : Real) / (37307713155613 : Real))
  | 14 => ((1057472349609375000 : Real) / (37307713155613 : Real))
  | 15 => ((524192094726562500 : Real) / (37307713155613 : Real))
  | 16 => ((189529870605468750 : Real) / (37307713155613 : Real))
  | 17 => ((47196166992187500 : Real) / (37307713155613 : Real))
  | 18 => ((7245025634765625 : Real) / (37307713155613 : Real))
  | 19 => ((1035003662109375 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg6_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-4 : Real) / (5 : Real)) < x) (hxhi : x < ((-3 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg6Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 7 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (7 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 7 := by simpa using hj
    have hj_le_nat : j <= 6 := by omega
    have hj_le_real : (j : Real) <= (6 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (6 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg6Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg6_expPolyIntegral :
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg6Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg6Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-4 : Real) / (5 : Real))
    ((-3 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg6_centeredBSplineR_expIntegral :
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg6Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-3 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-4 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-3 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-3 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg6_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg6_expPolyIntegral

def p0PieceK9D15PlusWindowSeg7Coeff : Nat -> Real
  | 0 => ((186538235556108 : Real) / (186538565778065 : Real))
  | 1 => ((-15685503067 : Real) / (186538565778065 : Real))
  | 2 => ((-271560080800476 : Real) / (37307713155613 : Real))
  | 3 => ((-999935562405 : Real) / (37307713155613 : Real))
  | 4 => ((958240462374000 : Real) / (37307713155613 : Real))
  | 5 => ((-74990589745500 : Real) / (37307713155613 : Real))
  | 6 => ((-2694073907070000 : Real) / (37307713155613 : Real))
  | 7 => ((-2030499250162500 : Real) / (37307713155613 : Real))
  | 8 => ((-3744639331875000 : Real) / (37307713155613 : Real))
  | 9 => ((-23243409005781250 : Real) / (37307713155613 : Real))
  | 10 => ((-63231153253125000 : Real) / (37307713155613 : Real))
  | 11 => ((-118393445777343750 : Real) / (37307713155613 : Real))
  | 12 => ((-190578832031250000 : Real) / (37307713155613 : Real))
  | 13 => ((-261454179492187500 : Real) / (37307713155613 : Real))
  | 14 => ((-279446730468750000 : Real) / (37307713155613 : Real))
  | 15 => ((-218540727539062500 : Real) / (37307713155613 : Real))
  | 16 => ((-119942138671875000 : Real) / (37307713155613 : Real))
  | 17 => ((-43825012207031250 : Real) / (37307713155613 : Real))
  | 18 => ((-9610748291015625 : Real) / (37307713155613 : Real))
  | 19 => ((-1922149658203125 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg7_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-3 : Real) / (5 : Real)) < x) (hxhi : x < ((-2 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg7Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 8 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (8 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 8 := by simpa using hj
    have hj_le_nat : j <= 7 := by omega
    have hj_le_real : (j : Real) <= (7 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (7 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg7Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg7_expPolyIntegral :
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg7Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg7Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-3 : Real) / (5 : Real))
    ((-2 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg7_centeredBSplineR_expIntegral :
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg7Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-2 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-3 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-2 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-2 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg7_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg7_expPolyIntegral

def p0PieceK9D15PlusWindowSeg8Coeff : Nat -> Real
  | 0 => ((932692828894524 : Real) / (932692828890325 : Real))
  | 1 => ((79781 : Real) / (186538565778065 : Real))
  | 2 => ((-271489495677660 : Real) / (37307713155613 : Real))
  | 3 => ((20344155 : Real) / (37307713155613 : Real))
  | 4 => ((968240021439600 : Real) / (37307713155613 : Real))
  | 5 => ((6103246500 : Real) / (37307713155613 : Real))
  | 6 => ((-2256593197950000 : Real) / (37307713155613 : Real))
  | 7 => ((661185037500 : Real) / (37307713155613 : Real))
  | 8 => ((3872212300125000 : Real) / (37307713155613 : Real))
  | 9 => ((30304314218750 : Real) / (37307713155613 : Real))
  | 10 => ((-5046869953125000 : Real) / (37307713155613 : Real))
  | 11 => ((619860972656250 : Real) / (37307713155613 : Real))
  | 12 => ((7776679218750000 : Real) / (37307713155613 : Real))
  | 13 => ((5562854882812500 : Real) / (37307713155613 : Real))
  | 14 => ((6642949218750000 : Real) / (37307713155613 : Real))
  | 15 => ((19867338867187500 : Real) / (37307713155613 : Real))
  | 16 => ((29062902832031250 : Real) / (37307713155613 : Real))
  | 17 => ((21912506103515625 : Real) / (37307713155613 : Real))
  | 18 => ((17299346923828125 : Real) / (74615426311226 : Real))
  | 19 => ((5766448974609375 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg8_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real) / (5 : Real)) < x) (hxhi : x < ((-1 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg8Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 9 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (9 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 9 := by simpa using hj
    have hj_le_nat : j <= 8 := by omega
    have hj_le_real : (j : Real) <= (8 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (8 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg8Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg8_expPolyIntegral :
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg8Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg8Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-2 : Real) / (5 : Real))
    ((-1 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg8_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg8Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg8_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg8_expPolyIntegral

def p0PieceK9D15PlusWindowSeg9Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-271489496395689 : Real) / (37307713155613 : Real))
  | 3 => ((0 : Real))
  | 4 => ((968239614556500 : Real) / (37307713155613 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-2256664402492500 : Real) / (37307713155613 : Real))
  | 7 => ((0 : Real))
  | 8 => ((3867253412343750 : Real) / (37307713155613 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-5198391524218750 : Real) / (37307713155613 : Real))
  | 11 => ((0 : Real))
  | 12 => ((5710475976562500 : Real) / (37307713155613 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-5277454101562500 : Real) / (37307713155613 : Real))
  | 15 => ((0 : Real))
  | 16 => ((4228729248046875 : Real) / (37307713155613 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-7047882080078125 : Real) / (74615426311226 : Real))
  | 19 => ((-7047882080078125 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg9_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (5 : Real)) < x) (hxhi : x < ((0 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg9Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 10 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (10 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 10 := by simpa using hj
    have hj_le_nat : j <= 9 := by omega
    have hj_le_real : (j : Real) <= (9 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (9 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg9Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg9_expPolyIntegral :
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg9Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg9Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (5 : Real))
    ((0 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg9_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg9Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((0 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((0 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((0 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg9_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg9_expPolyIntegral

def p0PieceK9D15PlusWindowSeg10Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-271489496395689 : Real) / (37307713155613 : Real))
  | 3 => ((0 : Real))
  | 4 => ((968239614556500 : Real) / (37307713155613 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-2256664402492500 : Real) / (37307713155613 : Real))
  | 7 => ((0 : Real))
  | 8 => ((3867253412343750 : Real) / (37307713155613 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-5198391524218750 : Real) / (37307713155613 : Real))
  | 11 => ((0 : Real))
  | 12 => ((5710475976562500 : Real) / (37307713155613 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-5277454101562500 : Real) / (37307713155613 : Real))
  | 15 => ((0 : Real))
  | 16 => ((4228729248046875 : Real) / (37307713155613 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-7047882080078125 : Real) / (74615426311226 : Real))
  | 19 => ((7047882080078125 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg10_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((0 : Real)) < x) (hxhi : x < ((1 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg10Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 11 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (11 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 11 := by simpa using hj
    have hj_le_nat : j <= 10 := by omega
    have hj_le_real : (j : Real) <= (10 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (10 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg10Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg10_expPolyIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg10Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg10Coeff 20
    ((-3 : Real) / (20 : Real))
    ((0 : Real))
    ((1 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg10_centeredBSplineR_expIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg10Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((0 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg10_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg10_expPolyIntegral

def p0PieceK9D15PlusWindowSeg11Coeff : Nat -> Real
  | 0 => ((932692828894524 : Real) / (932692828890325 : Real))
  | 1 => ((-79781 : Real) / (186538565778065 : Real))
  | 2 => ((-271489495677660 : Real) / (37307713155613 : Real))
  | 3 => ((-20344155 : Real) / (37307713155613 : Real))
  | 4 => ((968240021439600 : Real) / (37307713155613 : Real))
  | 5 => ((-6103246500 : Real) / (37307713155613 : Real))
  | 6 => ((-2256593197950000 : Real) / (37307713155613 : Real))
  | 7 => ((-661185037500 : Real) / (37307713155613 : Real))
  | 8 => ((3872212300125000 : Real) / (37307713155613 : Real))
  | 9 => ((-30304314218750 : Real) / (37307713155613 : Real))
  | 10 => ((-5046869953125000 : Real) / (37307713155613 : Real))
  | 11 => ((-619860972656250 : Real) / (37307713155613 : Real))
  | 12 => ((7776679218750000 : Real) / (37307713155613 : Real))
  | 13 => ((-5562854882812500 : Real) / (37307713155613 : Real))
  | 14 => ((6642949218750000 : Real) / (37307713155613 : Real))
  | 15 => ((-19867338867187500 : Real) / (37307713155613 : Real))
  | 16 => ((29062902832031250 : Real) / (37307713155613 : Real))
  | 17 => ((-21912506103515625 : Real) / (37307713155613 : Real))
  | 18 => ((17299346923828125 : Real) / (74615426311226 : Real))
  | 19 => ((-5766448974609375 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg11_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (5 : Real)) < x) (hxhi : x < ((2 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg11Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 12 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (12 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 12 := by simpa using hj
    have hj_le_nat : j <= 11 := by omega
    have hj_le_real : (j : Real) <= (11 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (11 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg11Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg11_expPolyIntegral :
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg11Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg11Coeff 20
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (5 : Real))
    ((2 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg11_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg11Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg11_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg11_expPolyIntegral

def p0PieceK9D15PlusWindowSeg12Coeff : Nat -> Real
  | 0 => ((186538235556108 : Real) / (186538565778065 : Real))
  | 1 => ((15685503067 : Real) / (186538565778065 : Real))
  | 2 => ((-271560080800476 : Real) / (37307713155613 : Real))
  | 3 => ((999935562405 : Real) / (37307713155613 : Real))
  | 4 => ((958240462374000 : Real) / (37307713155613 : Real))
  | 5 => ((74990589745500 : Real) / (37307713155613 : Real))
  | 6 => ((-2694073907070000 : Real) / (37307713155613 : Real))
  | 7 => ((2030499250162500 : Real) / (37307713155613 : Real))
  | 8 => ((-3744639331875000 : Real) / (37307713155613 : Real))
  | 9 => ((23243409005781250 : Real) / (37307713155613 : Real))
  | 10 => ((-63231153253125000 : Real) / (37307713155613 : Real))
  | 11 => ((118393445777343750 : Real) / (37307713155613 : Real))
  | 12 => ((-190578832031250000 : Real) / (37307713155613 : Real))
  | 13 => ((261454179492187500 : Real) / (37307713155613 : Real))
  | 14 => ((-279446730468750000 : Real) / (37307713155613 : Real))
  | 15 => ((218540727539062500 : Real) / (37307713155613 : Real))
  | 16 => ((-119942138671875000 : Real) / (37307713155613 : Real))
  | 17 => ((43825012207031250 : Real) / (37307713155613 : Real))
  | 18 => ((-9610748291015625 : Real) / (37307713155613 : Real))
  | 19 => ((1922149658203125 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg12_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((2 : Real) / (5 : Real)) < x) (hxhi : x < ((3 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg12Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 13 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (13 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 13 := by simpa using hj
    have hj_le_nat : j <= 12 := by omega
    have hj_le_real : (j : Real) <= (12 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (12 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg12Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg12_expPolyIntegral :
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg12Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg12Coeff 20
    ((-3 : Real) / (20 : Real))
    ((2 : Real) / (5 : Real))
    ((3 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg12_centeredBSplineR_expIntegral :
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg12Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((3 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((2 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((3 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((3 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg12_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg12_expPolyIntegral

def p0PieceK9D15PlusWindowSeg13Coeff : Nat -> Real
  | 0 => ((934943640503586 : Real) / (932692828890325 : Real))
  | 1 => ((-14249911742891 : Real) / (186538565778065 : Real))
  | 2 => ((-228763289062602 : Real) / (37307713155613 : Real))
  | 3 => ((-403191986406405 : Real) / (37307713155613 : Real))
  | 4 => ((3652853275499400 : Real) / (37307713155613 : Real))
  | 5 => ((-13398073475881500 : Real) / (37307713155613 : Real))
  | 6 => ((49701175237035000 : Real) / (37307713155613 : Real))
  | 7 => ((-160145271910162500 : Real) / (37307713155613 : Real))
  | 8 => ((401694788568937500 : Real) / (37307713155613 : Real))
  | 9 => ((-802651721903281250 : Real) / (37307713155613 : Real))
  | 10 => ((1313260731595312500 : Real) / (37307713155613 : Real))
  | 11 => ((-1758640942652343750 : Real) / (37307713155613 : Real))
  | 12 => ((1895014932890625000 : Real) / (37307713155613 : Real))
  | 13 => ((-1610232532617187500 : Real) / (37307713155613 : Real))
  | 14 => ((1057472349609375000 : Real) / (37307713155613 : Real))
  | 15 => ((-524192094726562500 : Real) / (37307713155613 : Real))
  | 16 => ((189529870605468750 : Real) / (37307713155613 : Real))
  | 17 => ((-47196166992187500 : Real) / (37307713155613 : Real))
  | 18 => ((7245025634765625 : Real) / (37307713155613 : Real))
  | 19 => ((-1035003662109375 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg13_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((3 : Real) / (5 : Real)) < x) (hxhi : x < ((4 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg13Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 14 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (14 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 14 := by simpa using hj
    have hj_le_nat : j <= 13 := by omega
    have hj_le_real : (j : Real) <= (13 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (13 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg13Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg13_expPolyIntegral :
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg13Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg13Coeff 20
    ((-3 : Real) / (20 : Real))
    ((3 : Real) / (5 : Real))
    ((4 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg13_centeredBSplineR_expIntegral :
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg13Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((4 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((3 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((4 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((4 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg13_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg13_expPolyIntegral

def p0PieceK9D15PlusWindowSeg14Coeff : Nat -> Real
  | 0 => ((26743477946994 : Real) / (37307713155613 : Real))
  | 1 => ((250188874888721 : Real) / (37307713155613 : Real))
  | 2 => ((-3075450432982218 : Real) / (37307713155613 : Real))
  | 3 => ((19760841949690875 : Real) / (37307713155613 : Real))
  | 4 => ((-97167316404987000 : Real) / (37307713155613 : Real))
  | 5 => ((364677562825942500 : Real) / (37307713155613 : Real))
  | 6 => ((-1053019430643285000 : Real) / (37307713155613 : Real))
  | 7 => ((2399741848883437500 : Real) / (37307713155613 : Real))
  | 8 => ((-4398093562919062500 : Real) / (37307713155613 : Real))
  | 9 => ((6530358259536718750 : Real) / (37307713155613 : Real))
  | 10 => ((-7853001745204687500 : Real) / (37307713155613 : Real))
  | 11 => ((7615945681347656250 : Real) / (37307713155613 : Real))
  | 12 => ((-5917140587109375000 : Real) / (37307713155613 : Real))
  | 13 => ((117675776367187500 : Real) / (1203474617923 : Real))
  | 14 => ((-1759410650390625000 : Real) / (37307713155613 : Real))
  | 15 => ((649509155273437500 : Real) / (37307713155613 : Real))
  | 16 => ((-177251770019531250 : Real) / (37307713155613 : Real))
  | 17 => ((33711547851562500 : Real) / (37307713155613 : Real))
  | 18 => ((-3992156982421875 : Real) / (37307713155613 : Real))
  | 19 => ((443572998046875 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg14_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((4 : Real) / (5 : Real)) < x) (hxhi : x < ((1 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg14Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 15 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (15 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 15 := by simpa using hj
    have hj_le_nat : j <= 14 := by omega
    have hj_le_real : (j : Real) <= (14 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (14 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg14Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg14_expPolyIntegral :
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg14Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg14Coeff 20
    ((-3 : Real) / (20 : Real))
    ((4 : Real) / (5 : Real))
    ((1 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg14_centeredBSplineR_expIntegral :
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
  calc
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg14Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((4 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg14_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg14_expPolyIntegral

def p0PieceK9D15PlusWindowSeg15Coeff : Nat -> Real
  | 0 => ((322458809978244 : Real) / (37307713155613 : Real))
  | 1 => ((-5368402433705029 : Real) / (37307713155613 : Real))
  | 2 => ((47491871344361532 : Real) / (37307713155613 : Real))
  | 3 => ((-266787314788590375 : Real) / (37307713155613 : Real))
  | 4 => ((1049025310548138000 : Real) / (37307713155613 : Real))
  | 5 => ((-3073900318033432500 : Real) / (37307713155613 : Real))
  | 6 => ((6970328958028590000 : Real) / (37307713155613 : Real))
  | 7 => ((-403250396822812500 : Real) / (1203474617923 : Real))
  | 8 => ((17952662662666875000 : Real) / (37307713155613 : Real))
  | 9 => ((-20787232682846093750 : Real) / (37307713155613 : Real))
  | 10 => ((19464589197178125000 : Real) / (37307713155613 : Real))
  | 11 => ((-14734810544238281250 : Real) / (37307713155613 : Real))
  | 12 => ((8983363563281250000 : Real) / (37307713155613 : Real))
  | 13 => ((-4375399321289062500 : Real) / (37307713155613 : Real))
  | 14 => ((1679167230468750000 : Real) / (37307713155613 : Real))
  | 15 => ((-496683471679687500 : Real) / (37307713155613 : Real))
  | 16 => ((109296386718750000 : Real) / (37307713155613 : Real))
  | 17 => ((-16855773925781250 : Real) / (37307713155613 : Real))
  | 18 => ((1626434326171875 : Real) / (37307713155613 : Real))
  | 19 => ((-147857666015625 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg15_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real)) < x) (hxhi : x < ((6 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg15Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 16 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (16 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 16 := by simpa using hj
    have hj_le_nat : j <= 15 := by omega
    have hj_le_real : (j : Real) <= (15 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (15 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg15Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg15_expPolyIntegral :
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg15Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg15Coeff 20
    ((-3 : Real) / (20 : Real))
    ((1 : Real))
    ((6 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg15_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg15Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((6 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((6 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((6 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg15_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg15_expPolyIntegral

def p0PieceK9D15PlusWindowSeg16Coeff : Nat -> Real
  | 0 => ((-65747228259315228 : Real) / (932692828890325 : Real))
  | 1 => ((206885533109250727 : Real) / (186538565778065 : Real))
  | 2 => ((-303099446572302276 : Real) / (37307713155613 : Real))
  | 3 => ((1388782797595655385 : Real) / (37307713155613 : Real))
  | 4 => ((-4469541730732681200 : Real) / (37307713155613 : Real))
  | 5 => ((10722517285168615500 : Real) / (37307713155613 : Real))
  | 6 => ((-19856038603753170000 : Real) / (37307713155613 : Real))
  | 7 => ((29016235115536012500 : Real) / (37307713155613 : Real))
  | 8 => ((-33943584108637125000 : Real) / (37307713155613 : Real))
  | 9 => ((32070055695333906250 : Real) / (37307713155613 : Real))
  | 10 => ((-24583151117971875000 : Real) / (37307713155613 : Real))
  | 11 => ((15297739670636718750 : Real) / (37307713155613 : Real))
  | 12 => ((-7701386556093750000 : Real) / (37307713155613 : Real))
  | 13 => ((3111347527148437500 : Real) / (37307713155613 : Real))
  | 14 => ((-994670929687500000 : Real) / (37307713155613 : Real))
  | 15 => ((246049350585937500 : Real) / (37307713155613 : Real))
  | 16 => ((-45439617919921875 : Real) / (37307713155613 : Real))
  | 17 => ((11799041748046875 : Real) / (74615426311226 : Real))
  | 18 => ((-1922149658203125 : Real) / (149230852622452 : Real))
  | 19 => ((147857666015625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg16_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((6 : Real) / (5 : Real)) < x) (hxhi : x < ((7 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg16Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 17 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (17 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 17 := by simpa using hj
    have hj_le_nat : j <= 16 := by omega
    have hj_le_real : (j : Real) <= (16 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (16 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg16Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg16_expPolyIntegral :
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg16Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg16Coeff 20
    ((-3 : Real) / (20 : Real))
    ((6 : Real) / (5 : Real))
    ((7 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg16_centeredBSplineR_expIntegral :
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg16Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((7 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((6 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((7 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((7 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg16_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg16_expPolyIntegral

def p0PieceK9D15PlusWindowSeg17Coeff : Nat -> Real
  | 0 => ((103648513809527739 : Real) / (373077131556130 : Real))
  | 1 => ((-43541963236081123 : Real) / (12034746179230 : Real))
  | 2 => ((1661250726688702077 : Real) / (74615426311226 : Real))
  | 3 => ((-6400206675562549395 : Real) / (74615426311226 : Real))
  | 4 => ((8641561513201404750 : Real) / (37307713155613 : Real))
  | 5 => ((-17372703951832997250 : Real) / (37307713155613 : Real))
  | 6 => ((26969330124582851250 : Real) / (37307713155613 : Real))
  | 7 => ((-33099049932256668750 : Real) / (37307713155613 : Real))
  | 8 => ((32608507013997890625 : Real) / (37307713155613 : Real))
  | 9 => ((-26030976237125234375 : Real) / (37307713155613 : Real))
  | 10 => ((16917585976641796875 : Real) / (37307713155613 : Real))
  | 11 => ((-8955937852189453125 : Real) / (37307713155613 : Real))
  | 12 => ((3847983692871093750 : Real) / (37307713155613 : Real))
  | 13 => ((-1330717953222656250 : Real) / (37307713155613 : Real))
  | 14 => ((365145033691406250 : Real) / (37307713155613 : Real))
  | 15 => ((-77716354980468750 : Real) / (37307713155613 : Real))
  | 16 => ((798431396484375 : Real) / (2406949235846 : Real))
  | 17 => ((-1388122558593750 : Real) / (37307713155613 : Real))
  | 18 => ((391387939453125 : Real) / (149230852622452 : Real))
  | 19 => ((-26092529296875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg17_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((7 : Real) / (5 : Real)) < x) (hxhi : x < ((8 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg17Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 18 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (18 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 18 := by simpa using hj
    have hj_le_nat : j <= 17 := by omega
    have hj_le_real : (j : Real) <= (17 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (17 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg17Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg17_expPolyIntegral :
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg17Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg17Coeff 20
    ((-3 : Real) / (20 : Real))
    ((7 : Real) / (5 : Real))
    ((8 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg17_centeredBSplineR_expIntegral :
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg17Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((8 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((7 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((8 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((8 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg17_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg17_expPolyIntegral

def p0PieceK9D15PlusWindowSeg18Coeff : Nat -> Real
  | 0 => ((-850851717672992089 : Real) / (1865385657780650 : Real))
  | 1 => ((1901798070642983299 : Real) / (373077131556130 : Real))
  | 2 => ((-1996798070642983299 : Real) / (74615426311226 : Real))
  | 3 => ((6555382814987169645 : Real) / (74615426311226 : Real))
  | 4 => ((-7552925349985744050 : Real) / (37307713155613 : Real))
  | 5 => ((12991958916642906750 : Real) / (37307713155613 : Real))
  | 6 => ((-17312469891944508750 : Real) / (37307713155613 : Real))
  | 7 => ((18299467944069731250 : Real) / (37307713155613 : Real))
  | 8 => ((-15577603495058109375 : Real) / (37307713155613 : Real))
  | 9 => ((10777858179514765625 : Real) / (37307713155613 : Real))
  | 10 => ((-6087935533758203125 : Real) / (37307713155613 : Real))
  | 11 => ((2808249283810546875 : Real) / (37307713155613 : Real))
  | 12 => ((-1053760947128906250 : Real) / (37307713155613 : Real))
  | 13 => ((318907646777343750 : Real) / (37307713155613 : Real))
  | 14 => ((-76718966308593750 : Real) / (37307713155613 : Real))
  | 15 => ((14338645019531250 : Real) / (37307713155613 : Real))
  | 16 => ((-4015814208984375 : Real) / (74615426311226 : Real))
  | 17 => ((198303222656250 : Real) / (37307713155613 : Real))
  | 18 => ((-49285888671875 : Real) / (149230852622452 : Real))
  | 19 => ((2899169921875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg18_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((8 : Real) / (5 : Real)) < x) (hxhi : x < ((9 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg18Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 19 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (19 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 19 := by simpa using hj
    have hj_le_nat : j <= 18 := by omega
    have hj_le_real : (j : Real) <= (18 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (18 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg18Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg18_expPolyIntegral :
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg18Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg18Coeff 20
    ((-3 : Real) / (20 : Real))
    ((8 : Real) / (5 : Real))
    ((9 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg18_centeredBSplineR_expIntegral :
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg18Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((9 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((8 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((9 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((9 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg18_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg18_expPolyIntegral

def p0PieceK9D15PlusWindowSeg19Coeff : Nat -> Real
  | 0 => ((10000000000000000 : Real) / (37307713155613 : Real))
  | 1 => ((-95000000000000000 : Real) / (37307713155613 : Real))
  | 2 => ((427500000000000000 : Real) / (37307713155613 : Real))
  | 3 => ((-1211250000000000000 : Real) / (37307713155613 : Real))
  | 4 => ((2422500000000000000 : Real) / (37307713155613 : Real))
  | 5 => ((-3633750000000000000 : Real) / (37307713155613 : Real))
  | 6 => ((4239375000000000000 : Real) / (37307713155613 : Real))
  | 7 => ((-3936562500000000000 : Real) / (37307713155613 : Real))
  | 8 => ((2952421875000000000 : Real) / (37307713155613 : Real))
  | 9 => ((-1804257812500000000 : Real) / (37307713155613 : Real))
  | 10 => ((902128906250000000 : Real) / (37307713155613 : Real))
  | 11 => ((-369052734375000000 : Real) / (37307713155613 : Real))
  | 12 => ((123017578125000000 : Real) / (37307713155613 : Real))
  | 13 => ((-33120117187500000 : Real) / (37307713155613 : Real))
  | 14 => ((7097167968750000 : Real) / (37307713155613 : Real))
  | 15 => ((-1182861328125000 : Real) / (37307713155613 : Real))
  | 16 => ((147857666015625 : Real) / (37307713155613 : Real))
  | 17 => ((-26092529296875 : Real) / (74615426311226 : Real))
  | 18 => ((2899169921875 : Real) / (149230852622452 : Real))
  | 19 => ((-152587890625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D15PlusWindowSeg19_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((9 : Real) / (5 : Real)) < x) (hxhi : x < ((2 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D15PlusWindowSeg19Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 20 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (20 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 20 := by simpa using hj
    have hj_le_nat : j <= 19 := by omega
    have hj_le_real : (j : Real) <= (19 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (19 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D15PlusWindowSeg19Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D15PlusWindowSeg19_expPolyIntegral :
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D15PlusWindowSeg19Coeff 20 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D15PlusWindowSeg19Coeff 20
    ((-3 : Real) / (20 : Real))
    ((9 : Real) / (5 : Real))
    ((2 : Real))
    (by norm_num)

theorem p0PieceK9D15PlusWindowSeg19_centeredBSplineR_expIntegral :
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D15PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
  calc
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D15PlusWindowSeg19Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((9 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D15PlusWindowSeg19_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D15PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
        exact p0PieceK9D15PlusWindowSeg19_expPolyIntegral

def p0PieceK9D15PlusWindowBreak : Nat -> Real
  | 0 => ((-2 : Real))
  | 1 => ((-9 : Real) / (5 : Real))
  | 2 => ((-8 : Real) / (5 : Real))
  | 3 => ((-7 : Real) / (5 : Real))
  | 4 => ((-6 : Real) / (5 : Real))
  | 5 => ((-1 : Real))
  | 6 => ((-4 : Real) / (5 : Real))
  | 7 => ((-3 : Real) / (5 : Real))
  | 8 => ((-2 : Real) / (5 : Real))
  | 9 => ((-1 : Real) / (5 : Real))
  | 10 => ((0 : Real))
  | 11 => ((1 : Real) / (5 : Real))
  | 12 => ((2 : Real) / (5 : Real))
  | 13 => ((3 : Real) / (5 : Real))
  | 14 => ((4 : Real) / (5 : Real))
  | 15 => ((1 : Real))
  | 16 => ((6 : Real) / (5 : Real))
  | 17 => ((7 : Real) / (5 : Real))
  | 18 => ((8 : Real) / (5 : Real))
  | 19 => ((9 : Real) / (5 : Real))
  | 20 => ((2 : Real))
  | _ => ((2 : Real))

def p0PieceK9D15PlusWindowSegmentExpIntegral : Nat -> Real
  | 0 => expPolyIntegral p0PieceK9D15PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real))
  | 1 => expPolyIntegral p0PieceK9D15PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real))
  | 2 => expPolyIntegral p0PieceK9D15PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real))
  | 3 => expPolyIntegral p0PieceK9D15PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real))
  | 4 => expPolyIntegral p0PieceK9D15PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real))
  | 5 => expPolyIntegral p0PieceK9D15PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real))
  | 6 => expPolyIntegral p0PieceK9D15PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real))
  | 7 => expPolyIntegral p0PieceK9D15PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real))
  | 8 => expPolyIntegral p0PieceK9D15PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real))
  | 9 => expPolyIntegral p0PieceK9D15PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real))
  | 10 => expPolyIntegral p0PieceK9D15PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real))
  | 11 => expPolyIntegral p0PieceK9D15PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real))
  | 12 => expPolyIntegral p0PieceK9D15PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real))
  | 13 => expPolyIntegral p0PieceK9D15PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real))
  | 14 => expPolyIntegral p0PieceK9D15PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real))
  | 15 => expPolyIntegral p0PieceK9D15PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real))
  | 16 => expPolyIntegral p0PieceK9D15PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real))
  | 17 => expPolyIntegral p0PieceK9D15PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real))
  | 18 => expPolyIntegral p0PieceK9D15PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real))
  | 19 => expPolyIntegral p0PieceK9D15PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real))
  | _ => 0

def p0PieceK9D15PlusWindowExpPolyIntegralSum : Real :=
  (Finset.range 20).sum p0PieceK9D15PlusWindowSegmentExpIntegral

theorem p0PieceK9D15PlusWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D15PlusWindowExpPolyIntegralSum := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (a := p0PieceK9D15PlusWindowBreak) (n := 20)
    (μ := volume) ?hint
  calc
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        (Finset.range 20).sum (fun i =>
          ∫ x in p0PieceK9D15PlusWindowBreak i..p0PieceK9D15PlusWindowBreak (i + 1),
            Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
          simpa [p0PieceK9D15PlusWindowBreak] using hsplit.symm
    _ = (Finset.range 20).sum p0PieceK9D15PlusWindowSegmentExpIntegral := by
        apply Finset.sum_congr rfl
        intro i hi
        simp at hi
        interval_cases i <;>
          simp [p0PieceK9D15PlusWindowBreak, p0PieceK9D15PlusWindowSegmentExpIntegral]
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg0_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg1_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg2_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg3_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg4_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg5_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg6_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg7_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg8_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg9_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg10_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg11_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg12_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg13_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg14_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg15_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg16_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg17_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg18_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D15PlusWindowSeg19_centeredBSplineR_expIntegral
    _ = p0PieceK9D15PlusWindowExpPolyIntegralSum := by
        rfl
  · intro k hk
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _

def p0PieceK9D15MinusWindowExpPolyIntegralSum : Real := 0

theorem p0PieceK9D15PlusWindow_leftSupportZeroIntegral :
    ∫ x in ((-15 : Real) / (2 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((-15 : Real) / (2 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-15 : Real) / (2 : Real))..((-2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D15PlusWindow_rightSupportZeroIntegral :
    ∫ x in ((2 : Real))..((25 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((2 : Real))..((25 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((2 : Real))..((25 : Real) / (2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D15PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D15PlusWindowExpPolyIntegralSum := by
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-15 : Real) / (2 : Real))) (b := ((-2 : Real))) (c := ((25 : Real) / (2 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-2 : Real))) (b := ((2 : Real))) (c := ((25 : Real) / (2 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
  calc
    ∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        (∫ x in ((-15 : Real) / (2 : Real))..((-2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) +
        (∫ x in ((-2 : Real))..((25 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
        simpa using hsplitLeft.symm
    _ = ∫ x in ((-2 : Real))..((25 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
        rw [p0PieceK9D15PlusWindow_leftSupportZeroIntegral]
        ring
    _ = (∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) +
        (∫ x in ((2 : Real))..((25 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
        simpa using hsplitRight.symm
    _ = ∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
        rw [p0PieceK9D15PlusWindow_rightSupportZeroIntegral]
        ring
    _ = p0PieceK9D15PlusWindowExpPolyIntegralSum := by
        exact p0PieceK9D15PlusWindow_centeredBSplineR_expIntegral_sum

theorem p0PieceK9D15MinusWindow_rightSupportZeroIntegral :
    ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D15MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D15MinusWindowExpPolyIntegralSum := by
  simpa [p0PieceK9D15MinusWindowExpPolyIntegralSum] using
    p0PieceK9D15MinusWindow_rightSupportZeroIntegral

theorem p0PieceK9D15_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((15 : Real) / (4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((15 : Real) / (4 : Real)) / 2) *
        p0PieceK9D15PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((15 : Real) / (4 : Real)) / 2)) *
        p0PieceK9D15MinusWindowExpPolyIntegralSum := by
  have hprofile :=
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile_eq_transformed_integrals
      (k := 9)
      (ell := ((3 : Real) / (10 : Real)))
      (L := ((3 : Real)))
      (d := ((15 : Real) / (4 : Real)))
      (by norm_num)
  calc
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((15 : Real) / (4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((15 : Real) / (4 : Real)) / 2) *
        (∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
          Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x) +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((15 : Real) / (4 : Real)) / 2)) *
        (∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
          Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x) := by
        norm_num at hprofile ⊢
        simpa [mul_assoc] using hprofile
    _ = ((3 : Real) / (10 : Real)) * Real.exp (((15 : Real) / (4 : Real)) / 2) *
        p0PieceK9D15PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((15 : Real) / (4 : Real)) / 2)) *
        p0PieceK9D15MinusWindowExpPolyIntegralSum := by
        have hplus :
            ∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
            p0PieceK9D15PlusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                ∫ x in ((-15 : Real) / (2 : Real))..((25 : Real) / (2 : Real)),
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x
                have harg : -(((3 : Real) / (10 : Real)) / 2) * x = ((-3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK9D15PlusWindowExpPolyIntegralSum := by
                exact p0PieceK9D15PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        have hminus :
            ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
            p0PieceK9D15MinusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                ∫ x in ((25 : Real) / (2 : Real))..((65 : Real) / (2 : Real)),
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x
                have harg : (((3 : Real) / (10 : Real)) / 2) * x = ((3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK9D15MinusWindowExpPolyIntegralSum := by
                exact p0PieceK9D15MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        rw [hplus, hminus]

def p0PieceK9D16PlusWindowSeg0Coeff : Nat -> Real
  | 0 => ((10000000000000000 : Real) / (37307713155613 : Real))
  | 1 => ((95000000000000000 : Real) / (37307713155613 : Real))
  | 2 => ((427500000000000000 : Real) / (37307713155613 : Real))
  | 3 => ((1211250000000000000 : Real) / (37307713155613 : Real))
  | 4 => ((2422500000000000000 : Real) / (37307713155613 : Real))
  | 5 => ((3633750000000000000 : Real) / (37307713155613 : Real))
  | 6 => ((4239375000000000000 : Real) / (37307713155613 : Real))
  | 7 => ((3936562500000000000 : Real) / (37307713155613 : Real))
  | 8 => ((2952421875000000000 : Real) / (37307713155613 : Real))
  | 9 => ((1804257812500000000 : Real) / (37307713155613 : Real))
  | 10 => ((902128906250000000 : Real) / (37307713155613 : Real))
  | 11 => ((369052734375000000 : Real) / (37307713155613 : Real))
  | 12 => ((123017578125000000 : Real) / (37307713155613 : Real))
  | 13 => ((33120117187500000 : Real) / (37307713155613 : Real))
  | 14 => ((7097167968750000 : Real) / (37307713155613 : Real))
  | 15 => ((1182861328125000 : Real) / (37307713155613 : Real))
  | 16 => ((147857666015625 : Real) / (37307713155613 : Real))
  | 17 => ((26092529296875 : Real) / (74615426311226 : Real))
  | 18 => ((2899169921875 : Real) / (149230852622452 : Real))
  | 19 => ((152587890625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg0_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real)) < x) (hxhi : x < ((-9 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg0Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 1 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (1 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 1 := by simpa using hj
    have hj_le_nat : j <= 0 := by omega
    have hj_le_real : (j : Real) <= (0 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (0 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg0Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg0_expPolyIntegral :
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg0Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg0Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-2 : Real))
    ((-9 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg0_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-2 : Real))..((-9 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg0Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-9 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-9 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-9 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg0_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg0_expPolyIntegral

def p0PieceK9D16PlusWindowSeg1Coeff : Nat -> Real
  | 0 => ((-850851717672992089 : Real) / (1865385657780650 : Real))
  | 1 => ((-1901798070642983299 : Real) / (373077131556130 : Real))
  | 2 => ((-1996798070642983299 : Real) / (74615426311226 : Real))
  | 3 => ((-6555382814987169645 : Real) / (74615426311226 : Real))
  | 4 => ((-7552925349985744050 : Real) / (37307713155613 : Real))
  | 5 => ((-12991958916642906750 : Real) / (37307713155613 : Real))
  | 6 => ((-17312469891944508750 : Real) / (37307713155613 : Real))
  | 7 => ((-18299467944069731250 : Real) / (37307713155613 : Real))
  | 8 => ((-15577603495058109375 : Real) / (37307713155613 : Real))
  | 9 => ((-10777858179514765625 : Real) / (37307713155613 : Real))
  | 10 => ((-6087935533758203125 : Real) / (37307713155613 : Real))
  | 11 => ((-2808249283810546875 : Real) / (37307713155613 : Real))
  | 12 => ((-1053760947128906250 : Real) / (37307713155613 : Real))
  | 13 => ((-318907646777343750 : Real) / (37307713155613 : Real))
  | 14 => ((-76718966308593750 : Real) / (37307713155613 : Real))
  | 15 => ((-14338645019531250 : Real) / (37307713155613 : Real))
  | 16 => ((-4015814208984375 : Real) / (74615426311226 : Real))
  | 17 => ((-198303222656250 : Real) / (37307713155613 : Real))
  | 18 => ((-49285888671875 : Real) / (149230852622452 : Real))
  | 19 => ((-2899169921875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg1_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-9 : Real) / (5 : Real)) < x) (hxhi : x < ((-8 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg1Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 2 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (2 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 2 := by simpa using hj
    have hj_le_nat : j <= 1 := by omega
    have hj_le_real : (j : Real) <= (1 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (1 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg1Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg1_expPolyIntegral :
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg1Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg1Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-9 : Real) / (5 : Real))
    ((-8 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg1_centeredBSplineR_expIntegral :
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-9 : Real) / (5 : Real))..((-8 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg1Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-8 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-9 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-8 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-8 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg1_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg1_expPolyIntegral

def p0PieceK9D16PlusWindowSeg2Coeff : Nat -> Real
  | 0 => ((103648513809527739 : Real) / (373077131556130 : Real))
  | 1 => ((43541963236081123 : Real) / (12034746179230 : Real))
  | 2 => ((1661250726688702077 : Real) / (74615426311226 : Real))
  | 3 => ((6400206675562549395 : Real) / (74615426311226 : Real))
  | 4 => ((8641561513201404750 : Real) / (37307713155613 : Real))
  | 5 => ((17372703951832997250 : Real) / (37307713155613 : Real))
  | 6 => ((26969330124582851250 : Real) / (37307713155613 : Real))
  | 7 => ((33099049932256668750 : Real) / (37307713155613 : Real))
  | 8 => ((32608507013997890625 : Real) / (37307713155613 : Real))
  | 9 => ((26030976237125234375 : Real) / (37307713155613 : Real))
  | 10 => ((16917585976641796875 : Real) / (37307713155613 : Real))
  | 11 => ((8955937852189453125 : Real) / (37307713155613 : Real))
  | 12 => ((3847983692871093750 : Real) / (37307713155613 : Real))
  | 13 => ((1330717953222656250 : Real) / (37307713155613 : Real))
  | 14 => ((365145033691406250 : Real) / (37307713155613 : Real))
  | 15 => ((77716354980468750 : Real) / (37307713155613 : Real))
  | 16 => ((798431396484375 : Real) / (2406949235846 : Real))
  | 17 => ((1388122558593750 : Real) / (37307713155613 : Real))
  | 18 => ((391387939453125 : Real) / (149230852622452 : Real))
  | 19 => ((26092529296875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg2_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-8 : Real) / (5 : Real)) < x) (hxhi : x < ((-7 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg2Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 3 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (3 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 3 := by simpa using hj
    have hj_le_nat : j <= 2 := by omega
    have hj_le_real : (j : Real) <= (2 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (2 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg2Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg2_expPolyIntegral :
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg2Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg2Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-8 : Real) / (5 : Real))
    ((-7 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg2_centeredBSplineR_expIntegral :
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-8 : Real) / (5 : Real))..((-7 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg2Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-7 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-8 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-7 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-7 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg2_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg2_expPolyIntegral

def p0PieceK9D16PlusWindowSeg3Coeff : Nat -> Real
  | 0 => ((-65747228259315228 : Real) / (932692828890325 : Real))
  | 1 => ((-206885533109250727 : Real) / (186538565778065 : Real))
  | 2 => ((-303099446572302276 : Real) / (37307713155613 : Real))
  | 3 => ((-1388782797595655385 : Real) / (37307713155613 : Real))
  | 4 => ((-4469541730732681200 : Real) / (37307713155613 : Real))
  | 5 => ((-10722517285168615500 : Real) / (37307713155613 : Real))
  | 6 => ((-19856038603753170000 : Real) / (37307713155613 : Real))
  | 7 => ((-29016235115536012500 : Real) / (37307713155613 : Real))
  | 8 => ((-33943584108637125000 : Real) / (37307713155613 : Real))
  | 9 => ((-32070055695333906250 : Real) / (37307713155613 : Real))
  | 10 => ((-24583151117971875000 : Real) / (37307713155613 : Real))
  | 11 => ((-15297739670636718750 : Real) / (37307713155613 : Real))
  | 12 => ((-7701386556093750000 : Real) / (37307713155613 : Real))
  | 13 => ((-3111347527148437500 : Real) / (37307713155613 : Real))
  | 14 => ((-994670929687500000 : Real) / (37307713155613 : Real))
  | 15 => ((-246049350585937500 : Real) / (37307713155613 : Real))
  | 16 => ((-45439617919921875 : Real) / (37307713155613 : Real))
  | 17 => ((-11799041748046875 : Real) / (74615426311226 : Real))
  | 18 => ((-1922149658203125 : Real) / (149230852622452 : Real))
  | 19 => ((-147857666015625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg3_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-7 : Real) / (5 : Real)) < x) (hxhi : x < ((-6 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg3Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 4 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (4 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 4 := by simpa using hj
    have hj_le_nat : j <= 3 := by omega
    have hj_le_real : (j : Real) <= (3 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (3 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg3Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg3_expPolyIntegral :
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg3Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg3Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-7 : Real) / (5 : Real))
    ((-6 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg3_centeredBSplineR_expIntegral :
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-7 : Real) / (5 : Real))..((-6 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg3Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-6 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-7 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-6 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-6 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg3_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg3_expPolyIntegral

def p0PieceK9D16PlusWindowSeg4Coeff : Nat -> Real
  | 0 => ((322458809978244 : Real) / (37307713155613 : Real))
  | 1 => ((5368402433705029 : Real) / (37307713155613 : Real))
  | 2 => ((47491871344361532 : Real) / (37307713155613 : Real))
  | 3 => ((266787314788590375 : Real) / (37307713155613 : Real))
  | 4 => ((1049025310548138000 : Real) / (37307713155613 : Real))
  | 5 => ((3073900318033432500 : Real) / (37307713155613 : Real))
  | 6 => ((6970328958028590000 : Real) / (37307713155613 : Real))
  | 7 => ((403250396822812500 : Real) / (1203474617923 : Real))
  | 8 => ((17952662662666875000 : Real) / (37307713155613 : Real))
  | 9 => ((20787232682846093750 : Real) / (37307713155613 : Real))
  | 10 => ((19464589197178125000 : Real) / (37307713155613 : Real))
  | 11 => ((14734810544238281250 : Real) / (37307713155613 : Real))
  | 12 => ((8983363563281250000 : Real) / (37307713155613 : Real))
  | 13 => ((4375399321289062500 : Real) / (37307713155613 : Real))
  | 14 => ((1679167230468750000 : Real) / (37307713155613 : Real))
  | 15 => ((496683471679687500 : Real) / (37307713155613 : Real))
  | 16 => ((109296386718750000 : Real) / (37307713155613 : Real))
  | 17 => ((16855773925781250 : Real) / (37307713155613 : Real))
  | 18 => ((1626434326171875 : Real) / (37307713155613 : Real))
  | 19 => ((147857666015625 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg4_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-6 : Real) / (5 : Real)) < x) (hxhi : x < ((-1 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg4Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 5 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (5 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 5 := by simpa using hj
    have hj_le_nat : j <= 4 := by omega
    have hj_le_real : (j : Real) <= (4 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (4 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg4Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg4_expPolyIntegral :
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg4Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg4Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-6 : Real) / (5 : Real))
    ((-1 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg4_centeredBSplineR_expIntegral :
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
  calc
    ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-6 : Real) / (5 : Real))..((-1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg4Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-6 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg4_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg4_expPolyIntegral

def p0PieceK9D16PlusWindowSeg5Coeff : Nat -> Real
  | 0 => ((26743477946994 : Real) / (37307713155613 : Real))
  | 1 => ((-250188874888721 : Real) / (37307713155613 : Real))
  | 2 => ((-3075450432982218 : Real) / (37307713155613 : Real))
  | 3 => ((-19760841949690875 : Real) / (37307713155613 : Real))
  | 4 => ((-97167316404987000 : Real) / (37307713155613 : Real))
  | 5 => ((-364677562825942500 : Real) / (37307713155613 : Real))
  | 6 => ((-1053019430643285000 : Real) / (37307713155613 : Real))
  | 7 => ((-2399741848883437500 : Real) / (37307713155613 : Real))
  | 8 => ((-4398093562919062500 : Real) / (37307713155613 : Real))
  | 9 => ((-6530358259536718750 : Real) / (37307713155613 : Real))
  | 10 => ((-7853001745204687500 : Real) / (37307713155613 : Real))
  | 11 => ((-7615945681347656250 : Real) / (37307713155613 : Real))
  | 12 => ((-5917140587109375000 : Real) / (37307713155613 : Real))
  | 13 => ((-117675776367187500 : Real) / (1203474617923 : Real))
  | 14 => ((-1759410650390625000 : Real) / (37307713155613 : Real))
  | 15 => ((-649509155273437500 : Real) / (37307713155613 : Real))
  | 16 => ((-177251770019531250 : Real) / (37307713155613 : Real))
  | 17 => ((-33711547851562500 : Real) / (37307713155613 : Real))
  | 18 => ((-3992156982421875 : Real) / (37307713155613 : Real))
  | 19 => ((-443572998046875 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg5_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real)) < x) (hxhi : x < ((-4 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg5Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 6 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (6 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 6 := by simpa using hj
    have hj_le_nat : j <= 5 := by omega
    have hj_le_real : (j : Real) <= (5 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (5 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg5Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg5_expPolyIntegral :
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg5Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg5Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-1 : Real))
    ((-4 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg5_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-1 : Real))..((-4 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg5Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-4 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-4 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-4 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg5_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg5_expPolyIntegral

def p0PieceK9D16PlusWindowSeg6Coeff : Nat -> Real
  | 0 => ((934943640503586 : Real) / (932692828890325 : Real))
  | 1 => ((14249911742891 : Real) / (186538565778065 : Real))
  | 2 => ((-228763289062602 : Real) / (37307713155613 : Real))
  | 3 => ((403191986406405 : Real) / (37307713155613 : Real))
  | 4 => ((3652853275499400 : Real) / (37307713155613 : Real))
  | 5 => ((13398073475881500 : Real) / (37307713155613 : Real))
  | 6 => ((49701175237035000 : Real) / (37307713155613 : Real))
  | 7 => ((160145271910162500 : Real) / (37307713155613 : Real))
  | 8 => ((401694788568937500 : Real) / (37307713155613 : Real))
  | 9 => ((802651721903281250 : Real) / (37307713155613 : Real))
  | 10 => ((1313260731595312500 : Real) / (37307713155613 : Real))
  | 11 => ((1758640942652343750 : Real) / (37307713155613 : Real))
  | 12 => ((1895014932890625000 : Real) / (37307713155613 : Real))
  | 13 => ((1610232532617187500 : Real) / (37307713155613 : Real))
  | 14 => ((1057472349609375000 : Real) / (37307713155613 : Real))
  | 15 => ((524192094726562500 : Real) / (37307713155613 : Real))
  | 16 => ((189529870605468750 : Real) / (37307713155613 : Real))
  | 17 => ((47196166992187500 : Real) / (37307713155613 : Real))
  | 18 => ((7245025634765625 : Real) / (37307713155613 : Real))
  | 19 => ((1035003662109375 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg6_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-4 : Real) / (5 : Real)) < x) (hxhi : x < ((-3 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg6Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 7 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (7 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 7 := by simpa using hj
    have hj_le_nat : j <= 6 := by omega
    have hj_le_real : (j : Real) <= (6 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (6 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg6Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg6_expPolyIntegral :
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg6Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg6Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-4 : Real) / (5 : Real))
    ((-3 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg6_centeredBSplineR_expIntegral :
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-4 : Real) / (5 : Real))..((-3 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg6Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-3 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-4 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-3 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-3 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg6_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg6_expPolyIntegral

def p0PieceK9D16PlusWindowSeg7Coeff : Nat -> Real
  | 0 => ((186538235556108 : Real) / (186538565778065 : Real))
  | 1 => ((-15685503067 : Real) / (186538565778065 : Real))
  | 2 => ((-271560080800476 : Real) / (37307713155613 : Real))
  | 3 => ((-999935562405 : Real) / (37307713155613 : Real))
  | 4 => ((958240462374000 : Real) / (37307713155613 : Real))
  | 5 => ((-74990589745500 : Real) / (37307713155613 : Real))
  | 6 => ((-2694073907070000 : Real) / (37307713155613 : Real))
  | 7 => ((-2030499250162500 : Real) / (37307713155613 : Real))
  | 8 => ((-3744639331875000 : Real) / (37307713155613 : Real))
  | 9 => ((-23243409005781250 : Real) / (37307713155613 : Real))
  | 10 => ((-63231153253125000 : Real) / (37307713155613 : Real))
  | 11 => ((-118393445777343750 : Real) / (37307713155613 : Real))
  | 12 => ((-190578832031250000 : Real) / (37307713155613 : Real))
  | 13 => ((-261454179492187500 : Real) / (37307713155613 : Real))
  | 14 => ((-279446730468750000 : Real) / (37307713155613 : Real))
  | 15 => ((-218540727539062500 : Real) / (37307713155613 : Real))
  | 16 => ((-119942138671875000 : Real) / (37307713155613 : Real))
  | 17 => ((-43825012207031250 : Real) / (37307713155613 : Real))
  | 18 => ((-9610748291015625 : Real) / (37307713155613 : Real))
  | 19 => ((-1922149658203125 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg7_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-3 : Real) / (5 : Real)) < x) (hxhi : x < ((-2 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg7Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 8 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (8 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 8 := by simpa using hj
    have hj_le_nat : j <= 7 := by omega
    have hj_le_real : (j : Real) <= (7 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (7 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg7Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg7_expPolyIntegral :
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg7Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg7Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-3 : Real) / (5 : Real))
    ((-2 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg7_centeredBSplineR_expIntegral :
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-3 : Real) / (5 : Real))..((-2 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg7Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-2 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-3 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-2 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-2 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg7_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg7_expPolyIntegral

def p0PieceK9D16PlusWindowSeg8Coeff : Nat -> Real
  | 0 => ((932692828894524 : Real) / (932692828890325 : Real))
  | 1 => ((79781 : Real) / (186538565778065 : Real))
  | 2 => ((-271489495677660 : Real) / (37307713155613 : Real))
  | 3 => ((20344155 : Real) / (37307713155613 : Real))
  | 4 => ((968240021439600 : Real) / (37307713155613 : Real))
  | 5 => ((6103246500 : Real) / (37307713155613 : Real))
  | 6 => ((-2256593197950000 : Real) / (37307713155613 : Real))
  | 7 => ((661185037500 : Real) / (37307713155613 : Real))
  | 8 => ((3872212300125000 : Real) / (37307713155613 : Real))
  | 9 => ((30304314218750 : Real) / (37307713155613 : Real))
  | 10 => ((-5046869953125000 : Real) / (37307713155613 : Real))
  | 11 => ((619860972656250 : Real) / (37307713155613 : Real))
  | 12 => ((7776679218750000 : Real) / (37307713155613 : Real))
  | 13 => ((5562854882812500 : Real) / (37307713155613 : Real))
  | 14 => ((6642949218750000 : Real) / (37307713155613 : Real))
  | 15 => ((19867338867187500 : Real) / (37307713155613 : Real))
  | 16 => ((29062902832031250 : Real) / (37307713155613 : Real))
  | 17 => ((21912506103515625 : Real) / (37307713155613 : Real))
  | 18 => ((17299346923828125 : Real) / (74615426311226 : Real))
  | 19 => ((5766448974609375 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg8_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real) / (5 : Real)) < x) (hxhi : x < ((-1 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg8Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 9 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (9 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 9 := by simpa using hj
    have hj_le_nat : j <= 8 := by omega
    have hj_le_real : (j : Real) <= (8 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (8 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg8Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg8_expPolyIntegral :
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg8Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg8Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-2 : Real) / (5 : Real))
    ((-1 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg8_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-2 : Real) / (5 : Real))..((-1 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg8Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg8_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg8_expPolyIntegral

def p0PieceK9D16PlusWindowSeg9Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-271489496395689 : Real) / (37307713155613 : Real))
  | 3 => ((0 : Real))
  | 4 => ((968239614556500 : Real) / (37307713155613 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-2256664402492500 : Real) / (37307713155613 : Real))
  | 7 => ((0 : Real))
  | 8 => ((3867253412343750 : Real) / (37307713155613 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-5198391524218750 : Real) / (37307713155613 : Real))
  | 11 => ((0 : Real))
  | 12 => ((5710475976562500 : Real) / (37307713155613 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-5277454101562500 : Real) / (37307713155613 : Real))
  | 15 => ((0 : Real))
  | 16 => ((4228729248046875 : Real) / (37307713155613 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-7047882080078125 : Real) / (74615426311226 : Real))
  | 19 => ((-7047882080078125 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg9_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (5 : Real)) < x) (hxhi : x < ((0 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg9Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 10 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (10 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 10 := by simpa using hj
    have hj_le_nat : j <= 9 := by omega
    have hj_le_real : (j : Real) <= (9 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (9 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg9Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg9_expPolyIntegral :
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg9Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg9Coeff 20
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (5 : Real))
    ((0 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg9_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-1 : Real) / (5 : Real))..((0 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg9Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((0 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((0 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((0 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg9_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg9_expPolyIntegral

def p0PieceK9D16PlusWindowSeg10Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-271489496395689 : Real) / (37307713155613 : Real))
  | 3 => ((0 : Real))
  | 4 => ((968239614556500 : Real) / (37307713155613 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-2256664402492500 : Real) / (37307713155613 : Real))
  | 7 => ((0 : Real))
  | 8 => ((3867253412343750 : Real) / (37307713155613 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-5198391524218750 : Real) / (37307713155613 : Real))
  | 11 => ((0 : Real))
  | 12 => ((5710475976562500 : Real) / (37307713155613 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-5277454101562500 : Real) / (37307713155613 : Real))
  | 15 => ((0 : Real))
  | 16 => ((4228729248046875 : Real) / (37307713155613 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-7047882080078125 : Real) / (74615426311226 : Real))
  | 19 => ((7047882080078125 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg10_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((0 : Real)) < x) (hxhi : x < ((1 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg10Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 11 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (11 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 11 := by simpa using hj
    have hj_le_nat : j <= 10 := by omega
    have hj_le_real : (j : Real) <= (10 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (10 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg10Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg10_expPolyIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg10Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg10Coeff 20
    ((-3 : Real) / (20 : Real))
    ((0 : Real))
    ((1 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg10_centeredBSplineR_expIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((0 : Real))..((1 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg10Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((0 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg10_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg10_expPolyIntegral

def p0PieceK9D16PlusWindowSeg11Coeff : Nat -> Real
  | 0 => ((932692828894524 : Real) / (932692828890325 : Real))
  | 1 => ((-79781 : Real) / (186538565778065 : Real))
  | 2 => ((-271489495677660 : Real) / (37307713155613 : Real))
  | 3 => ((-20344155 : Real) / (37307713155613 : Real))
  | 4 => ((968240021439600 : Real) / (37307713155613 : Real))
  | 5 => ((-6103246500 : Real) / (37307713155613 : Real))
  | 6 => ((-2256593197950000 : Real) / (37307713155613 : Real))
  | 7 => ((-661185037500 : Real) / (37307713155613 : Real))
  | 8 => ((3872212300125000 : Real) / (37307713155613 : Real))
  | 9 => ((-30304314218750 : Real) / (37307713155613 : Real))
  | 10 => ((-5046869953125000 : Real) / (37307713155613 : Real))
  | 11 => ((-619860972656250 : Real) / (37307713155613 : Real))
  | 12 => ((7776679218750000 : Real) / (37307713155613 : Real))
  | 13 => ((-5562854882812500 : Real) / (37307713155613 : Real))
  | 14 => ((6642949218750000 : Real) / (37307713155613 : Real))
  | 15 => ((-19867338867187500 : Real) / (37307713155613 : Real))
  | 16 => ((29062902832031250 : Real) / (37307713155613 : Real))
  | 17 => ((-21912506103515625 : Real) / (37307713155613 : Real))
  | 18 => ((17299346923828125 : Real) / (74615426311226 : Real))
  | 19 => ((-5766448974609375 : Real) / (149230852622452 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg11_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (5 : Real)) < x) (hxhi : x < ((2 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg11Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 12 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (12 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 12 := by simpa using hj
    have hj_le_nat : j <= 11 := by omega
    have hj_le_real : (j : Real) <= (11 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (11 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg11Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg11_expPolyIntegral :
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg11Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg11Coeff 20
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (5 : Real))
    ((2 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg11_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((1 : Real) / (5 : Real))..((2 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg11Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg11_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg11_expPolyIntegral

def p0PieceK9D16PlusWindowSeg12Coeff : Nat -> Real
  | 0 => ((186538235556108 : Real) / (186538565778065 : Real))
  | 1 => ((15685503067 : Real) / (186538565778065 : Real))
  | 2 => ((-271560080800476 : Real) / (37307713155613 : Real))
  | 3 => ((999935562405 : Real) / (37307713155613 : Real))
  | 4 => ((958240462374000 : Real) / (37307713155613 : Real))
  | 5 => ((74990589745500 : Real) / (37307713155613 : Real))
  | 6 => ((-2694073907070000 : Real) / (37307713155613 : Real))
  | 7 => ((2030499250162500 : Real) / (37307713155613 : Real))
  | 8 => ((-3744639331875000 : Real) / (37307713155613 : Real))
  | 9 => ((23243409005781250 : Real) / (37307713155613 : Real))
  | 10 => ((-63231153253125000 : Real) / (37307713155613 : Real))
  | 11 => ((118393445777343750 : Real) / (37307713155613 : Real))
  | 12 => ((-190578832031250000 : Real) / (37307713155613 : Real))
  | 13 => ((261454179492187500 : Real) / (37307713155613 : Real))
  | 14 => ((-279446730468750000 : Real) / (37307713155613 : Real))
  | 15 => ((218540727539062500 : Real) / (37307713155613 : Real))
  | 16 => ((-119942138671875000 : Real) / (37307713155613 : Real))
  | 17 => ((43825012207031250 : Real) / (37307713155613 : Real))
  | 18 => ((-9610748291015625 : Real) / (37307713155613 : Real))
  | 19 => ((1922149658203125 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg12_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((2 : Real) / (5 : Real)) < x) (hxhi : x < ((3 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg12Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 13 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (13 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 13 := by simpa using hj
    have hj_le_nat : j <= 12 := by omega
    have hj_le_real : (j : Real) <= (12 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (12 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg12Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg12_expPolyIntegral :
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg12Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg12Coeff 20
    ((-3 : Real) / (20 : Real))
    ((2 : Real) / (5 : Real))
    ((3 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg12_centeredBSplineR_expIntegral :
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((2 : Real) / (5 : Real))..((3 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg12Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((3 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((2 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((3 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((3 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg12_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg12_expPolyIntegral

def p0PieceK9D16PlusWindowSeg13Coeff : Nat -> Real
  | 0 => ((934943640503586 : Real) / (932692828890325 : Real))
  | 1 => ((-14249911742891 : Real) / (186538565778065 : Real))
  | 2 => ((-228763289062602 : Real) / (37307713155613 : Real))
  | 3 => ((-403191986406405 : Real) / (37307713155613 : Real))
  | 4 => ((3652853275499400 : Real) / (37307713155613 : Real))
  | 5 => ((-13398073475881500 : Real) / (37307713155613 : Real))
  | 6 => ((49701175237035000 : Real) / (37307713155613 : Real))
  | 7 => ((-160145271910162500 : Real) / (37307713155613 : Real))
  | 8 => ((401694788568937500 : Real) / (37307713155613 : Real))
  | 9 => ((-802651721903281250 : Real) / (37307713155613 : Real))
  | 10 => ((1313260731595312500 : Real) / (37307713155613 : Real))
  | 11 => ((-1758640942652343750 : Real) / (37307713155613 : Real))
  | 12 => ((1895014932890625000 : Real) / (37307713155613 : Real))
  | 13 => ((-1610232532617187500 : Real) / (37307713155613 : Real))
  | 14 => ((1057472349609375000 : Real) / (37307713155613 : Real))
  | 15 => ((-524192094726562500 : Real) / (37307713155613 : Real))
  | 16 => ((189529870605468750 : Real) / (37307713155613 : Real))
  | 17 => ((-47196166992187500 : Real) / (37307713155613 : Real))
  | 18 => ((7245025634765625 : Real) / (37307713155613 : Real))
  | 19 => ((-1035003662109375 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg13_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((3 : Real) / (5 : Real)) < x) (hxhi : x < ((4 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg13Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 14 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (14 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 14 := by simpa using hj
    have hj_le_nat : j <= 13 := by omega
    have hj_le_real : (j : Real) <= (13 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (13 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg13Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg13_expPolyIntegral :
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg13Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg13Coeff 20
    ((-3 : Real) / (20 : Real))
    ((3 : Real) / (5 : Real))
    ((4 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg13_centeredBSplineR_expIntegral :
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((3 : Real) / (5 : Real))..((4 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg13Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((4 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((3 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((4 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((4 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg13_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg13_expPolyIntegral

def p0PieceK9D16PlusWindowSeg14Coeff : Nat -> Real
  | 0 => ((26743477946994 : Real) / (37307713155613 : Real))
  | 1 => ((250188874888721 : Real) / (37307713155613 : Real))
  | 2 => ((-3075450432982218 : Real) / (37307713155613 : Real))
  | 3 => ((19760841949690875 : Real) / (37307713155613 : Real))
  | 4 => ((-97167316404987000 : Real) / (37307713155613 : Real))
  | 5 => ((364677562825942500 : Real) / (37307713155613 : Real))
  | 6 => ((-1053019430643285000 : Real) / (37307713155613 : Real))
  | 7 => ((2399741848883437500 : Real) / (37307713155613 : Real))
  | 8 => ((-4398093562919062500 : Real) / (37307713155613 : Real))
  | 9 => ((6530358259536718750 : Real) / (37307713155613 : Real))
  | 10 => ((-7853001745204687500 : Real) / (37307713155613 : Real))
  | 11 => ((7615945681347656250 : Real) / (37307713155613 : Real))
  | 12 => ((-5917140587109375000 : Real) / (37307713155613 : Real))
  | 13 => ((117675776367187500 : Real) / (1203474617923 : Real))
  | 14 => ((-1759410650390625000 : Real) / (37307713155613 : Real))
  | 15 => ((649509155273437500 : Real) / (37307713155613 : Real))
  | 16 => ((-177251770019531250 : Real) / (37307713155613 : Real))
  | 17 => ((33711547851562500 : Real) / (37307713155613 : Real))
  | 18 => ((-3992156982421875 : Real) / (37307713155613 : Real))
  | 19 => ((443572998046875 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg14_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((4 : Real) / (5 : Real)) < x) (hxhi : x < ((1 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg14Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 15 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (15 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 15 := by simpa using hj
    have hj_le_nat : j <= 14 := by omega
    have hj_le_real : (j : Real) <= (14 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (14 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg14Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg14_expPolyIntegral :
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg14Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg14Coeff 20
    ((-3 : Real) / (20 : Real))
    ((4 : Real) / (5 : Real))
    ((1 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg14_centeredBSplineR_expIntegral :
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
  calc
    ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((4 : Real) / (5 : Real))..((1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg14Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((4 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg14_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg14_expPolyIntegral

def p0PieceK9D16PlusWindowSeg15Coeff : Nat -> Real
  | 0 => ((322458809978244 : Real) / (37307713155613 : Real))
  | 1 => ((-5368402433705029 : Real) / (37307713155613 : Real))
  | 2 => ((47491871344361532 : Real) / (37307713155613 : Real))
  | 3 => ((-266787314788590375 : Real) / (37307713155613 : Real))
  | 4 => ((1049025310548138000 : Real) / (37307713155613 : Real))
  | 5 => ((-3073900318033432500 : Real) / (37307713155613 : Real))
  | 6 => ((6970328958028590000 : Real) / (37307713155613 : Real))
  | 7 => ((-403250396822812500 : Real) / (1203474617923 : Real))
  | 8 => ((17952662662666875000 : Real) / (37307713155613 : Real))
  | 9 => ((-20787232682846093750 : Real) / (37307713155613 : Real))
  | 10 => ((19464589197178125000 : Real) / (37307713155613 : Real))
  | 11 => ((-14734810544238281250 : Real) / (37307713155613 : Real))
  | 12 => ((8983363563281250000 : Real) / (37307713155613 : Real))
  | 13 => ((-4375399321289062500 : Real) / (37307713155613 : Real))
  | 14 => ((1679167230468750000 : Real) / (37307713155613 : Real))
  | 15 => ((-496683471679687500 : Real) / (37307713155613 : Real))
  | 16 => ((109296386718750000 : Real) / (37307713155613 : Real))
  | 17 => ((-16855773925781250 : Real) / (37307713155613 : Real))
  | 18 => ((1626434326171875 : Real) / (37307713155613 : Real))
  | 19 => ((-147857666015625 : Real) / (74615426311226 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg15_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real)) < x) (hxhi : x < ((6 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg15Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 16 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (16 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 16 := by simpa using hj
    have hj_le_nat : j <= 15 := by omega
    have hj_le_real : (j : Real) <= (15 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (15 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg15Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg15_expPolyIntegral :
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg15Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg15Coeff 20
    ((-3 : Real) / (20 : Real))
    ((1 : Real))
    ((6 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg15_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((1 : Real))..((6 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg15Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((6 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((6 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((6 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg15_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg15_expPolyIntegral

def p0PieceK9D16PlusWindowSeg16Coeff : Nat -> Real
  | 0 => ((-65747228259315228 : Real) / (932692828890325 : Real))
  | 1 => ((206885533109250727 : Real) / (186538565778065 : Real))
  | 2 => ((-303099446572302276 : Real) / (37307713155613 : Real))
  | 3 => ((1388782797595655385 : Real) / (37307713155613 : Real))
  | 4 => ((-4469541730732681200 : Real) / (37307713155613 : Real))
  | 5 => ((10722517285168615500 : Real) / (37307713155613 : Real))
  | 6 => ((-19856038603753170000 : Real) / (37307713155613 : Real))
  | 7 => ((29016235115536012500 : Real) / (37307713155613 : Real))
  | 8 => ((-33943584108637125000 : Real) / (37307713155613 : Real))
  | 9 => ((32070055695333906250 : Real) / (37307713155613 : Real))
  | 10 => ((-24583151117971875000 : Real) / (37307713155613 : Real))
  | 11 => ((15297739670636718750 : Real) / (37307713155613 : Real))
  | 12 => ((-7701386556093750000 : Real) / (37307713155613 : Real))
  | 13 => ((3111347527148437500 : Real) / (37307713155613 : Real))
  | 14 => ((-994670929687500000 : Real) / (37307713155613 : Real))
  | 15 => ((246049350585937500 : Real) / (37307713155613 : Real))
  | 16 => ((-45439617919921875 : Real) / (37307713155613 : Real))
  | 17 => ((11799041748046875 : Real) / (74615426311226 : Real))
  | 18 => ((-1922149658203125 : Real) / (149230852622452 : Real))
  | 19 => ((147857666015625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg16_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((6 : Real) / (5 : Real)) < x) (hxhi : x < ((7 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg16Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 17 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (17 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 17 := by simpa using hj
    have hj_le_nat : j <= 16 := by omega
    have hj_le_real : (j : Real) <= (16 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (16 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg16Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg16_expPolyIntegral :
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg16Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg16Coeff 20
    ((-3 : Real) / (20 : Real))
    ((6 : Real) / (5 : Real))
    ((7 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg16_centeredBSplineR_expIntegral :
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((6 : Real) / (5 : Real))..((7 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg16Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((7 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((6 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((7 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((7 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg16_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg16_expPolyIntegral

def p0PieceK9D16PlusWindowSeg17Coeff : Nat -> Real
  | 0 => ((103648513809527739 : Real) / (373077131556130 : Real))
  | 1 => ((-43541963236081123 : Real) / (12034746179230 : Real))
  | 2 => ((1661250726688702077 : Real) / (74615426311226 : Real))
  | 3 => ((-6400206675562549395 : Real) / (74615426311226 : Real))
  | 4 => ((8641561513201404750 : Real) / (37307713155613 : Real))
  | 5 => ((-17372703951832997250 : Real) / (37307713155613 : Real))
  | 6 => ((26969330124582851250 : Real) / (37307713155613 : Real))
  | 7 => ((-33099049932256668750 : Real) / (37307713155613 : Real))
  | 8 => ((32608507013997890625 : Real) / (37307713155613 : Real))
  | 9 => ((-26030976237125234375 : Real) / (37307713155613 : Real))
  | 10 => ((16917585976641796875 : Real) / (37307713155613 : Real))
  | 11 => ((-8955937852189453125 : Real) / (37307713155613 : Real))
  | 12 => ((3847983692871093750 : Real) / (37307713155613 : Real))
  | 13 => ((-1330717953222656250 : Real) / (37307713155613 : Real))
  | 14 => ((365145033691406250 : Real) / (37307713155613 : Real))
  | 15 => ((-77716354980468750 : Real) / (37307713155613 : Real))
  | 16 => ((798431396484375 : Real) / (2406949235846 : Real))
  | 17 => ((-1388122558593750 : Real) / (37307713155613 : Real))
  | 18 => ((391387939453125 : Real) / (149230852622452 : Real))
  | 19 => ((-26092529296875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg17_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((7 : Real) / (5 : Real)) < x) (hxhi : x < ((8 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg17Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 18 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (18 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 18 := by simpa using hj
    have hj_le_nat : j <= 17 := by omega
    have hj_le_real : (j : Real) <= (17 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (17 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg17Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg17_expPolyIntegral :
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg17Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg17Coeff 20
    ((-3 : Real) / (20 : Real))
    ((7 : Real) / (5 : Real))
    ((8 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg17_centeredBSplineR_expIntegral :
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((7 : Real) / (5 : Real))..((8 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg17Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((8 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((7 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((8 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((8 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg17_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg17_expPolyIntegral

def p0PieceK9D16PlusWindowSeg18Coeff : Nat -> Real
  | 0 => ((-850851717672992089 : Real) / (1865385657780650 : Real))
  | 1 => ((1901798070642983299 : Real) / (373077131556130 : Real))
  | 2 => ((-1996798070642983299 : Real) / (74615426311226 : Real))
  | 3 => ((6555382814987169645 : Real) / (74615426311226 : Real))
  | 4 => ((-7552925349985744050 : Real) / (37307713155613 : Real))
  | 5 => ((12991958916642906750 : Real) / (37307713155613 : Real))
  | 6 => ((-17312469891944508750 : Real) / (37307713155613 : Real))
  | 7 => ((18299467944069731250 : Real) / (37307713155613 : Real))
  | 8 => ((-15577603495058109375 : Real) / (37307713155613 : Real))
  | 9 => ((10777858179514765625 : Real) / (37307713155613 : Real))
  | 10 => ((-6087935533758203125 : Real) / (37307713155613 : Real))
  | 11 => ((2808249283810546875 : Real) / (37307713155613 : Real))
  | 12 => ((-1053760947128906250 : Real) / (37307713155613 : Real))
  | 13 => ((318907646777343750 : Real) / (37307713155613 : Real))
  | 14 => ((-76718966308593750 : Real) / (37307713155613 : Real))
  | 15 => ((14338645019531250 : Real) / (37307713155613 : Real))
  | 16 => ((-4015814208984375 : Real) / (74615426311226 : Real))
  | 17 => ((198303222656250 : Real) / (37307713155613 : Real))
  | 18 => ((-49285888671875 : Real) / (149230852622452 : Real))
  | 19 => ((2899169921875 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg18_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((8 : Real) / (5 : Real)) < x) (hxhi : x < ((9 : Real) / (5 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg18Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 19 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (19 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 19 := by simpa using hj
    have hj_le_nat : j <= 18 := by omega
    have hj_le_real : (j : Real) <= (18 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (18 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg18Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg18_expPolyIntegral :
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg18Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg18Coeff 20
    ((-3 : Real) / (20 : Real))
    ((8 : Real) / (5 : Real))
    ((9 : Real) / (5 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg18_centeredBSplineR_expIntegral :
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
  calc
    ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((8 : Real) / (5 : Real))..((9 : Real) / (5 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg18Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((9 : Real) / (5 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((8 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((9 : Real) / (5 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((9 : Real) / (5 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg18_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg18_expPolyIntegral

def p0PieceK9D16PlusWindowSeg19Coeff : Nat -> Real
  | 0 => ((10000000000000000 : Real) / (37307713155613 : Real))
  | 1 => ((-95000000000000000 : Real) / (37307713155613 : Real))
  | 2 => ((427500000000000000 : Real) / (37307713155613 : Real))
  | 3 => ((-1211250000000000000 : Real) / (37307713155613 : Real))
  | 4 => ((2422500000000000000 : Real) / (37307713155613 : Real))
  | 5 => ((-3633750000000000000 : Real) / (37307713155613 : Real))
  | 6 => ((4239375000000000000 : Real) / (37307713155613 : Real))
  | 7 => ((-3936562500000000000 : Real) / (37307713155613 : Real))
  | 8 => ((2952421875000000000 : Real) / (37307713155613 : Real))
  | 9 => ((-1804257812500000000 : Real) / (37307713155613 : Real))
  | 10 => ((902128906250000000 : Real) / (37307713155613 : Real))
  | 11 => ((-369052734375000000 : Real) / (37307713155613 : Real))
  | 12 => ((123017578125000000 : Real) / (37307713155613 : Real))
  | 13 => ((-33120117187500000 : Real) / (37307713155613 : Real))
  | 14 => ((7097167968750000 : Real) / (37307713155613 : Real))
  | 15 => ((-1182861328125000 : Real) / (37307713155613 : Real))
  | 16 => ((147857666015625 : Real) / (37307713155613 : Real))
  | 17 => ((-26092529296875 : Real) / (74615426311226 : Real))
  | 18 => ((2899169921875 : Real) / (149230852622452 : Real))
  | 19 => ((-152587890625 : Real) / (298461705244904 : Real))
  | _ => 0

theorem p0PieceK9D16PlusWindowSeg19_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((9 : Real) / (5 : Real)) < x) (hxhi : x < ((2 : Real))) :
    centeredBSplineR 9 x = expPoly p0PieceK9D16PlusWindowSeg19Coeff 20 x := by
  have hsum :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 20 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (20 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
              ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 19 hnon]
      ring
  have hactive :
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          positivePartPower 19
            (bsplineScale 9 * x + ((10 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 20 j : Real) *
          (bsplineScale 9 * x + ((10 : Real)) - (j : Real)) ^ 19) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 20 := by simpa using hj
    have hj_le_nat : j <= 19 := by omega
    have hj_le_real : (j : Real) <= (19 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 9 * x + ((10 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 9 * x + ((10 : Real)) - (j : Real) =
            ((5 : Real)) * x + ((10 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (19 : Real) < ((5 : Real)) * x + ((10 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 19 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK9D16PlusWindowSeg19Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_9_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK9D16PlusWindowSeg19_expPolyIntegral :
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK9D16PlusWindowSeg19Coeff 20 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK9D16PlusWindowSeg19Coeff 20
    ((-3 : Real) / (20 : Real))
    ((9 : Real) / (5 : Real))
    ((2 : Real))
    (by norm_num)

theorem p0PieceK9D16PlusWindowSeg19_centeredBSplineR_expIntegral :
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      expPolyIntegral p0PieceK9D16PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
  calc
    ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((9 : Real) / (5 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK9D16PlusWindowSeg19Coeff 20 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((9 : Real) / (5 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK9D16PlusWindowSeg19_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK9D16PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real)) := by
        exact p0PieceK9D16PlusWindowSeg19_expPolyIntegral

def p0PieceK9D16PlusWindowBreak : Nat -> Real
  | 0 => ((-2 : Real))
  | 1 => ((-9 : Real) / (5 : Real))
  | 2 => ((-8 : Real) / (5 : Real))
  | 3 => ((-7 : Real) / (5 : Real))
  | 4 => ((-6 : Real) / (5 : Real))
  | 5 => ((-1 : Real))
  | 6 => ((-4 : Real) / (5 : Real))
  | 7 => ((-3 : Real) / (5 : Real))
  | 8 => ((-2 : Real) / (5 : Real))
  | 9 => ((-1 : Real) / (5 : Real))
  | 10 => ((0 : Real))
  | 11 => ((1 : Real) / (5 : Real))
  | 12 => ((2 : Real) / (5 : Real))
  | 13 => ((3 : Real) / (5 : Real))
  | 14 => ((4 : Real) / (5 : Real))
  | 15 => ((1 : Real))
  | 16 => ((6 : Real) / (5 : Real))
  | 17 => ((7 : Real) / (5 : Real))
  | 18 => ((8 : Real) / (5 : Real))
  | 19 => ((9 : Real) / (5 : Real))
  | 20 => ((2 : Real))
  | _ => ((2 : Real))

def p0PieceK9D16PlusWindowSegmentExpIntegral : Nat -> Real
  | 0 => expPolyIntegral p0PieceK9D16PlusWindowSeg0Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-9 : Real) / (5 : Real))
  | 1 => expPolyIntegral p0PieceK9D16PlusWindowSeg1Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-9 : Real) / (5 : Real))
        ((-8 : Real) / (5 : Real))
  | 2 => expPolyIntegral p0PieceK9D16PlusWindowSeg2Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-8 : Real) / (5 : Real))
        ((-7 : Real) / (5 : Real))
  | 3 => expPolyIntegral p0PieceK9D16PlusWindowSeg3Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (5 : Real))
        ((-6 : Real) / (5 : Real))
  | 4 => expPolyIntegral p0PieceK9D16PlusWindowSeg4Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-6 : Real) / (5 : Real))
        ((-1 : Real))
  | 5 => expPolyIntegral p0PieceK9D16PlusWindowSeg5Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-4 : Real) / (5 : Real))
  | 6 => expPolyIntegral p0PieceK9D16PlusWindowSeg6Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (5 : Real))
        ((-3 : Real) / (5 : Real))
  | 7 => expPolyIntegral p0PieceK9D16PlusWindowSeg7Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (5 : Real))
        ((-2 : Real) / (5 : Real))
  | 8 => expPolyIntegral p0PieceK9D16PlusWindowSeg8Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (5 : Real))
        ((-1 : Real) / (5 : Real))
  | 9 => expPolyIntegral p0PieceK9D16PlusWindowSeg9Coeff 20
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (5 : Real))
        ((0 : Real))
  | 10 => expPolyIntegral p0PieceK9D16PlusWindowSeg10Coeff 20
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (5 : Real))
  | 11 => expPolyIntegral p0PieceK9D16PlusWindowSeg11Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (5 : Real))
        ((2 : Real) / (5 : Real))
  | 12 => expPolyIntegral p0PieceK9D16PlusWindowSeg12Coeff 20
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (5 : Real))
        ((3 : Real) / (5 : Real))
  | 13 => expPolyIntegral p0PieceK9D16PlusWindowSeg13Coeff 20
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (5 : Real))
        ((4 : Real) / (5 : Real))
  | 14 => expPolyIntegral p0PieceK9D16PlusWindowSeg14Coeff 20
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (5 : Real))
        ((1 : Real))
  | 15 => expPolyIntegral p0PieceK9D16PlusWindowSeg15Coeff 20
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((6 : Real) / (5 : Real))
  | 16 => expPolyIntegral p0PieceK9D16PlusWindowSeg16Coeff 20
        ((-3 : Real) / (20 : Real))
        ((6 : Real) / (5 : Real))
        ((7 : Real) / (5 : Real))
  | 17 => expPolyIntegral p0PieceK9D16PlusWindowSeg17Coeff 20
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (5 : Real))
        ((8 : Real) / (5 : Real))
  | 18 => expPolyIntegral p0PieceK9D16PlusWindowSeg18Coeff 20
        ((-3 : Real) / (20 : Real))
        ((8 : Real) / (5 : Real))
        ((9 : Real) / (5 : Real))
  | 19 => expPolyIntegral p0PieceK9D16PlusWindowSeg19Coeff 20
        ((-3 : Real) / (20 : Real))
        ((9 : Real) / (5 : Real))
        ((2 : Real))
  | _ => 0

def p0PieceK9D16PlusWindowExpPolyIntegralSum : Real :=
  (Finset.range 20).sum p0PieceK9D16PlusWindowSegmentExpIntegral

theorem p0PieceK9D16PlusWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D16PlusWindowExpPolyIntegralSum := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (a := p0PieceK9D16PlusWindowBreak) (n := 20)
    (μ := volume) ?hint
  calc
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        (Finset.range 20).sum (fun i =>
          ∫ x in p0PieceK9D16PlusWindowBreak i..p0PieceK9D16PlusWindowBreak (i + 1),
            Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
          simpa [p0PieceK9D16PlusWindowBreak] using hsplit.symm
    _ = (Finset.range 20).sum p0PieceK9D16PlusWindowSegmentExpIntegral := by
        apply Finset.sum_congr rfl
        intro i hi
        simp at hi
        interval_cases i <;>
          simp [p0PieceK9D16PlusWindowBreak, p0PieceK9D16PlusWindowSegmentExpIntegral]
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg0_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg1_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg2_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg3_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg4_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg5_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg6_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg7_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg8_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg9_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg10_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg11_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg12_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg13_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg14_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg15_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg16_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg17_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg18_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK9D16PlusWindowSeg19_centeredBSplineR_expIntegral
    _ = p0PieceK9D16PlusWindowExpPolyIntegralSum := by
        rfl
  · intro k hk
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _

def p0PieceK9D16MinusWindowExpPolyIntegralSum : Real := 0

theorem p0PieceK9D16PlusWindow_leftSupportZeroIntegral :
    ∫ x in ((-20 : Real) / (3 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((-20 : Real) / (3 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((-20 : Real) / (3 : Real))..((-2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D16PlusWindow_rightSupportZeroIntegral :
    ∫ x in ((2 : Real))..((40 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((2 : Real))..((40 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((2 : Real))..((40 : Real) / (3 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D16PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D16PlusWindowExpPolyIntegralSum := by
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-20 : Real) / (3 : Real))) (b := ((-2 : Real))) (c := ((40 : Real) / (3 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-2 : Real))) (b := ((2 : Real))) (c := ((40 : Real) / (3 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 9 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 9)).intervalIntegrable _ _)
  calc
    ∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        (∫ x in ((-20 : Real) / (3 : Real))..((-2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) +
        (∫ x in ((-2 : Real))..((40 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
        simpa using hsplitLeft.symm
    _ = ∫ x in ((-2 : Real))..((40 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
        rw [p0PieceK9D16PlusWindow_leftSupportZeroIntegral]
        ring
    _ = (∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) +
        (∫ x in ((2 : Real))..((40 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x) := by
        simpa using hsplitRight.symm
    _ = ∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
        rw [p0PieceK9D16PlusWindow_rightSupportZeroIntegral]
        ring
    _ = p0PieceK9D16PlusWindowExpPolyIntegralSum := by
        exact p0PieceK9D16PlusWindow_centeredBSplineR_expIntegral_sum

theorem p0PieceK9D16MinusWindow_rightSupportZeroIntegral :
    ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = 0 := by
  calc
    ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
        ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK9D16MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x =
      p0PieceK9D16MinusWindowExpPolyIntegralSum := by
  simpa [p0PieceK9D16MinusWindowExpPolyIntegralSum] using
    p0PieceK9D16MinusWindow_rightSupportZeroIntegral

theorem p0PieceK9D16_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((4 : Real)) / 2) *
        p0PieceK9D16PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((4 : Real)) / 2)) *
        p0PieceK9D16MinusWindowExpPolyIntegralSum := by
  have hprofile :=
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile_eq_transformed_integrals
      (k := 9)
      (ell := ((3 : Real) / (10 : Real)))
      (L := ((3 : Real)))
      (d := ((4 : Real)))
      (by norm_num)
  calc
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((4 : Real)) / 2) *
        (∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
          Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x) +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((4 : Real)) / 2)) *
        (∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
          Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x) := by
        norm_num at hprofile ⊢
        simpa [mul_assoc] using hprofile
    _ = ((3 : Real) / (10 : Real)) * Real.exp (((4 : Real)) / 2) *
        p0PieceK9D16PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((4 : Real)) / 2)) *
        p0PieceK9D16MinusWindowExpPolyIntegralSum := by
        have hplus :
            ∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
            p0PieceK9D16PlusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                ∫ x in ((-20 : Real) / (3 : Real))..((40 : Real) / (3 : Real)),
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x
                have harg : -(((3 : Real) / (10 : Real)) / 2) * x = ((-3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK9D16PlusWindowExpPolyIntegralSum := by
                exact p0PieceK9D16PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        have hminus :
            ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
            p0PieceK9D16MinusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                ∫ x in ((40 : Real) / (3 : Real))..((100 : Real) / (3 : Real)),
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 9 x =
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 9 x
                have harg : (((3 : Real) / (10 : Real)) / 2) * x = ((3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK9D16MinusWindowExpPolyIntegralSum := by
                exact p0PieceK9D16MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        rw [hplus, hminus]

end PSDpd
end Q3
