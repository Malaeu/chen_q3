import Q3.Proofs.PSD_P0Piecewise
import Q3.Proofs.PSD_CenteredBSplineRBoundsImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory

namespace Q3
namespace PSDpd

def p0PieceK11D13PlusWindowSeg0Coeff : Nat -> Real
  | 0 => ((69007679864054552199168 : Real) / (75489558096433522049 : Real))
  | 1 => ((793588318436627350290432 : Real) / (75489558096433522049 : Real))
  | 2 => ((4364735751401450426597376 : Real) / (75489558096433522049 : Real))
  | 3 => ((15276575129905076493090816 : Real) / (75489558096433522049 : Real))
  | 4 => ((38191437824762691232727040 : Real) / (75489558096433522049 : Real))
  | 5 => ((72563731867049113342181376 : Real) / (75489558096433522049 : Real))
  | 6 => ((108845597800573670013272064 : Real) / (75489558096433522049 : Real))
  | 7 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 8 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 9 => ((110141378726770975608668160 : Real) / (75489558096433522049 : Real))
  | 10 => ((77098965108739682926067712 : Real) / (75489558096433522049 : Real))
  | 11 => ((45558479382437085365403648 : Real) / (75489558096433522049 : Real))
  | 12 => ((22779239691218542682701824 : Real) / (75489558096433522049 : Real))
  | 13 => ((9637370638592460365758464 : Real) / (75489558096433522049 : Real))
  | 14 => ((3441918085211592987770880 : Real) / (75489558096433522049 : Real))
  | 15 => ((1032575425563477896331264 : Real) / (75489558096433522049 : Real))
  | 16 => ((258143856390869474082816 : Real) / (75489558096433522049 : Real))
  | 17 => ((53147264551061362311168 : Real) / (75489558096433522049 : Real))
  | 18 => ((8857877425176893718528 : Real) / (75489558096433522049 : Real))
  | 19 => ((1165510187523275489280 : Real) / (75489558096433522049 : Real))
  | 20 => ((116551018752327548928 : Real) / (75489558096433522049 : Real))
  | 21 => ((8325072768023396352 : Real) / (75489558096433522049 : Real))
  | 22 => ((378412398546518016 : Real) / (75489558096433522049 : Real))
  | 23 => ((8226356490141696 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg0_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real)) < x) (hxhi : x < ((-11 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg0Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 1 := by simpa using hj
    have hj_le_nat : j <= 0 := by omega
    have hj_le_real : (j : Real) <= (0 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (0 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg0Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg0_expPolyIntegral :
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg0Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg0Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-2 : Real))
    ((-11 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg0_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg0Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-11 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-11 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-11 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg0_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg0_expPolyIntegral

def p0PieceK11D13PlusWindowSeg1Coeff : Nat -> Real
  | 0 => ((-619399523799019163449859 : Real) / (301958232385734088196 : Real))
  | 1 => ((-4029613070818688816238285 : Real) / (150979116192867044098 : Real))
  | 2 => ((-12485633371674380123860071 : Real) / (75489558096433522049 : Real))
  | 3 => ((-49061197885475367426837618 : Real) / (75489558096433522049 : Real))
  | 4 => ((-137275215853547610367077780 : Real) / (75489558096433522049 : Real))
  | 5 => ((-291130786666175875428323160 : Real) / (75489558096433522049 : Real))
  | 6 => ((-486290887071976311611189904 : Real) / (75489558096433522049 : Real))
  | 7 => ((-656192961852551428304599776 : Real) / (75489558096433522049 : Real))
  | 8 => ((-727862290609340210035054464 : Real) / (75489558096433522049 : Real))
  | 9 => ((-671705844074561188723564800 : Real) / (75489558096433522049 : Real))
  | 10 => ((-519948005030459424382182912 : Real) / (75489558096433522049 : Real))
  | 11 => ((-339314774095724322651485184 : Real) / (75489558096433522049 : Real))
  | 12 => ((-187151625842324043508328448 : Real) / (75489558096433522049 : Real))
  | 13 => ((-87253798069196425568563200 : Real) / (75489558096433522049 : Real))
  | 14 => ((-34307887904836024908718080 : Real) / (75489558096433522049 : Real))
  | 15 => ((-11321906534815742506156032 : Real) / (75489558096433522049 : Real))
  | 16 => ((-3111260314621645181140992 : Real) / (75489558096433522049 : Real))
  | 17 => ((-703617308617524816936960 : Real) / (75489558096433522049 : Real))
  | 18 => ((-128735681332747866144768 : Real) / (75489558096433522049 : Real))
  | 19 => ((-18584761404523340759040 : Real) / (75489558096433522049 : Real))
  | 20 => ((-2038024064016394223616 : Real) / (75489558096433522049 : Real))
  | 21 => ((-159563894720448430080 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7946660369476878336 : Real) / (75489558096433522049 : Real))
  | 23 => ((-189206199273259008 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg1_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-11 : Real) / (6 : Real)) < x) (hxhi : x < ((-5 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg1Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 2 := by simpa using hj
    have hj_le_nat : j <= 1 := by omega
    have hj_le_real : (j : Real) <= (1 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (1 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg1Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg1_expPolyIntegral :
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg1Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg1Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-11 : Real) / (6 : Real))
    ((-5 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg1_centeredBSplineR_expIntegral :
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg1Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-5 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-11 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-5 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-5 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg1_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg1_expPolyIntegral

def p0PieceK11D13PlusWindowSeg2Coeff : Nat -> Real
  | 0 => ((530600476200980836550141 : Real) / (301958232385734088196 : Real))
  | 1 => ((3905386929181311183761715 : Real) / (150979116192867044098 : Real))
  | 2 => ((13699866628325619876139929 : Real) / (75489558096433522049 : Real))
  | 3 => ((60917902114524632573162382 : Real) / (75489558096433522049 : Real))
  | 4 => ((192662084146452389632922220 : Real) / (75489558096433522049 : Real))
  | 5 => ((461126257333824124571676840 : Real) / (75489558096433522049 : Real))
  | 6 => ((867771792128023688388810096 : Real) / (75489558096433522049 : Real))
  | 7 => ((1316869799267448571695400224 : Real) / (75489558096433522049 : Real))
  | 8 => ((1639813022734659789964945536 : Real) / (75489558096433522049 : Real))
  | 9 => ((1695969469269438811276435200 : Real) / (75489558096433522049 : Real))
  | 10 => ((1468899258178500575617817088 : Real) / (75489558096433522049 : Real))
  | 11 => ((1070958739816083677348514816 : Real) / (75489558096433522049 : Real))
  | 12 => ((659012482504760756491671552 : Real) / (75489558096433522049 : Real))
  | 13 => ((342337210783938934431436800 : Real) / (75489558096433522049 : Real))
  | 14 => ((149802544460793415091281920 : Real) / (75489558096433522049 : Real))
  | 15 => ((54957849116810855893843968 : Real) / (75489558096433522049 : Real))
  | 16 => ((16772666380866334338859008 : Real) / (75489558096433522049 : Real))
  | 17 => ((4208882227914799535063040 : Real) / (75489558096433522049 : Real))
  | 18 => ((853764225973717004255232 : Real) / (75489558096433522049 : Real))
  | 19 => ((136546802907023744040960 : Real) / (75489558096433522049 : Real))
  | 20 => ((16577763653369255952384 : Real) / (75489558096433522049 : Real))
  | 21 => ((1436075052484035870720 : Real) / (75489558096433522049 : Real))
  | 22 => ((79088191296222265344 : Real) / (75489558096433522049 : Real))
  | 23 => ((2081268192005849088 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg2_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-5 : Real) / (3 : Real)) < x) (hxhi : x < ((-3 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg2Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 3 := by simpa using hj
    have hj_le_nat : j <= 2 := by omega
    have hj_le_real : (j : Real) <= (2 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (2 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg2Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg2_expPolyIntegral :
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg2Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg2Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-5 : Real) / (3 : Real))
    ((-3 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg2_centeredBSplineR_expIntegral :
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg2Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-3 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-5 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-3 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-3 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg2_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg2_expPolyIntegral

def p0PieceK11D13PlusWindowSeg3Coeff : Nat -> Real
  | 0 => ((-108420319278190044603269 : Real) / (150979116192867044098 : Real))
  | 1 => ((-912497475312561290186412 : Real) / (75489558096433522049 : Real))
  | 2 => ((-7311533597631303925686714 : Real) / (75489558096433522049 : Real))
  | 3 => ((-37135298939941011835361952 : Real) / (75489558096433522049 : Real))
  | 4 => ((-134181919368433091728825560 : Real) / (75489558096433522049 : Real))
  | 5 => ((-366878551570552428211417536 : Real) / (75489558096433522049 : Real))
  | 6 => ((-788237825680729417177378656 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1364288629565770742078429184 : Real) / (75489558096433522049 : Real))
  | 8 => ((-1935064882376299295066827008 : Real) / (75489558096433522049 : Real))
  | 9 => ((-2276117091964960172092200960 : Real) / (75489558096433522049 : Real))
  | 10 => ((-2238381532306938475526243328 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1849929155717898605371047936 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1288246114517894098654703616 : Real) / (75489558096433522049 : Real))
  | 13 => ((-756116356767302265907544064 : Real) / (75489558096433522049 : Real))
  | 14 => ((-373270582944559537451089920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-154271401845330325123104768 : Real) / (75489558096433522049 : Real))
  | 16 => ((-52970417273180726000123904 : Real) / (75489558096433522049 : Real))
  | 17 => ((-14936277990843217028579328 : Real) / (75489558096433522049 : Real))
  | 18 => ((-3400715822639175565443072 : Real) / (75489558096433522049 : Real))
  | 19 => ((-609853205621553899765760 : Real) / (75489558096433522049 : Real))
  | 20 => ((-82942237483774429888512 : Real) / (75489558096433522049 : Real))
  | 21 => ((-8042020293910600876032 : Real) / (75489558096433522049 : Real))
  | 22 => ((-495341829697392082944 : Real) / (75489558096433522049 : Real))
  | 23 => ((-14568877344040943616 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg3_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-3 : Real) / (2 : Real)) < x) (hxhi : x < ((-4 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg3Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 4 := by simpa using hj
    have hj_le_nat : j <= 3 := by omega
    have hj_le_real : (j : Real) <= (3 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (3 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg3Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg3_expPolyIntegral :
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg3Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg3Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-3 : Real) / (2 : Real))
    ((-4 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg3_centeredBSplineR_expIntegral :
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg3Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-4 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-3 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-4 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-4 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg3_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg3_expPolyIntegral

def p0PieceK11D13PlusWindowSeg4Coeff : Nat -> Real
  | 0 => ((22256415739968419044475 : Real) / (150979116192867044098 : Real))
  | 1 => ((214589364219055458775380 : Real) / (75489558096433522049 : Real))
  | 2 => ((1986932828504534253248070 : Real) / (75489558096433522049 : Real))
  | 3 => ((11681649797272138604045664 : Real) / (75489558096433522049 : Real))
  | 4 => ((48881638396116222418953000 : Real) / (75489558096433522049 : Real))
  | 5 => ((154852588058413117109751360 : Real) / (75489558096433522049 : Real))
  | 6 => ((385657238484443059795251360 : Real) / (75489558096433522049 : Real))
  | 7 => ((773877380163650555264575488 : Real) / (75489558096433522049 : Real))
  | 8 => ((1272184132217832650947680000 : Real) / (75489558096433522049 : Real))
  | 9 => ((1732944176277704760425932800 : Real) / (75489558096433522049 : Real))
  | 10 => ((1971132799347859703617797120 : Real) / (75489558096433522049 : Real))
  | 11 => ((1881231274612490689779351552 : Real) / (75489558096433522049 : Real))
  | 12 => ((1510124208229897872708096000 : Real) / (75489558096433522049 : Real))
  | 13 => ((1019772501899565715918848000 : Real) / (75489558096433522049 : Real))
  | 14 => ((578098448484119738527334400 : Real) / (75489558096433522049 : Real))
  | 15 => ((273844662297575349067186176 : Real) / (75489558096433522049 : Real))
  | 16 => ((107573106780408901821235200 : Real) / (75489558096433522049 : Real))
  | 17 => ((34643339731588873916252160 : Real) / (75489558096433522049 : Real))
  | 18 => ((8994188607968847170764800 : Real) / (75489558096433522049 : Real))
  | 19 => ((1836509510945819008696320 : Real) / (75489558096433522049 : Real))
  | 20 => ((284012170001331506380800 : Real) / (75489558096433522049 : Real))
  | 21 => ((31274523365207892295680 : Real) / (75489558096433522049 : Real))
  | 22 => ((2185331601606141542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((72844386720204718080 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg4_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-4 : Real) / (3 : Real)) < x) (hxhi : x < ((-7 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg4Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 5 := by simpa using hj
    have hj_le_nat : j <= 4 := by omega
    have hj_le_real : (j : Real) <= (4 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (4 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg4Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg4_expPolyIntegral :
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg4Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg4Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-4 : Real) / (3 : Real))
    ((-7 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg4_centeredBSplineR_expIntegral :
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg4Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-7 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-4 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-7 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-7 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg4_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg4_expPolyIntegral

def p0PieceK11D13PlusWindowSeg5Coeff : Nat -> Real
  | 0 => ((-3957220059346464754503 : Real) / (301958232385734088196 : Real))
  | 1 => ((-48597493877681639048991 : Real) / (150979116192867044098 : Real))
  | 2 => ((-265440790984202085007899 : Real) / (75489558096433522049 : Real))
  | 3 => ((-1832591919660279425490150 : Real) / (75489558096433522049 : Real))
  | 4 => ((-9036540390736997707629060 : Real) / (75489558096433522049 : Real))
  | 5 => ((-33795194275908799873973064 : Real) / (75489558096433522049 : Real))
  | 6 => ((-99437058946670441020040016 : Real) / (75489558096433522049 : Real))
  | 7 => ((-235910749182748977044806560 : Real) / (75489558096433522049 : Real))
  | 8 => ((-458881232375995118725546368 : Real) / (75489558096433522049 : Real))
  | 9 => ((-740006344570620624821533440 : Real) / (75489558096433522049 : Real))
  | 10 => ((-996407825670130758679162368 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1124848839042097051248737280 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1066515889188320191030265856 : Real) / (75489558096433522049 : Real))
  | 13 => ((-848999436887273758880403456 : Real) / (75489558096433522049 : Real))
  | 14 => ((-566047636487414633798737920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-314573324259213756700508160 : Real) / (75489558096433522049 : Real))
  | 16 => ((-144606030315357857793490944 : Real) / (75489558096433522049 : Real))
  | 17 => ((-54361061596328805947768832 : Real) / (75489558096433522049 : Real))
  | 18 => ((-16435640342864775647526912 : Real) / (75489558096433522049 : Real))
  | 19 => ((-3899542132099359070617600 : Real) / (75489558096433522049 : Real))
  | 20 => ((-699310968806413307215872 : Real) / (75489558096433522049 : Real))
  | 21 => ((-89132391590842493042688 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7197025407956226146304 : Real) / (75489558096433522049 : Real))
  | 23 => ((-276808669536777928704 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg5_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-7 : Real) / (6 : Real)) < x) (hxhi : x < ((-1 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg5Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 6 := by simpa using hj
    have hj_le_nat : j <= 5 := by omega
    have hj_le_real : (j : Real) <= (5 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (5 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg5Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg5_expPolyIntegral :
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg5Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg5Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-7 : Real) / (6 : Real))
    ((-1 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg5_centeredBSplineR_expIntegral :
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
  calc
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg5Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-7 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg5_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg5_expPolyIntegral

def p0PieceK11D13PlusWindowSeg6Coeff : Nat -> Real
  | 0 => ((471718653241982104761 : Real) / (301958232385734088196 : Real))
  | 1 => ((2335301317085499832545 : Real) / (150979116192867044098 : Real))
  | 2 => ((14689582587017178840549 : Real) / (75489558096433522049 : Real))
  | 3 => ((128320695338255421448986 : Real) / (75489558096433522049 : Real))
  | 4 => ((768022684255676527066620 : Real) / (75489558096433522049 : Real))
  | 5 => ((3462145409063362217870520 : Real) / (75489558096433522049 : Real))
  | 6 => ((12334960108246045255490736 : Real) / (75489558096433522049 : Real))
  | 7 => ((35535582807762489624339552 : Real) / (75489558096433522049 : Real))
  | 8 => ((84011431605027814612745856 : Real) / (75489558096433522049 : Real))
  | 9 => ((164814762064417597408953600 : Real) / (75489558096433522049 : Real))
  | 10 => ((270341723618922752443519488 : Real) / (75489558096433522049 : Real))
  | 11 => ((372218810117693461896250368 : Real) / (75489558096433522049 : Real))
  | 12 => ((430551759971470322114721792 : Real) / (75489558096433522049 : Real))
  | 13 => ((417750112401779752242278400 : Real) / (75489558096433522049 : Real))
  | 14 => ((338773470147623588431749120 : Real) / (75489558096433522049 : Real))
  | 15 => ((228319339721809176637784064 : Real) / (75489558096433522049 : Real))
  | 16 => ((126840301675153608875655168 : Real) / (75489558096433522049 : Real))
  | 17 => ((57410957458587680327761920 : Real) / (75489558096433522049 : Real))
  | 18 => ((20821699342107386444316672 : Real) / (75489558096433522049 : Real))
  | 19 => ((5905020942893315164078080 : Real) / (75489558096433522049 : Real))
  | 20 => ((1261601646192121539723264 : Real) / (75489558096433522049 : Real))
  | 21 => ((190997981980376770805760 : Real) / (75489558096433522049 : Real))
  | 22 => ((18269372189427343294464 : Real) / (75489558096433522049 : Real))
  | 23 => ((830426008610333786112 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg6_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real)) < x) (hxhi : x < ((-5 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg6Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 7 := by simpa using hj
    have hj_le_nat : j <= 6 := by omega
    have hj_le_real : (j : Real) <= (6 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (6 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg6Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg6_expPolyIntegral :
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg6Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg6Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real))
    ((-5 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg6_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg6Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-5 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-5 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-5 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg6_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg6_expPolyIntegral

def p0PieceK11D13PlusWindowSeg7Coeff : Nat -> Real
  | 0 => ((74951734195200116034 : Real) / (75489558096433522049 : Real))
  | 1 => ((-18540185039403404040 : Real) / (75489558096433522049 : Real))
  | 2 => ((-968136548267244987576 : Real) / (75489558096433522049 : Real))
  | 3 => ((-3204145398133738707264 : Real) / (75489558096433522049 : Real))
  | 4 => ((-21126360162658433870880 : Real) / (75489558096433522049 : Real))
  | 5 => ((-136374233484245204004480 : Real) / (75489558096433522049 : Real))
  | 6 => ((-619710604925341463259264 : Real) / (75489558096433522049 : Real))
  | 7 => ((-2218028984908408813160448 : Real) / (75489558096433522049 : Real))
  | 8 => ((-6597236697382341637254144 : Real) / (75489558096433522049 : Real))
  | 9 => ((-16402574540402715091046400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-34103401877175372556480512 : Real) / (75489558096433522049 : Real))
  | 11 => ((-59539731494954788103749632 : Real) / (75489558096433522049 : Real))
  | 12 => ((-87558489963707577885278208 : Real) / (75489558096433522049 : Real))
  | 13 => ((-108331064455477807757721600 : Real) / (75489558096433522049 : Real))
  | 14 => ((-112153252872882891568250880 : Real) / (75489558096433522049 : Real))
  | 15 => ((-96347900852955488962215936 : Real) / (75489558096433522049 : Real))
  | 16 => ((-67960042669705190484344832 : Real) / (75489558096433522049 : Real))
  | 17 => ((-38843330335342549944238080 : Real) / (75489558096433522049 : Real))
  | 18 => ((-17680015775464705664483328 : Real) / (75489558096433522049 : Real))
  | 19 => ((-6253415410024187607121920 : Real) / (75489558096433522049 : Real))
  | 20 => ((-1656423078508079125364736 : Real) / (75489558096433522049 : Real))
  | 21 => ((-309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-36301479804966019792896 : Real) / (75489558096433522049 : Real))
  | 23 => ((-2016748878053667766272 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg7_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-5 : Real) / (6 : Real)) < x) (hxhi : x < ((-2 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg7Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 8 := by simpa using hj
    have hj_le_nat : j <= 7 := by omega
    have hj_le_real : (j : Real) <= (7 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (7 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg7Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg7_expPolyIntegral :
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg7Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg7Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-5 : Real) / (6 : Real))
    ((-2 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg7_centeredBSplineR_expIntegral :
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg7Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-2 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-5 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-2 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-2 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg7_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg7_expPolyIntegral

def p0PieceK11D13PlusWindowSeg8Coeff : Nat -> Real
  | 0 => ((75490840139461477698 : Real) / (75489558096433522049 : Real))
  | 1 => ((58970037613573368 : Real) / (75489558096433522049 : Real))
  | 2 => ((-661250489496464860344 : Real) / (75489558096433522049 : Real))
  | 3 => ((18158218959452628672 : Real) / (75489558096433522049 : Real))
  | 4 => ((3040916965540501148640 : Real) / (75489558096433522049 : Real))
  | 5 => ((1379246146488725606784 : Real) / (75489558096433522049 : Real))
  | 6 => ((180053412961219991424 : Real) / (75489558096433522049 : Real))
  | 7 => ((40144127609693818681344 : Real) / (75489558096433522049 : Real))
  | 8 => ((177282640171966258271232 : Real) / (75489558096433522049 : Real))
  | 9 => ((533723803483054647767040 : Real) / (75489558096433522049 : Real))
  | 10 => ((1462824644984743895027712 : Real) / (75489558096433522049 : Real))
  | 11 => ((3509488248874509242105856 : Real) / (75489558096433522049 : Real))
  | 12 => ((7015339652036368133505024 : Real) / (75489558096433522049 : Real))
  | 13 => ((11704950056812585266118656 : Real) / (75489558096433522049 : Real))
  | 14 => ((16456762675999672385863680 : Real) / (75489558096433522049 : Real))
  | 15 => ((19401113141038818596487168 : Real) / (75489558096433522049 : Real))
  | 16 => ((18851717825790540184682496 : Real) / (75489558096433522049 : Real))
  | 17 => ((14775698205993048410161152 : Real) / (75489558096433522049 : Real))
  | 18 => ((9129498495203093512716288 : Real) / (75489558096433522049 : Real))
  | 19 => ((4329287591555206804930560 : Real) / (75489558096433522049 : Real))
  | 20 => ((1518387821965739198251008 : Real) / (75489558096433522049 : Real))
  | 21 => ((371081793561874868994048 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((4033497756107335532544 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg8_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real) / (3 : Real)) < x) (hxhi : x < ((-1 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg8Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 9 := by simpa using hj
    have hj_le_nat : j <= 8 := by omega
    have hj_le_real : (j : Real) <= (8 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (8 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg8Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg8_expPolyIntegral :
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg8Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg8Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-2 : Real) / (3 : Real))
    ((-1 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg8_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg8Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg8_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg8_expPolyIntegral

def p0PieceK11D13PlusWindowSeg9Coeff : Nat -> Real
  | 0 => ((150979115850112767525 : Real) / (150979116192867044098 : Real))
  | 1 => ((-11825020747665 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662548090474419923070 : Real) / (75489558096433522049 : Real))
  | 3 => ((-8194731918249492 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859252828626792367000 : Real) / (75489558096433522049 : Real))
  | 5 => ((-1401294055461133680 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8103831230303900451360 : Real) / (75489558096433522049 : Real))
  | 7 => ((-91883514736766326464 : Real) / (75489558096433522049 : Real))
  | 8 => ((16338595674243918240000 : Real) / (75489558096433522049 : Real))
  | 9 => ((-2756344842686485670400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-39319770327331278597120 : Real) / (75489558096433522049 : Real))
  | 11 => ((-41034914590395713734656 : Real) / (75489558096433522049 : Real))
  | 12 => ((-85706674893441778176000 : Real) / (75489558096433522049 : Real))
  | 13 => ((-312205265684016122880000 : Real) / (75489558096433522049 : Real))
  | 14 => ((-710602070424043884134400 : Real) / (75489558096433522049 : Real))
  | 15 => ((-1199724554669640927510528 : Real) / (75489558096433522049 : Real))
  | 16 => ((-1749119869917919339315200 : Real) / (75489558096433522049 : Real))
  | 17 => ((-2189697543413918256660480 : Real) / (75489558096433522049 : Real))
  | 18 => ((-2180765337734884265164800 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1623482846833202551848960 : Real) / (75489558096433522049 : Real))
  | 20 => ((-862720353389624544460800 : Real) / (75489558096433522049 : Real))
  | 21 => ((-309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-67224962601788925542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((-6722496260178892554240 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg9_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (2 : Real)) < x) (hxhi : x < ((-1 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg9Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 10 := by simpa using hj
    have hj_le_nat : j <= 9 := by omega
    have hj_le_real : (j : Real) <= (9 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (9 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg9Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg9_expPolyIntegral :
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg9Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg9Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (2 : Real))
    ((-1 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg9_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg9Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg9_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg9_expPolyIntegral

def p0PieceK11D13PlusWindowSeg10Coeff : Nat -> Real
  | 0 => ((150979116192867096101 : Real) / (150979116192867044098 : Real))
  | 1 => ((3588207 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662547700248616839294 : Real) / (75489558096433522049 : Real))
  | 3 => ((9946509804 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859375749754763756440 : Real) / (75489558096433522049 : Real))
  | 5 => ((6803412705936 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8091219522574035894816 : Real) / (75489558096433522049 : Real))
  | 7 => ((1784437961156928 : Real) / (75489558096433522049 : Real))
  | 8 => ((16889907469292283140352 : Real) / (75489558096433522049 : Real))
  | 9 => ((214132555338831360 : Real) / (75489558096433522049 : Real))
  | 10 => ((-27742222631315615689728 : Real) / (75489558096433522049 : Real))
  | 11 => ((12754513659818391552 : Real) / (75489558096433522049 : Real))
  | 12 => ((37436332418724818202624 : Real) / (75489558096433522049 : Real))
  | 13 => ((388522108406775619584 : Real) / (75489558096433522049 : Real))
  | 14 => ((-40758239440280530206720 : Real) / (75489558096433522049 : Real))
  | 15 => ((5994341101133109559296 : Real) / (75489558096433522049 : Real))
  | 16 => ((59458473738241716289536 : Real) / (75489558096433522049 : Real))
  | 17 => ((44428645808398341439488 : Real) / (75489558096433522049 : Real))
  | 18 => ((53360851487432332935168 : Real) / (75489558096433522049 : Real))
  | 19 => ((140300986763363183493120 : Real) / (75489558096433522049 : Real))
  | 20 => ((195549946768314896744448 : Real) / (75489558096433522049 : Real))
  | 21 => ((144309586385173560164352 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((9411494764250449575936 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg10_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (3 : Real)) < x) (hxhi : x < ((-1 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg10Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 11 := by simpa using hj
    have hj_le_nat : j <= 10 := by omega
    have hj_le_real : (j : Real) <= (10 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (10 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg10Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg10_expPolyIntegral :
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg10Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg10Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (3 : Real))
    ((-1 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg10_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg10Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg10_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg10_expPolyIntegral

def p0PieceK11D13PlusWindowSeg11Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-662547700248853660956 : Real) / (75489558096433522049 : Real))
  | 3 => ((0 : Real))
  | 4 => ((2859375749456368462320 : Real) / (75489558096433522049 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-8091219645035464601664 : Real) / (75489558096433522049 : Real))
  | 7 => ((0 : Real))
  | 8 => ((16889886056036749257216 : Real) / (75489558096433522049 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-27744021344780461873152 : Real) / (75489558096433522049 : Real))
  | 11 => ((0 : Real))
  | 12 => ((37359805336765907853312 : Real) / (75489558096433522049 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-42423334190595282862080 : Real) / (75489558096433522049 : Real))
  | 15 => ((0 : Real))
  | 16 => ((41475450434842387611648 : Real) / (75489558096433522049 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-35496440129364349943808 : Real) / (75489558096433522049 : Real))
  | 19 => ((0 : Real))
  | 20 => ((27188762652279076552704 : Real) / (75489558096433522049 : Real))
  | 21 => ((0 : Real))
  | 22 => ((-22245351260955608088576 : Real) / (75489558096433522049 : Real))
  | 23 => ((-11122675630477804044288 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg11_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (6 : Real)) < x) (hxhi : x < ((0 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg11Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 12 := by simpa using hj
    have hj_le_nat : j <= 11 := by omega
    have hj_le_real : (j : Real) <= (11 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (11 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg11Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg11_expPolyIntegral :
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg11Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg11Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (6 : Real))
    ((0 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg11_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg11Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((0 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((0 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((0 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg11_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg11_expPolyIntegral

def p0PieceK11D13PlusWindowSeg12Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-662547700248853660956 : Real) / (75489558096433522049 : Real))
  | 3 => ((0 : Real))
  | 4 => ((2859375749456368462320 : Real) / (75489558096433522049 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-8091219645035464601664 : Real) / (75489558096433522049 : Real))
  | 7 => ((0 : Real))
  | 8 => ((16889886056036749257216 : Real) / (75489558096433522049 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-27744021344780461873152 : Real) / (75489558096433522049 : Real))
  | 11 => ((0 : Real))
  | 12 => ((37359805336765907853312 : Real) / (75489558096433522049 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-42423334190595282862080 : Real) / (75489558096433522049 : Real))
  | 15 => ((0 : Real))
  | 16 => ((41475450434842387611648 : Real) / (75489558096433522049 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-35496440129364349943808 : Real) / (75489558096433522049 : Real))
  | 19 => ((0 : Real))
  | 20 => ((27188762652279076552704 : Real) / (75489558096433522049 : Real))
  | 21 => ((0 : Real))
  | 22 => ((-22245351260955608088576 : Real) / (75489558096433522049 : Real))
  | 23 => ((11122675630477804044288 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg12_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((0 : Real)) < x) (hxhi : x < ((1 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg12Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 13 := by simpa using hj
    have hj_le_nat : j <= 12 := by omega
    have hj_le_real : (j : Real) <= (12 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (12 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg12Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg12_expPolyIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg12Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg12Coeff 24
    ((-3 : Real) / (20 : Real))
    ((0 : Real))
    ((1 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg12_centeredBSplineR_expIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg12Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((0 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg12_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg12_expPolyIntegral

def p0PieceK11D13PlusWindowSeg13Coeff : Nat -> Real
  | 0 => ((150979116192867096101 : Real) / (150979116192867044098 : Real))
  | 1 => ((-3588207 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662547700248616839294 : Real) / (75489558096433522049 : Real))
  | 3 => ((-9946509804 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859375749754763756440 : Real) / (75489558096433522049 : Real))
  | 5 => ((-6803412705936 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8091219522574035894816 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1784437961156928 : Real) / (75489558096433522049 : Real))
  | 8 => ((16889907469292283140352 : Real) / (75489558096433522049 : Real))
  | 9 => ((-214132555338831360 : Real) / (75489558096433522049 : Real))
  | 10 => ((-27742222631315615689728 : Real) / (75489558096433522049 : Real))
  | 11 => ((-12754513659818391552 : Real) / (75489558096433522049 : Real))
  | 12 => ((37436332418724818202624 : Real) / (75489558096433522049 : Real))
  | 13 => ((-388522108406775619584 : Real) / (75489558096433522049 : Real))
  | 14 => ((-40758239440280530206720 : Real) / (75489558096433522049 : Real))
  | 15 => ((-5994341101133109559296 : Real) / (75489558096433522049 : Real))
  | 16 => ((59458473738241716289536 : Real) / (75489558096433522049 : Real))
  | 17 => ((-44428645808398341439488 : Real) / (75489558096433522049 : Real))
  | 18 => ((53360851487432332935168 : Real) / (75489558096433522049 : Real))
  | 19 => ((-140300986763363183493120 : Real) / (75489558096433522049 : Real))
  | 20 => ((195549946768314896744448 : Real) / (75489558096433522049 : Real))
  | 21 => ((-144309586385173560164352 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((-9411494764250449575936 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg13_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (6 : Real)) < x) (hxhi : x < ((1 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg13Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 14 := by simpa using hj
    have hj_le_nat : j <= 13 := by omega
    have hj_le_real : (j : Real) <= (13 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (13 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg13Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg13_expPolyIntegral :
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg13Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg13Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (6 : Real))
    ((1 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg13_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg13Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg13_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg13_expPolyIntegral

def p0PieceK11D13PlusWindowSeg14Coeff : Nat -> Real
  | 0 => ((150979115850112767525 : Real) / (150979116192867044098 : Real))
  | 1 => ((11825020747665 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662548090474419923070 : Real) / (75489558096433522049 : Real))
  | 3 => ((8194731918249492 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859252828626792367000 : Real) / (75489558096433522049 : Real))
  | 5 => ((1401294055461133680 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8103831230303900451360 : Real) / (75489558096433522049 : Real))
  | 7 => ((91883514736766326464 : Real) / (75489558096433522049 : Real))
  | 8 => ((16338595674243918240000 : Real) / (75489558096433522049 : Real))
  | 9 => ((2756344842686485670400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-39319770327331278597120 : Real) / (75489558096433522049 : Real))
  | 11 => ((41034914590395713734656 : Real) / (75489558096433522049 : Real))
  | 12 => ((-85706674893441778176000 : Real) / (75489558096433522049 : Real))
  | 13 => ((312205265684016122880000 : Real) / (75489558096433522049 : Real))
  | 14 => ((-710602070424043884134400 : Real) / (75489558096433522049 : Real))
  | 15 => ((1199724554669640927510528 : Real) / (75489558096433522049 : Real))
  | 16 => ((-1749119869917919339315200 : Real) / (75489558096433522049 : Real))
  | 17 => ((2189697543413918256660480 : Real) / (75489558096433522049 : Real))
  | 18 => ((-2180765337734884265164800 : Real) / (75489558096433522049 : Real))
  | 19 => ((1623482846833202551848960 : Real) / (75489558096433522049 : Real))
  | 20 => ((-862720353389624544460800 : Real) / (75489558096433522049 : Real))
  | 21 => ((309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-67224962601788925542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((6722496260178892554240 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg14_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (3 : Real)) < x) (hxhi : x < ((1 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg14Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 15 := by simpa using hj
    have hj_le_nat : j <= 14 := by omega
    have hj_le_real : (j : Real) <= (14 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (14 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg14Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg14_expPolyIntegral :
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg14Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg14Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (3 : Real))
    ((1 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg14_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg14Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg14_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg14_expPolyIntegral

def p0PieceK11D13PlusWindowSeg15Coeff : Nat -> Real
  | 0 => ((75490840139461477698 : Real) / (75489558096433522049 : Real))
  | 1 => ((-58970037613573368 : Real) / (75489558096433522049 : Real))
  | 2 => ((-661250489496464860344 : Real) / (75489558096433522049 : Real))
  | 3 => ((-18158218959452628672 : Real) / (75489558096433522049 : Real))
  | 4 => ((3040916965540501148640 : Real) / (75489558096433522049 : Real))
  | 5 => ((-1379246146488725606784 : Real) / (75489558096433522049 : Real))
  | 6 => ((180053412961219991424 : Real) / (75489558096433522049 : Real))
  | 7 => ((-40144127609693818681344 : Real) / (75489558096433522049 : Real))
  | 8 => ((177282640171966258271232 : Real) / (75489558096433522049 : Real))
  | 9 => ((-533723803483054647767040 : Real) / (75489558096433522049 : Real))
  | 10 => ((1462824644984743895027712 : Real) / (75489558096433522049 : Real))
  | 11 => ((-3509488248874509242105856 : Real) / (75489558096433522049 : Real))
  | 12 => ((7015339652036368133505024 : Real) / (75489558096433522049 : Real))
  | 13 => ((-11704950056812585266118656 : Real) / (75489558096433522049 : Real))
  | 14 => ((16456762675999672385863680 : Real) / (75489558096433522049 : Real))
  | 15 => ((-19401113141038818596487168 : Real) / (75489558096433522049 : Real))
  | 16 => ((18851717825790540184682496 : Real) / (75489558096433522049 : Real))
  | 17 => ((-14775698205993048410161152 : Real) / (75489558096433522049 : Real))
  | 18 => ((9129498495203093512716288 : Real) / (75489558096433522049 : Real))
  | 19 => ((-4329287591555206804930560 : Real) / (75489558096433522049 : Real))
  | 20 => ((1518387821965739198251008 : Real) / (75489558096433522049 : Real))
  | 21 => ((-371081793561874868994048 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((-4033497756107335532544 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg15_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (2 : Real)) < x) (hxhi : x < ((2 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg15Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 16 := by simpa using hj
    have hj_le_nat : j <= 15 := by omega
    have hj_le_real : (j : Real) <= (15 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (15 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg15Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg15_expPolyIntegral :
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg15Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg15Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (2 : Real))
    ((2 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg15_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg15Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg15_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg15_expPolyIntegral

def p0PieceK11D13PlusWindowSeg16Coeff : Nat -> Real
  | 0 => ((74951734195200116034 : Real) / (75489558096433522049 : Real))
  | 1 => ((18540185039403404040 : Real) / (75489558096433522049 : Real))
  | 2 => ((-968136548267244987576 : Real) / (75489558096433522049 : Real))
  | 3 => ((3204145398133738707264 : Real) / (75489558096433522049 : Real))
  | 4 => ((-21126360162658433870880 : Real) / (75489558096433522049 : Real))
  | 5 => ((136374233484245204004480 : Real) / (75489558096433522049 : Real))
  | 6 => ((-619710604925341463259264 : Real) / (75489558096433522049 : Real))
  | 7 => ((2218028984908408813160448 : Real) / (75489558096433522049 : Real))
  | 8 => ((-6597236697382341637254144 : Real) / (75489558096433522049 : Real))
  | 9 => ((16402574540402715091046400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-34103401877175372556480512 : Real) / (75489558096433522049 : Real))
  | 11 => ((59539731494954788103749632 : Real) / (75489558096433522049 : Real))
  | 12 => ((-87558489963707577885278208 : Real) / (75489558096433522049 : Real))
  | 13 => ((108331064455477807757721600 : Real) / (75489558096433522049 : Real))
  | 14 => ((-112153252872882891568250880 : Real) / (75489558096433522049 : Real))
  | 15 => ((96347900852955488962215936 : Real) / (75489558096433522049 : Real))
  | 16 => ((-67960042669705190484344832 : Real) / (75489558096433522049 : Real))
  | 17 => ((38843330335342549944238080 : Real) / (75489558096433522049 : Real))
  | 18 => ((-17680015775464705664483328 : Real) / (75489558096433522049 : Real))
  | 19 => ((6253415410024187607121920 : Real) / (75489558096433522049 : Real))
  | 20 => ((-1656423078508079125364736 : Real) / (75489558096433522049 : Real))
  | 21 => ((309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-36301479804966019792896 : Real) / (75489558096433522049 : Real))
  | 23 => ((2016748878053667766272 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg16_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((2 : Real) / (3 : Real)) < x) (hxhi : x < ((5 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg16Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 17 := by simpa using hj
    have hj_le_nat : j <= 16 := by omega
    have hj_le_real : (j : Real) <= (16 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (16 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg16Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg16_expPolyIntegral :
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg16Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg16Coeff 24
    ((-3 : Real) / (20 : Real))
    ((2 : Real) / (3 : Real))
    ((5 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg16_centeredBSplineR_expIntegral :
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg16Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((5 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((2 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((5 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((5 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg16_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg16_expPolyIntegral

def p0PieceK11D13PlusWindowSeg17Coeff : Nat -> Real
  | 0 => ((471718653241982104761 : Real) / (301958232385734088196 : Real))
  | 1 => ((-2335301317085499832545 : Real) / (150979116192867044098 : Real))
  | 2 => ((14689582587017178840549 : Real) / (75489558096433522049 : Real))
  | 3 => ((-128320695338255421448986 : Real) / (75489558096433522049 : Real))
  | 4 => ((768022684255676527066620 : Real) / (75489558096433522049 : Real))
  | 5 => ((-3462145409063362217870520 : Real) / (75489558096433522049 : Real))
  | 6 => ((12334960108246045255490736 : Real) / (75489558096433522049 : Real))
  | 7 => ((-35535582807762489624339552 : Real) / (75489558096433522049 : Real))
  | 8 => ((84011431605027814612745856 : Real) / (75489558096433522049 : Real))
  | 9 => ((-164814762064417597408953600 : Real) / (75489558096433522049 : Real))
  | 10 => ((270341723618922752443519488 : Real) / (75489558096433522049 : Real))
  | 11 => ((-372218810117693461896250368 : Real) / (75489558096433522049 : Real))
  | 12 => ((430551759971470322114721792 : Real) / (75489558096433522049 : Real))
  | 13 => ((-417750112401779752242278400 : Real) / (75489558096433522049 : Real))
  | 14 => ((338773470147623588431749120 : Real) / (75489558096433522049 : Real))
  | 15 => ((-228319339721809176637784064 : Real) / (75489558096433522049 : Real))
  | 16 => ((126840301675153608875655168 : Real) / (75489558096433522049 : Real))
  | 17 => ((-57410957458587680327761920 : Real) / (75489558096433522049 : Real))
  | 18 => ((20821699342107386444316672 : Real) / (75489558096433522049 : Real))
  | 19 => ((-5905020942893315164078080 : Real) / (75489558096433522049 : Real))
  | 20 => ((1261601646192121539723264 : Real) / (75489558096433522049 : Real))
  | 21 => ((-190997981980376770805760 : Real) / (75489558096433522049 : Real))
  | 22 => ((18269372189427343294464 : Real) / (75489558096433522049 : Real))
  | 23 => ((-830426008610333786112 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg17_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((5 : Real) / (6 : Real)) < x) (hxhi : x < ((1 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg17Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 18 := by simpa using hj
    have hj_le_nat : j <= 17 := by omega
    have hj_le_real : (j : Real) <= (17 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (17 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg17Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg17_expPolyIntegral :
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg17Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg17Coeff 24
    ((-3 : Real) / (20 : Real))
    ((5 : Real) / (6 : Real))
    ((1 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg17_centeredBSplineR_expIntegral :
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
  calc
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg17Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((5 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg17_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg17_expPolyIntegral

def p0PieceK11D13PlusWindowSeg18Coeff : Nat -> Real
  | 0 => ((-3957220059346464754503 : Real) / (301958232385734088196 : Real))
  | 1 => ((48597493877681639048991 : Real) / (150979116192867044098 : Real))
  | 2 => ((-265440790984202085007899 : Real) / (75489558096433522049 : Real))
  | 3 => ((1832591919660279425490150 : Real) / (75489558096433522049 : Real))
  | 4 => ((-9036540390736997707629060 : Real) / (75489558096433522049 : Real))
  | 5 => ((33795194275908799873973064 : Real) / (75489558096433522049 : Real))
  | 6 => ((-99437058946670441020040016 : Real) / (75489558096433522049 : Real))
  | 7 => ((235910749182748977044806560 : Real) / (75489558096433522049 : Real))
  | 8 => ((-458881232375995118725546368 : Real) / (75489558096433522049 : Real))
  | 9 => ((740006344570620624821533440 : Real) / (75489558096433522049 : Real))
  | 10 => ((-996407825670130758679162368 : Real) / (75489558096433522049 : Real))
  | 11 => ((1124848839042097051248737280 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1066515889188320191030265856 : Real) / (75489558096433522049 : Real))
  | 13 => ((848999436887273758880403456 : Real) / (75489558096433522049 : Real))
  | 14 => ((-566047636487414633798737920 : Real) / (75489558096433522049 : Real))
  | 15 => ((314573324259213756700508160 : Real) / (75489558096433522049 : Real))
  | 16 => ((-144606030315357857793490944 : Real) / (75489558096433522049 : Real))
  | 17 => ((54361061596328805947768832 : Real) / (75489558096433522049 : Real))
  | 18 => ((-16435640342864775647526912 : Real) / (75489558096433522049 : Real))
  | 19 => ((3899542132099359070617600 : Real) / (75489558096433522049 : Real))
  | 20 => ((-699310968806413307215872 : Real) / (75489558096433522049 : Real))
  | 21 => ((89132391590842493042688 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7197025407956226146304 : Real) / (75489558096433522049 : Real))
  | 23 => ((276808669536777928704 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg18_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real)) < x) (hxhi : x < ((7 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg18Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 19 := by simpa using hj
    have hj_le_nat : j <= 18 := by omega
    have hj_le_real : (j : Real) <= (18 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (18 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg18Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg18_expPolyIntegral :
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg18Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg18Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real))
    ((7 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg18_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg18Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((7 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((7 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((7 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg18_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg18_expPolyIntegral

def p0PieceK11D13PlusWindowSeg19Coeff : Nat -> Real
  | 0 => ((22256415739968419044475 : Real) / (150979116192867044098 : Real))
  | 1 => ((-214589364219055458775380 : Real) / (75489558096433522049 : Real))
  | 2 => ((1986932828504534253248070 : Real) / (75489558096433522049 : Real))
  | 3 => ((-11681649797272138604045664 : Real) / (75489558096433522049 : Real))
  | 4 => ((48881638396116222418953000 : Real) / (75489558096433522049 : Real))
  | 5 => ((-154852588058413117109751360 : Real) / (75489558096433522049 : Real))
  | 6 => ((385657238484443059795251360 : Real) / (75489558096433522049 : Real))
  | 7 => ((-773877380163650555264575488 : Real) / (75489558096433522049 : Real))
  | 8 => ((1272184132217832650947680000 : Real) / (75489558096433522049 : Real))
  | 9 => ((-1732944176277704760425932800 : Real) / (75489558096433522049 : Real))
  | 10 => ((1971132799347859703617797120 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1881231274612490689779351552 : Real) / (75489558096433522049 : Real))
  | 12 => ((1510124208229897872708096000 : Real) / (75489558096433522049 : Real))
  | 13 => ((-1019772501899565715918848000 : Real) / (75489558096433522049 : Real))
  | 14 => ((578098448484119738527334400 : Real) / (75489558096433522049 : Real))
  | 15 => ((-273844662297575349067186176 : Real) / (75489558096433522049 : Real))
  | 16 => ((107573106780408901821235200 : Real) / (75489558096433522049 : Real))
  | 17 => ((-34643339731588873916252160 : Real) / (75489558096433522049 : Real))
  | 18 => ((8994188607968847170764800 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1836509510945819008696320 : Real) / (75489558096433522049 : Real))
  | 20 => ((284012170001331506380800 : Real) / (75489558096433522049 : Real))
  | 21 => ((-31274523365207892295680 : Real) / (75489558096433522049 : Real))
  | 22 => ((2185331601606141542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((-72844386720204718080 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg19_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((7 : Real) / (6 : Real)) < x) (hxhi : x < ((4 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg19Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 20 := by simpa using hj
    have hj_le_nat : j <= 19 := by omega
    have hj_le_real : (j : Real) <= (19 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (19 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg19Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg19_expPolyIntegral :
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg19Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg19Coeff 24
    ((-3 : Real) / (20 : Real))
    ((7 : Real) / (6 : Real))
    ((4 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg19_centeredBSplineR_expIntegral :
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg19Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((4 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((7 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((4 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((4 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg19_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg19_expPolyIntegral

def p0PieceK11D13PlusWindowSeg20Coeff : Nat -> Real
  | 0 => ((-108420319278190044603269 : Real) / (150979116192867044098 : Real))
  | 1 => ((912497475312561290186412 : Real) / (75489558096433522049 : Real))
  | 2 => ((-7311533597631303925686714 : Real) / (75489558096433522049 : Real))
  | 3 => ((37135298939941011835361952 : Real) / (75489558096433522049 : Real))
  | 4 => ((-134181919368433091728825560 : Real) / (75489558096433522049 : Real))
  | 5 => ((366878551570552428211417536 : Real) / (75489558096433522049 : Real))
  | 6 => ((-788237825680729417177378656 : Real) / (75489558096433522049 : Real))
  | 7 => ((1364288629565770742078429184 : Real) / (75489558096433522049 : Real))
  | 8 => ((-1935064882376299295066827008 : Real) / (75489558096433522049 : Real))
  | 9 => ((2276117091964960172092200960 : Real) / (75489558096433522049 : Real))
  | 10 => ((-2238381532306938475526243328 : Real) / (75489558096433522049 : Real))
  | 11 => ((1849929155717898605371047936 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1288246114517894098654703616 : Real) / (75489558096433522049 : Real))
  | 13 => ((756116356767302265907544064 : Real) / (75489558096433522049 : Real))
  | 14 => ((-373270582944559537451089920 : Real) / (75489558096433522049 : Real))
  | 15 => ((154271401845330325123104768 : Real) / (75489558096433522049 : Real))
  | 16 => ((-52970417273180726000123904 : Real) / (75489558096433522049 : Real))
  | 17 => ((14936277990843217028579328 : Real) / (75489558096433522049 : Real))
  | 18 => ((-3400715822639175565443072 : Real) / (75489558096433522049 : Real))
  | 19 => ((609853205621553899765760 : Real) / (75489558096433522049 : Real))
  | 20 => ((-82942237483774429888512 : Real) / (75489558096433522049 : Real))
  | 21 => ((8042020293910600876032 : Real) / (75489558096433522049 : Real))
  | 22 => ((-495341829697392082944 : Real) / (75489558096433522049 : Real))
  | 23 => ((14568877344040943616 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg20_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((4 : Real) / (3 : Real)) < x) (hxhi : x < ((3 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg20Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 21 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (21 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 21 := by simpa using hj
    have hj_le_nat : j <= 20 := by omega
    have hj_le_real : (j : Real) <= (20 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (20 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg20Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg20_expPolyIntegral :
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg20Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg20Coeff 24
    ((-3 : Real) / (20 : Real))
    ((4 : Real) / (3 : Real))
    ((3 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg20_centeredBSplineR_expIntegral :
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg20Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((3 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((4 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((3 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((3 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg20_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg20_expPolyIntegral

def p0PieceK11D13PlusWindowSeg21Coeff : Nat -> Real
  | 0 => ((530600476200980836550141 : Real) / (301958232385734088196 : Real))
  | 1 => ((-3905386929181311183761715 : Real) / (150979116192867044098 : Real))
  | 2 => ((13699866628325619876139929 : Real) / (75489558096433522049 : Real))
  | 3 => ((-60917902114524632573162382 : Real) / (75489558096433522049 : Real))
  | 4 => ((192662084146452389632922220 : Real) / (75489558096433522049 : Real))
  | 5 => ((-461126257333824124571676840 : Real) / (75489558096433522049 : Real))
  | 6 => ((867771792128023688388810096 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1316869799267448571695400224 : Real) / (75489558096433522049 : Real))
  | 8 => ((1639813022734659789964945536 : Real) / (75489558096433522049 : Real))
  | 9 => ((-1695969469269438811276435200 : Real) / (75489558096433522049 : Real))
  | 10 => ((1468899258178500575617817088 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1070958739816083677348514816 : Real) / (75489558096433522049 : Real))
  | 12 => ((659012482504760756491671552 : Real) / (75489558096433522049 : Real))
  | 13 => ((-342337210783938934431436800 : Real) / (75489558096433522049 : Real))
  | 14 => ((149802544460793415091281920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-54957849116810855893843968 : Real) / (75489558096433522049 : Real))
  | 16 => ((16772666380866334338859008 : Real) / (75489558096433522049 : Real))
  | 17 => ((-4208882227914799535063040 : Real) / (75489558096433522049 : Real))
  | 18 => ((853764225973717004255232 : Real) / (75489558096433522049 : Real))
  | 19 => ((-136546802907023744040960 : Real) / (75489558096433522049 : Real))
  | 20 => ((16577763653369255952384 : Real) / (75489558096433522049 : Real))
  | 21 => ((-1436075052484035870720 : Real) / (75489558096433522049 : Real))
  | 22 => ((79088191296222265344 : Real) / (75489558096433522049 : Real))
  | 23 => ((-2081268192005849088 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg21_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((3 : Real) / (2 : Real)) < x) (hxhi : x < ((5 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg21Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 22 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (22 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 22 := by simpa using hj
    have hj_le_nat : j <= 21 := by omega
    have hj_le_real : (j : Real) <= (21 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (21 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg21Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg21_expPolyIntegral :
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg21Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg21Coeff 24
    ((-3 : Real) / (20 : Real))
    ((3 : Real) / (2 : Real))
    ((5 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg21_centeredBSplineR_expIntegral :
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg21Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((5 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((3 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((5 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((5 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg21_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg21_expPolyIntegral

def p0PieceK11D13PlusWindowSeg22Coeff : Nat -> Real
  | 0 => ((-619399523799019163449859 : Real) / (301958232385734088196 : Real))
  | 1 => ((4029613070818688816238285 : Real) / (150979116192867044098 : Real))
  | 2 => ((-12485633371674380123860071 : Real) / (75489558096433522049 : Real))
  | 3 => ((49061197885475367426837618 : Real) / (75489558096433522049 : Real))
  | 4 => ((-137275215853547610367077780 : Real) / (75489558096433522049 : Real))
  | 5 => ((291130786666175875428323160 : Real) / (75489558096433522049 : Real))
  | 6 => ((-486290887071976311611189904 : Real) / (75489558096433522049 : Real))
  | 7 => ((656192961852551428304599776 : Real) / (75489558096433522049 : Real))
  | 8 => ((-727862290609340210035054464 : Real) / (75489558096433522049 : Real))
  | 9 => ((671705844074561188723564800 : Real) / (75489558096433522049 : Real))
  | 10 => ((-519948005030459424382182912 : Real) / (75489558096433522049 : Real))
  | 11 => ((339314774095724322651485184 : Real) / (75489558096433522049 : Real))
  | 12 => ((-187151625842324043508328448 : Real) / (75489558096433522049 : Real))
  | 13 => ((87253798069196425568563200 : Real) / (75489558096433522049 : Real))
  | 14 => ((-34307887904836024908718080 : Real) / (75489558096433522049 : Real))
  | 15 => ((11321906534815742506156032 : Real) / (75489558096433522049 : Real))
  | 16 => ((-3111260314621645181140992 : Real) / (75489558096433522049 : Real))
  | 17 => ((703617308617524816936960 : Real) / (75489558096433522049 : Real))
  | 18 => ((-128735681332747866144768 : Real) / (75489558096433522049 : Real))
  | 19 => ((18584761404523340759040 : Real) / (75489558096433522049 : Real))
  | 20 => ((-2038024064016394223616 : Real) / (75489558096433522049 : Real))
  | 21 => ((159563894720448430080 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7946660369476878336 : Real) / (75489558096433522049 : Real))
  | 23 => ((189206199273259008 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg22_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((5 : Real) / (3 : Real)) < x) (hxhi : x < ((11 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg22Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 23 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (23 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 23 := by simpa using hj
    have hj_le_nat : j <= 22 := by omega
    have hj_le_real : (j : Real) <= (22 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (22 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg22Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg22_expPolyIntegral :
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg22Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg22Coeff 24
    ((-3 : Real) / (20 : Real))
    ((5 : Real) / (3 : Real))
    ((11 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg22_centeredBSplineR_expIntegral :
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg22Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((11 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((5 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((11 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((11 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg22_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg22_expPolyIntegral

def p0PieceK11D13PlusWindowSeg23Coeff : Nat -> Real
  | 0 => ((69007679864054552199168 : Real) / (75489558096433522049 : Real))
  | 1 => ((-793588318436627350290432 : Real) / (75489558096433522049 : Real))
  | 2 => ((4364735751401450426597376 : Real) / (75489558096433522049 : Real))
  | 3 => ((-15276575129905076493090816 : Real) / (75489558096433522049 : Real))
  | 4 => ((38191437824762691232727040 : Real) / (75489558096433522049 : Real))
  | 5 => ((-72563731867049113342181376 : Real) / (75489558096433522049 : Real))
  | 6 => ((108845597800573670013272064 : Real) / (75489558096433522049 : Real))
  | 7 => ((-132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 8 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 9 => ((-110141378726770975608668160 : Real) / (75489558096433522049 : Real))
  | 10 => ((77098965108739682926067712 : Real) / (75489558096433522049 : Real))
  | 11 => ((-45558479382437085365403648 : Real) / (75489558096433522049 : Real))
  | 12 => ((22779239691218542682701824 : Real) / (75489558096433522049 : Real))
  | 13 => ((-9637370638592460365758464 : Real) / (75489558096433522049 : Real))
  | 14 => ((3441918085211592987770880 : Real) / (75489558096433522049 : Real))
  | 15 => ((-1032575425563477896331264 : Real) / (75489558096433522049 : Real))
  | 16 => ((258143856390869474082816 : Real) / (75489558096433522049 : Real))
  | 17 => ((-53147264551061362311168 : Real) / (75489558096433522049 : Real))
  | 18 => ((8857877425176893718528 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1165510187523275489280 : Real) / (75489558096433522049 : Real))
  | 20 => ((116551018752327548928 : Real) / (75489558096433522049 : Real))
  | 21 => ((-8325072768023396352 : Real) / (75489558096433522049 : Real))
  | 22 => ((378412398546518016 : Real) / (75489558096433522049 : Real))
  | 23 => ((-8226356490141696 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D13PlusWindowSeg23_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((11 : Real) / (6 : Real)) < x) (hxhi : x < ((2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D13PlusWindowSeg23Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 24 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (24 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 24 := by simpa using hj
    have hj_le_nat : j <= 23 := by omega
    have hj_le_real : (j : Real) <= (23 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (23 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D13PlusWindowSeg23Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D13PlusWindowSeg23_expPolyIntegral :
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D13PlusWindowSeg23Coeff 24 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D13PlusWindowSeg23Coeff 24
    ((-3 : Real) / (20 : Real))
    ((11 : Real) / (6 : Real))
    ((2 : Real))
    (by norm_num)

theorem p0PieceK11D13PlusWindowSeg23_centeredBSplineR_expIntegral :
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D13PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
  calc
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D13PlusWindowSeg23Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((11 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D13PlusWindowSeg23_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D13PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
        exact p0PieceK11D13PlusWindowSeg23_expPolyIntegral

def p0PieceK11D13PlusWindowBreak : Nat -> Real
  | 0 => ((-2 : Real))
  | 1 => ((-11 : Real) / (6 : Real))
  | 2 => ((-5 : Real) / (3 : Real))
  | 3 => ((-3 : Real) / (2 : Real))
  | 4 => ((-4 : Real) / (3 : Real))
  | 5 => ((-7 : Real) / (6 : Real))
  | 6 => ((-1 : Real))
  | 7 => ((-5 : Real) / (6 : Real))
  | 8 => ((-2 : Real) / (3 : Real))
  | 9 => ((-1 : Real) / (2 : Real))
  | 10 => ((-1 : Real) / (3 : Real))
  | 11 => ((-1 : Real) / (6 : Real))
  | 12 => ((0 : Real))
  | 13 => ((1 : Real) / (6 : Real))
  | 14 => ((1 : Real) / (3 : Real))
  | 15 => ((1 : Real) / (2 : Real))
  | 16 => ((2 : Real) / (3 : Real))
  | 17 => ((5 : Real) / (6 : Real))
  | 18 => ((1 : Real))
  | 19 => ((7 : Real) / (6 : Real))
  | 20 => ((4 : Real) / (3 : Real))
  | 21 => ((3 : Real) / (2 : Real))
  | 22 => ((5 : Real) / (3 : Real))
  | 23 => ((11 : Real) / (6 : Real))
  | 24 => ((2 : Real))
  | _ => ((2 : Real))

def p0PieceK11D13PlusWindowSegmentExpIntegral : Nat -> Real
  | 0 => expPolyIntegral p0PieceK11D13PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real))
  | 1 => expPolyIntegral p0PieceK11D13PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real))
  | 2 => expPolyIntegral p0PieceK11D13PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real))
  | 3 => expPolyIntegral p0PieceK11D13PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real))
  | 4 => expPolyIntegral p0PieceK11D13PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real))
  | 5 => expPolyIntegral p0PieceK11D13PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real))
  | 6 => expPolyIntegral p0PieceK11D13PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real))
  | 7 => expPolyIntegral p0PieceK11D13PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real))
  | 8 => expPolyIntegral p0PieceK11D13PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real))
  | 9 => expPolyIntegral p0PieceK11D13PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real))
  | 10 => expPolyIntegral p0PieceK11D13PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real))
  | 11 => expPolyIntegral p0PieceK11D13PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real))
  | 12 => expPolyIntegral p0PieceK11D13PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real))
  | 13 => expPolyIntegral p0PieceK11D13PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real))
  | 14 => expPolyIntegral p0PieceK11D13PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real))
  | 15 => expPolyIntegral p0PieceK11D13PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real))
  | 16 => expPolyIntegral p0PieceK11D13PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real))
  | 17 => expPolyIntegral p0PieceK11D13PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real))
  | 18 => expPolyIntegral p0PieceK11D13PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real))
  | 19 => expPolyIntegral p0PieceK11D13PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real))
  | 20 => expPolyIntegral p0PieceK11D13PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real))
  | 21 => expPolyIntegral p0PieceK11D13PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real))
  | 22 => expPolyIntegral p0PieceK11D13PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real))
  | 23 => expPolyIntegral p0PieceK11D13PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real))
  | _ => 0

def p0PieceK11D13PlusWindowExpPolyIntegralSum : Real :=
  (Finset.range 24).sum p0PieceK11D13PlusWindowSegmentExpIntegral

theorem p0PieceK11D13PlusWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D13PlusWindowExpPolyIntegralSum := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (a := p0PieceK11D13PlusWindowBreak) (n := 24)
    (μ := volume) ?hint
  calc
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        (Finset.range 24).sum (fun i =>
          ∫ x in p0PieceK11D13PlusWindowBreak i..p0PieceK11D13PlusWindowBreak (i + 1),
            Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
          simpa [p0PieceK11D13PlusWindowBreak] using hsplit.symm
    _ = (Finset.range 24).sum p0PieceK11D13PlusWindowSegmentExpIntegral := by
        apply Finset.sum_congr rfl
        intro i hi
        simp at hi
        interval_cases i <;>
          simp [p0PieceK11D13PlusWindowBreak, p0PieceK11D13PlusWindowSegmentExpIntegral]
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg0_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg1_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg2_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg3_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg4_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg5_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg6_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg7_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg8_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg9_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg10_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg11_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg12_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg13_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg14_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg15_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg16_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg17_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg18_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg19_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg20_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg21_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg22_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D13PlusWindowSeg23_centeredBSplineR_expIntegral
    _ = p0PieceK11D13PlusWindowExpPolyIntegralSum := by
        rfl
  · intro k hk
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _

def p0PieceK11D13MinusWindowExpPolyIntegralSum : Real := 0

theorem p0PieceK11D13PlusWindow_leftSupportZeroIntegral :
    ∫ x in ((-55 : Real) / (6 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((-55 : Real) / (6 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-55 : Real) / (6 : Real))..((-2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D13PlusWindow_rightSupportZeroIntegral :
    ∫ x in ((2 : Real))..((65 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((2 : Real))..((65 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((2 : Real))..((65 : Real) / (6 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D13PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D13PlusWindowExpPolyIntegralSum := by
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-55 : Real) / (6 : Real))) (b := ((-2 : Real))) (c := ((65 : Real) / (6 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-2 : Real))) (b := ((2 : Real))) (c := ((65 : Real) / (6 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
  calc
    ∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        (∫ x in ((-55 : Real) / (6 : Real))..((-2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) +
        (∫ x in ((-2 : Real))..((65 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
        simpa using hsplitLeft.symm
    _ = ∫ x in ((-2 : Real))..((65 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
        rw [p0PieceK11D13PlusWindow_leftSupportZeroIntegral]
        ring
    _ = (∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) +
        (∫ x in ((2 : Real))..((65 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
        simpa using hsplitRight.symm
    _ = ∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
        rw [p0PieceK11D13PlusWindow_rightSupportZeroIntegral]
        ring
    _ = p0PieceK11D13PlusWindowExpPolyIntegralSum := by
        exact p0PieceK11D13PlusWindow_centeredBSplineR_expIntegral_sum

theorem p0PieceK11D13MinusWindow_rightSupportZeroIntegral :
    ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D13MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D13MinusWindowExpPolyIntegralSum := by
  simpa [p0PieceK11D13MinusWindowExpPolyIntegralSum] using
    p0PieceK11D13MinusWindow_rightSupportZeroIntegral

theorem p0PieceK11D13_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((13 : Real) / (4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((13 : Real) / (4 : Real)) / 2) *
        p0PieceK11D13PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((13 : Real) / (4 : Real)) / 2)) *
        p0PieceK11D13MinusWindowExpPolyIntegralSum := by
  have hprofile :=
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile_eq_transformed_integrals
      (k := 11)
      (ell := ((3 : Real) / (10 : Real)))
      (L := ((3 : Real)))
      (d := ((13 : Real) / (4 : Real)))
      (by norm_num)
  calc
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((13 : Real) / (4 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((13 : Real) / (4 : Real)) / 2) *
        (∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
          Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x) +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((13 : Real) / (4 : Real)) / 2)) *
        (∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
          Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x) := by
        norm_num at hprofile ⊢
        simpa [mul_assoc] using hprofile
    _ = ((3 : Real) / (10 : Real)) * Real.exp (((13 : Real) / (4 : Real)) / 2) *
        p0PieceK11D13PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((13 : Real) / (4 : Real)) / 2)) *
        p0PieceK11D13MinusWindowExpPolyIntegralSum := by
        have hplus :
            ∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
            p0PieceK11D13PlusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                ∫ x in ((-55 : Real) / (6 : Real))..((65 : Real) / (6 : Real)),
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x
                have harg : -(((3 : Real) / (10 : Real)) / 2) * x = ((-3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK11D13PlusWindowExpPolyIntegralSum := by
                exact p0PieceK11D13PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        have hminus :
            ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
            p0PieceK11D13MinusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                ∫ x in ((65 : Real) / (6 : Real))..((185 : Real) / (6 : Real)),
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x
                have harg : (((3 : Real) / (10 : Real)) / 2) * x = ((3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK11D13MinusWindowExpPolyIntegralSum := by
                exact p0PieceK11D13MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        rw [hplus, hminus]

def p0PieceK11D14PlusWindowSeg0Coeff : Nat -> Real
  | 0 => ((69007679864054552199168 : Real) / (75489558096433522049 : Real))
  | 1 => ((793588318436627350290432 : Real) / (75489558096433522049 : Real))
  | 2 => ((4364735751401450426597376 : Real) / (75489558096433522049 : Real))
  | 3 => ((15276575129905076493090816 : Real) / (75489558096433522049 : Real))
  | 4 => ((38191437824762691232727040 : Real) / (75489558096433522049 : Real))
  | 5 => ((72563731867049113342181376 : Real) / (75489558096433522049 : Real))
  | 6 => ((108845597800573670013272064 : Real) / (75489558096433522049 : Real))
  | 7 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 8 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 9 => ((110141378726770975608668160 : Real) / (75489558096433522049 : Real))
  | 10 => ((77098965108739682926067712 : Real) / (75489558096433522049 : Real))
  | 11 => ((45558479382437085365403648 : Real) / (75489558096433522049 : Real))
  | 12 => ((22779239691218542682701824 : Real) / (75489558096433522049 : Real))
  | 13 => ((9637370638592460365758464 : Real) / (75489558096433522049 : Real))
  | 14 => ((3441918085211592987770880 : Real) / (75489558096433522049 : Real))
  | 15 => ((1032575425563477896331264 : Real) / (75489558096433522049 : Real))
  | 16 => ((258143856390869474082816 : Real) / (75489558096433522049 : Real))
  | 17 => ((53147264551061362311168 : Real) / (75489558096433522049 : Real))
  | 18 => ((8857877425176893718528 : Real) / (75489558096433522049 : Real))
  | 19 => ((1165510187523275489280 : Real) / (75489558096433522049 : Real))
  | 20 => ((116551018752327548928 : Real) / (75489558096433522049 : Real))
  | 21 => ((8325072768023396352 : Real) / (75489558096433522049 : Real))
  | 22 => ((378412398546518016 : Real) / (75489558096433522049 : Real))
  | 23 => ((8226356490141696 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg0_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real)) < x) (hxhi : x < ((-11 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg0Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 1).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 1 := by simpa using hj
    have hj_le_nat : j <= 0 := by omega
    have hj_le_real : (j : Real) <= (0 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (0 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg0Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg0_expPolyIntegral :
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg0Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg0Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-2 : Real))
    ((-11 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg0_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-2 : Real))..((-11 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg0Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-11 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-11 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-11 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg0_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg0_expPolyIntegral

def p0PieceK11D14PlusWindowSeg1Coeff : Nat -> Real
  | 0 => ((-619399523799019163449859 : Real) / (301958232385734088196 : Real))
  | 1 => ((-4029613070818688816238285 : Real) / (150979116192867044098 : Real))
  | 2 => ((-12485633371674380123860071 : Real) / (75489558096433522049 : Real))
  | 3 => ((-49061197885475367426837618 : Real) / (75489558096433522049 : Real))
  | 4 => ((-137275215853547610367077780 : Real) / (75489558096433522049 : Real))
  | 5 => ((-291130786666175875428323160 : Real) / (75489558096433522049 : Real))
  | 6 => ((-486290887071976311611189904 : Real) / (75489558096433522049 : Real))
  | 7 => ((-656192961852551428304599776 : Real) / (75489558096433522049 : Real))
  | 8 => ((-727862290609340210035054464 : Real) / (75489558096433522049 : Real))
  | 9 => ((-671705844074561188723564800 : Real) / (75489558096433522049 : Real))
  | 10 => ((-519948005030459424382182912 : Real) / (75489558096433522049 : Real))
  | 11 => ((-339314774095724322651485184 : Real) / (75489558096433522049 : Real))
  | 12 => ((-187151625842324043508328448 : Real) / (75489558096433522049 : Real))
  | 13 => ((-87253798069196425568563200 : Real) / (75489558096433522049 : Real))
  | 14 => ((-34307887904836024908718080 : Real) / (75489558096433522049 : Real))
  | 15 => ((-11321906534815742506156032 : Real) / (75489558096433522049 : Real))
  | 16 => ((-3111260314621645181140992 : Real) / (75489558096433522049 : Real))
  | 17 => ((-703617308617524816936960 : Real) / (75489558096433522049 : Real))
  | 18 => ((-128735681332747866144768 : Real) / (75489558096433522049 : Real))
  | 19 => ((-18584761404523340759040 : Real) / (75489558096433522049 : Real))
  | 20 => ((-2038024064016394223616 : Real) / (75489558096433522049 : Real))
  | 21 => ((-159563894720448430080 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7946660369476878336 : Real) / (75489558096433522049 : Real))
  | 23 => ((-189206199273259008 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg1_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-11 : Real) / (6 : Real)) < x) (hxhi : x < ((-5 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg1Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 2).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 2 := by simpa using hj
    have hj_le_nat : j <= 1 := by omega
    have hj_le_real : (j : Real) <= (1 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (1 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg1Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg1_expPolyIntegral :
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg1Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg1Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-11 : Real) / (6 : Real))
    ((-5 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg1_centeredBSplineR_expIntegral :
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-11 : Real) / (6 : Real))..((-5 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg1Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-5 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-11 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-5 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-5 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg1_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg1_expPolyIntegral

def p0PieceK11D14PlusWindowSeg2Coeff : Nat -> Real
  | 0 => ((530600476200980836550141 : Real) / (301958232385734088196 : Real))
  | 1 => ((3905386929181311183761715 : Real) / (150979116192867044098 : Real))
  | 2 => ((13699866628325619876139929 : Real) / (75489558096433522049 : Real))
  | 3 => ((60917902114524632573162382 : Real) / (75489558096433522049 : Real))
  | 4 => ((192662084146452389632922220 : Real) / (75489558096433522049 : Real))
  | 5 => ((461126257333824124571676840 : Real) / (75489558096433522049 : Real))
  | 6 => ((867771792128023688388810096 : Real) / (75489558096433522049 : Real))
  | 7 => ((1316869799267448571695400224 : Real) / (75489558096433522049 : Real))
  | 8 => ((1639813022734659789964945536 : Real) / (75489558096433522049 : Real))
  | 9 => ((1695969469269438811276435200 : Real) / (75489558096433522049 : Real))
  | 10 => ((1468899258178500575617817088 : Real) / (75489558096433522049 : Real))
  | 11 => ((1070958739816083677348514816 : Real) / (75489558096433522049 : Real))
  | 12 => ((659012482504760756491671552 : Real) / (75489558096433522049 : Real))
  | 13 => ((342337210783938934431436800 : Real) / (75489558096433522049 : Real))
  | 14 => ((149802544460793415091281920 : Real) / (75489558096433522049 : Real))
  | 15 => ((54957849116810855893843968 : Real) / (75489558096433522049 : Real))
  | 16 => ((16772666380866334338859008 : Real) / (75489558096433522049 : Real))
  | 17 => ((4208882227914799535063040 : Real) / (75489558096433522049 : Real))
  | 18 => ((853764225973717004255232 : Real) / (75489558096433522049 : Real))
  | 19 => ((136546802907023744040960 : Real) / (75489558096433522049 : Real))
  | 20 => ((16577763653369255952384 : Real) / (75489558096433522049 : Real))
  | 21 => ((1436075052484035870720 : Real) / (75489558096433522049 : Real))
  | 22 => ((79088191296222265344 : Real) / (75489558096433522049 : Real))
  | 23 => ((2081268192005849088 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg2_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-5 : Real) / (3 : Real)) < x) (hxhi : x < ((-3 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg2Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 3).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 3 := by simpa using hj
    have hj_le_nat : j <= 2 := by omega
    have hj_le_real : (j : Real) <= (2 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (2 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg2Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg2_expPolyIntegral :
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg2Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg2Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-5 : Real) / (3 : Real))
    ((-3 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg2_centeredBSplineR_expIntegral :
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-5 : Real) / (3 : Real))..((-3 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg2Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-3 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-5 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-3 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-3 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg2_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg2_expPolyIntegral

def p0PieceK11D14PlusWindowSeg3Coeff : Nat -> Real
  | 0 => ((-108420319278190044603269 : Real) / (150979116192867044098 : Real))
  | 1 => ((-912497475312561290186412 : Real) / (75489558096433522049 : Real))
  | 2 => ((-7311533597631303925686714 : Real) / (75489558096433522049 : Real))
  | 3 => ((-37135298939941011835361952 : Real) / (75489558096433522049 : Real))
  | 4 => ((-134181919368433091728825560 : Real) / (75489558096433522049 : Real))
  | 5 => ((-366878551570552428211417536 : Real) / (75489558096433522049 : Real))
  | 6 => ((-788237825680729417177378656 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1364288629565770742078429184 : Real) / (75489558096433522049 : Real))
  | 8 => ((-1935064882376299295066827008 : Real) / (75489558096433522049 : Real))
  | 9 => ((-2276117091964960172092200960 : Real) / (75489558096433522049 : Real))
  | 10 => ((-2238381532306938475526243328 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1849929155717898605371047936 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1288246114517894098654703616 : Real) / (75489558096433522049 : Real))
  | 13 => ((-756116356767302265907544064 : Real) / (75489558096433522049 : Real))
  | 14 => ((-373270582944559537451089920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-154271401845330325123104768 : Real) / (75489558096433522049 : Real))
  | 16 => ((-52970417273180726000123904 : Real) / (75489558096433522049 : Real))
  | 17 => ((-14936277990843217028579328 : Real) / (75489558096433522049 : Real))
  | 18 => ((-3400715822639175565443072 : Real) / (75489558096433522049 : Real))
  | 19 => ((-609853205621553899765760 : Real) / (75489558096433522049 : Real))
  | 20 => ((-82942237483774429888512 : Real) / (75489558096433522049 : Real))
  | 21 => ((-8042020293910600876032 : Real) / (75489558096433522049 : Real))
  | 22 => ((-495341829697392082944 : Real) / (75489558096433522049 : Real))
  | 23 => ((-14568877344040943616 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg3_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-3 : Real) / (2 : Real)) < x) (hxhi : x < ((-4 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg3Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 4).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 4 := by simpa using hj
    have hj_le_nat : j <= 3 := by omega
    have hj_le_real : (j : Real) <= (3 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (3 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg3Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg3_expPolyIntegral :
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg3Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg3Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-3 : Real) / (2 : Real))
    ((-4 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg3_centeredBSplineR_expIntegral :
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-3 : Real) / (2 : Real))..((-4 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg3Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-4 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-3 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-4 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-4 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg3_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg3_expPolyIntegral

def p0PieceK11D14PlusWindowSeg4Coeff : Nat -> Real
  | 0 => ((22256415739968419044475 : Real) / (150979116192867044098 : Real))
  | 1 => ((214589364219055458775380 : Real) / (75489558096433522049 : Real))
  | 2 => ((1986932828504534253248070 : Real) / (75489558096433522049 : Real))
  | 3 => ((11681649797272138604045664 : Real) / (75489558096433522049 : Real))
  | 4 => ((48881638396116222418953000 : Real) / (75489558096433522049 : Real))
  | 5 => ((154852588058413117109751360 : Real) / (75489558096433522049 : Real))
  | 6 => ((385657238484443059795251360 : Real) / (75489558096433522049 : Real))
  | 7 => ((773877380163650555264575488 : Real) / (75489558096433522049 : Real))
  | 8 => ((1272184132217832650947680000 : Real) / (75489558096433522049 : Real))
  | 9 => ((1732944176277704760425932800 : Real) / (75489558096433522049 : Real))
  | 10 => ((1971132799347859703617797120 : Real) / (75489558096433522049 : Real))
  | 11 => ((1881231274612490689779351552 : Real) / (75489558096433522049 : Real))
  | 12 => ((1510124208229897872708096000 : Real) / (75489558096433522049 : Real))
  | 13 => ((1019772501899565715918848000 : Real) / (75489558096433522049 : Real))
  | 14 => ((578098448484119738527334400 : Real) / (75489558096433522049 : Real))
  | 15 => ((273844662297575349067186176 : Real) / (75489558096433522049 : Real))
  | 16 => ((107573106780408901821235200 : Real) / (75489558096433522049 : Real))
  | 17 => ((34643339731588873916252160 : Real) / (75489558096433522049 : Real))
  | 18 => ((8994188607968847170764800 : Real) / (75489558096433522049 : Real))
  | 19 => ((1836509510945819008696320 : Real) / (75489558096433522049 : Real))
  | 20 => ((284012170001331506380800 : Real) / (75489558096433522049 : Real))
  | 21 => ((31274523365207892295680 : Real) / (75489558096433522049 : Real))
  | 22 => ((2185331601606141542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((72844386720204718080 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg4_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-4 : Real) / (3 : Real)) < x) (hxhi : x < ((-7 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg4Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 5).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 5 := by simpa using hj
    have hj_le_nat : j <= 4 := by omega
    have hj_le_real : (j : Real) <= (4 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (4 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg4Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg4_expPolyIntegral :
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg4Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg4Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-4 : Real) / (3 : Real))
    ((-7 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg4_centeredBSplineR_expIntegral :
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-4 : Real) / (3 : Real))..((-7 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg4Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-7 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-4 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-7 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-7 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg4_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg4_expPolyIntegral

def p0PieceK11D14PlusWindowSeg5Coeff : Nat -> Real
  | 0 => ((-3957220059346464754503 : Real) / (301958232385734088196 : Real))
  | 1 => ((-48597493877681639048991 : Real) / (150979116192867044098 : Real))
  | 2 => ((-265440790984202085007899 : Real) / (75489558096433522049 : Real))
  | 3 => ((-1832591919660279425490150 : Real) / (75489558096433522049 : Real))
  | 4 => ((-9036540390736997707629060 : Real) / (75489558096433522049 : Real))
  | 5 => ((-33795194275908799873973064 : Real) / (75489558096433522049 : Real))
  | 6 => ((-99437058946670441020040016 : Real) / (75489558096433522049 : Real))
  | 7 => ((-235910749182748977044806560 : Real) / (75489558096433522049 : Real))
  | 8 => ((-458881232375995118725546368 : Real) / (75489558096433522049 : Real))
  | 9 => ((-740006344570620624821533440 : Real) / (75489558096433522049 : Real))
  | 10 => ((-996407825670130758679162368 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1124848839042097051248737280 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1066515889188320191030265856 : Real) / (75489558096433522049 : Real))
  | 13 => ((-848999436887273758880403456 : Real) / (75489558096433522049 : Real))
  | 14 => ((-566047636487414633798737920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-314573324259213756700508160 : Real) / (75489558096433522049 : Real))
  | 16 => ((-144606030315357857793490944 : Real) / (75489558096433522049 : Real))
  | 17 => ((-54361061596328805947768832 : Real) / (75489558096433522049 : Real))
  | 18 => ((-16435640342864775647526912 : Real) / (75489558096433522049 : Real))
  | 19 => ((-3899542132099359070617600 : Real) / (75489558096433522049 : Real))
  | 20 => ((-699310968806413307215872 : Real) / (75489558096433522049 : Real))
  | 21 => ((-89132391590842493042688 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7197025407956226146304 : Real) / (75489558096433522049 : Real))
  | 23 => ((-276808669536777928704 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg5_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-7 : Real) / (6 : Real)) < x) (hxhi : x < ((-1 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg5Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 6).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 6 := by simpa using hj
    have hj_le_nat : j <= 5 := by omega
    have hj_le_real : (j : Real) <= (5 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (5 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg5Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg5_expPolyIntegral :
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg5Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg5Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-7 : Real) / (6 : Real))
    ((-1 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg5_centeredBSplineR_expIntegral :
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
  calc
    ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-7 : Real) / (6 : Real))..((-1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg5Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-7 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg5_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg5_expPolyIntegral

def p0PieceK11D14PlusWindowSeg6Coeff : Nat -> Real
  | 0 => ((471718653241982104761 : Real) / (301958232385734088196 : Real))
  | 1 => ((2335301317085499832545 : Real) / (150979116192867044098 : Real))
  | 2 => ((14689582587017178840549 : Real) / (75489558096433522049 : Real))
  | 3 => ((128320695338255421448986 : Real) / (75489558096433522049 : Real))
  | 4 => ((768022684255676527066620 : Real) / (75489558096433522049 : Real))
  | 5 => ((3462145409063362217870520 : Real) / (75489558096433522049 : Real))
  | 6 => ((12334960108246045255490736 : Real) / (75489558096433522049 : Real))
  | 7 => ((35535582807762489624339552 : Real) / (75489558096433522049 : Real))
  | 8 => ((84011431605027814612745856 : Real) / (75489558096433522049 : Real))
  | 9 => ((164814762064417597408953600 : Real) / (75489558096433522049 : Real))
  | 10 => ((270341723618922752443519488 : Real) / (75489558096433522049 : Real))
  | 11 => ((372218810117693461896250368 : Real) / (75489558096433522049 : Real))
  | 12 => ((430551759971470322114721792 : Real) / (75489558096433522049 : Real))
  | 13 => ((417750112401779752242278400 : Real) / (75489558096433522049 : Real))
  | 14 => ((338773470147623588431749120 : Real) / (75489558096433522049 : Real))
  | 15 => ((228319339721809176637784064 : Real) / (75489558096433522049 : Real))
  | 16 => ((126840301675153608875655168 : Real) / (75489558096433522049 : Real))
  | 17 => ((57410957458587680327761920 : Real) / (75489558096433522049 : Real))
  | 18 => ((20821699342107386444316672 : Real) / (75489558096433522049 : Real))
  | 19 => ((5905020942893315164078080 : Real) / (75489558096433522049 : Real))
  | 20 => ((1261601646192121539723264 : Real) / (75489558096433522049 : Real))
  | 21 => ((190997981980376770805760 : Real) / (75489558096433522049 : Real))
  | 22 => ((18269372189427343294464 : Real) / (75489558096433522049 : Real))
  | 23 => ((830426008610333786112 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg6_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real)) < x) (hxhi : x < ((-5 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg6Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 7).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 7 := by simpa using hj
    have hj_le_nat : j <= 6 := by omega
    have hj_le_real : (j : Real) <= (6 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (6 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg6Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg6_expPolyIntegral :
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg6Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg6Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real))
    ((-5 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg6_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real))..((-5 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg6Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-5 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-5 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-5 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg6_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg6_expPolyIntegral

def p0PieceK11D14PlusWindowSeg7Coeff : Nat -> Real
  | 0 => ((74951734195200116034 : Real) / (75489558096433522049 : Real))
  | 1 => ((-18540185039403404040 : Real) / (75489558096433522049 : Real))
  | 2 => ((-968136548267244987576 : Real) / (75489558096433522049 : Real))
  | 3 => ((-3204145398133738707264 : Real) / (75489558096433522049 : Real))
  | 4 => ((-21126360162658433870880 : Real) / (75489558096433522049 : Real))
  | 5 => ((-136374233484245204004480 : Real) / (75489558096433522049 : Real))
  | 6 => ((-619710604925341463259264 : Real) / (75489558096433522049 : Real))
  | 7 => ((-2218028984908408813160448 : Real) / (75489558096433522049 : Real))
  | 8 => ((-6597236697382341637254144 : Real) / (75489558096433522049 : Real))
  | 9 => ((-16402574540402715091046400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-34103401877175372556480512 : Real) / (75489558096433522049 : Real))
  | 11 => ((-59539731494954788103749632 : Real) / (75489558096433522049 : Real))
  | 12 => ((-87558489963707577885278208 : Real) / (75489558096433522049 : Real))
  | 13 => ((-108331064455477807757721600 : Real) / (75489558096433522049 : Real))
  | 14 => ((-112153252872882891568250880 : Real) / (75489558096433522049 : Real))
  | 15 => ((-96347900852955488962215936 : Real) / (75489558096433522049 : Real))
  | 16 => ((-67960042669705190484344832 : Real) / (75489558096433522049 : Real))
  | 17 => ((-38843330335342549944238080 : Real) / (75489558096433522049 : Real))
  | 18 => ((-17680015775464705664483328 : Real) / (75489558096433522049 : Real))
  | 19 => ((-6253415410024187607121920 : Real) / (75489558096433522049 : Real))
  | 20 => ((-1656423078508079125364736 : Real) / (75489558096433522049 : Real))
  | 21 => ((-309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-36301479804966019792896 : Real) / (75489558096433522049 : Real))
  | 23 => ((-2016748878053667766272 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg7_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-5 : Real) / (6 : Real)) < x) (hxhi : x < ((-2 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg7Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 8).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 8 := by simpa using hj
    have hj_le_nat : j <= 7 := by omega
    have hj_le_real : (j : Real) <= (7 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (7 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg7Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg7_expPolyIntegral :
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg7Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg7Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-5 : Real) / (6 : Real))
    ((-2 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg7_centeredBSplineR_expIntegral :
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-5 : Real) / (6 : Real))..((-2 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg7Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-2 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-5 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-2 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-2 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg7_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg7_expPolyIntegral

def p0PieceK11D14PlusWindowSeg8Coeff : Nat -> Real
  | 0 => ((75490840139461477698 : Real) / (75489558096433522049 : Real))
  | 1 => ((58970037613573368 : Real) / (75489558096433522049 : Real))
  | 2 => ((-661250489496464860344 : Real) / (75489558096433522049 : Real))
  | 3 => ((18158218959452628672 : Real) / (75489558096433522049 : Real))
  | 4 => ((3040916965540501148640 : Real) / (75489558096433522049 : Real))
  | 5 => ((1379246146488725606784 : Real) / (75489558096433522049 : Real))
  | 6 => ((180053412961219991424 : Real) / (75489558096433522049 : Real))
  | 7 => ((40144127609693818681344 : Real) / (75489558096433522049 : Real))
  | 8 => ((177282640171966258271232 : Real) / (75489558096433522049 : Real))
  | 9 => ((533723803483054647767040 : Real) / (75489558096433522049 : Real))
  | 10 => ((1462824644984743895027712 : Real) / (75489558096433522049 : Real))
  | 11 => ((3509488248874509242105856 : Real) / (75489558096433522049 : Real))
  | 12 => ((7015339652036368133505024 : Real) / (75489558096433522049 : Real))
  | 13 => ((11704950056812585266118656 : Real) / (75489558096433522049 : Real))
  | 14 => ((16456762675999672385863680 : Real) / (75489558096433522049 : Real))
  | 15 => ((19401113141038818596487168 : Real) / (75489558096433522049 : Real))
  | 16 => ((18851717825790540184682496 : Real) / (75489558096433522049 : Real))
  | 17 => ((14775698205993048410161152 : Real) / (75489558096433522049 : Real))
  | 18 => ((9129498495203093512716288 : Real) / (75489558096433522049 : Real))
  | 19 => ((4329287591555206804930560 : Real) / (75489558096433522049 : Real))
  | 20 => ((1518387821965739198251008 : Real) / (75489558096433522049 : Real))
  | 21 => ((371081793561874868994048 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((4033497756107335532544 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg8_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-2 : Real) / (3 : Real)) < x) (hxhi : x < ((-1 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg8Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 9).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 9 := by simpa using hj
    have hj_le_nat : j <= 8 := by omega
    have hj_le_real : (j : Real) <= (8 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (8 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg8Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg8_expPolyIntegral :
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg8Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg8Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-2 : Real) / (3 : Real))
    ((-1 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg8_centeredBSplineR_expIntegral :
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-2 : Real) / (3 : Real))..((-1 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg8Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-2 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg8_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg8_expPolyIntegral

def p0PieceK11D14PlusWindowSeg9Coeff : Nat -> Real
  | 0 => ((150979115850112767525 : Real) / (150979116192867044098 : Real))
  | 1 => ((-11825020747665 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662548090474419923070 : Real) / (75489558096433522049 : Real))
  | 3 => ((-8194731918249492 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859252828626792367000 : Real) / (75489558096433522049 : Real))
  | 5 => ((-1401294055461133680 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8103831230303900451360 : Real) / (75489558096433522049 : Real))
  | 7 => ((-91883514736766326464 : Real) / (75489558096433522049 : Real))
  | 8 => ((16338595674243918240000 : Real) / (75489558096433522049 : Real))
  | 9 => ((-2756344842686485670400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-39319770327331278597120 : Real) / (75489558096433522049 : Real))
  | 11 => ((-41034914590395713734656 : Real) / (75489558096433522049 : Real))
  | 12 => ((-85706674893441778176000 : Real) / (75489558096433522049 : Real))
  | 13 => ((-312205265684016122880000 : Real) / (75489558096433522049 : Real))
  | 14 => ((-710602070424043884134400 : Real) / (75489558096433522049 : Real))
  | 15 => ((-1199724554669640927510528 : Real) / (75489558096433522049 : Real))
  | 16 => ((-1749119869917919339315200 : Real) / (75489558096433522049 : Real))
  | 17 => ((-2189697543413918256660480 : Real) / (75489558096433522049 : Real))
  | 18 => ((-2180765337734884265164800 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1623482846833202551848960 : Real) / (75489558096433522049 : Real))
  | 20 => ((-862720353389624544460800 : Real) / (75489558096433522049 : Real))
  | 21 => ((-309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-67224962601788925542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((-6722496260178892554240 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg9_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (2 : Real)) < x) (hxhi : x < ((-1 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg9Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 10).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 10 := by simpa using hj
    have hj_le_nat : j <= 9 := by omega
    have hj_le_real : (j : Real) <= (9 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (9 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg9Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg9_expPolyIntegral :
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg9Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg9Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (2 : Real))
    ((-1 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg9_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (2 : Real))..((-1 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg9Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg9_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg9_expPolyIntegral

def p0PieceK11D14PlusWindowSeg10Coeff : Nat -> Real
  | 0 => ((150979116192867096101 : Real) / (150979116192867044098 : Real))
  | 1 => ((3588207 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662547700248616839294 : Real) / (75489558096433522049 : Real))
  | 3 => ((9946509804 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859375749754763756440 : Real) / (75489558096433522049 : Real))
  | 5 => ((6803412705936 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8091219522574035894816 : Real) / (75489558096433522049 : Real))
  | 7 => ((1784437961156928 : Real) / (75489558096433522049 : Real))
  | 8 => ((16889907469292283140352 : Real) / (75489558096433522049 : Real))
  | 9 => ((214132555338831360 : Real) / (75489558096433522049 : Real))
  | 10 => ((-27742222631315615689728 : Real) / (75489558096433522049 : Real))
  | 11 => ((12754513659818391552 : Real) / (75489558096433522049 : Real))
  | 12 => ((37436332418724818202624 : Real) / (75489558096433522049 : Real))
  | 13 => ((388522108406775619584 : Real) / (75489558096433522049 : Real))
  | 14 => ((-40758239440280530206720 : Real) / (75489558096433522049 : Real))
  | 15 => ((5994341101133109559296 : Real) / (75489558096433522049 : Real))
  | 16 => ((59458473738241716289536 : Real) / (75489558096433522049 : Real))
  | 17 => ((44428645808398341439488 : Real) / (75489558096433522049 : Real))
  | 18 => ((53360851487432332935168 : Real) / (75489558096433522049 : Real))
  | 19 => ((140300986763363183493120 : Real) / (75489558096433522049 : Real))
  | 20 => ((195549946768314896744448 : Real) / (75489558096433522049 : Real))
  | 21 => ((144309586385173560164352 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((9411494764250449575936 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg10_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (3 : Real)) < x) (hxhi : x < ((-1 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg10Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 11).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 11 := by simpa using hj
    have hj_le_nat : j <= 10 := by omega
    have hj_le_real : (j : Real) <= (10 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (10 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg10Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg10_expPolyIntegral :
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg10Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg10Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (3 : Real))
    ((-1 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg10_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (3 : Real))..((-1 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg10Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((-1 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((-1 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((-1 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg10_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg10_expPolyIntegral

def p0PieceK11D14PlusWindowSeg11Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-662547700248853660956 : Real) / (75489558096433522049 : Real))
  | 3 => ((0 : Real))
  | 4 => ((2859375749456368462320 : Real) / (75489558096433522049 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-8091219645035464601664 : Real) / (75489558096433522049 : Real))
  | 7 => ((0 : Real))
  | 8 => ((16889886056036749257216 : Real) / (75489558096433522049 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-27744021344780461873152 : Real) / (75489558096433522049 : Real))
  | 11 => ((0 : Real))
  | 12 => ((37359805336765907853312 : Real) / (75489558096433522049 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-42423334190595282862080 : Real) / (75489558096433522049 : Real))
  | 15 => ((0 : Real))
  | 16 => ((41475450434842387611648 : Real) / (75489558096433522049 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-35496440129364349943808 : Real) / (75489558096433522049 : Real))
  | 19 => ((0 : Real))
  | 20 => ((27188762652279076552704 : Real) / (75489558096433522049 : Real))
  | 21 => ((0 : Real))
  | 22 => ((-22245351260955608088576 : Real) / (75489558096433522049 : Real))
  | 23 => ((-11122675630477804044288 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg11_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((-1 : Real) / (6 : Real)) < x) (hxhi : x < ((0 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg11Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 12).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 12 := by simpa using hj
    have hj_le_nat : j <= 11 := by omega
    have hj_le_real : (j : Real) <= (11 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (11 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg11Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg11_expPolyIntegral :
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg11Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg11Coeff 24
    ((-3 : Real) / (20 : Real))
    ((-1 : Real) / (6 : Real))
    ((0 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg11_centeredBSplineR_expIntegral :
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
  calc
    ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-1 : Real) / (6 : Real))..((0 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg11Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((0 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((-1 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((0 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((0 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg11_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg11_expPolyIntegral

def p0PieceK11D14PlusWindowSeg12Coeff : Nat -> Real
  | 0 => ((1 : Real))
  | 1 => ((0 : Real))
  | 2 => ((-662547700248853660956 : Real) / (75489558096433522049 : Real))
  | 3 => ((0 : Real))
  | 4 => ((2859375749456368462320 : Real) / (75489558096433522049 : Real))
  | 5 => ((0 : Real))
  | 6 => ((-8091219645035464601664 : Real) / (75489558096433522049 : Real))
  | 7 => ((0 : Real))
  | 8 => ((16889886056036749257216 : Real) / (75489558096433522049 : Real))
  | 9 => ((0 : Real))
  | 10 => ((-27744021344780461873152 : Real) / (75489558096433522049 : Real))
  | 11 => ((0 : Real))
  | 12 => ((37359805336765907853312 : Real) / (75489558096433522049 : Real))
  | 13 => ((0 : Real))
  | 14 => ((-42423334190595282862080 : Real) / (75489558096433522049 : Real))
  | 15 => ((0 : Real))
  | 16 => ((41475450434842387611648 : Real) / (75489558096433522049 : Real))
  | 17 => ((0 : Real))
  | 18 => ((-35496440129364349943808 : Real) / (75489558096433522049 : Real))
  | 19 => ((0 : Real))
  | 20 => ((27188762652279076552704 : Real) / (75489558096433522049 : Real))
  | 21 => ((0 : Real))
  | 22 => ((-22245351260955608088576 : Real) / (75489558096433522049 : Real))
  | 23 => ((11122675630477804044288 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg12_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((0 : Real)) < x) (hxhi : x < ((1 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg12Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 13).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 13 := by simpa using hj
    have hj_le_nat : j <= 12 := by omega
    have hj_le_real : (j : Real) <= (12 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (12 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg12Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg12_expPolyIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg12Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg12Coeff 24
    ((-3 : Real) / (20 : Real))
    ((0 : Real))
    ((1 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg12_centeredBSplineR_expIntegral :
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((0 : Real))..((1 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg12Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((0 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg12_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg12_expPolyIntegral

def p0PieceK11D14PlusWindowSeg13Coeff : Nat -> Real
  | 0 => ((150979116192867096101 : Real) / (150979116192867044098 : Real))
  | 1 => ((-3588207 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662547700248616839294 : Real) / (75489558096433522049 : Real))
  | 3 => ((-9946509804 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859375749754763756440 : Real) / (75489558096433522049 : Real))
  | 5 => ((-6803412705936 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8091219522574035894816 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1784437961156928 : Real) / (75489558096433522049 : Real))
  | 8 => ((16889907469292283140352 : Real) / (75489558096433522049 : Real))
  | 9 => ((-214132555338831360 : Real) / (75489558096433522049 : Real))
  | 10 => ((-27742222631315615689728 : Real) / (75489558096433522049 : Real))
  | 11 => ((-12754513659818391552 : Real) / (75489558096433522049 : Real))
  | 12 => ((37436332418724818202624 : Real) / (75489558096433522049 : Real))
  | 13 => ((-388522108406775619584 : Real) / (75489558096433522049 : Real))
  | 14 => ((-40758239440280530206720 : Real) / (75489558096433522049 : Real))
  | 15 => ((-5994341101133109559296 : Real) / (75489558096433522049 : Real))
  | 16 => ((59458473738241716289536 : Real) / (75489558096433522049 : Real))
  | 17 => ((-44428645808398341439488 : Real) / (75489558096433522049 : Real))
  | 18 => ((53360851487432332935168 : Real) / (75489558096433522049 : Real))
  | 19 => ((-140300986763363183493120 : Real) / (75489558096433522049 : Real))
  | 20 => ((195549946768314896744448 : Real) / (75489558096433522049 : Real))
  | 21 => ((-144309586385173560164352 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((-9411494764250449575936 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg13_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (6 : Real)) < x) (hxhi : x < ((1 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg13Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 14).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 14 := by simpa using hj
    have hj_le_nat : j <= 13 := by omega
    have hj_le_real : (j : Real) <= (13 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (13 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg13Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg13_expPolyIntegral :
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg13Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg13Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (6 : Real))
    ((1 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg13_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (6 : Real))..((1 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg13Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg13_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg13_expPolyIntegral

def p0PieceK11D14PlusWindowSeg14Coeff : Nat -> Real
  | 0 => ((150979115850112767525 : Real) / (150979116192867044098 : Real))
  | 1 => ((11825020747665 : Real) / (75489558096433522049 : Real))
  | 2 => ((-662548090474419923070 : Real) / (75489558096433522049 : Real))
  | 3 => ((8194731918249492 : Real) / (75489558096433522049 : Real))
  | 4 => ((2859252828626792367000 : Real) / (75489558096433522049 : Real))
  | 5 => ((1401294055461133680 : Real) / (75489558096433522049 : Real))
  | 6 => ((-8103831230303900451360 : Real) / (75489558096433522049 : Real))
  | 7 => ((91883514736766326464 : Real) / (75489558096433522049 : Real))
  | 8 => ((16338595674243918240000 : Real) / (75489558096433522049 : Real))
  | 9 => ((2756344842686485670400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-39319770327331278597120 : Real) / (75489558096433522049 : Real))
  | 11 => ((41034914590395713734656 : Real) / (75489558096433522049 : Real))
  | 12 => ((-85706674893441778176000 : Real) / (75489558096433522049 : Real))
  | 13 => ((312205265684016122880000 : Real) / (75489558096433522049 : Real))
  | 14 => ((-710602070424043884134400 : Real) / (75489558096433522049 : Real))
  | 15 => ((1199724554669640927510528 : Real) / (75489558096433522049 : Real))
  | 16 => ((-1749119869917919339315200 : Real) / (75489558096433522049 : Real))
  | 17 => ((2189697543413918256660480 : Real) / (75489558096433522049 : Real))
  | 18 => ((-2180765337734884265164800 : Real) / (75489558096433522049 : Real))
  | 19 => ((1623482846833202551848960 : Real) / (75489558096433522049 : Real))
  | 20 => ((-862720353389624544460800 : Real) / (75489558096433522049 : Real))
  | 21 => ((309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-67224962601788925542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((6722496260178892554240 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg14_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (3 : Real)) < x) (hxhi : x < ((1 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg14Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 15).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 15 := by simpa using hj
    have hj_le_nat : j <= 14 := by omega
    have hj_le_real : (j : Real) <= (14 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (14 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg14Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg14_expPolyIntegral :
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg14Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg14Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (3 : Real))
    ((1 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg14_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (3 : Real))..((1 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg14Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg14_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg14_expPolyIntegral

def p0PieceK11D14PlusWindowSeg15Coeff : Nat -> Real
  | 0 => ((75490840139461477698 : Real) / (75489558096433522049 : Real))
  | 1 => ((-58970037613573368 : Real) / (75489558096433522049 : Real))
  | 2 => ((-661250489496464860344 : Real) / (75489558096433522049 : Real))
  | 3 => ((-18158218959452628672 : Real) / (75489558096433522049 : Real))
  | 4 => ((3040916965540501148640 : Real) / (75489558096433522049 : Real))
  | 5 => ((-1379246146488725606784 : Real) / (75489558096433522049 : Real))
  | 6 => ((180053412961219991424 : Real) / (75489558096433522049 : Real))
  | 7 => ((-40144127609693818681344 : Real) / (75489558096433522049 : Real))
  | 8 => ((177282640171966258271232 : Real) / (75489558096433522049 : Real))
  | 9 => ((-533723803483054647767040 : Real) / (75489558096433522049 : Real))
  | 10 => ((1462824644984743895027712 : Real) / (75489558096433522049 : Real))
  | 11 => ((-3509488248874509242105856 : Real) / (75489558096433522049 : Real))
  | 12 => ((7015339652036368133505024 : Real) / (75489558096433522049 : Real))
  | 13 => ((-11704950056812585266118656 : Real) / (75489558096433522049 : Real))
  | 14 => ((16456762675999672385863680 : Real) / (75489558096433522049 : Real))
  | 15 => ((-19401113141038818596487168 : Real) / (75489558096433522049 : Real))
  | 16 => ((18851717825790540184682496 : Real) / (75489558096433522049 : Real))
  | 17 => ((-14775698205993048410161152 : Real) / (75489558096433522049 : Real))
  | 18 => ((9129498495203093512716288 : Real) / (75489558096433522049 : Real))
  | 19 => ((-4329287591555206804930560 : Real) / (75489558096433522049 : Real))
  | 20 => ((1518387821965739198251008 : Real) / (75489558096433522049 : Real))
  | 21 => ((-371081793561874868994048 : Real) / (75489558096433522049 : Real))
  | 22 => ((56468968585502697455616 : Real) / (75489558096433522049 : Real))
  | 23 => ((-4033497756107335532544 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg15_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real) / (2 : Real)) < x) (hxhi : x < ((2 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg15Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 16).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 16 := by simpa using hj
    have hj_le_nat : j <= 15 := by omega
    have hj_le_real : (j : Real) <= (15 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (15 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg15Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg15_expPolyIntegral :
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg15Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg15Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real) / (2 : Real))
    ((2 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg15_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real) / (2 : Real))..((2 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg15Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg15_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg15_expPolyIntegral

def p0PieceK11D14PlusWindowSeg16Coeff : Nat -> Real
  | 0 => ((74951734195200116034 : Real) / (75489558096433522049 : Real))
  | 1 => ((18540185039403404040 : Real) / (75489558096433522049 : Real))
  | 2 => ((-968136548267244987576 : Real) / (75489558096433522049 : Real))
  | 3 => ((3204145398133738707264 : Real) / (75489558096433522049 : Real))
  | 4 => ((-21126360162658433870880 : Real) / (75489558096433522049 : Real))
  | 5 => ((136374233484245204004480 : Real) / (75489558096433522049 : Real))
  | 6 => ((-619710604925341463259264 : Real) / (75489558096433522049 : Real))
  | 7 => ((2218028984908408813160448 : Real) / (75489558096433522049 : Real))
  | 8 => ((-6597236697382341637254144 : Real) / (75489558096433522049 : Real))
  | 9 => ((16402574540402715091046400 : Real) / (75489558096433522049 : Real))
  | 10 => ((-34103401877175372556480512 : Real) / (75489558096433522049 : Real))
  | 11 => ((59539731494954788103749632 : Real) / (75489558096433522049 : Real))
  | 12 => ((-87558489963707577885278208 : Real) / (75489558096433522049 : Real))
  | 13 => ((108331064455477807757721600 : Real) / (75489558096433522049 : Real))
  | 14 => ((-112153252872882891568250880 : Real) / (75489558096433522049 : Real))
  | 15 => ((96347900852955488962215936 : Real) / (75489558096433522049 : Real))
  | 16 => ((-67960042669705190484344832 : Real) / (75489558096433522049 : Real))
  | 17 => ((38843330335342549944238080 : Real) / (75489558096433522049 : Real))
  | 18 => ((-17680015775464705664483328 : Real) / (75489558096433522049 : Real))
  | 19 => ((6253415410024187607121920 : Real) / (75489558096433522049 : Real))
  | 20 => ((-1656423078508079125364736 : Real) / (75489558096433522049 : Real))
  | 21 => ((309234827968229057495040 : Real) / (75489558096433522049 : Real))
  | 22 => ((-36301479804966019792896 : Real) / (75489558096433522049 : Real))
  | 23 => ((2016748878053667766272 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg16_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((2 : Real) / (3 : Real)) < x) (hxhi : x < ((5 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg16Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 17).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 17 := by simpa using hj
    have hj_le_nat : j <= 16 := by omega
    have hj_le_real : (j : Real) <= (16 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (16 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg16Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg16_expPolyIntegral :
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg16Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg16Coeff 24
    ((-3 : Real) / (20 : Real))
    ((2 : Real) / (3 : Real))
    ((5 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg16_centeredBSplineR_expIntegral :
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((2 : Real) / (3 : Real))..((5 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg16Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((5 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((2 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((5 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((5 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg16_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg16_expPolyIntegral

def p0PieceK11D14PlusWindowSeg17Coeff : Nat -> Real
  | 0 => ((471718653241982104761 : Real) / (301958232385734088196 : Real))
  | 1 => ((-2335301317085499832545 : Real) / (150979116192867044098 : Real))
  | 2 => ((14689582587017178840549 : Real) / (75489558096433522049 : Real))
  | 3 => ((-128320695338255421448986 : Real) / (75489558096433522049 : Real))
  | 4 => ((768022684255676527066620 : Real) / (75489558096433522049 : Real))
  | 5 => ((-3462145409063362217870520 : Real) / (75489558096433522049 : Real))
  | 6 => ((12334960108246045255490736 : Real) / (75489558096433522049 : Real))
  | 7 => ((-35535582807762489624339552 : Real) / (75489558096433522049 : Real))
  | 8 => ((84011431605027814612745856 : Real) / (75489558096433522049 : Real))
  | 9 => ((-164814762064417597408953600 : Real) / (75489558096433522049 : Real))
  | 10 => ((270341723618922752443519488 : Real) / (75489558096433522049 : Real))
  | 11 => ((-372218810117693461896250368 : Real) / (75489558096433522049 : Real))
  | 12 => ((430551759971470322114721792 : Real) / (75489558096433522049 : Real))
  | 13 => ((-417750112401779752242278400 : Real) / (75489558096433522049 : Real))
  | 14 => ((338773470147623588431749120 : Real) / (75489558096433522049 : Real))
  | 15 => ((-228319339721809176637784064 : Real) / (75489558096433522049 : Real))
  | 16 => ((126840301675153608875655168 : Real) / (75489558096433522049 : Real))
  | 17 => ((-57410957458587680327761920 : Real) / (75489558096433522049 : Real))
  | 18 => ((20821699342107386444316672 : Real) / (75489558096433522049 : Real))
  | 19 => ((-5905020942893315164078080 : Real) / (75489558096433522049 : Real))
  | 20 => ((1261601646192121539723264 : Real) / (75489558096433522049 : Real))
  | 21 => ((-190997981980376770805760 : Real) / (75489558096433522049 : Real))
  | 22 => ((18269372189427343294464 : Real) / (75489558096433522049 : Real))
  | 23 => ((-830426008610333786112 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg17_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((5 : Real) / (6 : Real)) < x) (hxhi : x < ((1 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg17Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 18).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 18 := by simpa using hj
    have hj_le_nat : j <= 17 := by omega
    have hj_le_real : (j : Real) <= (17 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (17 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg17Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg17_expPolyIntegral :
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg17Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg17Coeff 24
    ((-3 : Real) / (20 : Real))
    ((5 : Real) / (6 : Real))
    ((1 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg17_centeredBSplineR_expIntegral :
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
  calc
    ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((5 : Real) / (6 : Real))..((1 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg17Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((1 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((5 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((1 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((1 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg17_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg17_expPolyIntegral

def p0PieceK11D14PlusWindowSeg18Coeff : Nat -> Real
  | 0 => ((-3957220059346464754503 : Real) / (301958232385734088196 : Real))
  | 1 => ((48597493877681639048991 : Real) / (150979116192867044098 : Real))
  | 2 => ((-265440790984202085007899 : Real) / (75489558096433522049 : Real))
  | 3 => ((1832591919660279425490150 : Real) / (75489558096433522049 : Real))
  | 4 => ((-9036540390736997707629060 : Real) / (75489558096433522049 : Real))
  | 5 => ((33795194275908799873973064 : Real) / (75489558096433522049 : Real))
  | 6 => ((-99437058946670441020040016 : Real) / (75489558096433522049 : Real))
  | 7 => ((235910749182748977044806560 : Real) / (75489558096433522049 : Real))
  | 8 => ((-458881232375995118725546368 : Real) / (75489558096433522049 : Real))
  | 9 => ((740006344570620624821533440 : Real) / (75489558096433522049 : Real))
  | 10 => ((-996407825670130758679162368 : Real) / (75489558096433522049 : Real))
  | 11 => ((1124848839042097051248737280 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1066515889188320191030265856 : Real) / (75489558096433522049 : Real))
  | 13 => ((848999436887273758880403456 : Real) / (75489558096433522049 : Real))
  | 14 => ((-566047636487414633798737920 : Real) / (75489558096433522049 : Real))
  | 15 => ((314573324259213756700508160 : Real) / (75489558096433522049 : Real))
  | 16 => ((-144606030315357857793490944 : Real) / (75489558096433522049 : Real))
  | 17 => ((54361061596328805947768832 : Real) / (75489558096433522049 : Real))
  | 18 => ((-16435640342864775647526912 : Real) / (75489558096433522049 : Real))
  | 19 => ((3899542132099359070617600 : Real) / (75489558096433522049 : Real))
  | 20 => ((-699310968806413307215872 : Real) / (75489558096433522049 : Real))
  | 21 => ((89132391590842493042688 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7197025407956226146304 : Real) / (75489558096433522049 : Real))
  | 23 => ((276808669536777928704 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg18_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((1 : Real)) < x) (hxhi : x < ((7 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg18Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 19).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 19 := by simpa using hj
    have hj_le_nat : j <= 18 := by omega
    have hj_le_real : (j : Real) <= (18 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (18 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg18Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg18_expPolyIntegral :
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg18Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg18Coeff 24
    ((-3 : Real) / (20 : Real))
    ((1 : Real))
    ((7 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg18_centeredBSplineR_expIntegral :
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((1 : Real))..((7 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg18Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((7 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((1 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((7 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((7 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg18_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg18_expPolyIntegral

def p0PieceK11D14PlusWindowSeg19Coeff : Nat -> Real
  | 0 => ((22256415739968419044475 : Real) / (150979116192867044098 : Real))
  | 1 => ((-214589364219055458775380 : Real) / (75489558096433522049 : Real))
  | 2 => ((1986932828504534253248070 : Real) / (75489558096433522049 : Real))
  | 3 => ((-11681649797272138604045664 : Real) / (75489558096433522049 : Real))
  | 4 => ((48881638396116222418953000 : Real) / (75489558096433522049 : Real))
  | 5 => ((-154852588058413117109751360 : Real) / (75489558096433522049 : Real))
  | 6 => ((385657238484443059795251360 : Real) / (75489558096433522049 : Real))
  | 7 => ((-773877380163650555264575488 : Real) / (75489558096433522049 : Real))
  | 8 => ((1272184132217832650947680000 : Real) / (75489558096433522049 : Real))
  | 9 => ((-1732944176277704760425932800 : Real) / (75489558096433522049 : Real))
  | 10 => ((1971132799347859703617797120 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1881231274612490689779351552 : Real) / (75489558096433522049 : Real))
  | 12 => ((1510124208229897872708096000 : Real) / (75489558096433522049 : Real))
  | 13 => ((-1019772501899565715918848000 : Real) / (75489558096433522049 : Real))
  | 14 => ((578098448484119738527334400 : Real) / (75489558096433522049 : Real))
  | 15 => ((-273844662297575349067186176 : Real) / (75489558096433522049 : Real))
  | 16 => ((107573106780408901821235200 : Real) / (75489558096433522049 : Real))
  | 17 => ((-34643339731588873916252160 : Real) / (75489558096433522049 : Real))
  | 18 => ((8994188607968847170764800 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1836509510945819008696320 : Real) / (75489558096433522049 : Real))
  | 20 => ((284012170001331506380800 : Real) / (75489558096433522049 : Real))
  | 21 => ((-31274523365207892295680 : Real) / (75489558096433522049 : Real))
  | 22 => ((2185331601606141542400 : Real) / (75489558096433522049 : Real))
  | 23 => ((-72844386720204718080 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg19_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((7 : Real) / (6 : Real)) < x) (hxhi : x < ((4 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg19Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
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
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 20).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 20 := by simpa using hj
    have hj_le_nat : j <= 19 := by omega
    have hj_le_real : (j : Real) <= (19 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (19 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg19Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg19_expPolyIntegral :
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg19Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg19Coeff 24
    ((-3 : Real) / (20 : Real))
    ((7 : Real) / (6 : Real))
    ((4 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg19_centeredBSplineR_expIntegral :
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((7 : Real) / (6 : Real))..((4 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg19Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((4 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((7 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((4 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((4 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg19_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg19_expPolyIntegral

def p0PieceK11D14PlusWindowSeg20Coeff : Nat -> Real
  | 0 => ((-108420319278190044603269 : Real) / (150979116192867044098 : Real))
  | 1 => ((912497475312561290186412 : Real) / (75489558096433522049 : Real))
  | 2 => ((-7311533597631303925686714 : Real) / (75489558096433522049 : Real))
  | 3 => ((37135298939941011835361952 : Real) / (75489558096433522049 : Real))
  | 4 => ((-134181919368433091728825560 : Real) / (75489558096433522049 : Real))
  | 5 => ((366878551570552428211417536 : Real) / (75489558096433522049 : Real))
  | 6 => ((-788237825680729417177378656 : Real) / (75489558096433522049 : Real))
  | 7 => ((1364288629565770742078429184 : Real) / (75489558096433522049 : Real))
  | 8 => ((-1935064882376299295066827008 : Real) / (75489558096433522049 : Real))
  | 9 => ((2276117091964960172092200960 : Real) / (75489558096433522049 : Real))
  | 10 => ((-2238381532306938475526243328 : Real) / (75489558096433522049 : Real))
  | 11 => ((1849929155717898605371047936 : Real) / (75489558096433522049 : Real))
  | 12 => ((-1288246114517894098654703616 : Real) / (75489558096433522049 : Real))
  | 13 => ((756116356767302265907544064 : Real) / (75489558096433522049 : Real))
  | 14 => ((-373270582944559537451089920 : Real) / (75489558096433522049 : Real))
  | 15 => ((154271401845330325123104768 : Real) / (75489558096433522049 : Real))
  | 16 => ((-52970417273180726000123904 : Real) / (75489558096433522049 : Real))
  | 17 => ((14936277990843217028579328 : Real) / (75489558096433522049 : Real))
  | 18 => ((-3400715822639175565443072 : Real) / (75489558096433522049 : Real))
  | 19 => ((609853205621553899765760 : Real) / (75489558096433522049 : Real))
  | 20 => ((-82942237483774429888512 : Real) / (75489558096433522049 : Real))
  | 21 => ((8042020293910600876032 : Real) / (75489558096433522049 : Real))
  | 22 => ((-495341829697392082944 : Real) / (75489558096433522049 : Real))
  | 23 => ((14568877344040943616 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg20_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((4 : Real) / (3 : Real)) < x) (hxhi : x < ((3 : Real) / (2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg20Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 21 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (21 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 21).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 21 := by simpa using hj
    have hj_le_nat : j <= 20 := by omega
    have hj_le_real : (j : Real) <= (20 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (20 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg20Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg20_expPolyIntegral :
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg20Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg20Coeff 24
    ((-3 : Real) / (20 : Real))
    ((4 : Real) / (3 : Real))
    ((3 : Real) / (2 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg20_centeredBSplineR_expIntegral :
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
  calc
    ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((4 : Real) / (3 : Real))..((3 : Real) / (2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg20Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((3 : Real) / (2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((4 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((3 : Real) / (2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((3 : Real) / (2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg20_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg20_expPolyIntegral

def p0PieceK11D14PlusWindowSeg21Coeff : Nat -> Real
  | 0 => ((530600476200980836550141 : Real) / (301958232385734088196 : Real))
  | 1 => ((-3905386929181311183761715 : Real) / (150979116192867044098 : Real))
  | 2 => ((13699866628325619876139929 : Real) / (75489558096433522049 : Real))
  | 3 => ((-60917902114524632573162382 : Real) / (75489558096433522049 : Real))
  | 4 => ((192662084146452389632922220 : Real) / (75489558096433522049 : Real))
  | 5 => ((-461126257333824124571676840 : Real) / (75489558096433522049 : Real))
  | 6 => ((867771792128023688388810096 : Real) / (75489558096433522049 : Real))
  | 7 => ((-1316869799267448571695400224 : Real) / (75489558096433522049 : Real))
  | 8 => ((1639813022734659789964945536 : Real) / (75489558096433522049 : Real))
  | 9 => ((-1695969469269438811276435200 : Real) / (75489558096433522049 : Real))
  | 10 => ((1468899258178500575617817088 : Real) / (75489558096433522049 : Real))
  | 11 => ((-1070958739816083677348514816 : Real) / (75489558096433522049 : Real))
  | 12 => ((659012482504760756491671552 : Real) / (75489558096433522049 : Real))
  | 13 => ((-342337210783938934431436800 : Real) / (75489558096433522049 : Real))
  | 14 => ((149802544460793415091281920 : Real) / (75489558096433522049 : Real))
  | 15 => ((-54957849116810855893843968 : Real) / (75489558096433522049 : Real))
  | 16 => ((16772666380866334338859008 : Real) / (75489558096433522049 : Real))
  | 17 => ((-4208882227914799535063040 : Real) / (75489558096433522049 : Real))
  | 18 => ((853764225973717004255232 : Real) / (75489558096433522049 : Real))
  | 19 => ((-136546802907023744040960 : Real) / (75489558096433522049 : Real))
  | 20 => ((16577763653369255952384 : Real) / (75489558096433522049 : Real))
  | 21 => ((-1436075052484035870720 : Real) / (75489558096433522049 : Real))
  | 22 => ((79088191296222265344 : Real) / (75489558096433522049 : Real))
  | 23 => ((-2081268192005849088 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg21_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((3 : Real) / (2 : Real)) < x) (hxhi : x < ((5 : Real) / (3 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg21Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 22 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (22 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 22).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 22 := by simpa using hj
    have hj_le_nat : j <= 21 := by omega
    have hj_le_real : (j : Real) <= (21 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (21 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg21Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg21_expPolyIntegral :
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg21Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg21Coeff 24
    ((-3 : Real) / (20 : Real))
    ((3 : Real) / (2 : Real))
    ((5 : Real) / (3 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg21_centeredBSplineR_expIntegral :
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
  calc
    ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((3 : Real) / (2 : Real))..((5 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg21Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((5 : Real) / (3 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((3 : Real) / (2 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((5 : Real) / (3 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((5 : Real) / (3 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg21_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg21_expPolyIntegral

def p0PieceK11D14PlusWindowSeg22Coeff : Nat -> Real
  | 0 => ((-619399523799019163449859 : Real) / (301958232385734088196 : Real))
  | 1 => ((4029613070818688816238285 : Real) / (150979116192867044098 : Real))
  | 2 => ((-12485633371674380123860071 : Real) / (75489558096433522049 : Real))
  | 3 => ((49061197885475367426837618 : Real) / (75489558096433522049 : Real))
  | 4 => ((-137275215853547610367077780 : Real) / (75489558096433522049 : Real))
  | 5 => ((291130786666175875428323160 : Real) / (75489558096433522049 : Real))
  | 6 => ((-486290887071976311611189904 : Real) / (75489558096433522049 : Real))
  | 7 => ((656192961852551428304599776 : Real) / (75489558096433522049 : Real))
  | 8 => ((-727862290609340210035054464 : Real) / (75489558096433522049 : Real))
  | 9 => ((671705844074561188723564800 : Real) / (75489558096433522049 : Real))
  | 10 => ((-519948005030459424382182912 : Real) / (75489558096433522049 : Real))
  | 11 => ((339314774095724322651485184 : Real) / (75489558096433522049 : Real))
  | 12 => ((-187151625842324043508328448 : Real) / (75489558096433522049 : Real))
  | 13 => ((87253798069196425568563200 : Real) / (75489558096433522049 : Real))
  | 14 => ((-34307887904836024908718080 : Real) / (75489558096433522049 : Real))
  | 15 => ((11321906534815742506156032 : Real) / (75489558096433522049 : Real))
  | 16 => ((-3111260314621645181140992 : Real) / (75489558096433522049 : Real))
  | 17 => ((703617308617524816936960 : Real) / (75489558096433522049 : Real))
  | 18 => ((-128735681332747866144768 : Real) / (75489558096433522049 : Real))
  | 19 => ((18584761404523340759040 : Real) / (75489558096433522049 : Real))
  | 20 => ((-2038024064016394223616 : Real) / (75489558096433522049 : Real))
  | 21 => ((159563894720448430080 : Real) / (75489558096433522049 : Real))
  | 22 => ((-7946660369476878336 : Real) / (75489558096433522049 : Real))
  | 23 => ((189206199273259008 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg22_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((5 : Real) / (3 : Real)) < x) (hxhi : x < ((11 : Real) / (6 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg22Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 23 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (23 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 23).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 23 := by simpa using hj
    have hj_le_nat : j <= 22 := by omega
    have hj_le_real : (j : Real) <= (22 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (22 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg22Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg22_expPolyIntegral :
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg22Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg22Coeff 24
    ((-3 : Real) / (20 : Real))
    ((5 : Real) / (3 : Real))
    ((11 : Real) / (6 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg22_centeredBSplineR_expIntegral :
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
  calc
    ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((5 : Real) / (3 : Real))..((11 : Real) / (6 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg22Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((11 : Real) / (6 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((5 : Real) / (3 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((11 : Real) / (6 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((11 : Real) / (6 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg22_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg22_expPolyIntegral

def p0PieceK11D14PlusWindowSeg23Coeff : Nat -> Real
  | 0 => ((69007679864054552199168 : Real) / (75489558096433522049 : Real))
  | 1 => ((-793588318436627350290432 : Real) / (75489558096433522049 : Real))
  | 2 => ((4364735751401450426597376 : Real) / (75489558096433522049 : Real))
  | 3 => ((-15276575129905076493090816 : Real) / (75489558096433522049 : Real))
  | 4 => ((38191437824762691232727040 : Real) / (75489558096433522049 : Real))
  | 5 => ((-72563731867049113342181376 : Real) / (75489558096433522049 : Real))
  | 6 => ((108845597800573670013272064 : Real) / (75489558096433522049 : Real))
  | 7 => ((-132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 8 => ((132169654472125170730401792 : Real) / (75489558096433522049 : Real))
  | 9 => ((-110141378726770975608668160 : Real) / (75489558096433522049 : Real))
  | 10 => ((77098965108739682926067712 : Real) / (75489558096433522049 : Real))
  | 11 => ((-45558479382437085365403648 : Real) / (75489558096433522049 : Real))
  | 12 => ((22779239691218542682701824 : Real) / (75489558096433522049 : Real))
  | 13 => ((-9637370638592460365758464 : Real) / (75489558096433522049 : Real))
  | 14 => ((3441918085211592987770880 : Real) / (75489558096433522049 : Real))
  | 15 => ((-1032575425563477896331264 : Real) / (75489558096433522049 : Real))
  | 16 => ((258143856390869474082816 : Real) / (75489558096433522049 : Real))
  | 17 => ((-53147264551061362311168 : Real) / (75489558096433522049 : Real))
  | 18 => ((8857877425176893718528 : Real) / (75489558096433522049 : Real))
  | 19 => ((-1165510187523275489280 : Real) / (75489558096433522049 : Real))
  | 20 => ((116551018752327548928 : Real) / (75489558096433522049 : Real))
  | 21 => ((-8325072768023396352 : Real) / (75489558096433522049 : Real))
  | 22 => ((378412398546518016 : Real) / (75489558096433522049 : Real))
  | 23 => ((-8226356490141696 : Real) / (75489558096433522049 : Real))
  | _ => 0

theorem p0PieceK11D14PlusWindowSeg23_centeredBSplineR_eq_expPoly
    (x : Real) (hxlo : ((11 : Real) / (6 : Real)) < x) (hxhi : x < ((2 : Real))) :
    centeredBSplineR 11 x = expPoly p0PieceK11D14PlusWindowSeg23Coeff 24 x := by
  have hsum :
      (Finset.range 25).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) := by
    symm
    refine Finset.sum_subset ?subset ?zero_tail
    · intro j hj
      simp at hj ⊢
      omega
    · intro j hjRange hjNotActive
      have hj_ge : 24 <= j := by
        simp at hjNotActive
        omega
      have hj_ge_real : (24 : Real) <= (j : Real) := by
        exact_mod_cast hj_ge
      have hnon : ¬ (0 : Real) <
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
        intro hpos
        have hscale :
            bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
              ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
          norm_num [bsplineScale]
        rw [hscale] at hpos
        linarith
      rw [positivePartPower_of_nonpos 23 hnon]
      ring
  have hactive :
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          positivePartPower 23
            (bsplineScale 11 * x + ((12 : Real)) - (j : Real))) =
      (Finset.range 24).sum (fun j =>
        ((-1 : Real) ^ j) * (Nat.choose 24 j : Real) *
          (bsplineScale 11 * x + ((12 : Real)) - (j : Real)) ^ 23) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < 24 := by simpa using hj
    have hj_le_nat : j <= 23 := by omega
    have hj_le_real : (j : Real) <= (23 : Real) := by
      exact_mod_cast hj_le_nat
    have hpos : (0 : Real) <
        bsplineScale 11 * x + ((12 : Real)) - (j : Real) := by
      have hscale :
          bsplineScale 11 * x + ((12 : Real)) - (j : Real) =
            ((6 : Real)) * x + ((12 : Real)) - (j : Real) := by
        norm_num [bsplineScale]
      rw [hscale]
      have hy_gt : (23 : Real) < ((6 : Real)) * x + ((12 : Real)) := by
        linarith
      linarith
    rw [positivePartPower_of_pos 23 hpos]
  unfold centeredBSplineR centeredCardinalBSpline expPoly p0PieceK11D14PlusWindowSeg23Coeff
  norm_num [bsplineAutocorrDegree]
  rw [hsum, hactive, bsplineAutocorrNorm_11_exact]
  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]
  ring

theorem p0PieceK11D14PlusWindowSeg23_expPolyIntegral :
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) *
        expPoly p0PieceK11D14PlusWindowSeg23Coeff 24 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
  exact intervalIntegral_exp_mul_poly_eq_sum
    p0PieceK11D14PlusWindowSeg23Coeff 24
    ((-3 : Real) / (20 : Real))
    ((11 : Real) / (6 : Real))
    ((2 : Real))
    (by norm_num)

theorem p0PieceK11D14PlusWindowSeg23_centeredBSplineR_expIntegral :
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      expPolyIntegral p0PieceK11D14PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
  calc
    ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((11 : Real) / (6 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) *
            expPoly p0PieceK11D14PlusWindowSeg23Coeff 24 x := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
            (MeasureTheory.measure_singleton ((2 : Real)))] with x hxne hxmem
          norm_num [Set.uIoc] at hxmem
          have hxlo :
              ((11 : Real) / (6 : Real)) < x := by
            linarith [hxmem.1]
          have hxle_hi :
              x <= ((2 : Real)) := by
            linarith [hxmem.2]
          have hxhi :
              x < ((2 : Real)) := by
            exact lt_of_le_of_ne hxle_hi
              (by simpa [Set.mem_singleton_iff] using hxne)
          rw [p0PieceK11D14PlusWindowSeg23_centeredBSplineR_eq_expPoly x hxlo hxhi]
    _ = expPolyIntegral p0PieceK11D14PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real)) := by
        exact p0PieceK11D14PlusWindowSeg23_expPolyIntegral

def p0PieceK11D14PlusWindowBreak : Nat -> Real
  | 0 => ((-2 : Real))
  | 1 => ((-11 : Real) / (6 : Real))
  | 2 => ((-5 : Real) / (3 : Real))
  | 3 => ((-3 : Real) / (2 : Real))
  | 4 => ((-4 : Real) / (3 : Real))
  | 5 => ((-7 : Real) / (6 : Real))
  | 6 => ((-1 : Real))
  | 7 => ((-5 : Real) / (6 : Real))
  | 8 => ((-2 : Real) / (3 : Real))
  | 9 => ((-1 : Real) / (2 : Real))
  | 10 => ((-1 : Real) / (3 : Real))
  | 11 => ((-1 : Real) / (6 : Real))
  | 12 => ((0 : Real))
  | 13 => ((1 : Real) / (6 : Real))
  | 14 => ((1 : Real) / (3 : Real))
  | 15 => ((1 : Real) / (2 : Real))
  | 16 => ((2 : Real) / (3 : Real))
  | 17 => ((5 : Real) / (6 : Real))
  | 18 => ((1 : Real))
  | 19 => ((7 : Real) / (6 : Real))
  | 20 => ((4 : Real) / (3 : Real))
  | 21 => ((3 : Real) / (2 : Real))
  | 22 => ((5 : Real) / (3 : Real))
  | 23 => ((11 : Real) / (6 : Real))
  | 24 => ((2 : Real))
  | _ => ((2 : Real))

def p0PieceK11D14PlusWindowSegmentExpIntegral : Nat -> Real
  | 0 => expPolyIntegral p0PieceK11D14PlusWindowSeg0Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real))
        ((-11 : Real) / (6 : Real))
  | 1 => expPolyIntegral p0PieceK11D14PlusWindowSeg1Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-11 : Real) / (6 : Real))
        ((-5 : Real) / (3 : Real))
  | 2 => expPolyIntegral p0PieceK11D14PlusWindowSeg2Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (3 : Real))
        ((-3 : Real) / (2 : Real))
  | 3 => expPolyIntegral p0PieceK11D14PlusWindowSeg3Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-3 : Real) / (2 : Real))
        ((-4 : Real) / (3 : Real))
  | 4 => expPolyIntegral p0PieceK11D14PlusWindowSeg4Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-4 : Real) / (3 : Real))
        ((-7 : Real) / (6 : Real))
  | 5 => expPolyIntegral p0PieceK11D14PlusWindowSeg5Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-7 : Real) / (6 : Real))
        ((-1 : Real))
  | 6 => expPolyIntegral p0PieceK11D14PlusWindowSeg6Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real))
        ((-5 : Real) / (6 : Real))
  | 7 => expPolyIntegral p0PieceK11D14PlusWindowSeg7Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-5 : Real) / (6 : Real))
        ((-2 : Real) / (3 : Real))
  | 8 => expPolyIntegral p0PieceK11D14PlusWindowSeg8Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-2 : Real) / (3 : Real))
        ((-1 : Real) / (2 : Real))
  | 9 => expPolyIntegral p0PieceK11D14PlusWindowSeg9Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (2 : Real))
        ((-1 : Real) / (3 : Real))
  | 10 => expPolyIntegral p0PieceK11D14PlusWindowSeg10Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (3 : Real))
        ((-1 : Real) / (6 : Real))
  | 11 => expPolyIntegral p0PieceK11D14PlusWindowSeg11Coeff 24
        ((-3 : Real) / (20 : Real))
        ((-1 : Real) / (6 : Real))
        ((0 : Real))
  | 12 => expPolyIntegral p0PieceK11D14PlusWindowSeg12Coeff 24
        ((-3 : Real) / (20 : Real))
        ((0 : Real))
        ((1 : Real) / (6 : Real))
  | 13 => expPolyIntegral p0PieceK11D14PlusWindowSeg13Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (6 : Real))
        ((1 : Real) / (3 : Real))
  | 14 => expPolyIntegral p0PieceK11D14PlusWindowSeg14Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (3 : Real))
        ((1 : Real) / (2 : Real))
  | 15 => expPolyIntegral p0PieceK11D14PlusWindowSeg15Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real) / (2 : Real))
        ((2 : Real) / (3 : Real))
  | 16 => expPolyIntegral p0PieceK11D14PlusWindowSeg16Coeff 24
        ((-3 : Real) / (20 : Real))
        ((2 : Real) / (3 : Real))
        ((5 : Real) / (6 : Real))
  | 17 => expPolyIntegral p0PieceK11D14PlusWindowSeg17Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (6 : Real))
        ((1 : Real))
  | 18 => expPolyIntegral p0PieceK11D14PlusWindowSeg18Coeff 24
        ((-3 : Real) / (20 : Real))
        ((1 : Real))
        ((7 : Real) / (6 : Real))
  | 19 => expPolyIntegral p0PieceK11D14PlusWindowSeg19Coeff 24
        ((-3 : Real) / (20 : Real))
        ((7 : Real) / (6 : Real))
        ((4 : Real) / (3 : Real))
  | 20 => expPolyIntegral p0PieceK11D14PlusWindowSeg20Coeff 24
        ((-3 : Real) / (20 : Real))
        ((4 : Real) / (3 : Real))
        ((3 : Real) / (2 : Real))
  | 21 => expPolyIntegral p0PieceK11D14PlusWindowSeg21Coeff 24
        ((-3 : Real) / (20 : Real))
        ((3 : Real) / (2 : Real))
        ((5 : Real) / (3 : Real))
  | 22 => expPolyIntegral p0PieceK11D14PlusWindowSeg22Coeff 24
        ((-3 : Real) / (20 : Real))
        ((5 : Real) / (3 : Real))
        ((11 : Real) / (6 : Real))
  | 23 => expPolyIntegral p0PieceK11D14PlusWindowSeg23Coeff 24
        ((-3 : Real) / (20 : Real))
        ((11 : Real) / (6 : Real))
        ((2 : Real))
  | _ => 0

def p0PieceK11D14PlusWindowExpPolyIntegralSum : Real :=
  (Finset.range 24).sum p0PieceK11D14PlusWindowSegmentExpIntegral

theorem p0PieceK11D14PlusWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D14PlusWindowExpPolyIntegralSum := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (a := p0PieceK11D14PlusWindowBreak) (n := 24)
    (μ := volume) ?hint
  calc
    ∫ x in ((-2 : Real))..((2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        (Finset.range 24).sum (fun i =>
          ∫ x in p0PieceK11D14PlusWindowBreak i..p0PieceK11D14PlusWindowBreak (i + 1),
            Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
          simpa [p0PieceK11D14PlusWindowBreak] using hsplit.symm
    _ = (Finset.range 24).sum p0PieceK11D14PlusWindowSegmentExpIntegral := by
        apply Finset.sum_congr rfl
        intro i hi
        simp at hi
        interval_cases i <;>
          simp [p0PieceK11D14PlusWindowBreak, p0PieceK11D14PlusWindowSegmentExpIntegral]
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg0_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg1_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg2_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg3_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg4_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg5_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg6_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg7_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg8_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg9_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg10_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg11_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg12_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg13_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg14_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg15_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg16_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg17_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg18_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg19_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg20_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg21_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg22_centeredBSplineR_expIntegral
        · simpa [mul_assoc] using p0PieceK11D14PlusWindowSeg23_centeredBSplineR_expIntegral
    _ = p0PieceK11D14PlusWindowExpPolyIntegralSum := by
        rfl
  · intro k hk
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _

def p0PieceK11D14MinusWindowExpPolyIntegralSum : Real := 0

theorem p0PieceK11D14PlusWindow_leftSupportZeroIntegral :
    ∫ x in ((-25 : Real) / (3 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((-25 : Real) / (3 : Real))..((-2 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((-25 : Real) / (3 : Real))..((-2 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D14PlusWindow_rightSupportZeroIntegral :
    ∫ x in ((2 : Real))..((35 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((2 : Real))..((35 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((2 : Real))..((35 : Real) / (3 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D14PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D14PlusWindowExpPolyIntegralSum := by
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-25 : Real) / (3 : Real))) (b := ((-2 : Real))) (c := ((35 : Real) / (3 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (a := ((-2 : Real))) (b := ((2 : Real))) (c := ((35 : Real) / (3 : Real)))
    (f := fun x : Real => Real.exp (((-3 : Real) / (20 : Real)) * x) *
      centeredBSplineR 11 x)
    (μ := volume)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
    (((Real.continuous_exp.comp (by continuity)).mul
      (centeredBSplineR_continuous 11)).intervalIntegrable _ _)
  calc
    ∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
      Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        (∫ x in ((-25 : Real) / (3 : Real))..((-2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) +
        (∫ x in ((-2 : Real))..((35 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
        simpa using hsplitLeft.symm
    _ = ∫ x in ((-2 : Real))..((35 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
        rw [p0PieceK11D14PlusWindow_leftSupportZeroIntegral]
        ring
    _ = (∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) +
        (∫ x in ((2 : Real))..((35 : Real) / (3 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x) := by
        simpa using hsplitRight.symm
    _ = ∫ x in ((-2 : Real))..((2 : Real)),
          Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
        rw [p0PieceK11D14PlusWindow_rightSupportZeroIntegral]
        ring
    _ = p0PieceK11D14PlusWindowExpPolyIntegralSum := by
        exact p0PieceK11D14PlusWindow_centeredBSplineR_expIntegral_sum

theorem p0PieceK11D14MinusWindow_rightSupportZeroIntegral :
    ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = 0 := by
  calc
    ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
        ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro x hx
          norm_num [Set.uIcc] at hx
          have hzero := CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
            (x := x) (by linarith)
          change Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x = (0 : Real)
          rw [hzero]
          ring
    _ = 0 := by simp

theorem p0PieceK11D14MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum :
    ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
      Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x =
      p0PieceK11D14MinusWindowExpPolyIntegralSum := by
  simpa [p0PieceK11D14MinusWindowExpPolyIntegralSum] using
    p0PieceK11D14MinusWindow_rightSupportZeroIntegral

theorem p0PieceK11D14_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (2 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((7 : Real) / (2 : Real)) / 2) *
        p0PieceK11D14PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((7 : Real) / (2 : Real)) / 2)) *
        p0PieceK11D14MinusWindowExpPolyIntegralSum := by
  have hprofile :=
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile_eq_transformed_integrals
      (k := 11)
      (ell := ((3 : Real) / (10 : Real)))
      (L := ((3 : Real)))
      (d := ((7 : Real) / (2 : Real)))
      (by norm_num)
  calc
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (2 : Real)) =
      ((3 : Real) / (10 : Real)) * Real.exp (((7 : Real) / (2 : Real)) / 2) *
        (∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
          Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x) +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((7 : Real) / (2 : Real)) / 2)) *
        (∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
          Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x) := by
        norm_num at hprofile ⊢
        simpa [mul_assoc] using hprofile
    _ = ((3 : Real) / (10 : Real)) * Real.exp (((7 : Real) / (2 : Real)) / 2) *
        p0PieceK11D14PlusWindowExpPolyIntegralSum +
      ((3 : Real) / (10 : Real)) * Real.exp (-(((7 : Real) / (2 : Real)) / 2)) *
        p0PieceK11D14MinusWindowExpPolyIntegralSum := by
        have hplus :
            ∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
            p0PieceK11D14PlusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
              Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                ∫ x in ((-25 : Real) / (3 : Real))..((35 : Real) / (3 : Real)),
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp (-(((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                  Real.exp (((-3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x
                have harg : -(((3 : Real) / (10 : Real)) / 2) * x = ((-3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK11D14PlusWindowExpPolyIntegralSum := by
                exact p0PieceK11D14PlusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        have hminus :
            ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
            p0PieceK11D14MinusWindowExpPolyIntegralSum := by
          calc
            ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
              Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                ∫ x in ((35 : Real) / (3 : Real))..((95 : Real) / (3 : Real)),
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x := by
                apply intervalIntegral.integral_congr
                intro x hx
                change Real.exp ((((3 : Real) / (10 : Real)) / 2) * x) * centeredBSplineR 11 x =
                  Real.exp (((3 : Real) / (20 : Real)) * x) * centeredBSplineR 11 x
                have harg : (((3 : Real) / (10 : Real)) / 2) * x = ((3 : Real) / (20 : Real)) * x := by
                  ring
                rw [harg]
            _ = p0PieceK11D14MinusWindowExpPolyIntegralSum := by
                exact p0PieceK11D14MinusWindow_fullWindow_centeredBSplineR_expIntegral_sum
        rw [hplus, hminus]

end PSDpd
end Q3
