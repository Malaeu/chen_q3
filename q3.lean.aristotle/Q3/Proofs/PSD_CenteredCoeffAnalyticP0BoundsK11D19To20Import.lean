import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ProfileImport
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ExpHboxImport
import Q3.Proofs.PSD_CenteredCoeffBaseP0HboxImport

set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd

open CenteredCoeffPayloadImport

private theorem p0PieceK11D19PlusWindowSeg0_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-186522656023456636671403063539741048238712840200683484074521 : Real) / (3623498788628809058352 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((107 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg0Coeff 24 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-11 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-186522656023456636671403063539741048238712840200683484074521 : Real) / (3623498788628809058352 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((107 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg1_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((535662405627716531951446354022947566548453897926536369239627 : Real) / (452937348578601132294 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-4179494829677226087784758495905762951761287159799316515925479 : Real) / (3623498788628809058352 : Real)) * Real.exp ((53 : Real) / (20 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg1Coeff 24 ((-3 : Real) / (20 : Real)) ((-11 : Real) / (6 : Real)) ((-5 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((535662405627716531951446354022947566548453897926536369239627 : Real) / (452937348578601132294 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-4179494829677226087784758495905762951761287159799316515925479 : Real) / (3623498788628809058352 : Real)) * Real.exp ((53 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg2_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-15695490316860443465337283762121288028161572486312960607627997 : Real) / (1207832929542936352784 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((5740487730067014884454285887679964433451546102073463630760373 : Real) / (452937348578601132294 : Real)) * Real.exp ((21 : Real) / (8 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg2Coeff 24 ((-3 : Real) / (20 : Real)) ((-5 : Real) / (3 : Real)) ((-3 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-15695490316860443465337283762121288028161572486312960607627997 : Real) / (1207832929542936352784 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((5740487730067014884454285887679964433451546102073463630760373 : Real) / (452937348578601132294 : Real)) * Real.exp ((21 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg3_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((20577711572106932400371286239050049797501016049235869580660175 : Real) / (226468674289300566147 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((-107038112336725415344374813408957879971838427513687039392372003 : Real) / (1207832929542936352784 : Real)) * Real.exp ((13 : Real) / (5 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg3Coeff 24 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (2 : Real)) ((-4 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((20577711572106932400371286239050049797501016049235869580660175 : Real) / (226468674289300566147 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((-107038112336725415344374813408957879971838427513687039392372003 : Real) / (1207832929542936352784 : Real)) * Real.exp ((13 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg4_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-1644411521774502165742564001111537323269894728909637094724161075 : Real) / (3623498788628809058352 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((100238178540016647365439059413731006202498983950764130419339825 : Real) / (226468674289300566147 : Real)) * Real.exp ((103 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg4Coeff 24 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (3 : Real)) ((-7 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1644411521774502165742564001111537323269894728909637094724161075 : Real) / (3623498788628809058352 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((100238178540016647365439059413731006202498983950764130419339825 : Real) / (226468674289300566147 : Real)) * Real.exp ((103 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg5_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((260079957249209073171289017031217379600247356443469755530018581 : Real) / (150979116192867044098 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((-6087805445401406939269298120666450260730105271090362905275838925 : Real) / (3623498788628809058352 : Real)) * Real.exp ((51 : Real) / (20 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg5Coeff 24 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (6 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((260079957249209073171289017031217379600247356443469755530018581 : Real) / (150979116192867044098 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((-6087805445401406939269298120666450260730105271090362905275838925 : Real) / (3623498788628809058352 : Real)) * Real.exp ((51 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg6_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-6235089835007367679988047862465632762075371420380910086958879263 : Real) / (1207832929542936352784 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((760143114808723378184442790703378204399752643556530244469981419 : Real) / (150979116192867044098 : Real)) * Real.exp ((101 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg6Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-5 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-6235089835007367679988047862465632762075371420380910086958879263 : Real) / (1207832929542936352784 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((760143114808723378184442790703378204399752643556530244469981419 : Real) / (150979116192867044098 : Real)) * Real.exp ((101 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg7_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((945363368403307808257445905378866124810213516725634317883835548 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((-14752356218755814176472720753788904965924628579619089913041120737 : Real) / (1207832929542936352784 : Real)) * Real.exp ((5 : Real) / (2 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg7Coeff 24 ((-3 : Real) / (20 : Real)) ((-5 : Real) / (6 : Real)) ((-2 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((945363368403307808257445905378866124810213516725634317883835548 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((-14752356218755814176472720753788904965924628579619089913041120737 : Real) / (1207832929542936352784 : Real)) * Real.exp ((5 : Real) / (2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg8_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-15109304543260738785172494422907972219480819907137646615267815975 : Real) / (603916464771468176392 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((1842031810612114782053749926467439667189786483274365682116164452 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg8Coeff 24 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (3 : Real)) ((-1 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-15109304543260738785172494422907972219480819907137646615267815975 : Real) / (603916464771468176392 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((1842031810612114782053749926467439667189786483274365682116164452 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg9_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((9433020524275721150694946089264003746817064777229720625738512275 : Real) / (226468674289300566147 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((-24533649113847493610364512963350599044519180092862353384732184025 : Real) / (603916464771468176392 : Real)) * Real.exp ((49 : Real) / (20 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg9Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (2 : Real)) ((-1 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9433020524275721150694946089264003746817064777229720625738512275 : Real) / (226468674289300566147 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((-24533649113847493610364512963350599044519180092862353384732184025 : Real) / (603916464771468176392 : Real)) * Real.exp ((49 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg10_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-105534790524912859007010872931460937104219812896959386418793565403 : Real) / (1811749394314404529176 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((12866140907847659571794620565506442589182935222770279374261487725 : Real) / (226468674289300566147 : Real)) * Real.exp ((97 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg10Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (3 : Real)) ((-1 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-105534790524912859007010872931460937104219812896959386418793565403 : Real) / (1811749394314404529176 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((12866140907847659571794620565506442589182935222770279374261487725 : Real) / (226468674289300566147 : Real)) * Real.exp ((97 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg11_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((5191136995080674690635711715760295914967324652875278297471970302 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-121511216783979744712882896644383607407780187103040613581206434597 : Real) / (1811749394314404529176 : Real)) * Real.exp ((12 : Real) / (5 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg11Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (6 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((5191136995080674690635711715760295914967324652875278297471970302 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-121511216783979744712882896644383607407780187103040613581206434597 : Real) / (1811749394314404529176 : Real)) * Real.exp ((12 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg12_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-124451949620404082327611832449133264371068013330062445677798970283 : Real) / (1811749394314404529176 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((5057467501501283116165048716482686997032675347124721702528029698 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg12Coeff 24 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-124451949620404082327611832449133264371068013330062445677798970283 : Real) / (1811749394314404529176 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((5057467501501283116165048716482686997032675347124721702528029698 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg13_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((13148904827995351707997270841017806164808446834658996376142804675 : Real) / (226468674289300566147 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-102594057688488521392281937126711280140931986669937554322201029717 : Real) / (1811749394314404529176 : Real)) * Real.exp ((47 : Real) / (20 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg13Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (6 : Real)) ((1 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((13148904827995351707997270841017806164808446834658996376142804675 : Real) / (226468674289300566147 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-102594057688488521392281937126711280140931986669937554322201029717 : Real) / (1811749394314404529176 : Real)) * Real.exp ((47 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg14_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-25018390541042616072445114389542408647206962586362641716392239575 : Real) / (603916464771468176392 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((9150256604128029014492295813752640171191553165341003623857195325 : Real) / (226468674289300566147 : Real)) * Real.exp ((93 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg14Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (3 : Real)) ((1 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-25018390541042616072445114389542408647206962586362641716392239575 : Real) / (603916464771468176392 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((9150256604128029014492295813752640171191553165341003623857195325 : Real) / (226468674289300566147 : Real)) * Real.exp ((93 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg15_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((1874348211745741751070720114736518559003467507899604101915242268 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((-14624563116065616323091892996716162616793037413637358283607760425 : Real) / (603916464771468176392 : Real)) * Real.exp ((23 : Real) / (10 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg15Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (2 : Real)) ((2 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((1874348211745741751070720114736518559003467507899604101915242268 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((-14624563116065616323091892996716162616793037413637358283607760425 : Real) / (603916464771468176392 : Real)) * Real.exp ((23 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg16_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-14978573780649232713237932857481467616118616825434374694137182063 : Real) / (1207832929542936352784 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((913046967269680839240475717109787232996532492100395898084757732 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg16Coeff 24 ((-3 : Real) / (20 : Real)) ((2 : Real) / (3 : Real)) ((5 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-14978573780649232713237932857481467616118616825434374694137182063 : Real) / (1207832929542936352784 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((913046967269680839240475717109787232996532492100395898084757732 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg17_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((770123449865465932428609042160840952632851437673925373043502341 : Real) / (150979116192867044098 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((-6008872273113949143222835758773070111881383174565625305862817937 : Real) / (1207832929542936352784 : Real)) * Real.exp ((9 : Real) / (4 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg17Coeff 24 ((-3 : Real) / (20 : Real)) ((5 : Real) / (6 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((770123449865465932428609042160840952632851437673925373043502341 : Real) / (150979116192867044098 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((-6008872273113949143222835758773070111881383174565625305862817937 : Real) / (1207832929542936352784 : Real)) * Real.exp ((9 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg18_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-6154342182513190244883634231953482229838017369475417918115307875 : Real) / (3623498788628809058352 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((250099622192466518927122765573754631367148562326074626956497659 : Real) / (150979116192867044098 : Real)) * Real.exp ((89 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg18Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((7 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-6154342182513190244883634231953482229838017369475417918115307875 : Real) / (3623498788628809058352 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((250099622192466518927122765573754631367148562326074626956497659 : Real) / (150979116192867044098 : Real)) * Real.exp ((89 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg19_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((101113679688057049478399307747353281906234273042937337555055375 : Real) / (226468674289300566147 : Real)) * Real.exp ((87 : Real) / (40 : Real)) +
      ((-1577874784662718860128227889824505354161982630524582081884692125 : Real) / (3623498788628809058352 : Real)) * Real.exp ((11 : Real) / (5 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg19Coeff 24 ((-3 : Real) / (20 : Real)) ((7 : Real) / (6 : Real)) ((4 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((101113679688057049478399307747353281906234273042937337555055375 : Real) / (226468674289300566147 : Real)) * Real.exp ((87 : Real) / (40 : Real)) +
      ((-1577874784662718860128227889824505354161982630524582081884692125 : Real) / (3623498788628809058352 : Real)) * Real.exp ((11 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg20_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 20 * ((3 : Real) / (10 : Real)) =
      ((-107738529362930308059243276720422077352298768981955163927992077 : Real) / (1207832929542936352784 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((19702210424066530287411037905427774093765726957062662444944625 : Real) / (226468674289300566147 : Real)) * Real.exp ((87 : Real) / (40 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg20Coeff 24 ((-3 : Real) / (20 : Real)) ((4 : Real) / (3 : Real)) ((3 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-107738529362930308059243276720422077352298768981955163927992077 : Real) / (1207832929542936352784 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((19702210424066530287411037905427774093765726957062662444944625 : Real) / (226468674289300566147 : Real)) * Real.exp ((87 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg20Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg21_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 21 * ((3 : Real) / (10 : Real)) =
      ((5765503266855427424281303894940232773817605135882256910756027 : Real) / (452937348578601132294 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-14995073290655550750468820450657090647701231018044836072007923 : Real) / (1207832929542936352784 : Real)) * Real.exp ((43 : Real) / (20 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg21Coeff 24 ((-3 : Real) / (20 : Real)) ((3 : Real) / (2 : Real)) ((5 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((5765503266855427424281303894940232773817605135882256910756027 : Real) / (452937348578601132294 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-14995073290655550750468820450657090647701231018044836072007923 : Real) / (1207832929542936352784 : Real)) * Real.exp ((43 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg21Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg22_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 22 * ((3 : Real) / (10 : Real)) =
      ((-4188591646955145430582359681984271491704330702429493899944681 : Real) / (3623498788628809058352 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((510646868839303992124428346762679226182394864117743089243973 : Real) / (452937348578601132294 : Real)) * Real.exp ((17 : Real) / (8 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg22Coeff 24 ((-3 : Real) / (20 : Real)) ((5 : Real) / (3 : Real)) ((11 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4188591646955145430582359681984271491704330702429493899944681 : Real) / (3623498788628809058352 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((510646868839303992124428346762679226182394864117743089243973 : Real) / (452937348578601132294 : Real)) * Real.exp ((17 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg22Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D19PlusWindowSeg23_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK11D19PlusWindowSegmentExpIntegral 23 * ((3 : Real) / (10 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-177425838745537293873801877461232508295669297570506100055319 : Real) / (3623498788628809058352 : Real)) * Real.exp ((21 : Real) / (10 : Real)) := by
  unfold p0PieceK11D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK11D19PlusWindowSeg23Coeff 24 ((-3 : Real) / (20 : Real)) ((11 : Real) / (6 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-177425838745537293873801877461232508295669297570506100055319 : Real) / (3623498788628809058352 : Real)) * Real.exp ((21 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D19PlusWindowSeg23Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK11D19_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-90958697618764223426170032488448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((1046025022615788569400955373617152000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-7670850165849116175607006073192448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((40271963370707859921936781884260352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((87 : Real) / (40 : Real)) +
      ((-161087853482831439687747127537041408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((510111536028966225677865903867297792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((-1311715378360198866028798038515908608000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((2787395179015422590311195831846305792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((-4955369207138529049442125923282321408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((7433053810707793574163188884923482112000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-9460250304537191821662240398993522688000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((10248604496581957806800760432242982912000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-9460250304537191821662240398993522688000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((7433053810707793574163188884923482112000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((-4955369207138529049442125923282321408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((2787395179015422590311195831846305792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((-1311715378360198866028798038515908608000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((510111536028966225677865903867297792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((-161087853482831439687747127537041408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((40271963370707859921936781884260352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((-7670850165849116175607006073192448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((1046025022615788569400955373617152000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-90958697618764223426170032488448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((107 : Real) / (40 : Real)) := by
  rw [p0PieceK11D19_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK11D19PlusWindowExpPolyIntegralSum
  unfold p0PieceK11D19MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK11D19PlusWindowSeg0_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg1_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg2_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg3_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg4_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg5_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg6_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg7_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg8_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg9_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg10_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg11_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg12_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg13_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg14_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg15_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg16_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg17_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg18_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg19_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg20_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg21_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg22_profile_linear]
  rw [p0PieceK11D19PlusWindowSeg23_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem primaryK11AnalyticP0_hLower19_generated :
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) := by
  have h_p83_40 := abs_sub_le_iff.mp p0ExpK11_p83_40_hbox
  have h_p21_10 := abs_sub_le_iff.mp p0ExpK11_p21_10_hbox
  have h_p17_8 := abs_sub_le_iff.mp p0ExpK11_p17_8_hbox
  have h_p43_20 := abs_sub_le_iff.mp p0ExpK11_p43_20_hbox
  have h_p87_40 := abs_sub_le_iff.mp p0ExpK11_p87_40_hbox
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK11_p11_5_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK11_p89_40_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK11_p9_4_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK11_p91_40_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK11_p23_10_hbox
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK11_p93_40_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK11_p47_20_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK11_p19_8_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK11_p12_5_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK11_p97_40_hbox
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK11_p49_20_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK11_p99_40_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK11_p5_2_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK11_p101_40_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK11_p51_20_hbox
  have h_p103_40 := abs_sub_le_iff.mp p0ExpK11_p103_40_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK11_p13_5_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK11_p21_8_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK11_p53_20_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK11_p107_40_hbox
  rw [show ((19 : Real) / (4 : Real)) = ((19 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK11D19_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceLower,
    primaryK11P0AbsDistanceEntryRat,
    primaryK11P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p83_40.1, h_p83_40.2, h_p21_10.1, h_p21_10.2, h_p17_8.1, h_p17_8.2, h_p43_20.1, h_p43_20.2, h_p87_40.1, h_p87_40.2, h_p11_5.1, h_p11_5.2, h_p89_40.1, h_p89_40.2, h_p9_4.1, h_p9_4.2, h_p91_40.1, h_p91_40.2, h_p23_10.1, h_p23_10.2, h_p93_40.1, h_p93_40.2, h_p47_20.1, h_p47_20.2, h_p19_8.1, h_p19_8.2, h_p12_5.1, h_p12_5.2, h_p97_40.1, h_p97_40.2, h_p49_20.1, h_p49_20.2, h_p99_40.1, h_p99_40.2, h_p5_2.1, h_p5_2.2, h_p101_40.1, h_p101_40.2, h_p51_20.1, h_p51_20.2, h_p103_40.1, h_p103_40.2, h_p13_5.1, h_p13_5.2, h_p21_8.1, h_p21_8.2, h_p53_20.1, h_p53_20.2, h_p107_40.1, h_p107_40.2]

theorem primaryK11AnalyticP0_hUpper19_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23) := by
  have h_p83_40 := abs_sub_le_iff.mp p0ExpK11_p83_40_hbox
  have h_p21_10 := abs_sub_le_iff.mp p0ExpK11_p21_10_hbox
  have h_p17_8 := abs_sub_le_iff.mp p0ExpK11_p17_8_hbox
  have h_p43_20 := abs_sub_le_iff.mp p0ExpK11_p43_20_hbox
  have h_p87_40 := abs_sub_le_iff.mp p0ExpK11_p87_40_hbox
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK11_p11_5_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK11_p89_40_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK11_p9_4_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK11_p91_40_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK11_p23_10_hbox
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK11_p93_40_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK11_p47_20_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK11_p19_8_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK11_p12_5_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK11_p97_40_hbox
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK11_p49_20_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK11_p99_40_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK11_p5_2_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK11_p101_40_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK11_p51_20_hbox
  have h_p103_40 := abs_sub_le_iff.mp p0ExpK11_p103_40_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK11_p13_5_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK11_p21_8_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK11_p53_20_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK11_p107_40_hbox
  rw [show ((19 : Real) / (4 : Real)) = ((19 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK11D19_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceUpper,
    primaryK11P0AbsDistanceEntryRat,
    primaryK11P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p83_40.1, h_p83_40.2, h_p21_10.1, h_p21_10.2, h_p17_8.1, h_p17_8.2, h_p43_20.1, h_p43_20.2, h_p87_40.1, h_p87_40.2, h_p11_5.1, h_p11_5.2, h_p89_40.1, h_p89_40.2, h_p9_4.1, h_p9_4.2, h_p91_40.1, h_p91_40.2, h_p23_10.1, h_p23_10.2, h_p93_40.1, h_p93_40.2, h_p47_20.1, h_p47_20.2, h_p19_8.1, h_p19_8.2, h_p12_5.1, h_p12_5.2, h_p97_40.1, h_p97_40.2, h_p49_20.1, h_p49_20.2, h_p99_40.1, h_p99_40.2, h_p5_2.1, h_p5_2.2, h_p101_40.1, h_p101_40.2, h_p51_20.1, h_p51_20.2, h_p103_40.1, h_p103_40.2, h_p13_5.1, h_p13_5.2, h_p21_8.1, h_p21_8.2, h_p53_20.1, h_p53_20.2, h_p107_40.1, h_p107_40.2]

private theorem p0PieceK11D20PlusWindowSeg0_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-186522656023456636671403063539741048238712840200683484074521 : Real) / (3623498788628809058352 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((14 : Real) / (5 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg0Coeff 24 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-11 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-186522656023456636671403063539741048238712840200683484074521 : Real) / (3623498788628809058352 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((14 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg1_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((535662405627716531951446354022947566548453897926536369239627 : Real) / (452937348578601132294 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-4179494829677226087784758495905762951761287159799316515925479 : Real) / (3623498788628809058352 : Real)) * Real.exp ((111 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg1Coeff 24 ((-3 : Real) / (20 : Real)) ((-11 : Real) / (6 : Real)) ((-5 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((535662405627716531951446354022947566548453897926536369239627 : Real) / (452937348578601132294 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-4179494829677226087784758495905762951761287159799316515925479 : Real) / (3623498788628809058352 : Real)) * Real.exp ((111 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg2_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-15695490316860443465337283762121288028161572486312960607627997 : Real) / (1207832929542936352784 : Real)) * Real.exp ((109 : Real) / (40 : Real)) +
      ((5740487730067014884454285887679964433451546102073463630760373 : Real) / (452937348578601132294 : Real)) * Real.exp ((11 : Real) / (4 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg2Coeff 24 ((-3 : Real) / (20 : Real)) ((-5 : Real) / (3 : Real)) ((-3 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-15695490316860443465337283762121288028161572486312960607627997 : Real) / (1207832929542936352784 : Real)) * Real.exp ((109 : Real) / (40 : Real)) +
      ((5740487730067014884454285887679964433451546102073463630760373 : Real) / (452937348578601132294 : Real)) * Real.exp ((11 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg3_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((20577711572106932400371286239050049797501016049235869580660175 : Real) / (226468674289300566147 : Real)) * Real.exp ((27 : Real) / (10 : Real)) +
      ((-107038112336725415344374813408957879971838427513687039392372003 : Real) / (1207832929542936352784 : Real)) * Real.exp ((109 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg3Coeff 24 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (2 : Real)) ((-4 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((20577711572106932400371286239050049797501016049235869580660175 : Real) / (226468674289300566147 : Real)) * Real.exp ((27 : Real) / (10 : Real)) +
      ((-107038112336725415344374813408957879971838427513687039392372003 : Real) / (1207832929542936352784 : Real)) * Real.exp ((109 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg4_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-1644411521774502165742564001111537323269894728909637094724161075 : Real) / (3623498788628809058352 : Real)) * Real.exp ((107 : Real) / (40 : Real)) +
      ((100238178540016647365439059413731006202498983950764130419339825 : Real) / (226468674289300566147 : Real)) * Real.exp ((27 : Real) / (10 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg4Coeff 24 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (3 : Real)) ((-7 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1644411521774502165742564001111537323269894728909637094724161075 : Real) / (3623498788628809058352 : Real)) * Real.exp ((107 : Real) / (40 : Real)) +
      ((100238178540016647365439059413731006202498983950764130419339825 : Real) / (226468674289300566147 : Real)) * Real.exp ((27 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg5_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((260079957249209073171289017031217379600247356443469755530018581 : Real) / (150979116192867044098 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((-6087805445401406939269298120666450260730105271090362905275838925 : Real) / (3623498788628809058352 : Real)) * Real.exp ((107 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg5Coeff 24 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (6 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((260079957249209073171289017031217379600247356443469755530018581 : Real) / (150979116192867044098 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((-6087805445401406939269298120666450260730105271090362905275838925 : Real) / (3623498788628809058352 : Real)) * Real.exp ((107 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg6_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-6235089835007367679988047862465632762075371420380910086958879263 : Real) / (1207832929542936352784 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((760143114808723378184442790703378204399752643556530244469981419 : Real) / (150979116192867044098 : Real)) * Real.exp ((53 : Real) / (20 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg6Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-5 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-6235089835007367679988047862465632762075371420380910086958879263 : Real) / (1207832929542936352784 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((760143114808723378184442790703378204399752643556530244469981419 : Real) / (150979116192867044098 : Real)) * Real.exp ((53 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg7_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((945363368403307808257445905378866124810213516725634317883835548 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((-14752356218755814176472720753788904965924628579619089913041120737 : Real) / (1207832929542936352784 : Real)) * Real.exp ((21 : Real) / (8 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg7Coeff 24 ((-3 : Real) / (20 : Real)) ((-5 : Real) / (6 : Real)) ((-2 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((945363368403307808257445905378866124810213516725634317883835548 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((-14752356218755814176472720753788904965924628579619089913041120737 : Real) / (1207832929542936352784 : Real)) * Real.exp ((21 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg8_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-15109304543260738785172494422907972219480819907137646615267815975 : Real) / (603916464771468176392 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((1842031810612114782053749926467439667189786483274365682116164452 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg8Coeff 24 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (3 : Real)) ((-1 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-15109304543260738785172494422907972219480819907137646615267815975 : Real) / (603916464771468176392 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((1842031810612114782053749926467439667189786483274365682116164452 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg9_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((9433020524275721150694946089264003746817064777229720625738512275 : Real) / (226468674289300566147 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((-24533649113847493610364512963350599044519180092862353384732184025 : Real) / (603916464771468176392 : Real)) * Real.exp ((103 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg9Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (2 : Real)) ((-1 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9433020524275721150694946089264003746817064777229720625738512275 : Real) / (226468674289300566147 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((-24533649113847493610364512963350599044519180092862353384732184025 : Real) / (603916464771468176392 : Real)) * Real.exp ((103 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg10_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-105534790524912859007010872931460937104219812896959386418793565403 : Real) / (1811749394314404529176 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((12866140907847659571794620565506442589182935222770279374261487725 : Real) / (226468674289300566147 : Real)) * Real.exp ((51 : Real) / (20 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg10Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (3 : Real)) ((-1 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-105534790524912859007010872931460937104219812896959386418793565403 : Real) / (1811749394314404529176 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((12866140907847659571794620565506442589182935222770279374261487725 : Real) / (226468674289300566147 : Real)) * Real.exp ((51 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg11_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((5191136995080674690635711715760295914967324652875278297471970302 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-121511216783979744712882896644383607407780187103040613581206434597 : Real) / (1811749394314404529176 : Real)) * Real.exp ((101 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg11Coeff 24 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (6 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((5191136995080674690635711715760295914967324652875278297471970302 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-121511216783979744712882896644383607407780187103040613581206434597 : Real) / (1811749394314404529176 : Real)) * Real.exp ((101 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg12_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-124451949620404082327611832449133264371068013330062445677798970283 : Real) / (1811749394314404529176 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((5057467501501283116165048716482686997032675347124721702528029698 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg12Coeff 24 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-124451949620404082327611832449133264371068013330062445677798970283 : Real) / (1811749394314404529176 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((5057467501501283116165048716482686997032675347124721702528029698 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg13_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((13148904827995351707997270841017806164808446834658996376142804675 : Real) / (226468674289300566147 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-102594057688488521392281937126711280140931986669937554322201029717 : Real) / (1811749394314404529176 : Real)) * Real.exp ((99 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg13Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (6 : Real)) ((1 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((13148904827995351707997270841017806164808446834658996376142804675 : Real) / (226468674289300566147 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-102594057688488521392281937126711280140931986669937554322201029717 : Real) / (1811749394314404529176 : Real)) * Real.exp ((99 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg14_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-25018390541042616072445114389542408647206962586362641716392239575 : Real) / (603916464771468176392 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((9150256604128029014492295813752640171191553165341003623857195325 : Real) / (226468674289300566147 : Real)) * Real.exp ((49 : Real) / (20 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg14Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (3 : Real)) ((1 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-25018390541042616072445114389542408647206962586362641716392239575 : Real) / (603916464771468176392 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((9150256604128029014492295813752640171191553165341003623857195325 : Real) / (226468674289300566147 : Real)) * Real.exp ((49 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg15_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((1874348211745741751070720114736518559003467507899604101915242268 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((-14624563116065616323091892996716162616793037413637358283607760425 : Real) / (603916464771468176392 : Real)) * Real.exp ((97 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg15Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real) / (2 : Real)) ((2 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((1874348211745741751070720114736518559003467507899604101915242268 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((-14624563116065616323091892996716162616793037413637358283607760425 : Real) / (603916464771468176392 : Real)) * Real.exp ((97 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg16_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-14978573780649232713237932857481467616118616825434374694137182063 : Real) / (1207832929542936352784 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((913046967269680839240475717109787232996532492100395898084757732 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg16Coeff 24 ((-3 : Real) / (20 : Real)) ((2 : Real) / (3 : Real)) ((5 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-14978573780649232713237932857481467616118616825434374694137182063 : Real) / (1207832929542936352784 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((913046967269680839240475717109787232996532492100395898084757732 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg17_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((770123449865465932428609042160840952632851437673925373043502341 : Real) / (150979116192867044098 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((-6008872273113949143222835758773070111881383174565625305862817937 : Real) / (1207832929542936352784 : Real)) * Real.exp ((19 : Real) / (8 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg17Coeff 24 ((-3 : Real) / (20 : Real)) ((5 : Real) / (6 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((770123449865465932428609042160840952632851437673925373043502341 : Real) / (150979116192867044098 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((-6008872273113949143222835758773070111881383174565625305862817937 : Real) / (1207832929542936352784 : Real)) * Real.exp ((19 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg18_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-6154342182513190244883634231953482229838017369475417918115307875 : Real) / (3623498788628809058352 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((250099622192466518927122765573754631367148562326074626956497659 : Real) / (150979116192867044098 : Real)) * Real.exp ((47 : Real) / (20 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg18Coeff 24 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((7 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-6154342182513190244883634231953482229838017369475417918115307875 : Real) / (3623498788628809058352 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((250099622192466518927122765573754631367148562326074626956497659 : Real) / (150979116192867044098 : Real)) * Real.exp ((47 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg19_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((101113679688057049478399307747353281906234273042937337555055375 : Real) / (226468674289300566147 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((-1577874784662718860128227889824505354161982630524582081884692125 : Real) / (3623498788628809058352 : Real)) * Real.exp ((93 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg19Coeff 24 ((-3 : Real) / (20 : Real)) ((7 : Real) / (6 : Real)) ((4 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((101113679688057049478399307747353281906234273042937337555055375 : Real) / (226468674289300566147 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((-1577874784662718860128227889824505354161982630524582081884692125 : Real) / (3623498788628809058352 : Real)) * Real.exp ((93 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg20_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 20 * ((3 : Real) / (10 : Real)) =
      ((-107738529362930308059243276720422077352298768981955163927992077 : Real) / (1207832929542936352784 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((19702210424066530287411037905427774093765726957062662444944625 : Real) / (226468674289300566147 : Real)) * Real.exp ((23 : Real) / (10 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg20Coeff 24 ((-3 : Real) / (20 : Real)) ((4 : Real) / (3 : Real)) ((3 : Real) / (2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-107738529362930308059243276720422077352298768981955163927992077 : Real) / (1207832929542936352784 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((19702210424066530287411037905427774093765726957062662444944625 : Real) / (226468674289300566147 : Real)) * Real.exp ((23 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg20Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg21_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 21 * ((3 : Real) / (10 : Real)) =
      ((5765503266855427424281303894940232773817605135882256910756027 : Real) / (452937348578601132294 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-14995073290655550750468820450657090647701231018044836072007923 : Real) / (1207832929542936352784 : Real)) * Real.exp ((91 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg21Coeff 24 ((-3 : Real) / (20 : Real)) ((3 : Real) / (2 : Real)) ((5 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((5765503266855427424281303894940232773817605135882256910756027 : Real) / (452937348578601132294 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-14995073290655550750468820450657090647701231018044836072007923 : Real) / (1207832929542936352784 : Real)) * Real.exp ((91 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg21Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg22_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 22 * ((3 : Real) / (10 : Real)) =
      ((-4188591646955145430582359681984271491704330702429493899944681 : Real) / (3623498788628809058352 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((510646868839303992124428346762679226182394864117743089243973 : Real) / (452937348578601132294 : Real)) * Real.exp ((9 : Real) / (4 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg22Coeff 24 ((-3 : Real) / (20 : Real)) ((5 : Real) / (3 : Real)) ((11 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4188591646955145430582359681984271491704330702429493899944681 : Real) / (3623498788628809058352 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((510646868839303992124428346762679226182394864117743089243973 : Real) / (452937348578601132294 : Real)) * Real.exp ((9 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg22Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK11D20PlusWindowSeg23_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK11D20PlusWindowSegmentExpIntegral 23 * ((3 : Real) / (10 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-177425838745537293873801877461232508295669297570506100055319 : Real) / (3623498788628809058352 : Real)) * Real.exp ((89 : Real) / (40 : Real)) := by
  unfold p0PieceK11D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK11D20PlusWindowSeg23Coeff 24 ((-3 : Real) / (20 : Real)) ((11 : Real) / (6 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-177425838745537293873801877461232508295669297570506100055319 : Real) / (3623498788628809058352 : Real)) * Real.exp ((89 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D20PlusWindowSeg23Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK11D20_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real)) =
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-90958697618764223426170032488448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((1046025022615788569400955373617152000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-7670850165849116175607006073192448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((40271963370707859921936781884260352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((23 : Real) / (10 : Real)) +
      ((-161087853482831439687747127537041408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((510111536028966225677865903867297792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((-1311715378360198866028798038515908608000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((2787395179015422590311195831846305792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((-4955369207138529049442125923282321408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((97 : Real) / (40 : Real)) +
      ((7433053810707793574163188884923482112000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-9460250304537191821662240398993522688000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((10248604496581957806800760432242982912000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-9460250304537191821662240398993522688000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((7433053810707793574163188884923482112000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((51 : Real) / (20 : Real)) +
      ((-4955369207138529049442125923282321408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((103 : Real) / (40 : Real)) +
      ((2787395179015422590311195831846305792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((-1311715378360198866028798038515908608000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((510111536028966225677865903867297792000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((-161087853482831439687747127537041408000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((107 : Real) / (40 : Real)) +
      ((40271963370707859921936781884260352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((27 : Real) / (10 : Real)) +
      ((-7670850165849116175607006073192448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((109 : Real) / (40 : Real)) +
      ((1046025022615788569400955373617152000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-90958697618764223426170032488448000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((3789945734115175976090418020352000000000000000000000000000 : Real) / (75489558096433522049 : Real)) * Real.exp ((14 : Real) / (5 : Real)) := by
  rw [p0PieceK11D20_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK11D20PlusWindowExpPolyIntegralSum
  unfold p0PieceK11D20MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK11D20PlusWindowSeg0_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg1_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg2_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg3_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg4_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg5_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg6_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg7_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg8_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg9_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg10_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg11_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg12_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg13_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg14_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg15_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg16_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg17_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg18_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg19_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg20_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg21_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg22_profile_linear]
  rw [p0PieceK11D20PlusWindowSeg23_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem primaryK11AnalyticP0_hLower20_generated :
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((20 : Real) / (4 : Real)) := by
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK11_p11_5_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK11_p89_40_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK11_p9_4_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK11_p91_40_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK11_p23_10_hbox
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK11_p93_40_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK11_p47_20_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK11_p19_8_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK11_p12_5_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK11_p97_40_hbox
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK11_p49_20_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK11_p99_40_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK11_p5_2_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK11_p101_40_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK11_p51_20_hbox
  have h_p103_40 := abs_sub_le_iff.mp p0ExpK11_p103_40_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK11_p13_5_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK11_p21_8_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK11_p53_20_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK11_p107_40_hbox
  have h_p27_10 := abs_sub_le_iff.mp p0ExpK11_p27_10_hbox
  have h_p109_40 := abs_sub_le_iff.mp p0ExpK11_p109_40_hbox
  have h_p11_4 := abs_sub_le_iff.mp p0ExpK11_p11_4_hbox
  have h_p111_40 := abs_sub_le_iff.mp p0ExpK11_p111_40_hbox
  have h_p14_5 := abs_sub_le_iff.mp p0ExpK11_p14_5_hbox
  rw [show ((20 : Real) / (4 : Real)) = ((5 : Real)) by norm_num]
  rw [p0PieceK11D20_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceLower,
    primaryK11P0AbsDistanceEntryRat,
    primaryK11P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p11_5.1, h_p11_5.2, h_p89_40.1, h_p89_40.2, h_p9_4.1, h_p9_4.2, h_p91_40.1, h_p91_40.2, h_p23_10.1, h_p23_10.2, h_p93_40.1, h_p93_40.2, h_p47_20.1, h_p47_20.2, h_p19_8.1, h_p19_8.2, h_p12_5.1, h_p12_5.2, h_p97_40.1, h_p97_40.2, h_p49_20.1, h_p49_20.2, h_p99_40.1, h_p99_40.2, h_p5_2.1, h_p5_2.2, h_p101_40.1, h_p101_40.2, h_p51_20.1, h_p51_20.2, h_p103_40.1, h_p103_40.2, h_p13_5.1, h_p13_5.2, h_p21_8.1, h_p21_8.2, h_p53_20.1, h_p53_20.2, h_p107_40.1, h_p107_40.2, h_p27_10.1, h_p27_10.2, h_p109_40.1, h_p109_40.2, h_p11_4.1, h_p11_4.2, h_p111_40.1, h_p111_40.2, h_p14_5.1, h_p14_5.2]

theorem primaryK11AnalyticP0_hUpper20_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      11 ((3 : Real) / (10 : Real)) ((3 : Real)) ((20 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23) := by
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK11_p11_5_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK11_p89_40_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK11_p9_4_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK11_p91_40_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK11_p23_10_hbox
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK11_p93_40_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK11_p47_20_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK11_p19_8_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK11_p12_5_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK11_p97_40_hbox
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK11_p49_20_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK11_p99_40_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK11_p5_2_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK11_p101_40_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK11_p51_20_hbox
  have h_p103_40 := abs_sub_le_iff.mp p0ExpK11_p103_40_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK11_p13_5_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK11_p21_8_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK11_p53_20_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK11_p107_40_hbox
  have h_p27_10 := abs_sub_le_iff.mp p0ExpK11_p27_10_hbox
  have h_p109_40 := abs_sub_le_iff.mp p0ExpK11_p109_40_hbox
  have h_p11_4 := abs_sub_le_iff.mp p0ExpK11_p11_4_hbox
  have h_p111_40 := abs_sub_le_iff.mp p0ExpK11_p111_40_hbox
  have h_p14_5 := abs_sub_le_iff.mp p0ExpK11_p14_5_hbox
  rw [show ((20 : Real) / (4 : Real)) = ((5 : Real)) by norm_num]
  rw [p0PieceK11D20_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceUpper,
    primaryK11P0AbsDistanceEntryRat,
    primaryK11P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p11_5.1, h_p11_5.2, h_p89_40.1, h_p89_40.2, h_p9_4.1, h_p9_4.2, h_p91_40.1, h_p91_40.2, h_p23_10.1, h_p23_10.2, h_p93_40.1, h_p93_40.2, h_p47_20.1, h_p47_20.2, h_p19_8.1, h_p19_8.2, h_p12_5.1, h_p12_5.2, h_p97_40.1, h_p97_40.2, h_p49_20.1, h_p49_20.2, h_p99_40.1, h_p99_40.2, h_p5_2.1, h_p5_2.2, h_p101_40.1, h_p101_40.2, h_p51_20.1, h_p51_20.2, h_p103_40.1, h_p103_40.2, h_p13_5.1, h_p13_5.2, h_p21_8.1, h_p21_8.2, h_p53_20.1, h_p53_20.2, h_p107_40.1, h_p107_40.2, h_p27_10.1, h_p27_10.2, h_p109_40.1, h_p109_40.2, h_p11_4.1, h_p11_4.2, h_p111_40.1, h_p111_40.2, h_p14_5.1, h_p14_5.2]

end PSDpd
end Q3
