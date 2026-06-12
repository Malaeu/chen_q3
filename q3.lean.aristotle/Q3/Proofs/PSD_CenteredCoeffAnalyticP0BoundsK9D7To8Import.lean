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

private theorem p0PieceK9D7PlusWindowSeg0_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((229 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((47 : Real) / (40 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((229 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((47 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg1_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((223 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((229 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((223 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((229 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg2_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((217 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((223 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((217 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((223 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg3_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((211 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((217 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((211 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((217 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg4_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((41 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((211 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((41 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((211 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg5_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((199 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((41 : Real) / (40 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((199 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((41 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg6_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((199 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((199 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg7_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((187 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((187 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg8_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((181 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((187 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((181 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((187 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg9_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((181 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((181 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg10_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((169 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (8 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((169 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg11_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((163 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((169 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((163 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((169 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg12_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((163 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((163 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg13_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((151 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((151 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg14_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((29 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((151 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((29 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((151 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg15_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((139 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (40 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((139 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg16_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((133 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((139 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((133 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((139 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg17_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((127 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((133 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((127 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((133 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg18_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((121 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((127 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((121 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((127 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D7PlusWindowSeg19_profile_linear :
    Real.exp ((7 : Real) / (8 : Real)) * p0PieceK9D7PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((121 : Real) / (200 : Real)) := by
  unfold p0PieceK9D7PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D7PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((121 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D7PlusWindowSeg19Coeff,
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

theorem p0PieceK9D7_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((121 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((127 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((133 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((139 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((151 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((157 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((163 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((169 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((181 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((187 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((193 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((199 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((41 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((211 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((217 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((223 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((229 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((47 : Real) / (40 : Real)) := by
  rw [p0PieceK9D7_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D7PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D7MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D7PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D7PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower7_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨7, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (4 : Real)) := by
  have h_p23_40 := abs_sub_le_iff.mp p0ExpK9_p23_40_hbox
  have h_p121_200 := abs_sub_le_iff.mp p0ExpK9_p121_200_hbox
  have h_p127_200 := abs_sub_le_iff.mp p0ExpK9_p127_200_hbox
  have h_p133_200 := abs_sub_le_iff.mp p0ExpK9_p133_200_hbox
  have h_p139_200 := abs_sub_le_iff.mp p0ExpK9_p139_200_hbox
  have h_p29_40 := abs_sub_le_iff.mp p0ExpK9_p29_40_hbox
  have h_p151_200 := abs_sub_le_iff.mp p0ExpK9_p151_200_hbox
  have h_p157_200 := abs_sub_le_iff.mp p0ExpK9_p157_200_hbox
  have h_p163_200 := abs_sub_le_iff.mp p0ExpK9_p163_200_hbox
  have h_p169_200 := abs_sub_le_iff.mp p0ExpK9_p169_200_hbox
  have h_p7_8 := abs_sub_le_iff.mp p0ExpK9_p7_8_hbox
  have h_p181_200 := abs_sub_le_iff.mp p0ExpK9_p181_200_hbox
  have h_p187_200 := abs_sub_le_iff.mp p0ExpK9_p187_200_hbox
  have h_p193_200 := abs_sub_le_iff.mp p0ExpK9_p193_200_hbox
  have h_p199_200 := abs_sub_le_iff.mp p0ExpK9_p199_200_hbox
  have h_p41_40 := abs_sub_le_iff.mp p0ExpK9_p41_40_hbox
  have h_p211_200 := abs_sub_le_iff.mp p0ExpK9_p211_200_hbox
  have h_p217_200 := abs_sub_le_iff.mp p0ExpK9_p217_200_hbox
  have h_p223_200 := abs_sub_le_iff.mp p0ExpK9_p223_200_hbox
  have h_p229_200 := abs_sub_le_iff.mp p0ExpK9_p229_200_hbox
  have h_p47_40 := abs_sub_le_iff.mp p0ExpK9_p47_40_hbox
  rw [show ((7 : Real) / (4 : Real)) = ((7 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D7_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p23_40.1, h_p23_40.2, h_p121_200.1, h_p121_200.2, h_p127_200.1, h_p127_200.2, h_p133_200.1, h_p133_200.2, h_p139_200.1, h_p139_200.2, h_p29_40.1, h_p29_40.2, h_p151_200.1, h_p151_200.2, h_p157_200.1, h_p157_200.2, h_p163_200.1, h_p163_200.2, h_p169_200.1, h_p169_200.2, h_p7_8.1, h_p7_8.2, h_p181_200.1, h_p181_200.2, h_p187_200.1, h_p187_200.2, h_p193_200.1, h_p193_200.2, h_p199_200.1, h_p199_200.2, h_p41_40.1, h_p41_40.2, h_p211_200.1, h_p211_200.2, h_p217_200.1, h_p217_200.2, h_p223_200.1, h_p223_200.2, h_p229_200.1, h_p229_200.2, h_p47_40.1, h_p47_40.2]

theorem controlK9AnalyticP0_hUpper7_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨7, by norm_num⟩ : CoeffIndex23) := by
  have h_p23_40 := abs_sub_le_iff.mp p0ExpK9_p23_40_hbox
  have h_p121_200 := abs_sub_le_iff.mp p0ExpK9_p121_200_hbox
  have h_p127_200 := abs_sub_le_iff.mp p0ExpK9_p127_200_hbox
  have h_p133_200 := abs_sub_le_iff.mp p0ExpK9_p133_200_hbox
  have h_p139_200 := abs_sub_le_iff.mp p0ExpK9_p139_200_hbox
  have h_p29_40 := abs_sub_le_iff.mp p0ExpK9_p29_40_hbox
  have h_p151_200 := abs_sub_le_iff.mp p0ExpK9_p151_200_hbox
  have h_p157_200 := abs_sub_le_iff.mp p0ExpK9_p157_200_hbox
  have h_p163_200 := abs_sub_le_iff.mp p0ExpK9_p163_200_hbox
  have h_p169_200 := abs_sub_le_iff.mp p0ExpK9_p169_200_hbox
  have h_p7_8 := abs_sub_le_iff.mp p0ExpK9_p7_8_hbox
  have h_p181_200 := abs_sub_le_iff.mp p0ExpK9_p181_200_hbox
  have h_p187_200 := abs_sub_le_iff.mp p0ExpK9_p187_200_hbox
  have h_p193_200 := abs_sub_le_iff.mp p0ExpK9_p193_200_hbox
  have h_p199_200 := abs_sub_le_iff.mp p0ExpK9_p199_200_hbox
  have h_p41_40 := abs_sub_le_iff.mp p0ExpK9_p41_40_hbox
  have h_p211_200 := abs_sub_le_iff.mp p0ExpK9_p211_200_hbox
  have h_p217_200 := abs_sub_le_iff.mp p0ExpK9_p217_200_hbox
  have h_p223_200 := abs_sub_le_iff.mp p0ExpK9_p223_200_hbox
  have h_p229_200 := abs_sub_le_iff.mp p0ExpK9_p229_200_hbox
  have h_p47_40 := abs_sub_le_iff.mp p0ExpK9_p47_40_hbox
  rw [show ((7 : Real) / (4 : Real)) = ((7 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D7_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p23_40.1, h_p23_40.2, h_p121_200.1, h_p121_200.2, h_p127_200.1, h_p127_200.2, h_p133_200.1, h_p133_200.2, h_p139_200.1, h_p139_200.2, h_p29_40.1, h_p29_40.2, h_p151_200.1, h_p151_200.2, h_p157_200.1, h_p157_200.2, h_p163_200.1, h_p163_200.2, h_p169_200.1, h_p169_200.2, h_p7_8.1, h_p7_8.2, h_p181_200.1, h_p181_200.2, h_p187_200.1, h_p187_200.2, h_p193_200.1, h_p193_200.2, h_p199_200.1, h_p199_200.2, h_p41_40.1, h_p41_40.2, h_p211_200.1, h_p211_200.2, h_p217_200.1, h_p217_200.2, h_p223_200.1, h_p223_200.2, h_p229_200.1, h_p229_200.2, h_p47_40.1, h_p47_40.2]

private theorem p0PieceK9D8PlusWindowSeg0_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((127 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (10 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((127 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg1_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((31 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((127 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((31 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((127 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg2_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((121 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (25 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((121 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg3_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((121 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((121 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg4_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((23 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (50 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((23 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg5_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((28 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((23 : Real) / (20 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((28 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((23 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg6_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((28 : Real) / (25 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((28 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg7_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((53 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((53 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg8_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((103 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((53 : Real) / (50 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((103 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((53 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg9_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((103 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((103 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg10_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((97 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((97 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg11_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((47 : Real) / (50 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((97 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((47 : Real) / (50 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((97 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg12_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((47 : Real) / (50 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((47 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg13_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((22 : Real) / (25 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((22 : Real) / (25 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg14_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((17 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((22 : Real) / (25 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((17 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((22 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg15_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (50 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (20 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (50 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg16_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((79 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (50 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((79 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg17_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((19 : Real) / (25 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((79 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((19 : Real) / (25 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((79 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg18_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((73 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((19 : Real) / (25 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((73 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((19 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D8PlusWindowSeg19_profile_linear :
    Real.exp ((1 : Real)) * p0PieceK9D8PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (10 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((73 : Real) / (100 : Real)) := by
  unfold p0PieceK9D8PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real)) * expPolyIntegral p0PieceK9D8PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (10 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((73 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D8PlusWindowSeg19Coeff,
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

theorem p0PieceK9D8_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (10 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((73 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (25 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((79 : Real) / (100 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((41 : Real) / (50 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (20 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((22 : Real) / (25 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((91 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((47 : Real) / (50 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((97 : Real) / (100 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((103 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((53 : Real) / (50 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((109 : Real) / (100 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((28 : Real) / (25 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((23 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((59 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((121 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((31 : Real) / (25 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((127 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (10 : Real)) := by
  rw [p0PieceK9D8_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D8PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D8MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D8PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D8PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower8_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨8, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((8 : Real) / (4 : Real)) := by
  have h_p7_10 := abs_sub_le_iff.mp p0ExpK9_p7_10_hbox
  have h_p73_100 := abs_sub_le_iff.mp p0ExpK9_p73_100_hbox
  have h_p19_25 := abs_sub_le_iff.mp p0ExpK9_p19_25_hbox
  have h_p79_100 := abs_sub_le_iff.mp p0ExpK9_p79_100_hbox
  have h_p41_50 := abs_sub_le_iff.mp p0ExpK9_p41_50_hbox
  have h_p17_20 := abs_sub_le_iff.mp p0ExpK9_p17_20_hbox
  have h_p22_25 := abs_sub_le_iff.mp p0ExpK9_p22_25_hbox
  have h_p91_100 := abs_sub_le_iff.mp p0ExpK9_p91_100_hbox
  have h_p47_50 := abs_sub_le_iff.mp p0ExpK9_p47_50_hbox
  have h_p97_100 := abs_sub_le_iff.mp p0ExpK9_p97_100_hbox
  have h_p1_1 := abs_sub_le_iff.mp p0ExpK9_p1_1_hbox
  have h_p103_100 := abs_sub_le_iff.mp p0ExpK9_p103_100_hbox
  have h_p53_50 := abs_sub_le_iff.mp p0ExpK9_p53_50_hbox
  have h_p109_100 := abs_sub_le_iff.mp p0ExpK9_p109_100_hbox
  have h_p28_25 := abs_sub_le_iff.mp p0ExpK9_p28_25_hbox
  have h_p23_20 := abs_sub_le_iff.mp p0ExpK9_p23_20_hbox
  have h_p59_50 := abs_sub_le_iff.mp p0ExpK9_p59_50_hbox
  have h_p121_100 := abs_sub_le_iff.mp p0ExpK9_p121_100_hbox
  have h_p31_25 := abs_sub_le_iff.mp p0ExpK9_p31_25_hbox
  have h_p127_100 := abs_sub_le_iff.mp p0ExpK9_p127_100_hbox
  have h_p13_10 := abs_sub_le_iff.mp p0ExpK9_p13_10_hbox
  rw [show ((8 : Real) / (4 : Real)) = ((2 : Real)) by norm_num]
  rw [p0PieceK9D8_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p7_10.1, h_p7_10.2, h_p73_100.1, h_p73_100.2, h_p19_25.1, h_p19_25.2, h_p79_100.1, h_p79_100.2, h_p41_50.1, h_p41_50.2, h_p17_20.1, h_p17_20.2, h_p22_25.1, h_p22_25.2, h_p91_100.1, h_p91_100.2, h_p47_50.1, h_p47_50.2, h_p97_100.1, h_p97_100.2, h_p1_1.1, h_p1_1.2, h_p103_100.1, h_p103_100.2, h_p53_50.1, h_p53_50.2, h_p109_100.1, h_p109_100.2, h_p28_25.1, h_p28_25.2, h_p23_20.1, h_p23_20.2, h_p59_50.1, h_p59_50.2, h_p121_100.1, h_p121_100.2, h_p31_25.1, h_p31_25.2, h_p127_100.1, h_p127_100.2, h_p13_10.1, h_p13_10.2]

theorem controlK9AnalyticP0_hUpper8_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((8 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨8, by norm_num⟩ : CoeffIndex23) := by
  have h_p7_10 := abs_sub_le_iff.mp p0ExpK9_p7_10_hbox
  have h_p73_100 := abs_sub_le_iff.mp p0ExpK9_p73_100_hbox
  have h_p19_25 := abs_sub_le_iff.mp p0ExpK9_p19_25_hbox
  have h_p79_100 := abs_sub_le_iff.mp p0ExpK9_p79_100_hbox
  have h_p41_50 := abs_sub_le_iff.mp p0ExpK9_p41_50_hbox
  have h_p17_20 := abs_sub_le_iff.mp p0ExpK9_p17_20_hbox
  have h_p22_25 := abs_sub_le_iff.mp p0ExpK9_p22_25_hbox
  have h_p91_100 := abs_sub_le_iff.mp p0ExpK9_p91_100_hbox
  have h_p47_50 := abs_sub_le_iff.mp p0ExpK9_p47_50_hbox
  have h_p97_100 := abs_sub_le_iff.mp p0ExpK9_p97_100_hbox
  have h_p1_1 := abs_sub_le_iff.mp p0ExpK9_p1_1_hbox
  have h_p103_100 := abs_sub_le_iff.mp p0ExpK9_p103_100_hbox
  have h_p53_50 := abs_sub_le_iff.mp p0ExpK9_p53_50_hbox
  have h_p109_100 := abs_sub_le_iff.mp p0ExpK9_p109_100_hbox
  have h_p28_25 := abs_sub_le_iff.mp p0ExpK9_p28_25_hbox
  have h_p23_20 := abs_sub_le_iff.mp p0ExpK9_p23_20_hbox
  have h_p59_50 := abs_sub_le_iff.mp p0ExpK9_p59_50_hbox
  have h_p121_100 := abs_sub_le_iff.mp p0ExpK9_p121_100_hbox
  have h_p31_25 := abs_sub_le_iff.mp p0ExpK9_p31_25_hbox
  have h_p127_100 := abs_sub_le_iff.mp p0ExpK9_p127_100_hbox
  have h_p13_10 := abs_sub_le_iff.mp p0ExpK9_p13_10_hbox
  rw [show ((8 : Real) / (4 : Real)) = ((2 : Real)) by norm_num]
  rw [p0PieceK9D8_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p7_10.1, h_p7_10.2, h_p73_100.1, h_p73_100.2, h_p19_25.1, h_p19_25.2, h_p79_100.1, h_p79_100.2, h_p41_50.1, h_p41_50.2, h_p17_20.1, h_p17_20.2, h_p22_25.1, h_p22_25.2, h_p91_100.1, h_p91_100.2, h_p47_50.1, h_p47_50.2, h_p97_100.1, h_p97_100.2, h_p1_1.1, h_p1_1.2, h_p103_100.1, h_p103_100.2, h_p53_50.1, h_p53_50.2, h_p109_100.1, h_p109_100.2, h_p28_25.1, h_p28_25.2, h_p23_20.1, h_p23_20.2, h_p59_50.1, h_p59_50.2, h_p121_100.1, h_p121_100.2, h_p31_25.1, h_p31_25.2, h_p127_100.1, h_p127_100.2, h_p13_10.1, h_p13_10.2]

end PSDpd
end Q3
