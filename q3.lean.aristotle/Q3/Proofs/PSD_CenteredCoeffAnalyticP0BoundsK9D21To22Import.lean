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

private theorem p0PieceK9D21PlusWindowSeg0_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((579 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((117 : Real) / (40 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((579 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((117 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg1_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((573 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((579 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((573 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((579 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg2_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((567 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((573 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((567 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((573 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg3_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((561 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((567 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((561 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((567 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg4_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((561 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((561 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg5_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((549 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((111 : Real) / (40 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((549 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((111 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg6_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((543 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((549 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((543 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((549 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg7_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((537 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((543 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((537 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((543 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg8_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((531 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((537 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((531 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((537 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg9_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((531 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((531 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg10_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((519 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (8 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((519 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg11_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((513 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((519 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((513 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((519 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg12_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((507 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((513 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((507 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((513 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg13_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((501 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((507 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((501 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((507 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg14_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((501 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((501 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg15_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((489 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((99 : Real) / (40 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((489 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((99 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg16_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((483 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((489 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((483 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((489 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg17_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((477 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((483 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((477 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((483 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg18_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((471 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((477 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((471 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((477 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D21PlusWindowSeg19_profile_linear :
    Real.exp ((21 : Real) / (8 : Real)) * p0PieceK9D21PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((471 : Real) / (200 : Real)) := by
  unfold p0PieceK9D21PlusWindowSegmentExpIntegral
  change Real.exp ((21 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D21PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((471 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D21PlusWindowSeg19Coeff,
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

theorem p0PieceK9D21_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((21 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((93 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((471 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((477 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((483 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((489 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((99 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((501 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((507 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((513 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((519 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((531 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((537 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((543 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((549 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((111 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((561 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((567 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((573 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((579 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((117 : Real) / (40 : Real)) := by
  rw [p0PieceK9D21_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D21PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D21MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D21PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D21PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower21_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨21, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((21 : Real) / (4 : Real)) := by
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK9_p93_40_hbox
  have h_p471_200 := abs_sub_le_iff.mp p0ExpK9_p471_200_hbox
  have h_p477_200 := abs_sub_le_iff.mp p0ExpK9_p477_200_hbox
  have h_p483_200 := abs_sub_le_iff.mp p0ExpK9_p483_200_hbox
  have h_p489_200 := abs_sub_le_iff.mp p0ExpK9_p489_200_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK9_p99_40_hbox
  have h_p501_200 := abs_sub_le_iff.mp p0ExpK9_p501_200_hbox
  have h_p507_200 := abs_sub_le_iff.mp p0ExpK9_p507_200_hbox
  have h_p513_200 := abs_sub_le_iff.mp p0ExpK9_p513_200_hbox
  have h_p519_200 := abs_sub_le_iff.mp p0ExpK9_p519_200_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK9_p21_8_hbox
  have h_p531_200 := abs_sub_le_iff.mp p0ExpK9_p531_200_hbox
  have h_p537_200 := abs_sub_le_iff.mp p0ExpK9_p537_200_hbox
  have h_p543_200 := abs_sub_le_iff.mp p0ExpK9_p543_200_hbox
  have h_p549_200 := abs_sub_le_iff.mp p0ExpK9_p549_200_hbox
  have h_p111_40 := abs_sub_le_iff.mp p0ExpK9_p111_40_hbox
  have h_p561_200 := abs_sub_le_iff.mp p0ExpK9_p561_200_hbox
  have h_p567_200 := abs_sub_le_iff.mp p0ExpK9_p567_200_hbox
  have h_p573_200 := abs_sub_le_iff.mp p0ExpK9_p573_200_hbox
  have h_p579_200 := abs_sub_le_iff.mp p0ExpK9_p579_200_hbox
  have h_p117_40 := abs_sub_le_iff.mp p0ExpK9_p117_40_hbox
  rw [show ((21 : Real) / (4 : Real)) = ((21 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D21_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p93_40.1, h_p93_40.2, h_p471_200.1, h_p471_200.2, h_p477_200.1, h_p477_200.2, h_p483_200.1, h_p483_200.2, h_p489_200.1, h_p489_200.2, h_p99_40.1, h_p99_40.2, h_p501_200.1, h_p501_200.2, h_p507_200.1, h_p507_200.2, h_p513_200.1, h_p513_200.2, h_p519_200.1, h_p519_200.2, h_p21_8.1, h_p21_8.2, h_p531_200.1, h_p531_200.2, h_p537_200.1, h_p537_200.2, h_p543_200.1, h_p543_200.2, h_p549_200.1, h_p549_200.2, h_p111_40.1, h_p111_40.2, h_p561_200.1, h_p561_200.2, h_p567_200.1, h_p567_200.2, h_p573_200.1, h_p573_200.2, h_p579_200.1, h_p579_200.2, h_p117_40.1, h_p117_40.2]

theorem controlK9AnalyticP0_hUpper21_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((21 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨21, by norm_num⟩ : CoeffIndex23) := by
  have h_p93_40 := abs_sub_le_iff.mp p0ExpK9_p93_40_hbox
  have h_p471_200 := abs_sub_le_iff.mp p0ExpK9_p471_200_hbox
  have h_p477_200 := abs_sub_le_iff.mp p0ExpK9_p477_200_hbox
  have h_p483_200 := abs_sub_le_iff.mp p0ExpK9_p483_200_hbox
  have h_p489_200 := abs_sub_le_iff.mp p0ExpK9_p489_200_hbox
  have h_p99_40 := abs_sub_le_iff.mp p0ExpK9_p99_40_hbox
  have h_p501_200 := abs_sub_le_iff.mp p0ExpK9_p501_200_hbox
  have h_p507_200 := abs_sub_le_iff.mp p0ExpK9_p507_200_hbox
  have h_p513_200 := abs_sub_le_iff.mp p0ExpK9_p513_200_hbox
  have h_p519_200 := abs_sub_le_iff.mp p0ExpK9_p519_200_hbox
  have h_p21_8 := abs_sub_le_iff.mp p0ExpK9_p21_8_hbox
  have h_p531_200 := abs_sub_le_iff.mp p0ExpK9_p531_200_hbox
  have h_p537_200 := abs_sub_le_iff.mp p0ExpK9_p537_200_hbox
  have h_p543_200 := abs_sub_le_iff.mp p0ExpK9_p543_200_hbox
  have h_p549_200 := abs_sub_le_iff.mp p0ExpK9_p549_200_hbox
  have h_p111_40 := abs_sub_le_iff.mp p0ExpK9_p111_40_hbox
  have h_p561_200 := abs_sub_le_iff.mp p0ExpK9_p561_200_hbox
  have h_p567_200 := abs_sub_le_iff.mp p0ExpK9_p567_200_hbox
  have h_p573_200 := abs_sub_le_iff.mp p0ExpK9_p573_200_hbox
  have h_p579_200 := abs_sub_le_iff.mp p0ExpK9_p579_200_hbox
  have h_p117_40 := abs_sub_le_iff.mp p0ExpK9_p117_40_hbox
  rw [show ((21 : Real) / (4 : Real)) = ((21 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D21_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p93_40.1, h_p93_40.2, h_p471_200.1, h_p471_200.2, h_p477_200.1, h_p477_200.2, h_p483_200.1, h_p483_200.2, h_p489_200.1, h_p489_200.2, h_p99_40.1, h_p99_40.2, h_p501_200.1, h_p501_200.2, h_p507_200.1, h_p507_200.2, h_p513_200.1, h_p513_200.2, h_p519_200.1, h_p519_200.2, h_p21_8.1, h_p21_8.2, h_p531_200.1, h_p531_200.2, h_p537_200.1, h_p537_200.2, h_p543_200.1, h_p543_200.2, h_p549_200.1, h_p549_200.2, h_p111_40.1, h_p111_40.2, h_p561_200.1, h_p561_200.2, h_p567_200.1, h_p567_200.2, h_p573_200.1, h_p573_200.2, h_p579_200.1, h_p579_200.2, h_p117_40.1, h_p117_40.2]

private theorem p0PieceK9D22PlusWindowSeg0_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((299 : Real) / (100 : Real)) +
      ((-5231484246266731115959102064883801227913489607636627603 : Real) / (481792415807310718491900 : Real)) * Real.exp ((3 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-5 : Real) / (3 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((299 : Real) / (100 : Real)) +
      ((-5231484246266731115959102064883801227913489607636627603 : Real) / (481792415807310718491900 : Real)) * Real.exp ((3 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg1_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((74 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((299 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((74 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((299 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg2_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((74 : Real) / (25 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((74 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg3_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg4_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((287 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((29 : Real) / (10 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((287 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((29 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg5_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((71 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((287 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((71 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((287 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg6_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((281 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((71 : Real) / (25 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((281 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((71 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg7_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((139 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((281 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((139 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((281 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg8_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((139 : Real) / (50 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((139 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg9_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((68 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (4 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((68 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg10_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((269 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((68 : Real) / (25 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((269 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((68 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg11_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((133 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((269 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((133 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((269 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg12_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((263 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((133 : Real) / (50 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((263 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((133 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg13_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((263 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((263 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg14_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (5 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg15_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((127 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((127 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg16_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((251 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((127 : Real) / (50 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((251 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((127 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg17_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((62 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((251 : Real) / (100 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((62 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((251 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D22PlusWindowSeg18_profile_linear :
    Real.exp ((11 : Real) / (4 : Real)) * p0PieceK9D22PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((62 : Real) / (25 : Real)) := by
  unfold p0PieceK9D22PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D22PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((62 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D22PlusWindowSeg18Coeff,
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

theorem p0PieceK9D22_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((11 : Real) / (2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((49 : Real) / (20 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((62 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((251 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((127 : Real) / (50 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((257 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (5 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((263 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((133 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((269 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((68 : Real) / (25 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((139 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((281 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((71 : Real) / (25 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((287 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (10 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((293 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((74 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((299 : Real) / (100 : Real)) +
      ((-5231484246266731115959102064883801227913489607636627603 : Real) / (481792415807310718491900 : Real)) * Real.exp ((3 : Real)) := by
  rw [p0PieceK9D22_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D22PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D22MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D22PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D22PlusWindowSeg18_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower22_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨22, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((22 : Real) / (4 : Real)) := by
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK9_p49_20_hbox
  have h_p62_25 := abs_sub_le_iff.mp p0ExpK9_p62_25_hbox
  have h_p251_100 := abs_sub_le_iff.mp p0ExpK9_p251_100_hbox
  have h_p127_50 := abs_sub_le_iff.mp p0ExpK9_p127_50_hbox
  have h_p257_100 := abs_sub_le_iff.mp p0ExpK9_p257_100_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK9_p13_5_hbox
  have h_p263_100 := abs_sub_le_iff.mp p0ExpK9_p263_100_hbox
  have h_p133_50 := abs_sub_le_iff.mp p0ExpK9_p133_50_hbox
  have h_p269_100 := abs_sub_le_iff.mp p0ExpK9_p269_100_hbox
  have h_p68_25 := abs_sub_le_iff.mp p0ExpK9_p68_25_hbox
  have h_p11_4 := abs_sub_le_iff.mp p0ExpK9_p11_4_hbox
  have h_p139_50 := abs_sub_le_iff.mp p0ExpK9_p139_50_hbox
  have h_p281_100 := abs_sub_le_iff.mp p0ExpK9_p281_100_hbox
  have h_p71_25 := abs_sub_le_iff.mp p0ExpK9_p71_25_hbox
  have h_p287_100 := abs_sub_le_iff.mp p0ExpK9_p287_100_hbox
  have h_p29_10 := abs_sub_le_iff.mp p0ExpK9_p29_10_hbox
  have h_p293_100 := abs_sub_le_iff.mp p0ExpK9_p293_100_hbox
  have h_p74_25 := abs_sub_le_iff.mp p0ExpK9_p74_25_hbox
  have h_p299_100 := abs_sub_le_iff.mp p0ExpK9_p299_100_hbox
  have h_p3_1 := abs_sub_le_iff.mp p0ExpK9_p3_1_hbox
  rw [show ((22 : Real) / (4 : Real)) = ((11 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D22_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p49_20.1, h_p49_20.2, h_p62_25.1, h_p62_25.2, h_p251_100.1, h_p251_100.2, h_p127_50.1, h_p127_50.2, h_p257_100.1, h_p257_100.2, h_p13_5.1, h_p13_5.2, h_p263_100.1, h_p263_100.2, h_p133_50.1, h_p133_50.2, h_p269_100.1, h_p269_100.2, h_p68_25.1, h_p68_25.2, h_p11_4.1, h_p11_4.2, h_p139_50.1, h_p139_50.2, h_p281_100.1, h_p281_100.2, h_p71_25.1, h_p71_25.2, h_p287_100.1, h_p287_100.2, h_p29_10.1, h_p29_10.2, h_p293_100.1, h_p293_100.2, h_p74_25.1, h_p74_25.2, h_p299_100.1, h_p299_100.2, h_p3_1.1, h_p3_1.2]

theorem controlK9AnalyticP0_hUpper22_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((22 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨22, by norm_num⟩ : CoeffIndex23) := by
  have h_p49_20 := abs_sub_le_iff.mp p0ExpK9_p49_20_hbox
  have h_p62_25 := abs_sub_le_iff.mp p0ExpK9_p62_25_hbox
  have h_p251_100 := abs_sub_le_iff.mp p0ExpK9_p251_100_hbox
  have h_p127_50 := abs_sub_le_iff.mp p0ExpK9_p127_50_hbox
  have h_p257_100 := abs_sub_le_iff.mp p0ExpK9_p257_100_hbox
  have h_p13_5 := abs_sub_le_iff.mp p0ExpK9_p13_5_hbox
  have h_p263_100 := abs_sub_le_iff.mp p0ExpK9_p263_100_hbox
  have h_p133_50 := abs_sub_le_iff.mp p0ExpK9_p133_50_hbox
  have h_p269_100 := abs_sub_le_iff.mp p0ExpK9_p269_100_hbox
  have h_p68_25 := abs_sub_le_iff.mp p0ExpK9_p68_25_hbox
  have h_p11_4 := abs_sub_le_iff.mp p0ExpK9_p11_4_hbox
  have h_p139_50 := abs_sub_le_iff.mp p0ExpK9_p139_50_hbox
  have h_p281_100 := abs_sub_le_iff.mp p0ExpK9_p281_100_hbox
  have h_p71_25 := abs_sub_le_iff.mp p0ExpK9_p71_25_hbox
  have h_p287_100 := abs_sub_le_iff.mp p0ExpK9_p287_100_hbox
  have h_p29_10 := abs_sub_le_iff.mp p0ExpK9_p29_10_hbox
  have h_p293_100 := abs_sub_le_iff.mp p0ExpK9_p293_100_hbox
  have h_p74_25 := abs_sub_le_iff.mp p0ExpK9_p74_25_hbox
  have h_p299_100 := abs_sub_le_iff.mp p0ExpK9_p299_100_hbox
  have h_p3_1 := abs_sub_le_iff.mp p0ExpK9_p3_1_hbox
  rw [show ((22 : Real) / (4 : Real)) = ((11 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D22_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p49_20.1, h_p49_20.2, h_p62_25.1, h_p62_25.2, h_p251_100.1, h_p251_100.2, h_p127_50.1, h_p127_50.2, h_p257_100.1, h_p257_100.2, h_p13_5.1, h_p13_5.2, h_p263_100.1, h_p263_100.2, h_p133_50.1, h_p133_50.2, h_p269_100.1, h_p269_100.2, h_p68_25.1, h_p68_25.2, h_p11_4.1, h_p11_4.2, h_p139_50.1, h_p139_50.2, h_p281_100.1, h_p281_100.2, h_p71_25.1, h_p71_25.2, h_p287_100.1, h_p287_100.2, h_p29_10.1, h_p29_10.2, h_p293_100.1, h_p293_100.2, h_p74_25.1, h_p74_25.2, h_p299_100.1, h_p299_100.2, h_p3_1.1, h_p3_1.2]

end PSDpd
end Q3
