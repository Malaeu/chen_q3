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

private theorem p0PieceK9D19PlusWindowSeg0_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((529 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((107 : Real) / (40 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((529 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((107 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg1_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((523 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((529 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((523 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((529 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg2_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((517 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((523 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((517 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((523 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg3_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((511 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((517 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((511 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((517 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg4_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((511 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((511 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg5_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((499 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((101 : Real) / (40 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((499 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((101 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg6_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((493 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((499 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((493 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((499 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg7_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((487 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((493 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((487 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((493 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg8_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((481 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((487 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((481 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((487 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg9_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((481 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((481 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg10_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((469 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (8 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((469 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg11_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((463 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((469 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((463 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((469 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg12_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((457 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((463 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((457 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((463 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg13_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((451 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((457 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((451 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((457 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg14_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((451 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((451 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg15_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((439 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((89 : Real) / (40 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((439 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((89 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg16_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((433 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((439 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((433 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((439 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg17_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((427 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((433 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((427 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((433 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg18_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((421 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((427 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((421 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((427 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D19PlusWindowSeg19_profile_linear :
    Real.exp ((19 : Real) / (8 : Real)) * p0PieceK9D19PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((421 : Real) / (200 : Real)) := by
  unfold p0PieceK9D19PlusWindowSegmentExpIntegral
  change Real.exp ((19 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D19PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((421 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D19PlusWindowSeg19Coeff,
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

theorem p0PieceK9D19_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((83 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((421 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((427 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((433 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((439 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((89 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((451 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((457 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((463 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((469 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((481 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((487 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((493 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((499 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((101 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((511 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((517 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((523 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((529 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((107 : Real) / (40 : Real)) := by
  rw [p0PieceK9D19_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D19PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D19MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D19PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D19PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower19_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨19, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) := by
  have h_p83_40 := abs_sub_le_iff.mp p0ExpK9_p83_40_hbox
  have h_p421_200 := abs_sub_le_iff.mp p0ExpK9_p421_200_hbox
  have h_p427_200 := abs_sub_le_iff.mp p0ExpK9_p427_200_hbox
  have h_p433_200 := abs_sub_le_iff.mp p0ExpK9_p433_200_hbox
  have h_p439_200 := abs_sub_le_iff.mp p0ExpK9_p439_200_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK9_p89_40_hbox
  have h_p451_200 := abs_sub_le_iff.mp p0ExpK9_p451_200_hbox
  have h_p457_200 := abs_sub_le_iff.mp p0ExpK9_p457_200_hbox
  have h_p463_200 := abs_sub_le_iff.mp p0ExpK9_p463_200_hbox
  have h_p469_200 := abs_sub_le_iff.mp p0ExpK9_p469_200_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK9_p19_8_hbox
  have h_p481_200 := abs_sub_le_iff.mp p0ExpK9_p481_200_hbox
  have h_p487_200 := abs_sub_le_iff.mp p0ExpK9_p487_200_hbox
  have h_p493_200 := abs_sub_le_iff.mp p0ExpK9_p493_200_hbox
  have h_p499_200 := abs_sub_le_iff.mp p0ExpK9_p499_200_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK9_p101_40_hbox
  have h_p511_200 := abs_sub_le_iff.mp p0ExpK9_p511_200_hbox
  have h_p517_200 := abs_sub_le_iff.mp p0ExpK9_p517_200_hbox
  have h_p523_200 := abs_sub_le_iff.mp p0ExpK9_p523_200_hbox
  have h_p529_200 := abs_sub_le_iff.mp p0ExpK9_p529_200_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK9_p107_40_hbox
  rw [show ((19 : Real) / (4 : Real)) = ((19 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D19_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p83_40.1, h_p83_40.2, h_p421_200.1, h_p421_200.2, h_p427_200.1, h_p427_200.2, h_p433_200.1, h_p433_200.2, h_p439_200.1, h_p439_200.2, h_p89_40.1, h_p89_40.2, h_p451_200.1, h_p451_200.2, h_p457_200.1, h_p457_200.2, h_p463_200.1, h_p463_200.2, h_p469_200.1, h_p469_200.2, h_p19_8.1, h_p19_8.2, h_p481_200.1, h_p481_200.2, h_p487_200.1, h_p487_200.2, h_p493_200.1, h_p493_200.2, h_p499_200.1, h_p499_200.2, h_p101_40.1, h_p101_40.2, h_p511_200.1, h_p511_200.2, h_p517_200.1, h_p517_200.2, h_p523_200.1, h_p523_200.2, h_p529_200.1, h_p529_200.2, h_p107_40.1, h_p107_40.2]

theorem controlK9AnalyticP0_hUpper19_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((19 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨19, by norm_num⟩ : CoeffIndex23) := by
  have h_p83_40 := abs_sub_le_iff.mp p0ExpK9_p83_40_hbox
  have h_p421_200 := abs_sub_le_iff.mp p0ExpK9_p421_200_hbox
  have h_p427_200 := abs_sub_le_iff.mp p0ExpK9_p427_200_hbox
  have h_p433_200 := abs_sub_le_iff.mp p0ExpK9_p433_200_hbox
  have h_p439_200 := abs_sub_le_iff.mp p0ExpK9_p439_200_hbox
  have h_p89_40 := abs_sub_le_iff.mp p0ExpK9_p89_40_hbox
  have h_p451_200 := abs_sub_le_iff.mp p0ExpK9_p451_200_hbox
  have h_p457_200 := abs_sub_le_iff.mp p0ExpK9_p457_200_hbox
  have h_p463_200 := abs_sub_le_iff.mp p0ExpK9_p463_200_hbox
  have h_p469_200 := abs_sub_le_iff.mp p0ExpK9_p469_200_hbox
  have h_p19_8 := abs_sub_le_iff.mp p0ExpK9_p19_8_hbox
  have h_p481_200 := abs_sub_le_iff.mp p0ExpK9_p481_200_hbox
  have h_p487_200 := abs_sub_le_iff.mp p0ExpK9_p487_200_hbox
  have h_p493_200 := abs_sub_le_iff.mp p0ExpK9_p493_200_hbox
  have h_p499_200 := abs_sub_le_iff.mp p0ExpK9_p499_200_hbox
  have h_p101_40 := abs_sub_le_iff.mp p0ExpK9_p101_40_hbox
  have h_p511_200 := abs_sub_le_iff.mp p0ExpK9_p511_200_hbox
  have h_p517_200 := abs_sub_le_iff.mp p0ExpK9_p517_200_hbox
  have h_p523_200 := abs_sub_le_iff.mp p0ExpK9_p523_200_hbox
  have h_p529_200 := abs_sub_le_iff.mp p0ExpK9_p529_200_hbox
  have h_p107_40 := abs_sub_le_iff.mp p0ExpK9_p107_40_hbox
  rw [show ((19 : Real) / (4 : Real)) = ((19 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D19_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p83_40.1, h_p83_40.2, h_p421_200.1, h_p421_200.2, h_p427_200.1, h_p427_200.2, h_p433_200.1, h_p433_200.2, h_p439_200.1, h_p439_200.2, h_p89_40.1, h_p89_40.2, h_p451_200.1, h_p451_200.2, h_p457_200.1, h_p457_200.2, h_p463_200.1, h_p463_200.2, h_p469_200.1, h_p469_200.2, h_p19_8.1, h_p19_8.2, h_p481_200.1, h_p481_200.2, h_p487_200.1, h_p487_200.2, h_p493_200.1, h_p493_200.2, h_p499_200.1, h_p499_200.2, h_p101_40.1, h_p101_40.2, h_p511_200.1, h_p511_200.2, h_p517_200.1, h_p517_200.2, h_p523_200.1, h_p523_200.2, h_p529_200.1, h_p529_200.2, h_p107_40.1, h_p107_40.2]

private theorem p0PieceK9D20PlusWindowSeg0_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((277 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((14 : Real) / (5 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((277 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((14 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg1_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((137 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((277 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((137 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((277 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg2_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((271 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (50 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((271 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg3_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((271 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((271 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg4_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (25 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg5_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((131 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((53 : Real) / (20 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((131 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((53 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg6_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((259 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((131 : Real) / (50 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((259 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((131 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg7_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((64 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((259 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((64 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((259 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg8_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((253 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((64 : Real) / (25 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((253 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((64 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg9_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((253 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((253 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg10_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((247 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (2 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((247 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg11_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((61 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((247 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((61 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((247 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg12_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((241 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (25 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((241 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg13_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((119 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((241 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((119 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((241 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg14_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((119 : Real) / (50 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((119 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg15_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((58 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((47 : Real) / (20 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((58 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((47 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg16_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((229 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((58 : Real) / (25 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((229 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((58 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg17_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((113 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((229 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((113 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((229 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg18_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((223 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((113 : Real) / (50 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((223 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((113 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D20PlusWindowSeg19_profile_linear :
    Real.exp ((5 : Real) / (2 : Real)) * p0PieceK9D20PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((223 : Real) / (100 : Real)) := by
  unfold p0PieceK9D20PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D20PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((223 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D20PlusWindowSeg19Coeff,
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

theorem p0PieceK9D20_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (5 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((223 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((113 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((229 : Real) / (100 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((58 : Real) / (25 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((47 : Real) / (20 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((119 : Real) / (50 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((241 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((61 : Real) / (25 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((247 : Real) / (100 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (2 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((253 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((64 : Real) / (25 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((259 : Real) / (100 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((131 : Real) / (50 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((53 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((67 : Real) / (25 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((271 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((137 : Real) / (50 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((277 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((14 : Real) / (5 : Real)) := by
  rw [p0PieceK9D20_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D20PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D20MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D20PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D20PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower20_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨20, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((20 : Real) / (4 : Real)) := by
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK9_p11_5_hbox
  have h_p223_100 := abs_sub_le_iff.mp p0ExpK9_p223_100_hbox
  have h_p113_50 := abs_sub_le_iff.mp p0ExpK9_p113_50_hbox
  have h_p229_100 := abs_sub_le_iff.mp p0ExpK9_p229_100_hbox
  have h_p58_25 := abs_sub_le_iff.mp p0ExpK9_p58_25_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK9_p47_20_hbox
  have h_p119_50 := abs_sub_le_iff.mp p0ExpK9_p119_50_hbox
  have h_p241_100 := abs_sub_le_iff.mp p0ExpK9_p241_100_hbox
  have h_p61_25 := abs_sub_le_iff.mp p0ExpK9_p61_25_hbox
  have h_p247_100 := abs_sub_le_iff.mp p0ExpK9_p247_100_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK9_p5_2_hbox
  have h_p253_100 := abs_sub_le_iff.mp p0ExpK9_p253_100_hbox
  have h_p64_25 := abs_sub_le_iff.mp p0ExpK9_p64_25_hbox
  have h_p259_100 := abs_sub_le_iff.mp p0ExpK9_p259_100_hbox
  have h_p131_50 := abs_sub_le_iff.mp p0ExpK9_p131_50_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK9_p53_20_hbox
  have h_p67_25 := abs_sub_le_iff.mp p0ExpK9_p67_25_hbox
  have h_p271_100 := abs_sub_le_iff.mp p0ExpK9_p271_100_hbox
  have h_p137_50 := abs_sub_le_iff.mp p0ExpK9_p137_50_hbox
  have h_p277_100 := abs_sub_le_iff.mp p0ExpK9_p277_100_hbox
  have h_p14_5 := abs_sub_le_iff.mp p0ExpK9_p14_5_hbox
  rw [show ((20 : Real) / (4 : Real)) = ((5 : Real)) by norm_num]
  rw [p0PieceK9D20_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p11_5.1, h_p11_5.2, h_p223_100.1, h_p223_100.2, h_p113_50.1, h_p113_50.2, h_p229_100.1, h_p229_100.2, h_p58_25.1, h_p58_25.2, h_p47_20.1, h_p47_20.2, h_p119_50.1, h_p119_50.2, h_p241_100.1, h_p241_100.2, h_p61_25.1, h_p61_25.2, h_p247_100.1, h_p247_100.2, h_p5_2.1, h_p5_2.2, h_p253_100.1, h_p253_100.2, h_p64_25.1, h_p64_25.2, h_p259_100.1, h_p259_100.2, h_p131_50.1, h_p131_50.2, h_p53_20.1, h_p53_20.2, h_p67_25.1, h_p67_25.2, h_p271_100.1, h_p271_100.2, h_p137_50.1, h_p137_50.2, h_p277_100.1, h_p277_100.2, h_p14_5.1, h_p14_5.2]

theorem controlK9AnalyticP0_hUpper20_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((20 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨20, by norm_num⟩ : CoeffIndex23) := by
  have h_p11_5 := abs_sub_le_iff.mp p0ExpK9_p11_5_hbox
  have h_p223_100 := abs_sub_le_iff.mp p0ExpK9_p223_100_hbox
  have h_p113_50 := abs_sub_le_iff.mp p0ExpK9_p113_50_hbox
  have h_p229_100 := abs_sub_le_iff.mp p0ExpK9_p229_100_hbox
  have h_p58_25 := abs_sub_le_iff.mp p0ExpK9_p58_25_hbox
  have h_p47_20 := abs_sub_le_iff.mp p0ExpK9_p47_20_hbox
  have h_p119_50 := abs_sub_le_iff.mp p0ExpK9_p119_50_hbox
  have h_p241_100 := abs_sub_le_iff.mp p0ExpK9_p241_100_hbox
  have h_p61_25 := abs_sub_le_iff.mp p0ExpK9_p61_25_hbox
  have h_p247_100 := abs_sub_le_iff.mp p0ExpK9_p247_100_hbox
  have h_p5_2 := abs_sub_le_iff.mp p0ExpK9_p5_2_hbox
  have h_p253_100 := abs_sub_le_iff.mp p0ExpK9_p253_100_hbox
  have h_p64_25 := abs_sub_le_iff.mp p0ExpK9_p64_25_hbox
  have h_p259_100 := abs_sub_le_iff.mp p0ExpK9_p259_100_hbox
  have h_p131_50 := abs_sub_le_iff.mp p0ExpK9_p131_50_hbox
  have h_p53_20 := abs_sub_le_iff.mp p0ExpK9_p53_20_hbox
  have h_p67_25 := abs_sub_le_iff.mp p0ExpK9_p67_25_hbox
  have h_p271_100 := abs_sub_le_iff.mp p0ExpK9_p271_100_hbox
  have h_p137_50 := abs_sub_le_iff.mp p0ExpK9_p137_50_hbox
  have h_p277_100 := abs_sub_le_iff.mp p0ExpK9_p277_100_hbox
  have h_p14_5 := abs_sub_le_iff.mp p0ExpK9_p14_5_hbox
  rw [show ((20 : Real) / (4 : Real)) = ((5 : Real)) by norm_num]
  rw [p0PieceK9D20_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p11_5.1, h_p11_5.2, h_p223_100.1, h_p223_100.2, h_p113_50.1, h_p113_50.2, h_p229_100.1, h_p229_100.2, h_p58_25.1, h_p58_25.2, h_p47_20.1, h_p47_20.2, h_p119_50.1, h_p119_50.2, h_p241_100.1, h_p241_100.2, h_p61_25.1, h_p61_25.2, h_p247_100.1, h_p247_100.2, h_p5_2.1, h_p5_2.2, h_p253_100.1, h_p253_100.2, h_p64_25.1, h_p64_25.2, h_p259_100.1, h_p259_100.2, h_p131_50.1, h_p131_50.2, h_p53_20.1, h_p53_20.2, h_p67_25.1, h_p67_25.2, h_p271_100.1, h_p271_100.2, h_p137_50.1, h_p137_50.2, h_p277_100.1, h_p277_100.2, h_p14_5.1, h_p14_5.2]

end PSDpd
end Q3
