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

private theorem p0PieceK9D15PlusWindowSeg0_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((429 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((87 : Real) / (40 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((429 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((87 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg1_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((423 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((429 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((423 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((429 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg2_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((417 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((423 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((417 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((423 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg3_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((411 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((417 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((411 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((417 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg4_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((81 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((411 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((81 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((411 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg5_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((399 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((81 : Real) / (40 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((399 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((81 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg6_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((393 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((399 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((393 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((399 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg7_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((387 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((393 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((387 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((393 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg8_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((381 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((387 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((381 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((387 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg9_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((15 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((381 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((15 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((381 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg10_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((369 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((15 : Real) / (8 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((369 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((15 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg11_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((363 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((369 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((363 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((369 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg12_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((357 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((363 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((357 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((363 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg13_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((351 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((357 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((351 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((357 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg14_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((69 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((351 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((69 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((351 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg15_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((339 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((69 : Real) / (40 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((339 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((69 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg16_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((333 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((339 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((333 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((339 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg17_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((327 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((333 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((327 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((333 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg18_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((321 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((327 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((321 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((327 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D15PlusWindowSeg19_profile_linear :
    Real.exp ((15 : Real) / (8 : Real)) * p0PieceK9D15PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((63 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((321 : Real) / (200 : Real)) := by
  unfold p0PieceK9D15PlusWindowSegmentExpIntegral
  change Real.exp ((15 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D15PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((63 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((321 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D15PlusWindowSeg19Coeff,
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

theorem p0PieceK9D15_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((15 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((63 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((321 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((327 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((333 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((339 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((69 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((351 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((357 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((363 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((369 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((15 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((381 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((387 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((393 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((399 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((81 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((411 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((417 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((423 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((429 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((87 : Real) / (40 : Real)) := by
  rw [p0PieceK9D15_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D15PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D15MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D15PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D15PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower15_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨15, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((15 : Real) / (4 : Real)) := by
  have h_p63_40 := abs_sub_le_iff.mp p0ExpK9_p63_40_hbox
  have h_p321_200 := abs_sub_le_iff.mp p0ExpK9_p321_200_hbox
  have h_p327_200 := abs_sub_le_iff.mp p0ExpK9_p327_200_hbox
  have h_p333_200 := abs_sub_le_iff.mp p0ExpK9_p333_200_hbox
  have h_p339_200 := abs_sub_le_iff.mp p0ExpK9_p339_200_hbox
  have h_p69_40 := abs_sub_le_iff.mp p0ExpK9_p69_40_hbox
  have h_p351_200 := abs_sub_le_iff.mp p0ExpK9_p351_200_hbox
  have h_p357_200 := abs_sub_le_iff.mp p0ExpK9_p357_200_hbox
  have h_p363_200 := abs_sub_le_iff.mp p0ExpK9_p363_200_hbox
  have h_p369_200 := abs_sub_le_iff.mp p0ExpK9_p369_200_hbox
  have h_p15_8 := abs_sub_le_iff.mp p0ExpK9_p15_8_hbox
  have h_p381_200 := abs_sub_le_iff.mp p0ExpK9_p381_200_hbox
  have h_p387_200 := abs_sub_le_iff.mp p0ExpK9_p387_200_hbox
  have h_p393_200 := abs_sub_le_iff.mp p0ExpK9_p393_200_hbox
  have h_p399_200 := abs_sub_le_iff.mp p0ExpK9_p399_200_hbox
  have h_p81_40 := abs_sub_le_iff.mp p0ExpK9_p81_40_hbox
  have h_p411_200 := abs_sub_le_iff.mp p0ExpK9_p411_200_hbox
  have h_p417_200 := abs_sub_le_iff.mp p0ExpK9_p417_200_hbox
  have h_p423_200 := abs_sub_le_iff.mp p0ExpK9_p423_200_hbox
  have h_p429_200 := abs_sub_le_iff.mp p0ExpK9_p429_200_hbox
  have h_p87_40 := abs_sub_le_iff.mp p0ExpK9_p87_40_hbox
  rw [show ((15 : Real) / (4 : Real)) = ((15 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D15_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p63_40.1, h_p63_40.2, h_p321_200.1, h_p321_200.2, h_p327_200.1, h_p327_200.2, h_p333_200.1, h_p333_200.2, h_p339_200.1, h_p339_200.2, h_p69_40.1, h_p69_40.2, h_p351_200.1, h_p351_200.2, h_p357_200.1, h_p357_200.2, h_p363_200.1, h_p363_200.2, h_p369_200.1, h_p369_200.2, h_p15_8.1, h_p15_8.2, h_p381_200.1, h_p381_200.2, h_p387_200.1, h_p387_200.2, h_p393_200.1, h_p393_200.2, h_p399_200.1, h_p399_200.2, h_p81_40.1, h_p81_40.2, h_p411_200.1, h_p411_200.2, h_p417_200.1, h_p417_200.2, h_p423_200.1, h_p423_200.2, h_p429_200.1, h_p429_200.2, h_p87_40.1, h_p87_40.2]

theorem controlK9AnalyticP0_hUpper15_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((15 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨15, by norm_num⟩ : CoeffIndex23) := by
  have h_p63_40 := abs_sub_le_iff.mp p0ExpK9_p63_40_hbox
  have h_p321_200 := abs_sub_le_iff.mp p0ExpK9_p321_200_hbox
  have h_p327_200 := abs_sub_le_iff.mp p0ExpK9_p327_200_hbox
  have h_p333_200 := abs_sub_le_iff.mp p0ExpK9_p333_200_hbox
  have h_p339_200 := abs_sub_le_iff.mp p0ExpK9_p339_200_hbox
  have h_p69_40 := abs_sub_le_iff.mp p0ExpK9_p69_40_hbox
  have h_p351_200 := abs_sub_le_iff.mp p0ExpK9_p351_200_hbox
  have h_p357_200 := abs_sub_le_iff.mp p0ExpK9_p357_200_hbox
  have h_p363_200 := abs_sub_le_iff.mp p0ExpK9_p363_200_hbox
  have h_p369_200 := abs_sub_le_iff.mp p0ExpK9_p369_200_hbox
  have h_p15_8 := abs_sub_le_iff.mp p0ExpK9_p15_8_hbox
  have h_p381_200 := abs_sub_le_iff.mp p0ExpK9_p381_200_hbox
  have h_p387_200 := abs_sub_le_iff.mp p0ExpK9_p387_200_hbox
  have h_p393_200 := abs_sub_le_iff.mp p0ExpK9_p393_200_hbox
  have h_p399_200 := abs_sub_le_iff.mp p0ExpK9_p399_200_hbox
  have h_p81_40 := abs_sub_le_iff.mp p0ExpK9_p81_40_hbox
  have h_p411_200 := abs_sub_le_iff.mp p0ExpK9_p411_200_hbox
  have h_p417_200 := abs_sub_le_iff.mp p0ExpK9_p417_200_hbox
  have h_p423_200 := abs_sub_le_iff.mp p0ExpK9_p423_200_hbox
  have h_p429_200 := abs_sub_le_iff.mp p0ExpK9_p429_200_hbox
  have h_p87_40 := abs_sub_le_iff.mp p0ExpK9_p87_40_hbox
  rw [show ((15 : Real) / (4 : Real)) = ((15 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D15_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p63_40.1, h_p63_40.2, h_p321_200.1, h_p321_200.2, h_p327_200.1, h_p327_200.2, h_p333_200.1, h_p333_200.2, h_p339_200.1, h_p339_200.2, h_p69_40.1, h_p69_40.2, h_p351_200.1, h_p351_200.2, h_p357_200.1, h_p357_200.2, h_p363_200.1, h_p363_200.2, h_p369_200.1, h_p369_200.2, h_p15_8.1, h_p15_8.2, h_p381_200.1, h_p381_200.2, h_p387_200.1, h_p387_200.2, h_p393_200.1, h_p393_200.2, h_p399_200.1, h_p399_200.2, h_p81_40.1, h_p81_40.2, h_p411_200.1, h_p411_200.2, h_p417_200.1, h_p417_200.2, h_p423_200.1, h_p423_200.2, h_p429_200.1, h_p429_200.2, h_p87_40.1, h_p87_40.2]

private theorem p0PieceK9D16PlusWindowSeg0_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((227 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (10 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((227 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg1_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((56 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((227 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((56 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((227 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg2_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((221 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((56 : Real) / (25 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((221 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((56 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg3_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((221 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((221 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg4_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (50 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((109 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg5_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((53 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((43 : Real) / (20 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((53 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((43 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg6_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((209 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((53 : Real) / (25 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((209 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((53 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg7_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((103 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((209 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((103 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((209 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg8_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((203 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((103 : Real) / (50 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((203 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((103 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg9_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((203 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((203 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg10_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((197 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((2 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((197 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg11_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((97 : Real) / (50 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((197 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((97 : Real) / (50 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((197 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg12_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((191 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((97 : Real) / (50 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((191 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((97 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg13_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((47 : Real) / (25 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((191 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((47 : Real) / (25 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((191 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg14_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((37 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((47 : Real) / (25 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((37 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((47 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg15_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (50 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((37 : Real) / (20 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (50 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((37 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg16_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((179 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (50 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((179 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((91 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg17_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((44 : Real) / (25 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((179 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((44 : Real) / (25 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((179 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg18_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((173 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((44 : Real) / (25 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((173 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((44 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D16PlusWindowSeg19_profile_linear :
    Real.exp ((2 : Real)) * p0PieceK9D16PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (10 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((173 : Real) / (100 : Real)) := by
  unfold p0PieceK9D16PlusWindowSegmentExpIntegral
  change Real.exp ((2 : Real)) * expPolyIntegral p0PieceK9D16PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (10 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((173 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D16PlusWindowSeg19Coeff,
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

theorem p0PieceK9D16_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (10 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((173 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((44 : Real) / (25 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((179 : Real) / (100 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((91 : Real) / (50 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((37 : Real) / (20 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((47 : Real) / (25 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((191 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((97 : Real) / (50 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((197 : Real) / (100 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((2 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((203 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((103 : Real) / (50 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((209 : Real) / (100 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((53 : Real) / (25 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((43 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((109 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((221 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((56 : Real) / (25 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((227 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (10 : Real)) := by
  rw [p0PieceK9D16_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D16PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D16MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D16PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D16PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower16_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨16, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((16 : Real) / (4 : Real)) := by
  have h_p17_10 := abs_sub_le_iff.mp p0ExpK9_p17_10_hbox
  have h_p173_100 := abs_sub_le_iff.mp p0ExpK9_p173_100_hbox
  have h_p44_25 := abs_sub_le_iff.mp p0ExpK9_p44_25_hbox
  have h_p179_100 := abs_sub_le_iff.mp p0ExpK9_p179_100_hbox
  have h_p91_50 := abs_sub_le_iff.mp p0ExpK9_p91_50_hbox
  have h_p37_20 := abs_sub_le_iff.mp p0ExpK9_p37_20_hbox
  have h_p47_25 := abs_sub_le_iff.mp p0ExpK9_p47_25_hbox
  have h_p191_100 := abs_sub_le_iff.mp p0ExpK9_p191_100_hbox
  have h_p97_50 := abs_sub_le_iff.mp p0ExpK9_p97_50_hbox
  have h_p197_100 := abs_sub_le_iff.mp p0ExpK9_p197_100_hbox
  have h_p2_1 := abs_sub_le_iff.mp p0ExpK9_p2_1_hbox
  have h_p203_100 := abs_sub_le_iff.mp p0ExpK9_p203_100_hbox
  have h_p103_50 := abs_sub_le_iff.mp p0ExpK9_p103_50_hbox
  have h_p209_100 := abs_sub_le_iff.mp p0ExpK9_p209_100_hbox
  have h_p53_25 := abs_sub_le_iff.mp p0ExpK9_p53_25_hbox
  have h_p43_20 := abs_sub_le_iff.mp p0ExpK9_p43_20_hbox
  have h_p109_50 := abs_sub_le_iff.mp p0ExpK9_p109_50_hbox
  have h_p221_100 := abs_sub_le_iff.mp p0ExpK9_p221_100_hbox
  have h_p56_25 := abs_sub_le_iff.mp p0ExpK9_p56_25_hbox
  have h_p227_100 := abs_sub_le_iff.mp p0ExpK9_p227_100_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK9_p23_10_hbox
  rw [show ((16 : Real) / (4 : Real)) = ((4 : Real)) by norm_num]
  rw [p0PieceK9D16_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p17_10.1, h_p17_10.2, h_p173_100.1, h_p173_100.2, h_p44_25.1, h_p44_25.2, h_p179_100.1, h_p179_100.2, h_p91_50.1, h_p91_50.2, h_p37_20.1, h_p37_20.2, h_p47_25.1, h_p47_25.2, h_p191_100.1, h_p191_100.2, h_p97_50.1, h_p97_50.2, h_p197_100.1, h_p197_100.2, h_p2_1.1, h_p2_1.2, h_p203_100.1, h_p203_100.2, h_p103_50.1, h_p103_50.2, h_p209_100.1, h_p209_100.2, h_p53_25.1, h_p53_25.2, h_p43_20.1, h_p43_20.2, h_p109_50.1, h_p109_50.2, h_p221_100.1, h_p221_100.2, h_p56_25.1, h_p56_25.2, h_p227_100.1, h_p227_100.2, h_p23_10.1, h_p23_10.2]

theorem controlK9AnalyticP0_hUpper16_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((16 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨16, by norm_num⟩ : CoeffIndex23) := by
  have h_p17_10 := abs_sub_le_iff.mp p0ExpK9_p17_10_hbox
  have h_p173_100 := abs_sub_le_iff.mp p0ExpK9_p173_100_hbox
  have h_p44_25 := abs_sub_le_iff.mp p0ExpK9_p44_25_hbox
  have h_p179_100 := abs_sub_le_iff.mp p0ExpK9_p179_100_hbox
  have h_p91_50 := abs_sub_le_iff.mp p0ExpK9_p91_50_hbox
  have h_p37_20 := abs_sub_le_iff.mp p0ExpK9_p37_20_hbox
  have h_p47_25 := abs_sub_le_iff.mp p0ExpK9_p47_25_hbox
  have h_p191_100 := abs_sub_le_iff.mp p0ExpK9_p191_100_hbox
  have h_p97_50 := abs_sub_le_iff.mp p0ExpK9_p97_50_hbox
  have h_p197_100 := abs_sub_le_iff.mp p0ExpK9_p197_100_hbox
  have h_p2_1 := abs_sub_le_iff.mp p0ExpK9_p2_1_hbox
  have h_p203_100 := abs_sub_le_iff.mp p0ExpK9_p203_100_hbox
  have h_p103_50 := abs_sub_le_iff.mp p0ExpK9_p103_50_hbox
  have h_p209_100 := abs_sub_le_iff.mp p0ExpK9_p209_100_hbox
  have h_p53_25 := abs_sub_le_iff.mp p0ExpK9_p53_25_hbox
  have h_p43_20 := abs_sub_le_iff.mp p0ExpK9_p43_20_hbox
  have h_p109_50 := abs_sub_le_iff.mp p0ExpK9_p109_50_hbox
  have h_p221_100 := abs_sub_le_iff.mp p0ExpK9_p221_100_hbox
  have h_p56_25 := abs_sub_le_iff.mp p0ExpK9_p56_25_hbox
  have h_p227_100 := abs_sub_le_iff.mp p0ExpK9_p227_100_hbox
  have h_p23_10 := abs_sub_le_iff.mp p0ExpK9_p23_10_hbox
  rw [show ((16 : Real) / (4 : Real)) = ((4 : Real)) by norm_num]
  rw [p0PieceK9D16_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p17_10.1, h_p17_10.2, h_p173_100.1, h_p173_100.2, h_p44_25.1, h_p44_25.2, h_p179_100.1, h_p179_100.2, h_p91_50.1, h_p91_50.2, h_p37_20.1, h_p37_20.2, h_p47_25.1, h_p47_25.2, h_p191_100.1, h_p191_100.2, h_p97_50.1, h_p97_50.2, h_p197_100.1, h_p197_100.2, h_p2_1.1, h_p2_1.2, h_p203_100.1, h_p203_100.2, h_p103_50.1, h_p103_50.2, h_p209_100.1, h_p209_100.2, h_p53_25.1, h_p53_25.2, h_p43_20.1, h_p43_20.2, h_p109_50.1, h_p109_50.2, h_p221_100.1, h_p221_100.2, h_p56_25.1, h_p56_25.2, h_p227_100.1, h_p227_100.2, h_p23_10.1, h_p23_10.2]

end PSDpd
end Q3
