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

private theorem p0PieceK9D17PlusWindowSeg0_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((479 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((97 : Real) / (40 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((479 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((97 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg1_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((473 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((479 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((473 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((479 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg2_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((467 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((473 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((467 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((473 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg3_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((461 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((467 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((461 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((467 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg4_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((461 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((461 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg5_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((449 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((91 : Real) / (40 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((449 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((91 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg6_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((443 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((449 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((443 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((449 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg7_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((437 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((443 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((437 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((443 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg8_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((431 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((437 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((431 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((437 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg9_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((431 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((431 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg10_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((419 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (8 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((419 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg11_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((413 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((419 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((413 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((419 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg12_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((407 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((413 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((407 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((413 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg13_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((401 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((407 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((401 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((407 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg14_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((79 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((401 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((79 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((401 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg15_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((389 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((79 : Real) / (40 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((389 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((79 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg16_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((383 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((389 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((383 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((389 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg17_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((377 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((383 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((377 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((383 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg18_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((371 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((377 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((371 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((377 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D17PlusWindowSeg19_profile_linear :
    Real.exp ((17 : Real) / (8 : Real)) * p0PieceK9D17PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((73 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((371 : Real) / (200 : Real)) := by
  unfold p0PieceK9D17PlusWindowSegmentExpIntegral
  change Real.exp ((17 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D17PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((73 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((371 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D17PlusWindowSeg19Coeff,
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

theorem p0PieceK9D17_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((17 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((73 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((371 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((377 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((383 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((389 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((79 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((401 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((407 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((413 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((419 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((431 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((437 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((443 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((449 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((91 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((461 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((467 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((473 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((479 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((97 : Real) / (40 : Real)) := by
  rw [p0PieceK9D17_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D17PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D17MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D17PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D17PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower17_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨17, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((17 : Real) / (4 : Real)) := by
  have h_p73_40 := abs_sub_le_iff.mp p0ExpK9_p73_40_hbox
  have h_p371_200 := abs_sub_le_iff.mp p0ExpK9_p371_200_hbox
  have h_p377_200 := abs_sub_le_iff.mp p0ExpK9_p377_200_hbox
  have h_p383_200 := abs_sub_le_iff.mp p0ExpK9_p383_200_hbox
  have h_p389_200 := abs_sub_le_iff.mp p0ExpK9_p389_200_hbox
  have h_p79_40 := abs_sub_le_iff.mp p0ExpK9_p79_40_hbox
  have h_p401_200 := abs_sub_le_iff.mp p0ExpK9_p401_200_hbox
  have h_p407_200 := abs_sub_le_iff.mp p0ExpK9_p407_200_hbox
  have h_p413_200 := abs_sub_le_iff.mp p0ExpK9_p413_200_hbox
  have h_p419_200 := abs_sub_le_iff.mp p0ExpK9_p419_200_hbox
  have h_p17_8 := abs_sub_le_iff.mp p0ExpK9_p17_8_hbox
  have h_p431_200 := abs_sub_le_iff.mp p0ExpK9_p431_200_hbox
  have h_p437_200 := abs_sub_le_iff.mp p0ExpK9_p437_200_hbox
  have h_p443_200 := abs_sub_le_iff.mp p0ExpK9_p443_200_hbox
  have h_p449_200 := abs_sub_le_iff.mp p0ExpK9_p449_200_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK9_p91_40_hbox
  have h_p461_200 := abs_sub_le_iff.mp p0ExpK9_p461_200_hbox
  have h_p467_200 := abs_sub_le_iff.mp p0ExpK9_p467_200_hbox
  have h_p473_200 := abs_sub_le_iff.mp p0ExpK9_p473_200_hbox
  have h_p479_200 := abs_sub_le_iff.mp p0ExpK9_p479_200_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK9_p97_40_hbox
  rw [show ((17 : Real) / (4 : Real)) = ((17 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D17_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p73_40.1, h_p73_40.2, h_p371_200.1, h_p371_200.2, h_p377_200.1, h_p377_200.2, h_p383_200.1, h_p383_200.2, h_p389_200.1, h_p389_200.2, h_p79_40.1, h_p79_40.2, h_p401_200.1, h_p401_200.2, h_p407_200.1, h_p407_200.2, h_p413_200.1, h_p413_200.2, h_p419_200.1, h_p419_200.2, h_p17_8.1, h_p17_8.2, h_p431_200.1, h_p431_200.2, h_p437_200.1, h_p437_200.2, h_p443_200.1, h_p443_200.2, h_p449_200.1, h_p449_200.2, h_p91_40.1, h_p91_40.2, h_p461_200.1, h_p461_200.2, h_p467_200.1, h_p467_200.2, h_p473_200.1, h_p473_200.2, h_p479_200.1, h_p479_200.2, h_p97_40.1, h_p97_40.2]

theorem controlK9AnalyticP0_hUpper17_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((17 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨17, by norm_num⟩ : CoeffIndex23) := by
  have h_p73_40 := abs_sub_le_iff.mp p0ExpK9_p73_40_hbox
  have h_p371_200 := abs_sub_le_iff.mp p0ExpK9_p371_200_hbox
  have h_p377_200 := abs_sub_le_iff.mp p0ExpK9_p377_200_hbox
  have h_p383_200 := abs_sub_le_iff.mp p0ExpK9_p383_200_hbox
  have h_p389_200 := abs_sub_le_iff.mp p0ExpK9_p389_200_hbox
  have h_p79_40 := abs_sub_le_iff.mp p0ExpK9_p79_40_hbox
  have h_p401_200 := abs_sub_le_iff.mp p0ExpK9_p401_200_hbox
  have h_p407_200 := abs_sub_le_iff.mp p0ExpK9_p407_200_hbox
  have h_p413_200 := abs_sub_le_iff.mp p0ExpK9_p413_200_hbox
  have h_p419_200 := abs_sub_le_iff.mp p0ExpK9_p419_200_hbox
  have h_p17_8 := abs_sub_le_iff.mp p0ExpK9_p17_8_hbox
  have h_p431_200 := abs_sub_le_iff.mp p0ExpK9_p431_200_hbox
  have h_p437_200 := abs_sub_le_iff.mp p0ExpK9_p437_200_hbox
  have h_p443_200 := abs_sub_le_iff.mp p0ExpK9_p443_200_hbox
  have h_p449_200 := abs_sub_le_iff.mp p0ExpK9_p449_200_hbox
  have h_p91_40 := abs_sub_le_iff.mp p0ExpK9_p91_40_hbox
  have h_p461_200 := abs_sub_le_iff.mp p0ExpK9_p461_200_hbox
  have h_p467_200 := abs_sub_le_iff.mp p0ExpK9_p467_200_hbox
  have h_p473_200 := abs_sub_le_iff.mp p0ExpK9_p473_200_hbox
  have h_p479_200 := abs_sub_le_iff.mp p0ExpK9_p479_200_hbox
  have h_p97_40 := abs_sub_le_iff.mp p0ExpK9_p97_40_hbox
  rw [show ((17 : Real) / (4 : Real)) = ((17 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D17_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p73_40.1, h_p73_40.2, h_p371_200.1, h_p371_200.2, h_p377_200.1, h_p377_200.2, h_p383_200.1, h_p383_200.2, h_p389_200.1, h_p389_200.2, h_p79_40.1, h_p79_40.2, h_p401_200.1, h_p401_200.2, h_p407_200.1, h_p407_200.2, h_p413_200.1, h_p413_200.2, h_p419_200.1, h_p419_200.2, h_p17_8.1, h_p17_8.2, h_p431_200.1, h_p431_200.2, h_p437_200.1, h_p437_200.2, h_p443_200.1, h_p443_200.2, h_p449_200.1, h_p449_200.2, h_p91_40.1, h_p91_40.2, h_p461_200.1, h_p461_200.2, h_p467_200.1, h_p467_200.2, h_p473_200.1, h_p473_200.2, h_p479_200.1, h_p479_200.2, h_p97_40.1, h_p97_40.2]

private theorem p0PieceK9D18PlusWindowSeg0_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((63 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((51 : Real) / (20 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((63 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((51 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg1_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((249 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((63 : Real) / (25 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((249 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((63 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg2_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((123 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((249 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((123 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((249 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg3_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((123 : Real) / (50 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((123 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg4_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg5_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((237 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((12 : Real) / (5 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((237 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((12 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg6_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((117 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((237 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((117 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((237 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg7_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((231 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((117 : Real) / (50 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((231 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((117 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg8_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((57 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((231 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((57 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((231 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg9_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((57 : Real) / (25 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((57 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg10_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((111 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (4 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((111 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg11_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((219 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((111 : Real) / (50 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((219 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((111 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg12_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((54 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((219 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((54 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((219 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg13_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((213 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((54 : Real) / (25 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((213 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((54 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg14_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((213 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((213 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg15_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (10 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg16_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((51 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((51 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg17_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((201 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((51 : Real) / (25 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((201 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((51 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg18_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((99 : Real) / (50 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((201 : Real) / (100 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((99 : Real) / (50 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((201 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D18PlusWindowSeg19_profile_linear :
    Real.exp ((9 : Real) / (4 : Real)) * p0PieceK9D18PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((39 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((99 : Real) / (50 : Real)) := by
  unfold p0PieceK9D18PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D18PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((39 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((99 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D18PlusWindowSeg19Coeff,
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

theorem p0PieceK9D18_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((9 : Real) / (2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((39 : Real) / (20 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((99 : Real) / (50 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((201 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((51 : Real) / (25 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((207 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (10 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((213 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((54 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((219 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((111 : Real) / (50 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((57 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((231 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((117 : Real) / (50 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((237 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((12 : Real) / (5 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((243 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((123 : Real) / (50 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((249 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((63 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((51 : Real) / (20 : Real)) := by
  rw [p0PieceK9D18_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D18PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D18MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D18PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D18PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower18_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨18, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((18 : Real) / (4 : Real)) := by
  have h_p39_20 := abs_sub_le_iff.mp p0ExpK9_p39_20_hbox
  have h_p99_50 := abs_sub_le_iff.mp p0ExpK9_p99_50_hbox
  have h_p201_100 := abs_sub_le_iff.mp p0ExpK9_p201_100_hbox
  have h_p51_25 := abs_sub_le_iff.mp p0ExpK9_p51_25_hbox
  have h_p207_100 := abs_sub_le_iff.mp p0ExpK9_p207_100_hbox
  have h_p21_10 := abs_sub_le_iff.mp p0ExpK9_p21_10_hbox
  have h_p213_100 := abs_sub_le_iff.mp p0ExpK9_p213_100_hbox
  have h_p54_25 := abs_sub_le_iff.mp p0ExpK9_p54_25_hbox
  have h_p219_100 := abs_sub_le_iff.mp p0ExpK9_p219_100_hbox
  have h_p111_50 := abs_sub_le_iff.mp p0ExpK9_p111_50_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK9_p9_4_hbox
  have h_p57_25 := abs_sub_le_iff.mp p0ExpK9_p57_25_hbox
  have h_p231_100 := abs_sub_le_iff.mp p0ExpK9_p231_100_hbox
  have h_p117_50 := abs_sub_le_iff.mp p0ExpK9_p117_50_hbox
  have h_p237_100 := abs_sub_le_iff.mp p0ExpK9_p237_100_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK9_p12_5_hbox
  have h_p243_100 := abs_sub_le_iff.mp p0ExpK9_p243_100_hbox
  have h_p123_50 := abs_sub_le_iff.mp p0ExpK9_p123_50_hbox
  have h_p249_100 := abs_sub_le_iff.mp p0ExpK9_p249_100_hbox
  have h_p63_25 := abs_sub_le_iff.mp p0ExpK9_p63_25_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK9_p51_20_hbox
  rw [show ((18 : Real) / (4 : Real)) = ((9 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D18_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p39_20.1, h_p39_20.2, h_p99_50.1, h_p99_50.2, h_p201_100.1, h_p201_100.2, h_p51_25.1, h_p51_25.2, h_p207_100.1, h_p207_100.2, h_p21_10.1, h_p21_10.2, h_p213_100.1, h_p213_100.2, h_p54_25.1, h_p54_25.2, h_p219_100.1, h_p219_100.2, h_p111_50.1, h_p111_50.2, h_p9_4.1, h_p9_4.2, h_p57_25.1, h_p57_25.2, h_p231_100.1, h_p231_100.2, h_p117_50.1, h_p117_50.2, h_p237_100.1, h_p237_100.2, h_p12_5.1, h_p12_5.2, h_p243_100.1, h_p243_100.2, h_p123_50.1, h_p123_50.2, h_p249_100.1, h_p249_100.2, h_p63_25.1, h_p63_25.2, h_p51_20.1, h_p51_20.2]

theorem controlK9AnalyticP0_hUpper18_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((18 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨18, by norm_num⟩ : CoeffIndex23) := by
  have h_p39_20 := abs_sub_le_iff.mp p0ExpK9_p39_20_hbox
  have h_p99_50 := abs_sub_le_iff.mp p0ExpK9_p99_50_hbox
  have h_p201_100 := abs_sub_le_iff.mp p0ExpK9_p201_100_hbox
  have h_p51_25 := abs_sub_le_iff.mp p0ExpK9_p51_25_hbox
  have h_p207_100 := abs_sub_le_iff.mp p0ExpK9_p207_100_hbox
  have h_p21_10 := abs_sub_le_iff.mp p0ExpK9_p21_10_hbox
  have h_p213_100 := abs_sub_le_iff.mp p0ExpK9_p213_100_hbox
  have h_p54_25 := abs_sub_le_iff.mp p0ExpK9_p54_25_hbox
  have h_p219_100 := abs_sub_le_iff.mp p0ExpK9_p219_100_hbox
  have h_p111_50 := abs_sub_le_iff.mp p0ExpK9_p111_50_hbox
  have h_p9_4 := abs_sub_le_iff.mp p0ExpK9_p9_4_hbox
  have h_p57_25 := abs_sub_le_iff.mp p0ExpK9_p57_25_hbox
  have h_p231_100 := abs_sub_le_iff.mp p0ExpK9_p231_100_hbox
  have h_p117_50 := abs_sub_le_iff.mp p0ExpK9_p117_50_hbox
  have h_p237_100 := abs_sub_le_iff.mp p0ExpK9_p237_100_hbox
  have h_p12_5 := abs_sub_le_iff.mp p0ExpK9_p12_5_hbox
  have h_p243_100 := abs_sub_le_iff.mp p0ExpK9_p243_100_hbox
  have h_p123_50 := abs_sub_le_iff.mp p0ExpK9_p123_50_hbox
  have h_p249_100 := abs_sub_le_iff.mp p0ExpK9_p249_100_hbox
  have h_p63_25 := abs_sub_le_iff.mp p0ExpK9_p63_25_hbox
  have h_p51_20 := abs_sub_le_iff.mp p0ExpK9_p51_20_hbox
  rw [show ((18 : Real) / (4 : Real)) = ((9 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D18_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p39_20.1, h_p39_20.2, h_p99_50.1, h_p99_50.2, h_p201_100.1, h_p201_100.2, h_p51_25.1, h_p51_25.2, h_p207_100.1, h_p207_100.2, h_p21_10.1, h_p21_10.2, h_p213_100.1, h_p213_100.2, h_p54_25.1, h_p54_25.2, h_p219_100.1, h_p219_100.2, h_p111_50.1, h_p111_50.2, h_p9_4.1, h_p9_4.2, h_p57_25.1, h_p57_25.2, h_p231_100.1, h_p231_100.2, h_p117_50.1, h_p117_50.2, h_p237_100.1, h_p237_100.2, h_p12_5.1, h_p12_5.2, h_p243_100.1, h_p243_100.2, h_p123_50.1, h_p123_50.2, h_p249_100.1, h_p249_100.2, h_p63_25.1, h_p63_25.2, h_p51_20.1, h_p51_20.2]

end PSDpd
end Q3
