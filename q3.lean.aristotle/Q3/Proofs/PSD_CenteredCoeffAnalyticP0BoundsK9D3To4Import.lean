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

private theorem p0PieceK9D3PlusWindowSeg0_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((129 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((27 : Real) / (40 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((129 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((27 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg1_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((123 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((129 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((123 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((129 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg2_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((117 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((123 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((117 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((123 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg3_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((111 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((117 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((111 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((117 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg4_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((111 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((111 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg5_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((99 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((21 : Real) / (40 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((99 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((21 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg6_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((99 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((99 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg7_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((87 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((87 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg8_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((81 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((81 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg9_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((81 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((81 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg10_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((69 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (8 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((69 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg11_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((63 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((69 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((63 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((69 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg12_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((63 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((63 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg13_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((51 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((51 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg14_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((9 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((51 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((9 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((51 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg15_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((39 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (40 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((39 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg16_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((33 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((39 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((33 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((39 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg17_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((27 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((33 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((27 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((33 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg18_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((21 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((27 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((21 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((27 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D3PlusWindowSeg19_profile_linear :
    Real.exp ((3 : Real) / (8 : Real)) * p0PieceK9D3PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((21 : Real) / (200 : Real)) := by
  unfold p0PieceK9D3PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D3PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((21 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D3PlusWindowSeg19Coeff,
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

theorem p0PieceK9D3_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((3 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((27 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((39 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((51 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((57 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((63 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((69 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((81 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((87 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((93 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((99 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((111 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((117 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((123 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((129 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((27 : Real) / (40 : Real)) := by
  rw [p0PieceK9D3_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D3PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D3MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D3PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D3PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower3_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨3, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((3 : Real) / (4 : Real)) := by
  have h_p3_40 := abs_sub_le_iff.mp p0ExpK9_p3_40_hbox
  have h_p21_200 := abs_sub_le_iff.mp p0ExpK9_p21_200_hbox
  have h_p27_200 := abs_sub_le_iff.mp p0ExpK9_p27_200_hbox
  have h_p33_200 := abs_sub_le_iff.mp p0ExpK9_p33_200_hbox
  have h_p39_200 := abs_sub_le_iff.mp p0ExpK9_p39_200_hbox
  have h_p9_40 := abs_sub_le_iff.mp p0ExpK9_p9_40_hbox
  have h_p51_200 := abs_sub_le_iff.mp p0ExpK9_p51_200_hbox
  have h_p57_200 := abs_sub_le_iff.mp p0ExpK9_p57_200_hbox
  have h_p63_200 := abs_sub_le_iff.mp p0ExpK9_p63_200_hbox
  have h_p69_200 := abs_sub_le_iff.mp p0ExpK9_p69_200_hbox
  have h_p3_8 := abs_sub_le_iff.mp p0ExpK9_p3_8_hbox
  have h_p81_200 := abs_sub_le_iff.mp p0ExpK9_p81_200_hbox
  have h_p87_200 := abs_sub_le_iff.mp p0ExpK9_p87_200_hbox
  have h_p93_200 := abs_sub_le_iff.mp p0ExpK9_p93_200_hbox
  have h_p99_200 := abs_sub_le_iff.mp p0ExpK9_p99_200_hbox
  have h_p21_40 := abs_sub_le_iff.mp p0ExpK9_p21_40_hbox
  have h_p111_200 := abs_sub_le_iff.mp p0ExpK9_p111_200_hbox
  have h_p117_200 := abs_sub_le_iff.mp p0ExpK9_p117_200_hbox
  have h_p123_200 := abs_sub_le_iff.mp p0ExpK9_p123_200_hbox
  have h_p129_200 := abs_sub_le_iff.mp p0ExpK9_p129_200_hbox
  have h_p27_40 := abs_sub_le_iff.mp p0ExpK9_p27_40_hbox
  rw [show ((3 : Real) / (4 : Real)) = ((3 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D3_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p3_40.1, h_p3_40.2, h_p21_200.1, h_p21_200.2, h_p27_200.1, h_p27_200.2, h_p33_200.1, h_p33_200.2, h_p39_200.1, h_p39_200.2, h_p9_40.1, h_p9_40.2, h_p51_200.1, h_p51_200.2, h_p57_200.1, h_p57_200.2, h_p63_200.1, h_p63_200.2, h_p69_200.1, h_p69_200.2, h_p3_8.1, h_p3_8.2, h_p81_200.1, h_p81_200.2, h_p87_200.1, h_p87_200.2, h_p93_200.1, h_p93_200.2, h_p99_200.1, h_p99_200.2, h_p21_40.1, h_p21_40.2, h_p111_200.1, h_p111_200.2, h_p117_200.1, h_p117_200.2, h_p123_200.1, h_p123_200.2, h_p129_200.1, h_p129_200.2, h_p27_40.1, h_p27_40.2]

theorem controlK9AnalyticP0_hUpper3_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((3 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨3, by norm_num⟩ : CoeffIndex23) := by
  have h_p3_40 := abs_sub_le_iff.mp p0ExpK9_p3_40_hbox
  have h_p21_200 := abs_sub_le_iff.mp p0ExpK9_p21_200_hbox
  have h_p27_200 := abs_sub_le_iff.mp p0ExpK9_p27_200_hbox
  have h_p33_200 := abs_sub_le_iff.mp p0ExpK9_p33_200_hbox
  have h_p39_200 := abs_sub_le_iff.mp p0ExpK9_p39_200_hbox
  have h_p9_40 := abs_sub_le_iff.mp p0ExpK9_p9_40_hbox
  have h_p51_200 := abs_sub_le_iff.mp p0ExpK9_p51_200_hbox
  have h_p57_200 := abs_sub_le_iff.mp p0ExpK9_p57_200_hbox
  have h_p63_200 := abs_sub_le_iff.mp p0ExpK9_p63_200_hbox
  have h_p69_200 := abs_sub_le_iff.mp p0ExpK9_p69_200_hbox
  have h_p3_8 := abs_sub_le_iff.mp p0ExpK9_p3_8_hbox
  have h_p81_200 := abs_sub_le_iff.mp p0ExpK9_p81_200_hbox
  have h_p87_200 := abs_sub_le_iff.mp p0ExpK9_p87_200_hbox
  have h_p93_200 := abs_sub_le_iff.mp p0ExpK9_p93_200_hbox
  have h_p99_200 := abs_sub_le_iff.mp p0ExpK9_p99_200_hbox
  have h_p21_40 := abs_sub_le_iff.mp p0ExpK9_p21_40_hbox
  have h_p111_200 := abs_sub_le_iff.mp p0ExpK9_p111_200_hbox
  have h_p117_200 := abs_sub_le_iff.mp p0ExpK9_p117_200_hbox
  have h_p123_200 := abs_sub_le_iff.mp p0ExpK9_p123_200_hbox
  have h_p129_200 := abs_sub_le_iff.mp p0ExpK9_p129_200_hbox
  have h_p27_40 := abs_sub_le_iff.mp p0ExpK9_p27_40_hbox
  rw [show ((3 : Real) / (4 : Real)) = ((3 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D3_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p3_40.1, h_p3_40.2, h_p21_200.1, h_p21_200.2, h_p27_200.1, h_p27_200.2, h_p33_200.1, h_p33_200.2, h_p39_200.1, h_p39_200.2, h_p9_40.1, h_p9_40.2, h_p51_200.1, h_p51_200.2, h_p57_200.1, h_p57_200.2, h_p63_200.1, h_p63_200.2, h_p69_200.1, h_p69_200.2, h_p3_8.1, h_p3_8.2, h_p81_200.1, h_p81_200.2, h_p87_200.1, h_p87_200.2, h_p93_200.1, h_p93_200.2, h_p99_200.1, h_p99_200.2, h_p21_40.1, h_p21_40.2, h_p111_200.1, h_p111_200.2, h_p117_200.1, h_p117_200.2, h_p123_200.1, h_p123_200.2, h_p129_200.1, h_p129_200.2, h_p27_40.1, h_p27_40.2]

private theorem p0PieceK9D4PlusWindowSeg0_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((77 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((4 : Real) / (5 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((77 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((4 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg0Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg1_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((37 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((77 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((37 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((77 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg1Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg2_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((71 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (50 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((71 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg2Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg3_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((71 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((71 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg3Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg4_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (25 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg4Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg5_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((13 : Real) / (20 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((13 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg5Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg6_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((31 : Real) / (50 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((31 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg6Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg7_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((14 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((14 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((59 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg7Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg8_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((53 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((14 : Real) / (25 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((53 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((14 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg8Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg9_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((53 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((53 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg9Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg10_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((47 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (2 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((47 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg10Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg11_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((11 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((47 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((11 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((47 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg11Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg12_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (25 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg12Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg13_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((19 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((19 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((41 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg13Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg14_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((7 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((19 : Real) / (50 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((7 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((19 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg14Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg15_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((8 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (20 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((8 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg15Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg16_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((29 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((8 : Real) / (25 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((29 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((8 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg16Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg17_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((13 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((29 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((13 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((29 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg17Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg18_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((23 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((13 : Real) / (50 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((23 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((13 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg18Coeff,
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

private theorem p0PieceK9D4PlusWindowSeg19_profile_linear :
    Real.exp ((1 : Real) / (2 : Real)) * p0PieceK9D4PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((23 : Real) / (100 : Real)) := by
  unfold p0PieceK9D4PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D4PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((23 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D4PlusWindowSeg19Coeff,
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

theorem p0PieceK9D4_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((1 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (5 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (100 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((8 : Real) / (25 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (20 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (50 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((41 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (25 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((47 : Real) / (100 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (2 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((53 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((14 : Real) / (25 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((59 : Real) / (100 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((31 : Real) / (50 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (25 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((71 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((37 : Real) / (50 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((77 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((4 : Real) / (5 : Real)) := by
  rw [p0PieceK9D4_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D4PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D4MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D4PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D4PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower4_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨4, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((4 : Real) / (4 : Real)) := by
  have h_p1_5 := abs_sub_le_iff.mp p0ExpK9_p1_5_hbox
  have h_p23_100 := abs_sub_le_iff.mp p0ExpK9_p23_100_hbox
  have h_p13_50 := abs_sub_le_iff.mp p0ExpK9_p13_50_hbox
  have h_p29_100 := abs_sub_le_iff.mp p0ExpK9_p29_100_hbox
  have h_p8_25 := abs_sub_le_iff.mp p0ExpK9_p8_25_hbox
  have h_p7_20 := abs_sub_le_iff.mp p0ExpK9_p7_20_hbox
  have h_p19_50 := abs_sub_le_iff.mp p0ExpK9_p19_50_hbox
  have h_p41_100 := abs_sub_le_iff.mp p0ExpK9_p41_100_hbox
  have h_p11_25 := abs_sub_le_iff.mp p0ExpK9_p11_25_hbox
  have h_p47_100 := abs_sub_le_iff.mp p0ExpK9_p47_100_hbox
  have h_p1_2 := abs_sub_le_iff.mp p0ExpK9_p1_2_hbox
  have h_p53_100 := abs_sub_le_iff.mp p0ExpK9_p53_100_hbox
  have h_p14_25 := abs_sub_le_iff.mp p0ExpK9_p14_25_hbox
  have h_p59_100 := abs_sub_le_iff.mp p0ExpK9_p59_100_hbox
  have h_p31_50 := abs_sub_le_iff.mp p0ExpK9_p31_50_hbox
  have h_p13_20 := abs_sub_le_iff.mp p0ExpK9_p13_20_hbox
  have h_p17_25 := abs_sub_le_iff.mp p0ExpK9_p17_25_hbox
  have h_p71_100 := abs_sub_le_iff.mp p0ExpK9_p71_100_hbox
  have h_p37_50 := abs_sub_le_iff.mp p0ExpK9_p37_50_hbox
  have h_p77_100 := abs_sub_le_iff.mp p0ExpK9_p77_100_hbox
  have h_p4_5 := abs_sub_le_iff.mp p0ExpK9_p4_5_hbox
  rw [show ((4 : Real) / (4 : Real)) = ((1 : Real)) by norm_num]
  rw [p0PieceK9D4_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p1_5.1, h_p1_5.2, h_p23_100.1, h_p23_100.2, h_p13_50.1, h_p13_50.2, h_p29_100.1, h_p29_100.2, h_p8_25.1, h_p8_25.2, h_p7_20.1, h_p7_20.2, h_p19_50.1, h_p19_50.2, h_p41_100.1, h_p41_100.2, h_p11_25.1, h_p11_25.2, h_p47_100.1, h_p47_100.2, h_p1_2.1, h_p1_2.2, h_p53_100.1, h_p53_100.2, h_p14_25.1, h_p14_25.2, h_p59_100.1, h_p59_100.2, h_p31_50.1, h_p31_50.2, h_p13_20.1, h_p13_20.2, h_p17_25.1, h_p17_25.2, h_p71_100.1, h_p71_100.2, h_p37_50.1, h_p37_50.2, h_p77_100.1, h_p77_100.2, h_p4_5.1, h_p4_5.2]

theorem controlK9AnalyticP0_hUpper4_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((4 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨4, by norm_num⟩ : CoeffIndex23) := by
  have h_p1_5 := abs_sub_le_iff.mp p0ExpK9_p1_5_hbox
  have h_p23_100 := abs_sub_le_iff.mp p0ExpK9_p23_100_hbox
  have h_p13_50 := abs_sub_le_iff.mp p0ExpK9_p13_50_hbox
  have h_p29_100 := abs_sub_le_iff.mp p0ExpK9_p29_100_hbox
  have h_p8_25 := abs_sub_le_iff.mp p0ExpK9_p8_25_hbox
  have h_p7_20 := abs_sub_le_iff.mp p0ExpK9_p7_20_hbox
  have h_p19_50 := abs_sub_le_iff.mp p0ExpK9_p19_50_hbox
  have h_p41_100 := abs_sub_le_iff.mp p0ExpK9_p41_100_hbox
  have h_p11_25 := abs_sub_le_iff.mp p0ExpK9_p11_25_hbox
  have h_p47_100 := abs_sub_le_iff.mp p0ExpK9_p47_100_hbox
  have h_p1_2 := abs_sub_le_iff.mp p0ExpK9_p1_2_hbox
  have h_p53_100 := abs_sub_le_iff.mp p0ExpK9_p53_100_hbox
  have h_p14_25 := abs_sub_le_iff.mp p0ExpK9_p14_25_hbox
  have h_p59_100 := abs_sub_le_iff.mp p0ExpK9_p59_100_hbox
  have h_p31_50 := abs_sub_le_iff.mp p0ExpK9_p31_50_hbox
  have h_p13_20 := abs_sub_le_iff.mp p0ExpK9_p13_20_hbox
  have h_p17_25 := abs_sub_le_iff.mp p0ExpK9_p17_25_hbox
  have h_p71_100 := abs_sub_le_iff.mp p0ExpK9_p71_100_hbox
  have h_p37_50 := abs_sub_le_iff.mp p0ExpK9_p37_50_hbox
  have h_p77_100 := abs_sub_le_iff.mp p0ExpK9_p77_100_hbox
  have h_p4_5 := abs_sub_le_iff.mp p0ExpK9_p4_5_hbox
  rw [show ((4 : Real) / (4 : Real)) = ((1 : Real)) by norm_num]
  rw [p0PieceK9D4_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p1_5.1, h_p1_5.2, h_p23_100.1, h_p23_100.2, h_p13_50.1, h_p13_50.2, h_p29_100.1, h_p29_100.2, h_p8_25.1, h_p8_25.2, h_p7_20.1, h_p7_20.2, h_p19_50.1, h_p19_50.2, h_p41_100.1, h_p41_100.2, h_p11_25.1, h_p11_25.2, h_p47_100.1, h_p47_100.2, h_p1_2.1, h_p1_2.2, h_p53_100.1, h_p53_100.2, h_p14_25.1, h_p14_25.2, h_p59_100.1, h_p59_100.2, h_p31_50.1, h_p31_50.2, h_p13_20.1, h_p13_20.2, h_p17_25.1, h_p17_25.2, h_p71_100.1, h_p71_100.2, h_p37_50.1, h_p37_50.2, h_p77_100.1, h_p77_100.2, h_p4_5.1, h_p4_5.2]

end PSDpd
end Q3
