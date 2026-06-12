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

private theorem p0PieceK9D5PlusWindowSeg0_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((179 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((37 : Real) / (40 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((179 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((37 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg1_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((173 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((179 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((173 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((179 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg2_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((167 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((173 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((167 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((173 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg3_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((161 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((167 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((161 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((167 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg4_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((31 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((161 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((31 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((161 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg5_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((149 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((31 : Real) / (40 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((149 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((31 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg6_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((149 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((149 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg7_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((137 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((137 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg8_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((131 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((131 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg9_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((131 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((131 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg10_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((119 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (8 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((119 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg11_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((113 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((119 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((113 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((119 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg12_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((113 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((113 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg13_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((101 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((101 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg14_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((19 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((101 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((19 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((101 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg15_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((89 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (40 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((89 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg16_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((83 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((89 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((83 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((89 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg17_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((77 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((83 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((77 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((83 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg18_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((71 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((77 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((71 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((77 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D5PlusWindowSeg19_profile_linear :
    Real.exp ((5 : Real) / (8 : Real)) * p0PieceK9D5PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((71 : Real) / (200 : Real)) := by
  unfold p0PieceK9D5PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D5PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((71 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D5PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D5_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((71 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((77 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((83 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((89 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((101 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((107 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((113 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((119 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((131 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((137 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((143 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((149 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((31 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((161 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((167 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((173 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((179 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((37 : Real) / (40 : Real)) := by
  rw [p0PieceK9D5_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D5PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D5MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D5PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D5PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower5_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨5, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real) / (4 : Real)) := by
  have h_p13_40 := abs_sub_le_iff.mp p0ExpK9_p13_40_hbox
  have h_p71_200 := abs_sub_le_iff.mp p0ExpK9_p71_200_hbox
  have h_p77_200 := abs_sub_le_iff.mp p0ExpK9_p77_200_hbox
  have h_p83_200 := abs_sub_le_iff.mp p0ExpK9_p83_200_hbox
  have h_p89_200 := abs_sub_le_iff.mp p0ExpK9_p89_200_hbox
  have h_p19_40 := abs_sub_le_iff.mp p0ExpK9_p19_40_hbox
  have h_p101_200 := abs_sub_le_iff.mp p0ExpK9_p101_200_hbox
  have h_p107_200 := abs_sub_le_iff.mp p0ExpK9_p107_200_hbox
  have h_p113_200 := abs_sub_le_iff.mp p0ExpK9_p113_200_hbox
  have h_p119_200 := abs_sub_le_iff.mp p0ExpK9_p119_200_hbox
  have h_p5_8 := abs_sub_le_iff.mp p0ExpK9_p5_8_hbox
  have h_p131_200 := abs_sub_le_iff.mp p0ExpK9_p131_200_hbox
  have h_p137_200 := abs_sub_le_iff.mp p0ExpK9_p137_200_hbox
  have h_p143_200 := abs_sub_le_iff.mp p0ExpK9_p143_200_hbox
  have h_p149_200 := abs_sub_le_iff.mp p0ExpK9_p149_200_hbox
  have h_p31_40 := abs_sub_le_iff.mp p0ExpK9_p31_40_hbox
  have h_p161_200 := abs_sub_le_iff.mp p0ExpK9_p161_200_hbox
  have h_p167_200 := abs_sub_le_iff.mp p0ExpK9_p167_200_hbox
  have h_p173_200 := abs_sub_le_iff.mp p0ExpK9_p173_200_hbox
  have h_p179_200 := abs_sub_le_iff.mp p0ExpK9_p179_200_hbox
  have h_p37_40 := abs_sub_le_iff.mp p0ExpK9_p37_40_hbox
  rw [show ((5 : Real) / (4 : Real)) = ((5 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D5_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p13_40.1, h_p13_40.2, h_p71_200.1, h_p71_200.2, h_p77_200.1, h_p77_200.2, h_p83_200.1, h_p83_200.2, h_p89_200.1, h_p89_200.2, h_p19_40.1, h_p19_40.2, h_p101_200.1, h_p101_200.2, h_p107_200.1, h_p107_200.2, h_p113_200.1, h_p113_200.2, h_p119_200.1, h_p119_200.2, h_p5_8.1, h_p5_8.2, h_p131_200.1, h_p131_200.2, h_p137_200.1, h_p137_200.2, h_p143_200.1, h_p143_200.2, h_p149_200.1, h_p149_200.2, h_p31_40.1, h_p31_40.2, h_p161_200.1, h_p161_200.2, h_p167_200.1, h_p167_200.2, h_p173_200.1, h_p173_200.2, h_p179_200.1, h_p179_200.2, h_p37_40.1, h_p37_40.2]

theorem controlK9AnalyticP0_hUpper5_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨5, by norm_num⟩ : CoeffIndex23) := by
  have h_p13_40 := abs_sub_le_iff.mp p0ExpK9_p13_40_hbox
  have h_p71_200 := abs_sub_le_iff.mp p0ExpK9_p71_200_hbox
  have h_p77_200 := abs_sub_le_iff.mp p0ExpK9_p77_200_hbox
  have h_p83_200 := abs_sub_le_iff.mp p0ExpK9_p83_200_hbox
  have h_p89_200 := abs_sub_le_iff.mp p0ExpK9_p89_200_hbox
  have h_p19_40 := abs_sub_le_iff.mp p0ExpK9_p19_40_hbox
  have h_p101_200 := abs_sub_le_iff.mp p0ExpK9_p101_200_hbox
  have h_p107_200 := abs_sub_le_iff.mp p0ExpK9_p107_200_hbox
  have h_p113_200 := abs_sub_le_iff.mp p0ExpK9_p113_200_hbox
  have h_p119_200 := abs_sub_le_iff.mp p0ExpK9_p119_200_hbox
  have h_p5_8 := abs_sub_le_iff.mp p0ExpK9_p5_8_hbox
  have h_p131_200 := abs_sub_le_iff.mp p0ExpK9_p131_200_hbox
  have h_p137_200 := abs_sub_le_iff.mp p0ExpK9_p137_200_hbox
  have h_p143_200 := abs_sub_le_iff.mp p0ExpK9_p143_200_hbox
  have h_p149_200 := abs_sub_le_iff.mp p0ExpK9_p149_200_hbox
  have h_p31_40 := abs_sub_le_iff.mp p0ExpK9_p31_40_hbox
  have h_p161_200 := abs_sub_le_iff.mp p0ExpK9_p161_200_hbox
  have h_p167_200 := abs_sub_le_iff.mp p0ExpK9_p167_200_hbox
  have h_p173_200 := abs_sub_le_iff.mp p0ExpK9_p173_200_hbox
  have h_p179_200 := abs_sub_le_iff.mp p0ExpK9_p179_200_hbox
  have h_p37_40 := abs_sub_le_iff.mp p0ExpK9_p37_40_hbox
  rw [show ((5 : Real) / (4 : Real)) = ((5 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D5_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p13_40.1, h_p13_40.2, h_p71_200.1, h_p71_200.2, h_p77_200.1, h_p77_200.2, h_p83_200.1, h_p83_200.2, h_p89_200.1, h_p89_200.2, h_p19_40.1, h_p19_40.2, h_p101_200.1, h_p101_200.2, h_p107_200.1, h_p107_200.2, h_p113_200.1, h_p113_200.2, h_p119_200.1, h_p119_200.2, h_p5_8.1, h_p5_8.2, h_p131_200.1, h_p131_200.2, h_p137_200.1, h_p137_200.2, h_p143_200.1, h_p143_200.2, h_p149_200.1, h_p149_200.2, h_p31_40.1, h_p31_40.2, h_p161_200.1, h_p161_200.2, h_p167_200.1, h_p167_200.2, h_p173_200.1, h_p173_200.2, h_p179_200.1, h_p179_200.2, h_p37_40.1, h_p37_40.2]

private theorem p0PieceK9D6PlusWindowSeg0_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((51 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (20 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((51 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg1_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((99 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((51 : Real) / (50 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((99 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((51 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg2_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((24 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((99 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((24 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((99 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg3_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((24 : Real) / (25 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((24 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg4_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((93 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg5_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((9 : Real) / (10 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((9 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg6_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((21 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((87 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((21 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((87 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg7_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((81 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((21 : Real) / (25 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((81 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((21 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg8_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((39 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((81 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((39 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((81 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg9_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((39 : Real) / (50 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((39 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg10_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((18 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (4 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((18 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg11_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((69 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((18 : Real) / (25 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((69 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((18 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg12_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((69 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((69 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg13_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((63 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (50 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((63 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg14_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((3 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((63 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((3 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((63 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg15_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (5 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg16_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((27 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((27 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((57 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg17_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((51 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((27 : Real) / (50 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((51 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((27 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg18_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((12 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((51 : Real) / (100 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((12 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((51 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D6PlusWindowSeg19_profile_linear :
    Real.exp ((3 : Real) / (4 : Real)) * p0PieceK9D6PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((12 : Real) / (25 : Real)) := by
  unfold p0PieceK9D6PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D6PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((12 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D6PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D6_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((3 : Real) / (2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (20 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((12 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((51 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((27 : Real) / (50 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((57 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (5 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((63 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((69 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((18 : Real) / (25 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((39 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((81 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (25 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((87 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (10 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((93 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((24 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((99 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((51 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((21 : Real) / (20 : Real)) := by
  rw [p0PieceK9D6_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D6PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D6MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D6PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D6PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower6_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨6, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((6 : Real) / (4 : Real)) := by
  have h_p9_20 := abs_sub_le_iff.mp p0ExpK9_p9_20_hbox
  have h_p12_25 := abs_sub_le_iff.mp p0ExpK9_p12_25_hbox
  have h_p51_100 := abs_sub_le_iff.mp p0ExpK9_p51_100_hbox
  have h_p27_50 := abs_sub_le_iff.mp p0ExpK9_p27_50_hbox
  have h_p57_100 := abs_sub_le_iff.mp p0ExpK9_p57_100_hbox
  have h_p3_5 := abs_sub_le_iff.mp p0ExpK9_p3_5_hbox
  have h_p63_100 := abs_sub_le_iff.mp p0ExpK9_p63_100_hbox
  have h_p33_50 := abs_sub_le_iff.mp p0ExpK9_p33_50_hbox
  have h_p69_100 := abs_sub_le_iff.mp p0ExpK9_p69_100_hbox
  have h_p18_25 := abs_sub_le_iff.mp p0ExpK9_p18_25_hbox
  have h_p3_4 := abs_sub_le_iff.mp p0ExpK9_p3_4_hbox
  have h_p39_50 := abs_sub_le_iff.mp p0ExpK9_p39_50_hbox
  have h_p81_100 := abs_sub_le_iff.mp p0ExpK9_p81_100_hbox
  have h_p21_25 := abs_sub_le_iff.mp p0ExpK9_p21_25_hbox
  have h_p87_100 := abs_sub_le_iff.mp p0ExpK9_p87_100_hbox
  have h_p9_10 := abs_sub_le_iff.mp p0ExpK9_p9_10_hbox
  have h_p93_100 := abs_sub_le_iff.mp p0ExpK9_p93_100_hbox
  have h_p24_25 := abs_sub_le_iff.mp p0ExpK9_p24_25_hbox
  have h_p99_100 := abs_sub_le_iff.mp p0ExpK9_p99_100_hbox
  have h_p51_50 := abs_sub_le_iff.mp p0ExpK9_p51_50_hbox
  have h_p21_20 := abs_sub_le_iff.mp p0ExpK9_p21_20_hbox
  rw [show ((6 : Real) / (4 : Real)) = ((3 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D6_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p9_20.1, h_p9_20.2, h_p12_25.1, h_p12_25.2, h_p51_100.1, h_p51_100.2, h_p27_50.1, h_p27_50.2, h_p57_100.1, h_p57_100.2, h_p3_5.1, h_p3_5.2, h_p63_100.1, h_p63_100.2, h_p33_50.1, h_p33_50.2, h_p69_100.1, h_p69_100.2, h_p18_25.1, h_p18_25.2, h_p3_4.1, h_p3_4.2, h_p39_50.1, h_p39_50.2, h_p81_100.1, h_p81_100.2, h_p21_25.1, h_p21_25.2, h_p87_100.1, h_p87_100.2, h_p9_10.1, h_p9_10.2, h_p93_100.1, h_p93_100.2, h_p24_25.1, h_p24_25.2, h_p99_100.1, h_p99_100.2, h_p51_50.1, h_p51_50.2, h_p21_20.1, h_p21_20.2]

theorem controlK9AnalyticP0_hUpper6_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((6 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨6, by norm_num⟩ : CoeffIndex23) := by
  have h_p9_20 := abs_sub_le_iff.mp p0ExpK9_p9_20_hbox
  have h_p12_25 := abs_sub_le_iff.mp p0ExpK9_p12_25_hbox
  have h_p51_100 := abs_sub_le_iff.mp p0ExpK9_p51_100_hbox
  have h_p27_50 := abs_sub_le_iff.mp p0ExpK9_p27_50_hbox
  have h_p57_100 := abs_sub_le_iff.mp p0ExpK9_p57_100_hbox
  have h_p3_5 := abs_sub_le_iff.mp p0ExpK9_p3_5_hbox
  have h_p63_100 := abs_sub_le_iff.mp p0ExpK9_p63_100_hbox
  have h_p33_50 := abs_sub_le_iff.mp p0ExpK9_p33_50_hbox
  have h_p69_100 := abs_sub_le_iff.mp p0ExpK9_p69_100_hbox
  have h_p18_25 := abs_sub_le_iff.mp p0ExpK9_p18_25_hbox
  have h_p3_4 := abs_sub_le_iff.mp p0ExpK9_p3_4_hbox
  have h_p39_50 := abs_sub_le_iff.mp p0ExpK9_p39_50_hbox
  have h_p81_100 := abs_sub_le_iff.mp p0ExpK9_p81_100_hbox
  have h_p21_25 := abs_sub_le_iff.mp p0ExpK9_p21_25_hbox
  have h_p87_100 := abs_sub_le_iff.mp p0ExpK9_p87_100_hbox
  have h_p9_10 := abs_sub_le_iff.mp p0ExpK9_p9_10_hbox
  have h_p93_100 := abs_sub_le_iff.mp p0ExpK9_p93_100_hbox
  have h_p24_25 := abs_sub_le_iff.mp p0ExpK9_p24_25_hbox
  have h_p99_100 := abs_sub_le_iff.mp p0ExpK9_p99_100_hbox
  have h_p51_50 := abs_sub_le_iff.mp p0ExpK9_p51_50_hbox
  have h_p21_20 := abs_sub_le_iff.mp p0ExpK9_p21_20_hbox
  rw [show ((6 : Real) / (4 : Real)) = ((3 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D6_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p9_20.1, h_p9_20.2, h_p12_25.1, h_p12_25.2, h_p51_100.1, h_p51_100.2, h_p27_50.1, h_p27_50.2, h_p57_100.1, h_p57_100.2, h_p3_5.1, h_p3_5.2, h_p63_100.1, h_p63_100.2, h_p33_50.1, h_p33_50.2, h_p69_100.1, h_p69_100.2, h_p18_25.1, h_p18_25.2, h_p3_4.1, h_p3_4.2, h_p39_50.1, h_p39_50.2, h_p81_100.1, h_p81_100.2, h_p21_25.1, h_p21_25.2, h_p87_100.1, h_p87_100.2, h_p9_10.1, h_p9_10.2, h_p93_100.1, h_p93_100.2, h_p24_25.1, h_p24_25.2, h_p99_100.1, h_p99_100.2, h_p51_50.1, h_p51_50.2, h_p21_20.1, h_p21_20.2]

end PSDpd
end Q3
