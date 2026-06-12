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

private theorem p0PieceK9D9PlusWindowSeg0_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((279 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((57 : Real) / (40 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((279 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((57 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg1_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((273 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((279 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((273 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((279 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg2_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((267 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((273 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((267 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((273 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg3_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((261 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((267 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((261 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((267 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg4_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((51 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((261 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((51 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((261 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg5_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((249 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((51 : Real) / (40 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((249 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((51 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg6_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((249 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((249 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg7_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((237 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((237 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((243 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg8_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((231 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((237 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((231 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((237 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg9_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((231 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((231 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg10_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((219 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (8 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((219 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg11_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((213 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((219 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((213 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((219 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg12_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((213 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((213 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg13_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((201 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((201 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((207 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg14_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((39 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((201 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((39 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((201 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg15_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((189 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((39 : Real) / (40 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((189 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((39 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg16_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((183 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((189 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((183 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((189 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg17_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((177 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((183 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((177 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((183 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg18_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((171 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((177 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((171 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((177 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D9PlusWindowSeg19_profile_linear :
    Real.exp ((9 : Real) / (8 : Real)) * p0PieceK9D9PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((33 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((171 : Real) / (200 : Real)) := by
  unfold p0PieceK9D9PlusWindowSegmentExpIntegral
  change Real.exp ((9 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D9PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((33 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((171 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D9PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D9_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((9 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((33 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((171 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((177 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((183 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((189 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((39 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((201 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((207 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((213 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((219 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((231 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((237 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((243 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((249 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((51 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((261 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((267 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((273 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((279 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((57 : Real) / (40 : Real)) := by
  rw [p0PieceK9D9_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D9PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D9MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D9PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D9PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower9_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨9, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((9 : Real) / (4 : Real)) := by
  have h_p33_40 := abs_sub_le_iff.mp p0ExpK9_p33_40_hbox
  have h_p171_200 := abs_sub_le_iff.mp p0ExpK9_p171_200_hbox
  have h_p177_200 := abs_sub_le_iff.mp p0ExpK9_p177_200_hbox
  have h_p183_200 := abs_sub_le_iff.mp p0ExpK9_p183_200_hbox
  have h_p189_200 := abs_sub_le_iff.mp p0ExpK9_p189_200_hbox
  have h_p39_40 := abs_sub_le_iff.mp p0ExpK9_p39_40_hbox
  have h_p201_200 := abs_sub_le_iff.mp p0ExpK9_p201_200_hbox
  have h_p207_200 := abs_sub_le_iff.mp p0ExpK9_p207_200_hbox
  have h_p213_200 := abs_sub_le_iff.mp p0ExpK9_p213_200_hbox
  have h_p219_200 := abs_sub_le_iff.mp p0ExpK9_p219_200_hbox
  have h_p9_8 := abs_sub_le_iff.mp p0ExpK9_p9_8_hbox
  have h_p231_200 := abs_sub_le_iff.mp p0ExpK9_p231_200_hbox
  have h_p237_200 := abs_sub_le_iff.mp p0ExpK9_p237_200_hbox
  have h_p243_200 := abs_sub_le_iff.mp p0ExpK9_p243_200_hbox
  have h_p249_200 := abs_sub_le_iff.mp p0ExpK9_p249_200_hbox
  have h_p51_40 := abs_sub_le_iff.mp p0ExpK9_p51_40_hbox
  have h_p261_200 := abs_sub_le_iff.mp p0ExpK9_p261_200_hbox
  have h_p267_200 := abs_sub_le_iff.mp p0ExpK9_p267_200_hbox
  have h_p273_200 := abs_sub_le_iff.mp p0ExpK9_p273_200_hbox
  have h_p279_200 := abs_sub_le_iff.mp p0ExpK9_p279_200_hbox
  have h_p57_40 := abs_sub_le_iff.mp p0ExpK9_p57_40_hbox
  rw [show ((9 : Real) / (4 : Real)) = ((9 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D9_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p33_40.1, h_p33_40.2, h_p171_200.1, h_p171_200.2, h_p177_200.1, h_p177_200.2, h_p183_200.1, h_p183_200.2, h_p189_200.1, h_p189_200.2, h_p39_40.1, h_p39_40.2, h_p201_200.1, h_p201_200.2, h_p207_200.1, h_p207_200.2, h_p213_200.1, h_p213_200.2, h_p219_200.1, h_p219_200.2, h_p9_8.1, h_p9_8.2, h_p231_200.1, h_p231_200.2, h_p237_200.1, h_p237_200.2, h_p243_200.1, h_p243_200.2, h_p249_200.1, h_p249_200.2, h_p51_40.1, h_p51_40.2, h_p261_200.1, h_p261_200.2, h_p267_200.1, h_p267_200.2, h_p273_200.1, h_p273_200.2, h_p279_200.1, h_p279_200.2, h_p57_40.1, h_p57_40.2]

theorem controlK9AnalyticP0_hUpper9_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((9 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨9, by norm_num⟩ : CoeffIndex23) := by
  have h_p33_40 := abs_sub_le_iff.mp p0ExpK9_p33_40_hbox
  have h_p171_200 := abs_sub_le_iff.mp p0ExpK9_p171_200_hbox
  have h_p177_200 := abs_sub_le_iff.mp p0ExpK9_p177_200_hbox
  have h_p183_200 := abs_sub_le_iff.mp p0ExpK9_p183_200_hbox
  have h_p189_200 := abs_sub_le_iff.mp p0ExpK9_p189_200_hbox
  have h_p39_40 := abs_sub_le_iff.mp p0ExpK9_p39_40_hbox
  have h_p201_200 := abs_sub_le_iff.mp p0ExpK9_p201_200_hbox
  have h_p207_200 := abs_sub_le_iff.mp p0ExpK9_p207_200_hbox
  have h_p213_200 := abs_sub_le_iff.mp p0ExpK9_p213_200_hbox
  have h_p219_200 := abs_sub_le_iff.mp p0ExpK9_p219_200_hbox
  have h_p9_8 := abs_sub_le_iff.mp p0ExpK9_p9_8_hbox
  have h_p231_200 := abs_sub_le_iff.mp p0ExpK9_p231_200_hbox
  have h_p237_200 := abs_sub_le_iff.mp p0ExpK9_p237_200_hbox
  have h_p243_200 := abs_sub_le_iff.mp p0ExpK9_p243_200_hbox
  have h_p249_200 := abs_sub_le_iff.mp p0ExpK9_p249_200_hbox
  have h_p51_40 := abs_sub_le_iff.mp p0ExpK9_p51_40_hbox
  have h_p261_200 := abs_sub_le_iff.mp p0ExpK9_p261_200_hbox
  have h_p267_200 := abs_sub_le_iff.mp p0ExpK9_p267_200_hbox
  have h_p273_200 := abs_sub_le_iff.mp p0ExpK9_p273_200_hbox
  have h_p279_200 := abs_sub_le_iff.mp p0ExpK9_p279_200_hbox
  have h_p57_40 := abs_sub_le_iff.mp p0ExpK9_p57_40_hbox
  rw [show ((9 : Real) / (4 : Real)) = ((9 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D9_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p33_40.1, h_p33_40.2, h_p171_200.1, h_p171_200.2, h_p177_200.1, h_p177_200.2, h_p183_200.1, h_p183_200.2, h_p189_200.1, h_p189_200.2, h_p39_40.1, h_p39_40.2, h_p201_200.1, h_p201_200.2, h_p207_200.1, h_p207_200.2, h_p213_200.1, h_p213_200.2, h_p219_200.1, h_p219_200.2, h_p9_8.1, h_p9_8.2, h_p231_200.1, h_p231_200.2, h_p237_200.1, h_p237_200.2, h_p243_200.1, h_p243_200.2, h_p249_200.1, h_p249_200.2, h_p51_40.1, h_p51_40.2, h_p261_200.1, h_p261_200.2, h_p267_200.1, h_p267_200.2, h_p273_200.1, h_p273_200.2, h_p279_200.1, h_p279_200.2, h_p57_40.1, h_p57_40.2]

private theorem p0PieceK9D10PlusWindowSeg0_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((38 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((31 : Real) / (20 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((38 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((31 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg1_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((149 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((38 : Real) / (25 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((149 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((38 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg2_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((73 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((149 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((73 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((149 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg3_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((73 : Real) / (50 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((73 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg4_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((143 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg5_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((7 : Real) / (5 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((137 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((7 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg6_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((137 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((137 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg7_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((131 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (50 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((131 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((67 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg8_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((32 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((131 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((32 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((131 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg9_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((32 : Real) / (25 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((32 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg10_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((61 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (4 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((61 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg11_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((119 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((61 : Real) / (50 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((119 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((61 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg12_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((29 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((119 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((29 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((119 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg13_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((113 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((29 : Real) / (25 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((113 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((29 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg14_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((11 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((113 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((11 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((113 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg15_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (10 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg16_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((26 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((26 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((107 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg17_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((101 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((26 : Real) / (25 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((101 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((26 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg18_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((49 : Real) / (50 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((101 : Real) / (100 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((49 : Real) / (50 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((101 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D10PlusWindowSeg19_profile_linear :
    Real.exp ((5 : Real) / (4 : Real)) * p0PieceK9D10PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((49 : Real) / (50 : Real)) := by
  unfold p0PieceK9D10PlusWindowSegmentExpIntegral
  change Real.exp ((5 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D10PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((49 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D10PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D10_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((5 : Real) / (2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (20 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((49 : Real) / (50 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((101 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((26 : Real) / (25 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((107 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (10 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((113 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((29 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((119 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((61 : Real) / (50 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((5 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((32 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((131 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((67 : Real) / (50 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((137 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (5 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((143 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((73 : Real) / (50 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((149 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((38 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((31 : Real) / (20 : Real)) := by
  rw [p0PieceK9D10_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D10PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D10MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D10PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D10PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower10_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨10, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((10 : Real) / (4 : Real)) := by
  have h_p19_20 := abs_sub_le_iff.mp p0ExpK9_p19_20_hbox
  have h_p49_50 := abs_sub_le_iff.mp p0ExpK9_p49_50_hbox
  have h_p101_100 := abs_sub_le_iff.mp p0ExpK9_p101_100_hbox
  have h_p26_25 := abs_sub_le_iff.mp p0ExpK9_p26_25_hbox
  have h_p107_100 := abs_sub_le_iff.mp p0ExpK9_p107_100_hbox
  have h_p11_10 := abs_sub_le_iff.mp p0ExpK9_p11_10_hbox
  have h_p113_100 := abs_sub_le_iff.mp p0ExpK9_p113_100_hbox
  have h_p29_25 := abs_sub_le_iff.mp p0ExpK9_p29_25_hbox
  have h_p119_100 := abs_sub_le_iff.mp p0ExpK9_p119_100_hbox
  have h_p61_50 := abs_sub_le_iff.mp p0ExpK9_p61_50_hbox
  have h_p5_4 := abs_sub_le_iff.mp p0ExpK9_p5_4_hbox
  have h_p32_25 := abs_sub_le_iff.mp p0ExpK9_p32_25_hbox
  have h_p131_100 := abs_sub_le_iff.mp p0ExpK9_p131_100_hbox
  have h_p67_50 := abs_sub_le_iff.mp p0ExpK9_p67_50_hbox
  have h_p137_100 := abs_sub_le_iff.mp p0ExpK9_p137_100_hbox
  have h_p7_5 := abs_sub_le_iff.mp p0ExpK9_p7_5_hbox
  have h_p143_100 := abs_sub_le_iff.mp p0ExpK9_p143_100_hbox
  have h_p73_50 := abs_sub_le_iff.mp p0ExpK9_p73_50_hbox
  have h_p149_100 := abs_sub_le_iff.mp p0ExpK9_p149_100_hbox
  have h_p38_25 := abs_sub_le_iff.mp p0ExpK9_p38_25_hbox
  have h_p31_20 := abs_sub_le_iff.mp p0ExpK9_p31_20_hbox
  rw [show ((10 : Real) / (4 : Real)) = ((5 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D10_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p19_20.1, h_p19_20.2, h_p49_50.1, h_p49_50.2, h_p101_100.1, h_p101_100.2, h_p26_25.1, h_p26_25.2, h_p107_100.1, h_p107_100.2, h_p11_10.1, h_p11_10.2, h_p113_100.1, h_p113_100.2, h_p29_25.1, h_p29_25.2, h_p119_100.1, h_p119_100.2, h_p61_50.1, h_p61_50.2, h_p5_4.1, h_p5_4.2, h_p32_25.1, h_p32_25.2, h_p131_100.1, h_p131_100.2, h_p67_50.1, h_p67_50.2, h_p137_100.1, h_p137_100.2, h_p7_5.1, h_p7_5.2, h_p143_100.1, h_p143_100.2, h_p73_50.1, h_p73_50.2, h_p149_100.1, h_p149_100.2, h_p38_25.1, h_p38_25.2, h_p31_20.1, h_p31_20.2]

theorem controlK9AnalyticP0_hUpper10_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((10 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨10, by norm_num⟩ : CoeffIndex23) := by
  have h_p19_20 := abs_sub_le_iff.mp p0ExpK9_p19_20_hbox
  have h_p49_50 := abs_sub_le_iff.mp p0ExpK9_p49_50_hbox
  have h_p101_100 := abs_sub_le_iff.mp p0ExpK9_p101_100_hbox
  have h_p26_25 := abs_sub_le_iff.mp p0ExpK9_p26_25_hbox
  have h_p107_100 := abs_sub_le_iff.mp p0ExpK9_p107_100_hbox
  have h_p11_10 := abs_sub_le_iff.mp p0ExpK9_p11_10_hbox
  have h_p113_100 := abs_sub_le_iff.mp p0ExpK9_p113_100_hbox
  have h_p29_25 := abs_sub_le_iff.mp p0ExpK9_p29_25_hbox
  have h_p119_100 := abs_sub_le_iff.mp p0ExpK9_p119_100_hbox
  have h_p61_50 := abs_sub_le_iff.mp p0ExpK9_p61_50_hbox
  have h_p5_4 := abs_sub_le_iff.mp p0ExpK9_p5_4_hbox
  have h_p32_25 := abs_sub_le_iff.mp p0ExpK9_p32_25_hbox
  have h_p131_100 := abs_sub_le_iff.mp p0ExpK9_p131_100_hbox
  have h_p67_50 := abs_sub_le_iff.mp p0ExpK9_p67_50_hbox
  have h_p137_100 := abs_sub_le_iff.mp p0ExpK9_p137_100_hbox
  have h_p7_5 := abs_sub_le_iff.mp p0ExpK9_p7_5_hbox
  have h_p143_100 := abs_sub_le_iff.mp p0ExpK9_p143_100_hbox
  have h_p73_50 := abs_sub_le_iff.mp p0ExpK9_p73_50_hbox
  have h_p149_100 := abs_sub_le_iff.mp p0ExpK9_p149_100_hbox
  have h_p38_25 := abs_sub_le_iff.mp p0ExpK9_p38_25_hbox
  have h_p31_20 := abs_sub_le_iff.mp p0ExpK9_p31_20_hbox
  rw [show ((10 : Real) / (4 : Real)) = ((5 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D10_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p19_20.1, h_p19_20.2, h_p49_50.1, h_p49_50.2, h_p101_100.1, h_p101_100.2, h_p26_25.1, h_p26_25.2, h_p107_100.1, h_p107_100.2, h_p11_10.1, h_p11_10.2, h_p113_100.1, h_p113_100.2, h_p29_25.1, h_p29_25.2, h_p119_100.1, h_p119_100.2, h_p61_50.1, h_p61_50.2, h_p5_4.1, h_p5_4.2, h_p32_25.1, h_p32_25.2, h_p131_100.1, h_p131_100.2, h_p67_50.1, h_p67_50.2, h_p137_100.1, h_p137_100.2, h_p7_5.1, h_p7_5.2, h_p143_100.1, h_p143_100.2, h_p73_50.1, h_p73_50.2, h_p149_100.1, h_p149_100.2, h_p38_25.1, h_p38_25.2, h_p31_20.1, h_p31_20.2]

end PSDpd
end Q3
