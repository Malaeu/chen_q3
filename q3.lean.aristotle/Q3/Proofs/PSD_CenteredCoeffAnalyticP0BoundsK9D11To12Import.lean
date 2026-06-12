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

private theorem p0PieceK9D11PlusWindowSeg0_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((329 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((67 : Real) / (40 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((329 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((67 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg1_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((323 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((329 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((323 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((329 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg2_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((317 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((323 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((317 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((323 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg3_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((311 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((317 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((311 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((317 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg4_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((61 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((311 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((61 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((311 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg5_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((299 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((61 : Real) / (40 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((299 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((61 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg6_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((299 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((299 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg7_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((287 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((287 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((293 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg8_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((281 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((287 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((281 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((287 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg9_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((281 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((281 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg10_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((269 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (8 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((269 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg11_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((263 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((269 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((263 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((269 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg12_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((263 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((263 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg13_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((251 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((251 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((257 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg14_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((49 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((251 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((49 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((251 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg15_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((239 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((49 : Real) / (40 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((239 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((49 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg16_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((233 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((239 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((233 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((239 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg17_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((227 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((233 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((227 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((233 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg18_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((221 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((227 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((221 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((227 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D11PlusWindowSeg19_profile_linear :
    Real.exp ((11 : Real) / (8 : Real)) * p0PieceK9D11PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((43 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((221 : Real) / (200 : Real)) := by
  unfold p0PieceK9D11PlusWindowSegmentExpIntegral
  change Real.exp ((11 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D11PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((43 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((221 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D11PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D11_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((11 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((43 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((221 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((227 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((233 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((239 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((49 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((251 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((257 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((263 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((269 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((281 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((287 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((293 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((299 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((61 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((311 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((317 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((323 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((329 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((67 : Real) / (40 : Real)) := by
  rw [p0PieceK9D11_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D11PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D11MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D11PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D11PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower11_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨11, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((11 : Real) / (4 : Real)) := by
  have h_p43_40 := abs_sub_le_iff.mp p0ExpK9_p43_40_hbox
  have h_p221_200 := abs_sub_le_iff.mp p0ExpK9_p221_200_hbox
  have h_p227_200 := abs_sub_le_iff.mp p0ExpK9_p227_200_hbox
  have h_p233_200 := abs_sub_le_iff.mp p0ExpK9_p233_200_hbox
  have h_p239_200 := abs_sub_le_iff.mp p0ExpK9_p239_200_hbox
  have h_p49_40 := abs_sub_le_iff.mp p0ExpK9_p49_40_hbox
  have h_p251_200 := abs_sub_le_iff.mp p0ExpK9_p251_200_hbox
  have h_p257_200 := abs_sub_le_iff.mp p0ExpK9_p257_200_hbox
  have h_p263_200 := abs_sub_le_iff.mp p0ExpK9_p263_200_hbox
  have h_p269_200 := abs_sub_le_iff.mp p0ExpK9_p269_200_hbox
  have h_p11_8 := abs_sub_le_iff.mp p0ExpK9_p11_8_hbox
  have h_p281_200 := abs_sub_le_iff.mp p0ExpK9_p281_200_hbox
  have h_p287_200 := abs_sub_le_iff.mp p0ExpK9_p287_200_hbox
  have h_p293_200 := abs_sub_le_iff.mp p0ExpK9_p293_200_hbox
  have h_p299_200 := abs_sub_le_iff.mp p0ExpK9_p299_200_hbox
  have h_p61_40 := abs_sub_le_iff.mp p0ExpK9_p61_40_hbox
  have h_p311_200 := abs_sub_le_iff.mp p0ExpK9_p311_200_hbox
  have h_p317_200 := abs_sub_le_iff.mp p0ExpK9_p317_200_hbox
  have h_p323_200 := abs_sub_le_iff.mp p0ExpK9_p323_200_hbox
  have h_p329_200 := abs_sub_le_iff.mp p0ExpK9_p329_200_hbox
  have h_p67_40 := abs_sub_le_iff.mp p0ExpK9_p67_40_hbox
  rw [show ((11 : Real) / (4 : Real)) = ((11 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D11_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p43_40.1, h_p43_40.2, h_p221_200.1, h_p221_200.2, h_p227_200.1, h_p227_200.2, h_p233_200.1, h_p233_200.2, h_p239_200.1, h_p239_200.2, h_p49_40.1, h_p49_40.2, h_p251_200.1, h_p251_200.2, h_p257_200.1, h_p257_200.2, h_p263_200.1, h_p263_200.2, h_p269_200.1, h_p269_200.2, h_p11_8.1, h_p11_8.2, h_p281_200.1, h_p281_200.2, h_p287_200.1, h_p287_200.2, h_p293_200.1, h_p293_200.2, h_p299_200.1, h_p299_200.2, h_p61_40.1, h_p61_40.2, h_p311_200.1, h_p311_200.2, h_p317_200.1, h_p317_200.2, h_p323_200.1, h_p323_200.2, h_p329_200.1, h_p329_200.2, h_p67_40.1, h_p67_40.2]

theorem controlK9AnalyticP0_hUpper11_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((11 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨11, by norm_num⟩ : CoeffIndex23) := by
  have h_p43_40 := abs_sub_le_iff.mp p0ExpK9_p43_40_hbox
  have h_p221_200 := abs_sub_le_iff.mp p0ExpK9_p221_200_hbox
  have h_p227_200 := abs_sub_le_iff.mp p0ExpK9_p227_200_hbox
  have h_p233_200 := abs_sub_le_iff.mp p0ExpK9_p233_200_hbox
  have h_p239_200 := abs_sub_le_iff.mp p0ExpK9_p239_200_hbox
  have h_p49_40 := abs_sub_le_iff.mp p0ExpK9_p49_40_hbox
  have h_p251_200 := abs_sub_le_iff.mp p0ExpK9_p251_200_hbox
  have h_p257_200 := abs_sub_le_iff.mp p0ExpK9_p257_200_hbox
  have h_p263_200 := abs_sub_le_iff.mp p0ExpK9_p263_200_hbox
  have h_p269_200 := abs_sub_le_iff.mp p0ExpK9_p269_200_hbox
  have h_p11_8 := abs_sub_le_iff.mp p0ExpK9_p11_8_hbox
  have h_p281_200 := abs_sub_le_iff.mp p0ExpK9_p281_200_hbox
  have h_p287_200 := abs_sub_le_iff.mp p0ExpK9_p287_200_hbox
  have h_p293_200 := abs_sub_le_iff.mp p0ExpK9_p293_200_hbox
  have h_p299_200 := abs_sub_le_iff.mp p0ExpK9_p299_200_hbox
  have h_p61_40 := abs_sub_le_iff.mp p0ExpK9_p61_40_hbox
  have h_p311_200 := abs_sub_le_iff.mp p0ExpK9_p311_200_hbox
  have h_p317_200 := abs_sub_le_iff.mp p0ExpK9_p317_200_hbox
  have h_p323_200 := abs_sub_le_iff.mp p0ExpK9_p323_200_hbox
  have h_p329_200 := abs_sub_le_iff.mp p0ExpK9_p329_200_hbox
  have h_p67_40 := abs_sub_le_iff.mp p0ExpK9_p67_40_hbox
  rw [show ((11 : Real) / (4 : Real)) = ((11 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D11_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p43_40.1, h_p43_40.2, h_p221_200.1, h_p221_200.2, h_p227_200.1, h_p227_200.2, h_p233_200.1, h_p233_200.2, h_p239_200.1, h_p239_200.2, h_p49_40.1, h_p49_40.2, h_p251_200.1, h_p251_200.2, h_p257_200.1, h_p257_200.2, h_p263_200.1, h_p263_200.2, h_p269_200.1, h_p269_200.2, h_p11_8.1, h_p11_8.2, h_p281_200.1, h_p281_200.2, h_p287_200.1, h_p287_200.2, h_p293_200.1, h_p293_200.2, h_p299_200.1, h_p299_200.2, h_p61_40.1, h_p61_40.2, h_p311_200.1, h_p311_200.2, h_p317_200.1, h_p317_200.2, h_p323_200.1, h_p323_200.2, h_p329_200.1, h_p329_200.2, h_p67_40.1, h_p67_40.2]

private theorem p0PieceK9D12PlusWindowSeg0_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((177 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (5 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((177 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg1_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((87 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((177 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((87 : Real) / (50 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((177 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg2_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((171 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (50 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((171 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((87 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg3_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((42 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((171 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((42 : Real) / (25 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((171 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg4_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((42 : Real) / (25 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((42 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg5_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((81 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((33 : Real) / (20 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((81 : Real) / (50 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((33 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg6_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((159 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((81 : Real) / (50 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((159 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((81 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg7_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((39 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((159 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((39 : Real) / (25 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((159 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg8_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((153 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((39 : Real) / (25 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((153 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((39 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg9_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((153 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (2 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((153 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg10_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((147 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (2 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((147 : Real) / (100 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (2 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg11_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((36 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((147 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((36 : Real) / (25 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((147 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg12_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((141 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((36 : Real) / (25 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((141 : Real) / (100 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((36 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg13_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((69 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((141 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((69 : Real) / (50 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((141 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg14_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((27 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((69 : Real) / (50 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((27 : Real) / (20 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((69 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg15_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((27 : Real) / (20 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (25 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((27 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg16_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((129 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (25 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((129 : Real) / (100 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((33 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg17_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((63 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((129 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((63 : Real) / (50 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((129 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg18_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((123 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((63 : Real) / (50 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((123 : Real) / (100 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((63 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D12PlusWindowSeg19_profile_linear :
    Real.exp ((3 : Real) / (2 : Real)) * p0PieceK9D12PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((6 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((123 : Real) / (100 : Real)) := by
  unfold p0PieceK9D12PlusWindowSegmentExpIntegral
  change Real.exp ((3 : Real) / (2 : Real)) * expPolyIntegral p0PieceK9D12PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((6 : Real) / (5 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((123 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D12PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D12_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((3 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((6 : Real) / (5 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((123 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((63 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((129 : Real) / (100 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (25 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((27 : Real) / (20 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((69 : Real) / (50 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((141 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((36 : Real) / (25 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((147 : Real) / (100 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (2 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((153 : Real) / (100 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((39 : Real) / (25 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((159 : Real) / (100 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((81 : Real) / (50 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((33 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((42 : Real) / (25 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((171 : Real) / (100 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((87 : Real) / (50 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((177 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((9 : Real) / (5 : Real)) := by
  rw [p0PieceK9D12_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D12PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D12MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D12PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D12PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower12_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨12, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((12 : Real) / (4 : Real)) := by
  have h_p6_5 := abs_sub_le_iff.mp p0ExpK9_p6_5_hbox
  have h_p123_100 := abs_sub_le_iff.mp p0ExpK9_p123_100_hbox
  have h_p63_50 := abs_sub_le_iff.mp p0ExpK9_p63_50_hbox
  have h_p129_100 := abs_sub_le_iff.mp p0ExpK9_p129_100_hbox
  have h_p33_25 := abs_sub_le_iff.mp p0ExpK9_p33_25_hbox
  have h_p27_20 := abs_sub_le_iff.mp p0ExpK9_p27_20_hbox
  have h_p69_50 := abs_sub_le_iff.mp p0ExpK9_p69_50_hbox
  have h_p141_100 := abs_sub_le_iff.mp p0ExpK9_p141_100_hbox
  have h_p36_25 := abs_sub_le_iff.mp p0ExpK9_p36_25_hbox
  have h_p147_100 := abs_sub_le_iff.mp p0ExpK9_p147_100_hbox
  have h_p3_2 := abs_sub_le_iff.mp p0ExpK9_p3_2_hbox
  have h_p153_100 := abs_sub_le_iff.mp p0ExpK9_p153_100_hbox
  have h_p39_25 := abs_sub_le_iff.mp p0ExpK9_p39_25_hbox
  have h_p159_100 := abs_sub_le_iff.mp p0ExpK9_p159_100_hbox
  have h_p81_50 := abs_sub_le_iff.mp p0ExpK9_p81_50_hbox
  have h_p33_20 := abs_sub_le_iff.mp p0ExpK9_p33_20_hbox
  have h_p42_25 := abs_sub_le_iff.mp p0ExpK9_p42_25_hbox
  have h_p171_100 := abs_sub_le_iff.mp p0ExpK9_p171_100_hbox
  have h_p87_50 := abs_sub_le_iff.mp p0ExpK9_p87_50_hbox
  have h_p177_100 := abs_sub_le_iff.mp p0ExpK9_p177_100_hbox
  have h_p9_5 := abs_sub_le_iff.mp p0ExpK9_p9_5_hbox
  rw [show ((12 : Real) / (4 : Real)) = ((3 : Real)) by norm_num]
  rw [p0PieceK9D12_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p6_5.1, h_p6_5.2, h_p123_100.1, h_p123_100.2, h_p63_50.1, h_p63_50.2, h_p129_100.1, h_p129_100.2, h_p33_25.1, h_p33_25.2, h_p27_20.1, h_p27_20.2, h_p69_50.1, h_p69_50.2, h_p141_100.1, h_p141_100.2, h_p36_25.1, h_p36_25.2, h_p147_100.1, h_p147_100.2, h_p3_2.1, h_p3_2.2, h_p153_100.1, h_p153_100.2, h_p39_25.1, h_p39_25.2, h_p159_100.1, h_p159_100.2, h_p81_50.1, h_p81_50.2, h_p33_20.1, h_p33_20.2, h_p42_25.1, h_p42_25.2, h_p171_100.1, h_p171_100.2, h_p87_50.1, h_p87_50.2, h_p177_100.1, h_p177_100.2, h_p9_5.1, h_p9_5.2]

theorem controlK9AnalyticP0_hUpper12_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((12 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨12, by norm_num⟩ : CoeffIndex23) := by
  have h_p6_5 := abs_sub_le_iff.mp p0ExpK9_p6_5_hbox
  have h_p123_100 := abs_sub_le_iff.mp p0ExpK9_p123_100_hbox
  have h_p63_50 := abs_sub_le_iff.mp p0ExpK9_p63_50_hbox
  have h_p129_100 := abs_sub_le_iff.mp p0ExpK9_p129_100_hbox
  have h_p33_25 := abs_sub_le_iff.mp p0ExpK9_p33_25_hbox
  have h_p27_20 := abs_sub_le_iff.mp p0ExpK9_p27_20_hbox
  have h_p69_50 := abs_sub_le_iff.mp p0ExpK9_p69_50_hbox
  have h_p141_100 := abs_sub_le_iff.mp p0ExpK9_p141_100_hbox
  have h_p36_25 := abs_sub_le_iff.mp p0ExpK9_p36_25_hbox
  have h_p147_100 := abs_sub_le_iff.mp p0ExpK9_p147_100_hbox
  have h_p3_2 := abs_sub_le_iff.mp p0ExpK9_p3_2_hbox
  have h_p153_100 := abs_sub_le_iff.mp p0ExpK9_p153_100_hbox
  have h_p39_25 := abs_sub_le_iff.mp p0ExpK9_p39_25_hbox
  have h_p159_100 := abs_sub_le_iff.mp p0ExpK9_p159_100_hbox
  have h_p81_50 := abs_sub_le_iff.mp p0ExpK9_p81_50_hbox
  have h_p33_20 := abs_sub_le_iff.mp p0ExpK9_p33_20_hbox
  have h_p42_25 := abs_sub_le_iff.mp p0ExpK9_p42_25_hbox
  have h_p171_100 := abs_sub_le_iff.mp p0ExpK9_p171_100_hbox
  have h_p87_50 := abs_sub_le_iff.mp p0ExpK9_p87_50_hbox
  have h_p177_100 := abs_sub_le_iff.mp p0ExpK9_p177_100_hbox
  have h_p9_5 := abs_sub_le_iff.mp p0ExpK9_p9_5_hbox
  rw [show ((12 : Real) / (4 : Real)) = ((3 : Real)) by norm_num]
  rw [p0PieceK9D12_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p6_5.1, h_p6_5.2, h_p123_100.1, h_p123_100.2, h_p63_50.1, h_p63_50.2, h_p129_100.1, h_p129_100.2, h_p33_25.1, h_p33_25.2, h_p27_20.1, h_p27_20.2, h_p69_50.1, h_p69_50.2, h_p141_100.1, h_p141_100.2, h_p36_25.1, h_p36_25.2, h_p147_100.1, h_p147_100.2, h_p3_2.1, h_p3_2.2, h_p153_100.1, h_p153_100.2, h_p39_25.1, h_p39_25.2, h_p159_100.1, h_p159_100.2, h_p81_50.1, h_p81_50.2, h_p33_20.1, h_p33_20.2, h_p42_25.1, h_p42_25.2, h_p171_100.1, h_p171_100.2, h_p87_50.1, h_p87_50.2, h_p177_100.1, h_p177_100.2, h_p9_5.1, h_p9_5.2]

end PSDpd
end Q3
