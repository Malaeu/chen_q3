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

private theorem p0PieceK9D13PlusWindowSeg0_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((379 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((77 : Real) / (40 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((379 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((77 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg1_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((373 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((379 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((373 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((379 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg2_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((367 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((373 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((367 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((373 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg3_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((361 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((367 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((361 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((367 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg4_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((71 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((361 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((71 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((361 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg5_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((349 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((71 : Real) / (40 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((349 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((71 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg6_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((343 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((349 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((343 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((349 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg7_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((337 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((343 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((337 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((343 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg8_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((331 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((337 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((331 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((337 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg9_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((331 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((331 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg10_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((319 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (8 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((319 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg11_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((313 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((319 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((313 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((319 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg12_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((307 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((313 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((307 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((313 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg13_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((301 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((307 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((301 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((307 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg14_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((59 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((301 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((59 : Real) / (40 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((301 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg15_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((289 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((59 : Real) / (40 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((289 : Real) / (200 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((59 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg16_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((283 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((289 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((283 : Real) / (200 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((289 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg17_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((277 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((283 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((277 : Real) / (200 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((283 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg18_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((271 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((277 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((271 : Real) / (200 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((277 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D13PlusWindowSeg19_profile_linear :
    Real.exp ((13 : Real) / (8 : Real)) * p0PieceK9D13PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((53 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((271 : Real) / (200 : Real)) := by
  unfold p0PieceK9D13PlusWindowSegmentExpIntegral
  change Real.exp ((13 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D13PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((53 : Real) / (40 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((271 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D13PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D13_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((13 : Real) / (4 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((53 : Real) / (40 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((271 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((277 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((283 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((289 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((59 : Real) / (40 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((301 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((307 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((313 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((319 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (8 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((331 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((337 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((343 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((349 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((71 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((361 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((367 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((373 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((379 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((77 : Real) / (40 : Real)) := by
  rw [p0PieceK9D13_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D13PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D13MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D13PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D13PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower13_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨13, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((13 : Real) / (4 : Real)) := by
  have h_p53_40 := abs_sub_le_iff.mp p0ExpK9_p53_40_hbox
  have h_p271_200 := abs_sub_le_iff.mp p0ExpK9_p271_200_hbox
  have h_p277_200 := abs_sub_le_iff.mp p0ExpK9_p277_200_hbox
  have h_p283_200 := abs_sub_le_iff.mp p0ExpK9_p283_200_hbox
  have h_p289_200 := abs_sub_le_iff.mp p0ExpK9_p289_200_hbox
  have h_p59_40 := abs_sub_le_iff.mp p0ExpK9_p59_40_hbox
  have h_p301_200 := abs_sub_le_iff.mp p0ExpK9_p301_200_hbox
  have h_p307_200 := abs_sub_le_iff.mp p0ExpK9_p307_200_hbox
  have h_p313_200 := abs_sub_le_iff.mp p0ExpK9_p313_200_hbox
  have h_p319_200 := abs_sub_le_iff.mp p0ExpK9_p319_200_hbox
  have h_p13_8 := abs_sub_le_iff.mp p0ExpK9_p13_8_hbox
  have h_p331_200 := abs_sub_le_iff.mp p0ExpK9_p331_200_hbox
  have h_p337_200 := abs_sub_le_iff.mp p0ExpK9_p337_200_hbox
  have h_p343_200 := abs_sub_le_iff.mp p0ExpK9_p343_200_hbox
  have h_p349_200 := abs_sub_le_iff.mp p0ExpK9_p349_200_hbox
  have h_p71_40 := abs_sub_le_iff.mp p0ExpK9_p71_40_hbox
  have h_p361_200 := abs_sub_le_iff.mp p0ExpK9_p361_200_hbox
  have h_p367_200 := abs_sub_le_iff.mp p0ExpK9_p367_200_hbox
  have h_p373_200 := abs_sub_le_iff.mp p0ExpK9_p373_200_hbox
  have h_p379_200 := abs_sub_le_iff.mp p0ExpK9_p379_200_hbox
  have h_p77_40 := abs_sub_le_iff.mp p0ExpK9_p77_40_hbox
  rw [show ((13 : Real) / (4 : Real)) = ((13 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D13_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p53_40.1, h_p53_40.2, h_p271_200.1, h_p271_200.2, h_p277_200.1, h_p277_200.2, h_p283_200.1, h_p283_200.2, h_p289_200.1, h_p289_200.2, h_p59_40.1, h_p59_40.2, h_p301_200.1, h_p301_200.2, h_p307_200.1, h_p307_200.2, h_p313_200.1, h_p313_200.2, h_p319_200.1, h_p319_200.2, h_p13_8.1, h_p13_8.2, h_p331_200.1, h_p331_200.2, h_p337_200.1, h_p337_200.2, h_p343_200.1, h_p343_200.2, h_p349_200.1, h_p349_200.2, h_p71_40.1, h_p71_40.2, h_p361_200.1, h_p361_200.2, h_p367_200.1, h_p367_200.2, h_p373_200.1, h_p373_200.2, h_p379_200.1, h_p379_200.2, h_p77_40.1, h_p77_40.2]

theorem controlK9AnalyticP0_hUpper13_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((13 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨13, by norm_num⟩ : CoeffIndex23) := by
  have h_p53_40 := abs_sub_le_iff.mp p0ExpK9_p53_40_hbox
  have h_p271_200 := abs_sub_le_iff.mp p0ExpK9_p271_200_hbox
  have h_p277_200 := abs_sub_le_iff.mp p0ExpK9_p277_200_hbox
  have h_p283_200 := abs_sub_le_iff.mp p0ExpK9_p283_200_hbox
  have h_p289_200 := abs_sub_le_iff.mp p0ExpK9_p289_200_hbox
  have h_p59_40 := abs_sub_le_iff.mp p0ExpK9_p59_40_hbox
  have h_p301_200 := abs_sub_le_iff.mp p0ExpK9_p301_200_hbox
  have h_p307_200 := abs_sub_le_iff.mp p0ExpK9_p307_200_hbox
  have h_p313_200 := abs_sub_le_iff.mp p0ExpK9_p313_200_hbox
  have h_p319_200 := abs_sub_le_iff.mp p0ExpK9_p319_200_hbox
  have h_p13_8 := abs_sub_le_iff.mp p0ExpK9_p13_8_hbox
  have h_p331_200 := abs_sub_le_iff.mp p0ExpK9_p331_200_hbox
  have h_p337_200 := abs_sub_le_iff.mp p0ExpK9_p337_200_hbox
  have h_p343_200 := abs_sub_le_iff.mp p0ExpK9_p343_200_hbox
  have h_p349_200 := abs_sub_le_iff.mp p0ExpK9_p349_200_hbox
  have h_p71_40 := abs_sub_le_iff.mp p0ExpK9_p71_40_hbox
  have h_p361_200 := abs_sub_le_iff.mp p0ExpK9_p361_200_hbox
  have h_p367_200 := abs_sub_le_iff.mp p0ExpK9_p367_200_hbox
  have h_p373_200 := abs_sub_le_iff.mp p0ExpK9_p373_200_hbox
  have h_p379_200 := abs_sub_le_iff.mp p0ExpK9_p379_200_hbox
  have h_p77_40 := abs_sub_le_iff.mp p0ExpK9_p77_40_hbox
  rw [show ((13 : Real) / (4 : Real)) = ((13 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D13_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p53_40.1, h_p53_40.2, h_p271_200.1, h_p271_200.2, h_p277_200.1, h_p277_200.2, h_p283_200.1, h_p283_200.2, h_p289_200.1, h_p289_200.2, h_p59_40.1, h_p59_40.2, h_p301_200.1, h_p301_200.2, h_p307_200.1, h_p307_200.2, h_p313_200.1, h_p313_200.2, h_p319_200.1, h_p319_200.2, h_p13_8.1, h_p13_8.2, h_p331_200.1, h_p331_200.2, h_p337_200.1, h_p337_200.2, h_p343_200.1, h_p343_200.2, h_p349_200.1, h_p349_200.2, h_p71_40.1, h_p71_40.2, h_p361_200.1, h_p361_200.2, h_p367_200.1, h_p367_200.2, h_p373_200.1, h_p373_200.2, h_p379_200.1, h_p379_200.2, h_p77_40.1, h_p77_40.2]

private theorem p0PieceK9D14PlusWindowSeg0_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((101 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((41 : Real) / (20 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((101 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((41 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg1_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((199 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((101 : Real) / (50 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((199 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((101 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg2_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((49 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((199 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((49 : Real) / (25 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((199 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg3_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((49 : Real) / (25 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((49 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg4_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (10 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((193 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg5_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((187 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((19 : Real) / (10 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((187 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((19 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg6_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((46 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((187 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((46 : Real) / (25 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((187 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg7_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((181 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((46 : Real) / (25 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((181 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((46 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg8_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((89 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((181 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((89 : Real) / (50 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((181 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg9_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((89 : Real) / (50 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((89 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg10_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((43 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (4 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((43 : Real) / (25 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg11_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((169 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((43 : Real) / (25 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((169 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((43 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg12_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((83 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((169 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((83 : Real) / (50 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((169 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg13_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((163 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((83 : Real) / (50 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((163 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((83 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg14_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((8 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((163 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((8 : Real) / (5 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((163 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg15_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((8 : Real) / (5 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((8 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg16_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((77 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((77 : Real) / (50 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((157 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg17_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((151 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((77 : Real) / (50 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((151 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((77 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg18_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((37 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((151 : Real) / (100 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35282000667685248888805383331525821950851870349844047 : Real) / (3304474731188688055500 : Real)) * Real.exp ((37 : Real) / (25 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((151 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D14PlusWindowSeg19_profile_linear :
    Real.exp ((7 : Real) / (4 : Real)) * p0PieceK9D14PlusWindowSegmentExpIntegral 19 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((29 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((37 : Real) / (25 : Real)) := by
  unfold p0PieceK9D14PlusWindowSegmentExpIntegral
  change Real.exp ((7 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D14PlusWindowSeg19Coeff 20 ((-3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((29 : Real) / (20 : Real)) +
      ((-1799267556314751111194616668474178049148129650155953 : Real) / (3304474731188688055500 : Real)) * Real.exp ((37 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D14PlusWindowSeg19Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D14_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((7 : Real) / (2 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((29 : Real) / (20 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((37 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((151 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((77 : Real) / (50 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((157 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((8 : Real) / (5 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((163 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((83 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((169 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((43 : Real) / (25 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((89 : Real) / (50 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((181 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((46 : Real) / (25 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((187 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (10 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((193 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((49 : Real) / (25 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((199 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((101 : Real) / (50 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((41 : Real) / (20 : Real)) := by
  rw [p0PieceK9D14_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D14PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D14MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D14PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D14PlusWindowSeg19_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower14_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨14, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((14 : Real) / (4 : Real)) := by
  have h_p29_20 := abs_sub_le_iff.mp p0ExpK9_p29_20_hbox
  have h_p37_25 := abs_sub_le_iff.mp p0ExpK9_p37_25_hbox
  have h_p151_100 := abs_sub_le_iff.mp p0ExpK9_p151_100_hbox
  have h_p77_50 := abs_sub_le_iff.mp p0ExpK9_p77_50_hbox
  have h_p157_100 := abs_sub_le_iff.mp p0ExpK9_p157_100_hbox
  have h_p8_5 := abs_sub_le_iff.mp p0ExpK9_p8_5_hbox
  have h_p163_100 := abs_sub_le_iff.mp p0ExpK9_p163_100_hbox
  have h_p83_50 := abs_sub_le_iff.mp p0ExpK9_p83_50_hbox
  have h_p169_100 := abs_sub_le_iff.mp p0ExpK9_p169_100_hbox
  have h_p43_25 := abs_sub_le_iff.mp p0ExpK9_p43_25_hbox
  have h_p7_4 := abs_sub_le_iff.mp p0ExpK9_p7_4_hbox
  have h_p89_50 := abs_sub_le_iff.mp p0ExpK9_p89_50_hbox
  have h_p181_100 := abs_sub_le_iff.mp p0ExpK9_p181_100_hbox
  have h_p46_25 := abs_sub_le_iff.mp p0ExpK9_p46_25_hbox
  have h_p187_100 := abs_sub_le_iff.mp p0ExpK9_p187_100_hbox
  have h_p19_10 := abs_sub_le_iff.mp p0ExpK9_p19_10_hbox
  have h_p193_100 := abs_sub_le_iff.mp p0ExpK9_p193_100_hbox
  have h_p49_25 := abs_sub_le_iff.mp p0ExpK9_p49_25_hbox
  have h_p199_100 := abs_sub_le_iff.mp p0ExpK9_p199_100_hbox
  have h_p101_50 := abs_sub_le_iff.mp p0ExpK9_p101_50_hbox
  have h_p41_20 := abs_sub_le_iff.mp p0ExpK9_p41_20_hbox
  rw [show ((14 : Real) / (4 : Real)) = ((7 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D14_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p29_20.1, h_p29_20.2, h_p37_25.1, h_p37_25.2, h_p151_100.1, h_p151_100.2, h_p77_50.1, h_p77_50.2, h_p157_100.1, h_p157_100.2, h_p8_5.1, h_p8_5.2, h_p163_100.1, h_p163_100.2, h_p83_50.1, h_p83_50.2, h_p169_100.1, h_p169_100.2, h_p43_25.1, h_p43_25.2, h_p7_4.1, h_p7_4.2, h_p89_50.1, h_p89_50.2, h_p181_100.1, h_p181_100.2, h_p46_25.1, h_p46_25.2, h_p187_100.1, h_p187_100.2, h_p19_10.1, h_p19_10.2, h_p193_100.1, h_p193_100.2, h_p49_25.1, h_p49_25.2, h_p199_100.1, h_p199_100.2, h_p101_50.1, h_p101_50.2, h_p41_20.1, h_p41_20.2]

theorem controlK9AnalyticP0_hUpper14_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((14 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨14, by norm_num⟩ : CoeffIndex23) := by
  have h_p29_20 := abs_sub_le_iff.mp p0ExpK9_p29_20_hbox
  have h_p37_25 := abs_sub_le_iff.mp p0ExpK9_p37_25_hbox
  have h_p151_100 := abs_sub_le_iff.mp p0ExpK9_p151_100_hbox
  have h_p77_50 := abs_sub_le_iff.mp p0ExpK9_p77_50_hbox
  have h_p157_100 := abs_sub_le_iff.mp p0ExpK9_p157_100_hbox
  have h_p8_5 := abs_sub_le_iff.mp p0ExpK9_p8_5_hbox
  have h_p163_100 := abs_sub_le_iff.mp p0ExpK9_p163_100_hbox
  have h_p83_50 := abs_sub_le_iff.mp p0ExpK9_p83_50_hbox
  have h_p169_100 := abs_sub_le_iff.mp p0ExpK9_p169_100_hbox
  have h_p43_25 := abs_sub_le_iff.mp p0ExpK9_p43_25_hbox
  have h_p7_4 := abs_sub_le_iff.mp p0ExpK9_p7_4_hbox
  have h_p89_50 := abs_sub_le_iff.mp p0ExpK9_p89_50_hbox
  have h_p181_100 := abs_sub_le_iff.mp p0ExpK9_p181_100_hbox
  have h_p46_25 := abs_sub_le_iff.mp p0ExpK9_p46_25_hbox
  have h_p187_100 := abs_sub_le_iff.mp p0ExpK9_p187_100_hbox
  have h_p19_10 := abs_sub_le_iff.mp p0ExpK9_p19_10_hbox
  have h_p193_100 := abs_sub_le_iff.mp p0ExpK9_p193_100_hbox
  have h_p49_25 := abs_sub_le_iff.mp p0ExpK9_p49_25_hbox
  have h_p199_100 := abs_sub_le_iff.mp p0ExpK9_p199_100_hbox
  have h_p101_50 := abs_sub_le_iff.mp p0ExpK9_p101_50_hbox
  have h_p41_20 := abs_sub_le_iff.mp p0ExpK9_p41_20_hbox
  rw [show ((14 : Real) / (4 : Real)) = ((7 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D14_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_p29_20.1, h_p29_20.2, h_p37_25.1, h_p37_25.2, h_p151_100.1, h_p151_100.2, h_p77_50.1, h_p77_50.2, h_p157_100.1, h_p157_100.2, h_p8_5.1, h_p8_5.2, h_p163_100.1, h_p163_100.2, h_p83_50.1, h_p83_50.2, h_p169_100.1, h_p169_100.2, h_p43_25.1, h_p43_25.2, h_p7_4.1, h_p7_4.2, h_p89_50.1, h_p89_50.2, h_p181_100.1, h_p181_100.2, h_p46_25.1, h_p46_25.2, h_p187_100.1, h_p187_100.2, h_p19_10.1, h_p19_10.2, h_p193_100.1, h_p193_100.2, h_p49_25.1, h_p49_25.2, h_p199_100.1, h_p199_100.2, h_p101_50.1, h_p101_50.2, h_p41_20.1, h_p41_20.2]

end PSDpd
end Q3
