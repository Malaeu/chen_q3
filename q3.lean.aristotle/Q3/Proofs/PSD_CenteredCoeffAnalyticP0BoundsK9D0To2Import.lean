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

private theorem p0PieceK9D0PlusWindowSeg0_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (10 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg1_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg2_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((6 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg3_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((21 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg4_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (20 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg5_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((3 : Real) / (20 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (25 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((3 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg6_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((3 : Real) / (25 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((3 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg7_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((3 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((3 : Real) / (50 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg8_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (50 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0PlusWindowSeg9_profile_linear :
    p0PieceK9D0PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((0 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0PlusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((0 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((3 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg0_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) +
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((0 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg0Coeff 20 ((3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) +
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((0 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg1_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (50 : Real)) +
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((3 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg1Coeff 20 ((3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (50 : Real)) +
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((3 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg2_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) +
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((3 : Real) / (50 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg2Coeff 20 ((3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) +
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((3 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg3_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((3 : Real) / (25 : Real)) +
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg3Coeff 20 ((3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((3 : Real) / (25 : Real)) +
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg4_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((3 : Real) / (20 : Real)) +
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (25 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg4Coeff 20 ((3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((3 : Real) / (20 : Real)) +
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((3 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg5_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) +
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (20 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg5Coeff 20 ((3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) +
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg6_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) +
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg6Coeff 20 ((3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) +
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((9 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg7_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) +
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((21 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg7Coeff 20 ((3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) +
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((21 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg8_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) +
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((6 : Real) / (25 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg8Coeff 20 ((3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) +
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((6 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

private theorem p0PieceK9D0MinusWindowSeg9_profile_linear :
    p0PieceK9D0MinusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (10 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real)) := by
  unfold p0PieceK9D0MinusWindowSegmentExpIntegral
  change expPolyIntegral p0PieceK9D0MinusWindowSeg9Coeff 20 ((3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (10 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((27 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D0MinusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring

theorem p0PieceK9D0_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((0 : Real)) =
      ((695915072405453863782371690055140503346644524719573956 : Real) / (6608949462377376111 : Real)) * Real.exp ((0 : Real)) +
      ((-1245633962180608000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (100 : Real)) +
      ((311408490545152000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (50 : Real)) +
      ((-191635994181632000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (100 : Real)) +
      ((95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (25 : Real)) +
      ((-38327198836326400000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((3 : Real) / (20 : Real)) +
      ((11977249636352000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((9 : Real) / (50 : Real)) +
      ((-2818176385024000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((21 : Real) / (100 : Real)) +
      ((1409088192512000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((6 : Real) / (25 : Real)) +
      ((-148325072896000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((27 : Real) / (100 : Real)) +
      ((7416253644800000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((3 : Real) / (10 : Real)) := by
  rw [p0PieceK9D0_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D0PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D0MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D0PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D0PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg0_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg1_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg2_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg3_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg4_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg5_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg6_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg7_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg8_profile_linear]
  rw [p0PieceK9D0MinusWindowSeg9_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower0_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨0, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((0 : Real) / (4 : Real)) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p3_100 := abs_sub_le_iff.mp p0ExpK9_p3_100_hbox
  have h_p3_50 := abs_sub_le_iff.mp p0ExpK9_p3_50_hbox
  have h_p9_100 := abs_sub_le_iff.mp p0ExpK9_p9_100_hbox
  have h_p3_25 := abs_sub_le_iff.mp p0ExpK9_p3_25_hbox
  have h_p3_20 := abs_sub_le_iff.mp p0ExpK9_p3_20_hbox
  have h_p9_50 := abs_sub_le_iff.mp p0ExpK9_p9_50_hbox
  have h_p21_100 := abs_sub_le_iff.mp p0ExpK9_p21_100_hbox
  have h_p6_25 := abs_sub_le_iff.mp p0ExpK9_p6_25_hbox
  have h_p27_100 := abs_sub_le_iff.mp p0ExpK9_p27_100_hbox
  have h_p3_10 := abs_sub_le_iff.mp p0ExpK9_p3_10_hbox
  rw [show ((0 : Real) / (4 : Real)) = ((0 : Real)) by norm_num]
  rw [p0PieceK9D0_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p3_100.1, h_p3_100.2, h_p3_50.1, h_p3_50.2, h_p9_100.1, h_p9_100.2, h_p3_25.1, h_p3_25.2, h_p3_20.1, h_p3_20.2, h_p9_50.1, h_p9_50.2, h_p21_100.1, h_p21_100.2, h_p6_25.1, h_p6_25.2, h_p27_100.1, h_p27_100.2, h_p3_10.1, h_p3_10.2]

theorem controlK9AnalyticP0_hUpper0_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((0 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨0, by norm_num⟩ : CoeffIndex23) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p3_100 := abs_sub_le_iff.mp p0ExpK9_p3_100_hbox
  have h_p3_50 := abs_sub_le_iff.mp p0ExpK9_p3_50_hbox
  have h_p9_100 := abs_sub_le_iff.mp p0ExpK9_p9_100_hbox
  have h_p3_25 := abs_sub_le_iff.mp p0ExpK9_p3_25_hbox
  have h_p3_20 := abs_sub_le_iff.mp p0ExpK9_p3_20_hbox
  have h_p9_50 := abs_sub_le_iff.mp p0ExpK9_p9_50_hbox
  have h_p21_100 := abs_sub_le_iff.mp p0ExpK9_p21_100_hbox
  have h_p6_25 := abs_sub_le_iff.mp p0ExpK9_p6_25_hbox
  have h_p27_100 := abs_sub_le_iff.mp p0ExpK9_p27_100_hbox
  have h_p3_10 := abs_sub_le_iff.mp p0ExpK9_p3_10_hbox
  rw [show ((0 : Real) / (4 : Real)) = ((0 : Real)) by norm_num]
  rw [p0PieceK9D0_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p3_100.1, h_p3_100.2, h_p3_50.1, h_p3_50.2, h_p9_100.1, h_p9_100.2, h_p3_25.1, h_p3_25.2, h_p3_20.1, h_p3_20.2, h_p9_50.1, h_p9_50.2, h_p21_100.1, h_p21_100.2, h_p6_25.1, h_p6_25.2, h_p27_100.1, h_p27_100.2, h_p3_10.1, h_p3_10.2]

private theorem p0PieceK9D1PlusWindowSeg0_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((79 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (40 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((79 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg1_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((73 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((79 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((73 : Real) / (200 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((79 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg2_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((67 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((73 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((67 : Real) / (200 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((73 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg3_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((67 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (200 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((67 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg4_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (40 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((61 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg5_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((49 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((11 : Real) / (40 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((49 : Real) / (200 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((11 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg6_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((49 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (200 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((49 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg7_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((37 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((37 : Real) / (200 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg8_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((31 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((31 : Real) / (200 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg9_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((31 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (8 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((31 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg10_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((19 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (8 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((19 : Real) / (200 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (8 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg11_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((13 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((19 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((13 : Real) / (200 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((19 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg12_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((13 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (200 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((13 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg13_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((1 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((1 : Real) / (200 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1PlusWindowSeg14_profile_linear :
    Real.exp ((1 : Real) / (8 : Real)) * p0PieceK9D1PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-199986853988731452295649433382903691901076077695317160531147 : Real) / (31184936061578187898355712 : Real)) * Real.exp ((0 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((1 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((5 : Real) / (6 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-199986853988731452295649433382903691901076077695317160531147 : Real) / (31184936061578187898355712 : Real)) * Real.exp ((0 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((1 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg0_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((1 : Real) / (40 : Real)) +
      ((16762678575344915432248664986705877910796307999537317811408533 : Real) / (2525979820987833219766812672 : Real)) * Real.exp ((0 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg0Coeff 20 ((3 : Real) / (20 : Real)) ((5 : Real) / (6 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((1 : Real) / (40 : Real)) +
      ((16762678575344915432248664986705877910796307999537317811408533 : Real) / (2525979820987833219766812672 : Real)) * Real.exp ((0 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg1_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (200 : Real)) +
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (40 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg1Coeff 20 ((3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (200 : Real)) +
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (40 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg2_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((17 : Real) / (200 : Real)) +
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg2Coeff 20 ((3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((17 : Real) / (200 : Real)) +
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((11 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg3_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((23 : Real) / (200 : Real)) +
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((17 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg3Coeff 20 ((3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((23 : Real) / (200 : Real)) +
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((17 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg4_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((29 : Real) / (200 : Real)) +
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((23 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg4Coeff 20 ((3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((29 : Real) / (200 : Real)) +
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((23 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D1MinusWindowSeg5_profile_linear :
    Real.exp ((-1 : Real) / (8 : Real)) * p0PieceK9D1MinusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (40 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((29 : Real) / (200 : Real)) := by
  unfold p0PieceK9D1MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (8 : Real)) * expPolyIntegral p0PieceK9D1MinusWindowSeg5Coeff 20 ((3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (40 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((29 : Real) / (200 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D1MinusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D1_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((1 : Real) / (4 : Real)) =
      ((281871701128833898150530441345339433404572853108313904192813 : Real) / (1262989910493916609883406336 : Real)) * Real.exp ((0 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (40 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (200 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (200 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((19 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((23 : Real) / (200 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (8 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((29 : Real) / (200 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((31 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (40 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((37 : Real) / (200 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((43 : Real) / (200 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((49 : Real) / (200 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((11 : Real) / (40 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((61 : Real) / (200 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((67 : Real) / (200 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((73 : Real) / (200 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((79 : Real) / (200 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((17 : Real) / (40 : Real)) := by
  rw [p0PieceK9D1_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D1PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D1MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D1PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D1PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg0_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg1_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg2_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg3_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg4_profile_linear]
  rw [p0PieceK9D1MinusWindowSeg5_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower1_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨1, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((1 : Real) / (4 : Real)) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p1_200 := abs_sub_le_iff.mp p0ExpK9_p1_200_hbox
  have h_p1_40 := abs_sub_le_iff.mp p0ExpK9_p1_40_hbox
  have h_p7_200 := abs_sub_le_iff.mp p0ExpK9_p7_200_hbox
  have h_p11_200 := abs_sub_le_iff.mp p0ExpK9_p11_200_hbox
  have h_p13_200 := abs_sub_le_iff.mp p0ExpK9_p13_200_hbox
  have h_p17_200 := abs_sub_le_iff.mp p0ExpK9_p17_200_hbox
  have h_p19_200 := abs_sub_le_iff.mp p0ExpK9_p19_200_hbox
  have h_p23_200 := abs_sub_le_iff.mp p0ExpK9_p23_200_hbox
  have h_p1_8 := abs_sub_le_iff.mp p0ExpK9_p1_8_hbox
  have h_p29_200 := abs_sub_le_iff.mp p0ExpK9_p29_200_hbox
  have h_p31_200 := abs_sub_le_iff.mp p0ExpK9_p31_200_hbox
  have h_p7_40 := abs_sub_le_iff.mp p0ExpK9_p7_40_hbox
  have h_p37_200 := abs_sub_le_iff.mp p0ExpK9_p37_200_hbox
  have h_p43_200 := abs_sub_le_iff.mp p0ExpK9_p43_200_hbox
  have h_p49_200 := abs_sub_le_iff.mp p0ExpK9_p49_200_hbox
  have h_p11_40 := abs_sub_le_iff.mp p0ExpK9_p11_40_hbox
  have h_p61_200 := abs_sub_le_iff.mp p0ExpK9_p61_200_hbox
  have h_p67_200 := abs_sub_le_iff.mp p0ExpK9_p67_200_hbox
  have h_p73_200 := abs_sub_le_iff.mp p0ExpK9_p73_200_hbox
  have h_p79_200 := abs_sub_le_iff.mp p0ExpK9_p79_200_hbox
  have h_p17_40 := abs_sub_le_iff.mp p0ExpK9_p17_40_hbox
  rw [show ((1 : Real) / (4 : Real)) = ((1 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D1_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p1_200.1, h_p1_200.2, h_p1_40.1, h_p1_40.2, h_p7_200.1, h_p7_200.2, h_p11_200.1, h_p11_200.2, h_p13_200.1, h_p13_200.2, h_p17_200.1, h_p17_200.2, h_p19_200.1, h_p19_200.2, h_p23_200.1, h_p23_200.2, h_p1_8.1, h_p1_8.2, h_p29_200.1, h_p29_200.2, h_p31_200.1, h_p31_200.2, h_p7_40.1, h_p7_40.2, h_p37_200.1, h_p37_200.2, h_p43_200.1, h_p43_200.2, h_p49_200.1, h_p49_200.2, h_p11_40.1, h_p11_40.2, h_p61_200.1, h_p61_200.2, h_p67_200.1, h_p67_200.2, h_p73_200.1, h_p73_200.2, h_p79_200.1, h_p79_200.2, h_p17_40.1, h_p17_40.2]

theorem controlK9AnalyticP0_hUpper1_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((1 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨1, by norm_num⟩ : CoeffIndex23) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p1_200 := abs_sub_le_iff.mp p0ExpK9_p1_200_hbox
  have h_p1_40 := abs_sub_le_iff.mp p0ExpK9_p1_40_hbox
  have h_p7_200 := abs_sub_le_iff.mp p0ExpK9_p7_200_hbox
  have h_p11_200 := abs_sub_le_iff.mp p0ExpK9_p11_200_hbox
  have h_p13_200 := abs_sub_le_iff.mp p0ExpK9_p13_200_hbox
  have h_p17_200 := abs_sub_le_iff.mp p0ExpK9_p17_200_hbox
  have h_p19_200 := abs_sub_le_iff.mp p0ExpK9_p19_200_hbox
  have h_p23_200 := abs_sub_le_iff.mp p0ExpK9_p23_200_hbox
  have h_p1_8 := abs_sub_le_iff.mp p0ExpK9_p1_8_hbox
  have h_p29_200 := abs_sub_le_iff.mp p0ExpK9_p29_200_hbox
  have h_p31_200 := abs_sub_le_iff.mp p0ExpK9_p31_200_hbox
  have h_p7_40 := abs_sub_le_iff.mp p0ExpK9_p7_40_hbox
  have h_p37_200 := abs_sub_le_iff.mp p0ExpK9_p37_200_hbox
  have h_p43_200 := abs_sub_le_iff.mp p0ExpK9_p43_200_hbox
  have h_p49_200 := abs_sub_le_iff.mp p0ExpK9_p49_200_hbox
  have h_p11_40 := abs_sub_le_iff.mp p0ExpK9_p11_40_hbox
  have h_p61_200 := abs_sub_le_iff.mp p0ExpK9_p61_200_hbox
  have h_p67_200 := abs_sub_le_iff.mp p0ExpK9_p67_200_hbox
  have h_p73_200 := abs_sub_le_iff.mp p0ExpK9_p73_200_hbox
  have h_p79_200 := abs_sub_le_iff.mp p0ExpK9_p79_200_hbox
  have h_p17_40 := abs_sub_le_iff.mp p0ExpK9_p17_40_hbox
  rw [show ((1 : Real) / (4 : Real)) = ((1 : Real) / (4 : Real)) by norm_num]
  rw [p0PieceK9D1_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p1_200.1, h_p1_200.2, h_p1_40.1, h_p1_40.2, h_p7_200.1, h_p7_200.2, h_p11_200.1, h_p11_200.2, h_p13_200.1, h_p13_200.2, h_p17_200.1, h_p17_200.2, h_p19_200.1, h_p19_200.2, h_p23_200.1, h_p23_200.2, h_p1_8.1, h_p1_8.2, h_p29_200.1, h_p29_200.2, h_p31_200.1, h_p31_200.2, h_p7_40.1, h_p7_40.2, h_p37_200.1, h_p37_200.2, h_p43_200.1, h_p43_200.2, h_p49_200.1, h_p49_200.2, h_p11_40.1, h_p11_40.2, h_p61_200.1, h_p61_200.2, h_p67_200.1, h_p67_200.2, h_p73_200.1, h_p73_200.2, h_p79_200.1, h_p79_200.2, h_p17_40.1, h_p17_40.2]

private theorem p0PieceK9D2PlusWindowSeg0_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((13 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (20 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg0Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real)) ((-9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((13 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (20 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg1_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((49 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((13 : Real) / (25 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg1Coeff 20 ((-3 : Real) / (20 : Real)) ((-9 : Real) / (5 : Real)) ((-8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((9060462169135639158589330785725247247385462668658051 : Real) / (826118682797172013875 : Real)) * Real.exp ((49 : Real) / (100 : Real)) +
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((13 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg2_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 2 * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((23 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((49 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg2Coeff 20 ((-3 : Real) / (20 : Real)) ((-8 : Real) / (5 : Real)) ((-7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-36183861321220950892471468905701669282012601115554751 : Real) / (367163859020965339500 : Real)) * Real.exp ((23 : Real) / (50 : Real)) +
      ((8778616651429373426823407690474972528068281925704661 : Real) / (91790964755241334875 : Real)) * Real.exp ((49 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg2Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg3_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 3 * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((23 : Real) / (50 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg3Coeff 20 ((-3 : Real) / (20 : Real)) ((-7 : Real) / (5 : Real)) ((-6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((153535796623496485228098730476403932403180165379025196 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (100 : Real)) +
      ((-595992512292337147322585593282894992153962196653335747 : Real) / (1101491577062896018500 : Real)) * Real.exp ((23 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg3Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg4_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 4 * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((2 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg4Coeff 20 ((-3 : Real) / (20 : Real)) ((-6 : Real) / (5 : Real)) ((-1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4905312333997238557611804906158182718103289974483581 : Real) / (2202983154125792037 : Real)) * Real.exp ((2 : Real) / (5 : Real)) +
      ((595042305648503514771901269523596067596819834620974804 : Real) / (275372894265724004625 : Real)) * Real.exp ((43 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg4Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg5_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 5 * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((2 : Real) / (5 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg5Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real)) ((-4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((612188190512070189980230271511395272966215140809989236 : Real) / (91790964755241334875 : Real)) * Real.exp ((37 : Real) / (100 : Real)) +
      ((-153314914883504961746109624664965777224695806725983 : Real) / (23687990904578409 : Real)) * Real.exp ((2 : Real) / (5 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg5Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg6_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 6 * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((37 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg6Coeff 20 ((-3 : Real) / (20 : Real)) ((-4 : Real) / (5 : Real)) ((-3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4278509306398128467059485529980606668158053152787776341 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (50 : Real)) +
      ((4152060246639789430059309185465814181101354577570032292 : Real) / (275372894265724004625 : Real)) * Real.exp ((37 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg6Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg7_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 7 * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((31 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (50 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg7Coeff 20 ((-3 : Real) / (20 : Real)) ((-3 : Real) / (5 : Real)) ((-2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((255909738023605202374596967947818609058580057674922876 : Real) / (8882996589216903375 : Real)) * Real.exp ((31 : Real) / (100 : Real)) +
      ((-7698740329953871532940514470019393331841946847212223659 : Real) / (275372894265724004625 : Real)) * Real.exp ((17 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg7Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg8_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 8 * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((7 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg8Coeff 20 ((-3 : Real) / (20 : Real)) ((-2 : Real) / (5 : Real)) ((-1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7920642894939564241525318644320637914526062218791797657 : Real) / (183581929510482669750 : Real)) * Real.exp ((7 : Real) / (25 : Real)) +
      ((3843276260113412908795831331205874373061339404025796948 : Real) / (91790964755241334875 : Real)) * Real.exp ((31 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg8Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg9_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 9 * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((7 : Real) / (25 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg9Coeff 20 ((-3 : Real) / (20 : Real)) ((-1 : Real) / (5 : Real)) ((0 : Real)) * ((3 : Real) / (10 : Real)) =
      ((347957536202726931891185845027570251673322262359786978 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (4 : Real)) +
      ((-84418459218119921826272132201114258769265440030873821087 : Real) / (1652237365594344027750 : Real)) * Real.exp ((7 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg9Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg10_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 10 * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((11 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (4 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg10Coeff 20 ((-3 : Real) / (20 : Real)) ((0 : Real)) ((1 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-86852154845781282925522404489493410040361193283661190713 : Real) / (1652237365594344027750 : Real)) * Real.exp ((11 : Real) / (50 : Real)) +
      ((337141142996607468108814154972429748326677737640213022 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (4 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg10Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg11_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 11 * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((19 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((11 : Real) / (50 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg11Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real) / (5 : Real)) ((2 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((127148653678258332680911495230072182647035860966613892 : Real) / (2960998863072301125 : Real)) * Real.exp ((19 : Real) / (100 : Real)) +
      ((-7650232269643857452719732834500732217737645190704312143 : Real) / (183581929510482669750 : Real)) * Real.exp ((11 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg11Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg12_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 12 * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((4 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((19 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg12Coeff 20 ((-3 : Real) / (20 : Real)) ((2 : Real) / (5 : Real)) ((3 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-7870823866914294725778327618996331632858471646149288541 : Real) / (275372894265724004625 : Real)) * Real.exp ((4 : Real) / (25 : Real)) +
      ((7638205866993975060675230943603287013825664930104908044 : Real) / (275372894265724004625 : Real)) * Real.exp ((19 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg12Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg13_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 13 * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((13 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((4 : Real) / (25 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg13Coeff 20 ((-3 : Real) / (20 : Real)) ((3 : Real) / (5 : Real)) ((4 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((4231485052460642448419865411984565267654492553456324908 : Real) / (275372894265724004625 : Real)) * Real.exp ((13 : Real) / (100 : Real)) +
      ((-4106425769437705274221672381003668367141528353850711459 : Real) / (275372894265724004625 : Real)) * Real.exp ((4 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg13Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg14_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 14 * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((1 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((13 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg14Coeff 20 ((-3 : Real) / (20 : Real)) ((4 : Real) / (5 : Real)) ((1 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-4828407035657094829381381743315888771982542396700327 : Real) / (734327718041930679 : Real)) * Real.exp ((1 : Real) / (10 : Real)) +
      ((585713255238452517193378196005144910781835815514558364 : Real) / (91790964755241334875 : Real)) * Real.exp ((13 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg14Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg15_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 15 * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (10 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg15Coeff 20 ((-3 : Real) / (20 : Real)) ((1 : Real)) ((6 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((602607017789688318599754145948983146624711849550072796 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (100 : Real)) +
      ((-4678378311191915511855854770052333684052372809899019 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (10 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg15Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg16_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 16 * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((1 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg16Coeff 20 ((-3 : Real) / (20 : Real)) ((6 : Real) / (5 : Real)) ((7 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-601666263323639679614587157763552164677560152723339653 : Real) / (1101491577062896018500 : Real)) * Real.exp ((1 : Real) / (25 : Real)) +
      ((145971084482311681400245854051016853375288150449927204 : Real) / (275372894265724004625 : Real)) * Real.exp ((7 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg16Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg17_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 17 * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((1 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((1 : Real) / (25 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg17Coeff 20 ((-3 : Real) / (20 : Real)) ((7 : Real) / (5 : Real)) ((8 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((8834244115705260191697258835916770031546255628081139 : Real) / (91790964755241334875 : Real)) * Real.exp ((1 : Real) / (100 : Real)) +
      ((-34292610977453440128470947412149278440813282425553449 : Real) / (367163859020965339500 : Real)) * Real.exp ((1 : Real) / (25 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg17Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2PlusWindowSeg18_profile_linear :
    Real.exp ((1 : Real) / (4 : Real)) * p0PieceK9D2PlusWindowSegmentExpIntegral 18 * ((3 : Real) / (10 : Real)) =
      ((-45380298436897168692115349964335329344532603338265065373 : Real) / (4336131742265796466427100 : Real)) * Real.exp ((0 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((1 : Real) / (100 : Real)) := by
  unfold p0PieceK9D2PlusWindowSegmentExpIntegral
  change Real.exp ((1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2PlusWindowSeg18Coeff 20 ((-3 : Real) / (20 : Real)) ((8 : Real) / (5 : Real)) ((5 : Real) / (3 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-45380298436897168692115349964335329344532603338265065373 : Real) / (4336131742265796466427100 : Real)) * Real.exp ((0 : Real)) +
      ((8559814990652658274724670476749069716083699347269749 : Real) / (826118682797172013875 : Real)) * Real.exp ((1 : Real) / (100 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2PlusWindowSeg18Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2MinusWindowSeg0_profile_linear :
    Real.exp ((-1 : Real) / (4 : Real)) * p0PieceK9D2MinusWindowSegmentExpIntegral 0 * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((1 : Real) / (50 : Real)) +
      ((5231484246266731115959102064883801227913489607636627603 : Real) / (481792415807310718491900 : Real)) * Real.exp ((0 : Real)) := by
  unfold p0PieceK9D2MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2MinusWindowSeg0Coeff 20 ((3 : Real) / (20 : Real)) ((5 : Real) / (3 : Real)) ((9 : Real) / (5 : Real)) * ((3 : Real) / (10 : Real)) =
      ((-35170740175691636316446501714044558280723038117769753 : Real) / (3304474731188688055500 : Real)) * Real.exp ((1 : Real) / (50 : Real)) +
      ((5231484246266731115959102064883801227913489607636627603 : Real) / (481792415807310718491900 : Real)) * Real.exp ((0 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2MinusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

private theorem p0PieceK9D2MinusWindowSeg1_profile_linear :
    Real.exp ((-1 : Real) / (4 : Real)) * p0PieceK9D2MinusWindowSegmentExpIntegral 1 * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (20 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((1 : Real) / (50 : Real)) := by
  unfold p0PieceK9D2MinusWindowSegmentExpIntegral
  change Real.exp ((-1 : Real) / (4 : Real)) * expPolyIntegral p0PieceK9D2MinusWindowSeg1Coeff 20 ((3 : Real) / (20 : Real)) ((9 : Real) / (5 : Real)) ((2 : Real)) * ((3 : Real) / (10 : Real)) =
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (20 : Real)) +
      ((-1910528048308363683553498285955441719276961882230247 : Real) / (3304474731188688055500 : Real)) * Real.exp ((1 : Real) / (50 : Real))
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK9D2MinusWindowSeg1Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  ring_nf
  repeat rw [sq]
  repeat rw [← Real.exp_add]
  norm_num
  try ring

theorem p0PieceK9D2_profile_linear :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((1 : Real) / (2 : Real)) =
      ((851529889751705675758284309809440853344401565232291527 : Real) / (2168065871132898233213550 : Real)) * Real.exp ((0 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (50 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (20 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((7 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((1 : Real) / (10 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((13 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((4 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((19 : Real) / (100 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (50 : Real)) +
      ((685098679199334400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((1 : Real) / (4 : Real)) +
      ((-622816981090304000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((7 : Real) / (25 : Real)) +
      ((155704245272576000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((31 : Real) / (100 : Real)) +
      ((-95817997090816000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((17 : Real) / (50 : Real)) +
      ((47908998545408000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((37 : Real) / (100 : Real)) +
      ((-19163599418163200000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((2 : Real) / (5 : Real)) +
      ((5988624818176000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((43 : Real) / (100 : Real)) +
      ((-1409088192512000000000000000000000000000000000000000 : Real) / (2202983154125792037 : Real)) * Real.exp ((23 : Real) / (50 : Real)) +
      ((704544096256000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((49 : Real) / (100 : Real)) +
      ((-74162536448000000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((13 : Real) / (25 : Real)) +
      ((3708126822400000000000000000000000000000000000000 : Real) / (6608949462377376111 : Real)) * Real.exp ((11 : Real) / (20 : Real)) := by
  rw [p0PieceK9D2_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums]
  unfold p0PieceK9D2PlusWindowExpPolyIntegralSum
  unfold p0PieceK9D2MinusWindowExpPolyIntegralSum
  simp only [Finset.sum_range_succ]
  norm_num
  ring_nf
  rw [p0PieceK9D2PlusWindowSeg0_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg1_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg2_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg3_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg4_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg5_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg6_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg7_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg8_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg9_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg10_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg11_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg12_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg13_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg14_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg15_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg16_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg17_profile_linear]
  rw [p0PieceK9D2PlusWindowSeg18_profile_linear]
  rw [p0PieceK9D2MinusWindowSeg0_profile_linear]
  rw [p0PieceK9D2MinusWindowSeg1_profile_linear]
  try rw [Real.exp_zero]
  ring

theorem controlK9AnalyticP0_hLower2_generated :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower (⟨2, by norm_num⟩ : CoeffIndex23) <=
      CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((2 : Real) / (4 : Real)) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p1_100 := abs_sub_le_iff.mp p0ExpK9_p1_100_hbox
  have h_p1_50 := abs_sub_le_iff.mp p0ExpK9_p1_50_hbox
  have h_p1_25 := abs_sub_le_iff.mp p0ExpK9_p1_25_hbox
  have h_p1_20 := abs_sub_le_iff.mp p0ExpK9_p1_20_hbox
  have h_p7_100 := abs_sub_le_iff.mp p0ExpK9_p7_100_hbox
  have h_p1_10 := abs_sub_le_iff.mp p0ExpK9_p1_10_hbox
  have h_p13_100 := abs_sub_le_iff.mp p0ExpK9_p13_100_hbox
  have h_p4_25 := abs_sub_le_iff.mp p0ExpK9_p4_25_hbox
  have h_p19_100 := abs_sub_le_iff.mp p0ExpK9_p19_100_hbox
  have h_p11_50 := abs_sub_le_iff.mp p0ExpK9_p11_50_hbox
  have h_p1_4 := abs_sub_le_iff.mp p0ExpK9_p1_4_hbox
  have h_p7_25 := abs_sub_le_iff.mp p0ExpK9_p7_25_hbox
  have h_p31_100 := abs_sub_le_iff.mp p0ExpK9_p31_100_hbox
  have h_p17_50 := abs_sub_le_iff.mp p0ExpK9_p17_50_hbox
  have h_p37_100 := abs_sub_le_iff.mp p0ExpK9_p37_100_hbox
  have h_p2_5 := abs_sub_le_iff.mp p0ExpK9_p2_5_hbox
  have h_p43_100 := abs_sub_le_iff.mp p0ExpK9_p43_100_hbox
  have h_p23_50 := abs_sub_le_iff.mp p0ExpK9_p23_50_hbox
  have h_p49_100 := abs_sub_le_iff.mp p0ExpK9_p49_100_hbox
  have h_p13_25 := abs_sub_le_iff.mp p0ExpK9_p13_25_hbox
  have h_p11_20 := abs_sub_le_iff.mp p0ExpK9_p11_20_hbox
  rw [show ((2 : Real) / (4 : Real)) = ((1 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D2_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceLower,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p1_100.1, h_p1_100.2, h_p1_50.1, h_p1_50.2, h_p1_25.1, h_p1_25.2, h_p1_20.1, h_p1_20.2, h_p7_100.1, h_p7_100.2, h_p1_10.1, h_p1_10.2, h_p13_100.1, h_p13_100.2, h_p4_25.1, h_p4_25.2, h_p19_100.1, h_p19_100.2, h_p11_50.1, h_p11_50.2, h_p1_4.1, h_p1_4.2, h_p7_25.1, h_p7_25.2, h_p31_100.1, h_p31_100.2, h_p17_50.1, h_p17_50.2, h_p37_100.1, h_p37_100.2, h_p2_5.1, h_p2_5.2, h_p43_100.1, h_p43_100.2, h_p23_50.1, h_p23_50.2, h_p49_100.1, h_p49_100.2, h_p13_25.1, h_p13_25.2, h_p11_20.1, h_p11_20.2]

theorem controlK9AnalyticP0_hUpper2_generated :
    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile
      9 ((3 : Real) / (10 : Real)) ((3 : Real)) ((2 : Real) / (4 : Real)) <=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper (⟨2, by norm_num⟩ : CoeffIndex23) := by
  have h_zero := abs_sub_le_iff.mp p0ExpK9_zero_hbox
  have h_p1_100 := abs_sub_le_iff.mp p0ExpK9_p1_100_hbox
  have h_p1_50 := abs_sub_le_iff.mp p0ExpK9_p1_50_hbox
  have h_p1_25 := abs_sub_le_iff.mp p0ExpK9_p1_25_hbox
  have h_p1_20 := abs_sub_le_iff.mp p0ExpK9_p1_20_hbox
  have h_p7_100 := abs_sub_le_iff.mp p0ExpK9_p7_100_hbox
  have h_p1_10 := abs_sub_le_iff.mp p0ExpK9_p1_10_hbox
  have h_p13_100 := abs_sub_le_iff.mp p0ExpK9_p13_100_hbox
  have h_p4_25 := abs_sub_le_iff.mp p0ExpK9_p4_25_hbox
  have h_p19_100 := abs_sub_le_iff.mp p0ExpK9_p19_100_hbox
  have h_p11_50 := abs_sub_le_iff.mp p0ExpK9_p11_50_hbox
  have h_p1_4 := abs_sub_le_iff.mp p0ExpK9_p1_4_hbox
  have h_p7_25 := abs_sub_le_iff.mp p0ExpK9_p7_25_hbox
  have h_p31_100 := abs_sub_le_iff.mp p0ExpK9_p31_100_hbox
  have h_p17_50 := abs_sub_le_iff.mp p0ExpK9_p17_50_hbox
  have h_p37_100 := abs_sub_le_iff.mp p0ExpK9_p37_100_hbox
  have h_p2_5 := abs_sub_le_iff.mp p0ExpK9_p2_5_hbox
  have h_p43_100 := abs_sub_le_iff.mp p0ExpK9_p43_100_hbox
  have h_p23_50 := abs_sub_le_iff.mp p0ExpK9_p23_50_hbox
  have h_p49_100 := abs_sub_le_iff.mp p0ExpK9_p49_100_hbox
  have h_p13_25 := abs_sub_le_iff.mp p0ExpK9_p13_25_hbox
  have h_p11_20 := abs_sub_le_iff.mp p0ExpK9_p11_20_hbox
  rw [show ((2 : Real) / (4 : Real)) = ((1 : Real) / (2 : Real)) by norm_num]
  rw [p0PieceK9D2_profile_linear]
  norm_num [
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceUpper,
    controlK9P0AbsDistanceEntryRat,
    controlK9P0RadiusAbsDistanceEntryRat
  ]
  ring_nf
  linarith [h_zero.1, h_zero.2, h_p1_100.1, h_p1_100.2, h_p1_50.1, h_p1_50.2, h_p1_25.1, h_p1_25.2, h_p1_20.1, h_p1_20.2, h_p7_100.1, h_p7_100.2, h_p1_10.1, h_p1_10.2, h_p13_100.1, h_p13_100.2, h_p4_25.1, h_p4_25.2, h_p19_100.1, h_p19_100.2, h_p11_50.1, h_p11_50.2, h_p1_4.1, h_p1_4.2, h_p7_25.1, h_p7_25.2, h_p31_100.1, h_p31_100.2, h_p17_50.1, h_p17_50.2, h_p37_100.1, h_p37_100.2, h_p2_5.1, h_p2_5.2, h_p43_100.1, h_p43_100.2, h_p23_50.1, h_p23_50.2, h_p49_100.1, h_p49_100.2, h_p13_25.1, h_p13_25.2, h_p11_20.1, h_p11_20.2]

end PSDpd
end Q3
