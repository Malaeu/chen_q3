import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
First-endpoint landing theorem for the Step33A.1-A shifted-digamma m=6 route.
This file contains only glue from a future high-order analytic estimate to the
already checked generated endpoint facade.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0LogPiLower : Real :=
  (1144729885849400174143417351353058711 : Real) /
    (1000000000000000000000000000000000000 : Real)

def primaryFiniteRow0Parent0Split100Sub0LogPiUpper : Real :=
  (143091235731175021767929668919132339 : Real) /
    (125000000000000000000000000000000000 : Real)

private def primaryFiniteRow0Parent0Split100Sub0PiLower : Real :=
  (314159265358979323846262 : Real) /
    (100000000000000000000000 : Real)

private def primaryFiniteRow0Parent0Split100Sub0PiUpper : Real :=
  (1570796326794896619231337 : Real) /
    (500000000000000000000000 : Real)

private def primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper : Real :=
  (17724538509055160272981587 : Real) /
    (10000000000000000000000000 : Real)

private def primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower : Real :=
  (17724538509055160272981763 : Real) /
    (10000000000000000000000000 : Real)

private theorem primaryFiniteRow0Parent0Split100Sub0PiLower_lt_pi :
    primaryFiniteRow0Parent0Split100Sub0PiLower < Real.pi := by
  change
    ((314159265358979323846262 : Real) /
      (100000000000000000000000 : Real)) < Real.pi
  pi_lower_bound [
    28284271247461900976033774484193961571393437507539 / 20000000000000000000000000000000000000000000000000,
    2-15224093497742648774363362120642342635516674827271 / 100000000000000000000000000000000000000000000000000,
    2-960735979838477543690888193288048151303313455333 / 25000000000000000000000000000000000000000000000000,
    2-240763666390155687758152344526003921226256563507 / 25000000000000000000000000000000000000000000000000,
    2-240908758965521457045679048179861111359277059077 / 100000000000000000000000000000000000000000000000000,
    2-60236260759155976846870066765560629987783748453 / 100000000000000000000000000000000000000000000000000,
    2-3764908042772953917675440180838782469676559889 / 25000000000000000000000000000000000000000000000000,
    2-941235869942867150478113571614191304137452783 / 25000000000000000000000000000000000000000000000000,
    2-470619042382848841987429988010044701236637781 / 50000000000000000000000000000000000000000000000000,
    2-117654829809007097428982847398095173207711023 / 50000000000000000000000000000000000000000000000000,
    2-58827423556167954356452246864576747220130139 / 100000000000000000000000000000000000000000000000000,
    2-2941371285954210740771704485722071953772443 / 20000000000000000000000000000000000000000000000000,
    2-3676714141238330616919418057098984789751443 / 100000000000000000000000000000000000000000000000000,
    2-919178537421805613372078770208221139362109 / 100000000000000000000000000000000000000000000000000,
    2-229794634487465338441089178319892516761143 / 100000000000000000000000000000000000000000000000000,
    2-28724329315058602778135822391091054208171 / 50000000000000000000000000000000000000000000000000,
    2-897635291127811301451868871743995836131 / 6250000000000000000000000000000000000000000000000,
    2-448817645567934396305397315509020312593 / 12500000000000000000000000000000000000000000000000,
    2-112204411392235395675066888962134963367 / 12500000000000000000000000000000000000000000000000,
    2-44881764556919337929898539846031123579 / 20000000000000000000000000000000000000000000000000,
    2-56102205696157041056083109596398099993 / 100000000000000000000000000000000000000000000000000,
    2-3506387856009938013563162089472842663 / 25000000000000000000000000000000000000000000000000,
    2-438298482001246093806581753117026287 / 12500000000000000000000000000000000000000000000000,
    2-54787310250155881791797297013058313 / 6250000000000000000000000000000000000000000000000,
    2-5478731025015591180829094148144871 / 2500000000000000000000000000000000000000000000000,
    2-13696827562538979828103588149637091 / 25000000000000000000000000000000000000000000000000,
    2-13696827562538980297111301344455851 / 100000000000000000000000000000000000000000000000000,
    2-684841378126949020718161482158027 / 20000000000000000000000000000000000000000000000000,
    2-428025861329343138864881616182397 / 50000000000000000000000000000000000000000000000000,
    2-107006465332335784773472322160201 / 50000000000000000000000000000000000000000000000000,
    2-2140129306646715695755706033777 / 4000000000000000000000000000000000000000000000000,
    2-417994005204436659341263853793 / 3125000000000000000000000000000000000000000000000,
    2-668790408327098654951613173697 / 20000000000000000000000000000000000000000000000000,
    2-167197602081774663738252731401 / 20000000000000000000000000000000000000000000000000,
    2-104498501301109164836462556809 / 50000000000000000000000000000000000000000000000000,
    2-13062312662638645604559525841 / 25000000000000000000000000000000000000000000000000,
    2-13062312662638645604559952401 / 100000000000000000000000000000000000000000000000000
  ]

private theorem primaryFiniteRow0Parent0Split100Sub0Pi_lt_upper :
    Real.pi < primaryFiniteRow0Parent0Split100Sub0PiUpper := by
  change
    Real.pi <
      ((1570796326794896619231337 : Real) /
        (500000000000000000000000 : Real))
  pi_upper_bound [
    70710678118654752440084436210484903928483593768847 / 50000000000000000000000000000000000000000000000000,
    2-1903011687217831096795420265080292829439584353409 / 12500000000000000000000000000000000000000000000000,
    2-3842943919353910174763552773152192605213253821333 / 100000000000000000000000000000000000000000000000000,
    2-963054665560622751032609378104015684905026254029 / 100000000000000000000000000000000000000000000000000,
    2-120454379482760728522839524089930555679638529539 / 50000000000000000000000000000000000000000000000000,
    2-12047252151831195369374013353112125997556749691 / 20000000000000000000000000000000000000000000000000,
    2-15059632171091815670701760723355129878706239557 / 100000000000000000000000000000000000000000000000000,
    2-1882471739885734300956227143228382608274905567 / 50000000000000000000000000000000000000000000000000,
    2-941238084765697683974859976020089402473275563 / 100000000000000000000000000000000000000000000000000,
    2-7353426863062943589311427962380948325481939 / 3125000000000000000000000000000000000000000000000,
    2-2941371177808397717822612343228837361006507 / 5000000000000000000000000000000000000000000000000,
    2-1838357053721381712982315303576294971107777 / 12500000000000000000000000000000000000000000000000,
    2-735342828247666123383883611419796957950289 / 20000000000000000000000000000000000000000000000000,
    2-91917853742180561337207877020822113936211 / 10000000000000000000000000000000000000000000000000,
    2-28724329310933167305136147289986564595143 / 12500000000000000000000000000000000000000000000000,
    2-7181082328764650694533955597772763552043 / 12500000000000000000000000000000000000000000000000,
    2-7181082329022490411614950973951966689049 / 50000000000000000000000000000000000000000000000000,
    2-1795270582271737585221589262036081250373 / 50000000000000000000000000000000000000000000000000,
    2-448817645568941582700267555848539853469 / 50000000000000000000000000000000000000000000000000,
    2-28051102848074586206186587403769452237 / 12500000000000000000000000000000000000000000000000,
    2-11220441139231408211216621919279619999 / 20000000000000000000000000000000000000000000000000,
    2-7012775712019876027126324178945685327 / 50000000000000000000000000000000000000000000000000,
    2-1753193928004984375226327012468105149 / 50000000000000000000000000000000000000000000000000,
    2-87659696400249410866875675220893301 / 10000000000000000000000000000000000000000000000000,
    2-109574620500311823616581882962897421 / 50000000000000000000000000000000000000000000000000,
    2-27393655125077959656207176299274183 / 50000000000000000000000000000000000000000000000000,
    2-13696827562538980297111301344455853 / 100000000000000000000000000000000000000000000000000,
    2-3424206890634745103590807410790137 / 100000000000000000000000000000000000000000000000000,
    2-214012930664671569432440808091199 / 25000000000000000000000000000000000000000000000000,
    2-214012930664671569546944644320403 / 100000000000000000000000000000000000000000000000000,
    2-26751616333083946196946325422213 / 50000000000000000000000000000000000000000000000000,
    2-13375808166541973098920443321377 / 100000000000000000000000000000000000000000000000000,
    2-3343952041635493274758065868487 / 100000000000000000000000000000000000000000000000000,
    2-417994005204436659345631828503 / 50000000000000000000000000000000000000000000000000,
    2-10449850130110916483646255681 / 5000000000000000000000000000000000000000000000000,
    2-26124625325277291209119051683 / 50000000000000000000000000000000000000000000000000,
    2-6531156331319322802279976201 / 50000000000000000000000000000000000000000000000000,
    2-3265578165659661401140014761 / 100000000000000000000000000000000000000000000000000
  ]

private theorem primaryFiniteRow0Parent0Split100Sub0ExpLowerHalf_le :
    Real.exp (primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2) <=
      primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper := by
  have hx0 :
      (0 : Real) <= primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0LogPiLower]
  have hx1 :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2 <= 1 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0LogPiLower]
  have hTaylor :
      (∑ m ∈ Finset.range 40,
          (primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2) ^ m /
            (Nat.factorial m)) +
        (primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2) ^ 40 *
            (40 + 1) / (Nat.factorial 40 * 40) <=
          primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0LogPiLower,
      primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper]
  exact Q3.Proofs.PrimeCert.exp_le_of_taylor_bound
    (x := primaryFiniteRow0Parent0Split100Sub0LogPiLower / 2)
    (b := primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper)
    hx0 hx1 (n := 40) (by decide) hTaylor

private theorem primaryFiniteRow0Parent0Split100Sub0ExpLower_le_piLower :
    Real.exp primaryFiniteRow0Parent0Split100Sub0LogPiLower <=
      primaryFiniteRow0Parent0Split100Sub0PiLower := by
  have hpow := Q3.Proofs.PrimeCert.exp_le_pow_of_div_le
    (x := primaryFiniteRow0Parent0Split100Sub0LogPiLower)
    (b := primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper)
    (n := 2) (by decide)
    primaryFiniteRow0Parent0Split100Sub0ExpLowerHalf_le
  have hb :
      primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper ^ 2 <=
        primaryFiniteRow0Parent0Split100Sub0PiLower := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0ExpLowerHalfUpper,
      primaryFiniteRow0Parent0Split100Sub0PiLower]
  exact hpow.trans hb

private theorem primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower_le :
    primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower <=
      Real.exp (primaryFiniteRow0Parent0Split100Sub0LogPiUpper / 2) := by
  have hx0 :
      (0 : Real) <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper / 2 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0LogPiUpper]
  have hsum :
      primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower <=
        ∑ m ∈ Finset.range 41,
          (primaryFiniteRow0Parent0Split100Sub0LogPiUpper / 2) ^ m /
            (Nat.factorial m) := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0LogPiUpper,
      primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower]
  have hle :
      (∑ m ∈ Finset.range 41,
          (primaryFiniteRow0Parent0Split100Sub0LogPiUpper / 2) ^ m /
            (Nat.factorial m)) <=
        Real.exp (primaryFiniteRow0Parent0Split100Sub0LogPiUpper / 2) := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 41)
  exact hsum.trans hle

private theorem primaryFiniteRow0Parent0Split100Sub0PiUpper_le_expUpper :
    primaryFiniteRow0Parent0Split100Sub0PiUpper <=
      Real.exp primaryFiniteRow0Parent0Split100Sub0LogPiUpper := by
  have hpow := Q3.Proofs.PrimeCert.pow_le_exp_of_le_div
    (x := primaryFiniteRow0Parent0Split100Sub0LogPiUpper)
    (a := primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower)
    (n := 2) (by decide)
    (by norm_num [primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower])
    primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower_le
  have hb :
      primaryFiniteRow0Parent0Split100Sub0PiUpper <=
        primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower ^ 2 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0PiUpper,
      primaryFiniteRow0Parent0Split100Sub0ExpUpperHalfLower]
  exact hb.trans hpow

theorem primaryFiniteRow0Parent0Split100Sub0LogPiInterval :
    primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi ∧
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper := by
  exact Q3.log_pi_interval_of_exp_bounds
    primaryFiniteRow0Parent0Split100Sub0LogPiLower
    primaryFiniteRow0Parent0Split100Sub0LogPiUpper
    primaryFiniteRow0Parent0Split100Sub0PiLower
    primaryFiniteRow0Parent0Split100Sub0PiUpper
    primaryFiniteRow0Parent0Split100Sub0ExpLower_le_piLower
    (le_of_lt primaryFiniteRow0Parent0Split100Sub0PiLower_lt_pi)
    (le_of_lt primaryFiniteRow0Parent0Split100Sub0Pi_lt_upper)
    primaryFiniteRow0Parent0Split100Sub0PiUpper_le_expUpper

theorem primaryFiniteRow0Parent0Split100Sub0LogPiLower_le :
    primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi :=
  primaryFiniteRow0Parent0Split100Sub0LogPiInterval.1

theorem primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper :
    Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper :=
  primaryFiniteRow0Parent0Split100Sub0LogPiInterval.2

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
    (hShiftAbs :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hGenerated :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            ((1 : Real) / (20 : Real)) 16 + (16 : Complex)) -
        (((((3457934361506642309616650171583002119 : Real) /
          (1000000000000000000000000000000000000 : Real)) : Real) : Complex) +
          Complex.I * (((((393668171371225061774807882120813 : Real) /
            (500000000000000000000000000000000000 : Real)) : Real) : Complex)))‖ <=
          ((1 : Real) / (2000000000000000000000 : Real)) := by
    simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint_eq_generated,
      Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
      Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using hShiftAbs
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiIntervalGenerated
      hGenerated
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0LogPiLower] using
          hLogPiLower)
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0LogPiUpper] using
          hLogPiUpper)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main
    (mainErr centerErr : Real)
    (hMain :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
        Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <= mainErr)
    (hCenter :
      ‖Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
        Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <= centerErr)
    (hErr :
      mainErr + centerErr <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hBall :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius :=
    Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_m6_main
      mainErr centerErr hMain hCenter hErr
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
      (by
        simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using hBall)
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_component_abs
    (hre :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (him :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hBall :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius :=
    Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_component_abs
      hre him
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
      (by
        simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
          Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using hBall)
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_rect_interval
    (hReLower :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re)
    (hReUpper :
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImLower :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im)
    (hImUpper :
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius := by
    rw [abs_le]
    constructor
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
  have hIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius := by
    rw [abs_le]
    constructor
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
    · simp [Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter]
      linarith
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_component_abs
      hRe hIm hLogPiLower hLogPiUpper

/-- High-order backend receiver for the fixed-rectangle route.

The current endpoint point is the `shift = 16` Step22 argument shifted by
another `16`, so generated prefix/tail rows target the same series receiver at
`shift = 32`.  This theorem is only glue from checked series interval data to
the four fixed Re/Im inequalities consumed by the first endpoint facade. -/
theorem step33Shift16Digamma_fixed_rect_interval_of_shift32_series_prefix_tail_abs
    (N : Nat)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        imPrefixLower - imTailRadius)
    (hImUpperFinal :
      imPrefixUpper + imTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius) :
    Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re ∧
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).re <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius ∧
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im ∧
      (Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint).im <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius := by
  have hRe :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_re_interval_of_series_prefix_tail_abs
      ((1 : Real) / (20 : Real)) 32 N
      (Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
      (Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
      gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      hGammaLower hGammaUpper hRePrefixLower hRePrefixUpper hReTail
      hReLowerFinal hReUpperFinal
  have hIm :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_im_interval_of_series_prefix_tail_abs
      ((1 : Real) / (20 : Real)) 32 N
      (Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
      (Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
        Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
      imPrefixLower imPrefixUpper imTailRadius hImPrefixLower hImPrefixUpper
      hImTail hImLowerFinal hImUpperFinal
  have hPoint :
      Q3.PSDpd.Step33.step33Shift16DigammaPoint =
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
          ((1 : Real) / (20 : Real)) 32 := by
    calc
      Q3.PSDpd.Step33.step33Shift16DigammaPoint =
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            ((1 : Real) / (20 : Real)) 16 + (16 : Complex) :=
        Q3.PSDpd.Step33.step33Shift16DigammaPoint_eq_generated
      _ =
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            ((1 : Real) / (20 : Real)) (16 + 16) :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg_add_sixteen_eq
          ((1 : Real) / (20 : Real)) 16
      _ =
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            ((1 : Real) / (20 : Real)) 32 := by
        norm_num
  exact
    ⟨by simpa [hPoint] using hRe.1,
      by simpa [hPoint] using hRe.2,
      by simpa [hPoint] using hIm.1,
      by simpa [hPoint] using hIm.2⟩

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_rect_shift32_series_prefix_tail_abs
    (N : Nat)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        imPrefixLower - imTailRadius)
    (hImUpperFinal :
      imPrefixUpper + imTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hRect :=
    step33Shift16Digamma_fixed_rect_interval_of_shift32_series_prefix_tail_abs
      N gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLowerFinal hReUpperFinal
      hImPrefixLower hImPrefixUpper hImTail hImLowerFinal hImUpperFinal
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_rect_interval
      hRect.1 hRect.2.1 hRect.2.2.1 hRect.2.2.2
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_rect_shift32_series_prefix_tail_abs_closedLogPi
    (N : Nat)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedRe +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 32 +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm -
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius <=
        imPrefixLower - imTailRadius)
    (hImUpperFinal :
      imPrefixUpper + imTailRadius <=
        Q3.PSDpd.Step33.step33Shift16DigammaFixedIm +
          Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_rect_shift32_series_prefix_tail_abs
      N gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLowerFinal hReUpperFinal
      hImPrefixLower hImPrefixUpper hImTail hImLowerFinal hImUpperFinal
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_component_abs
    (mainReErr mainImErr centerReErr centerImErr : Real)
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <= mainReErr)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <= mainImErr)
    (hCenterRe :
      |(Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
        centerReErr)
    (hCenterIm :
      |(Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
        centerImErr)
    (hErr :
      (mainReErr + mainImErr) + (centerReErr + centerImErr) <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hBall :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius :=
    Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_m6_component_abs
      mainReErr mainImErr centerReErr centerImErr
      hMainRe hMainIm hCenterRe hCenterIm hErr
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
      (by
        simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using hBall)
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_component_abs
    (mainReErr mainImErr logReCenter logImCenter logReErr logImErr
      centerReErr centerImErr : Real)
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <= mainReErr)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <= mainImErr)
    (hLogRe :
      |(Complex.log Q3.PSDpd.Step33.step33Shift16DigammaPoint).re -
          logReCenter| <= logReErr)
    (hLogIm :
      |(Complex.log Q3.PSDpd.Step33.step33Shift16DigammaPoint).im -
          logImCenter| <= logImErr)
    (hReBudget :
      logReErr +
          |logReCenter +
              (Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart).re -
            Q3.PSDpd.Step33.step33Shift16DigammaFixedRe| <= centerReErr)
    (hImBudget :
      logImErr +
          |logImCenter +
              (Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart).im -
            Q3.PSDpd.Step33.step33Shift16DigammaFixedIm| <= centerImErr)
    (hErr :
      (mainReErr + mainImErr) + (centerReErr + centerImErr) <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hCenter :=
    Q3.PSDpd.Step33.step33_shift16_digamma_m6_center_component_abs_of_log_component_abs
      logReCenter logImCenter logReErr logImErr centerReErr centerImErr
      hLogRe hLogIm hReBudget hImBudget
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_component_abs
      mainReErr mainImErr centerReErr centerImErr
      hMainRe hMainIm hCenter.1 hCenter.2 hErr hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_re_arg_abs
    (mainReErr mainImErr logReCenter argCenter logReErr argErr
      centerReErr centerImErr : Real)
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <= mainReErr)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <= mainImErr)
    (hLogRe :
      |Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) -
          logReCenter| <= logReErr)
    (hArg :
      |Complex.arg Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          argCenter| <= argErr)
    (hReBudget :
      logReErr +
          |logReCenter +
              (Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart).re -
            Q3.PSDpd.Step33.step33Shift16DigammaFixedRe| <= centerReErr)
    (hImBudget :
      argErr +
          |argCenter +
              (Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart).im -
            Q3.PSDpd.Step33.step33Shift16DigammaFixedIm| <= centerImErr)
    (hErr :
      (mainReErr + mainImErr) + (centerReErr + centerImErr) <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hCenter :=
    Q3.PSDpd.Step33.step33_shift16_digamma_m6_center_component_abs_of_log_re_arg_abs
      logReCenter argCenter logReErr argErr centerReErr centerImErr
      hLogRe hArg hReBudget hImBudget
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_component_abs
      mainReErr mainImErr centerReErr centerImErr
      hMainRe hMainIm hCenter.1 hCenter.2 hErr hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_re_arg_fixed_components
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hLogRe :
      |Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) -
          Q3.PSDpd.Step33.step33Shift16DigammaLogReCenter| <=
        Q3.PSDpd.Step33.step33Shift16DigammaLogReRadius)
    (hArg :
      |Complex.arg Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaArgCenter| <=
        Q3.PSDpd.Step33.step33Shift16DigammaArgRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hBall :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius :=
    Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_m6_log_re_arg_fixed_components
      hMainRe hMainIm hLogRe hArg
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
      (by
        simpa [Q3.PSDpd.Step33.step33Shift16DigammaPoint,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedRe,
          Q3.PSDpd.Step33.step33Shift16DigammaFixedIm,
          Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius] using hBall)
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_arg_fixed_components
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hArg :
      |Complex.arg Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaArgCenter| <=
        Q3.PSDpd.Step33.step33Shift16DigammaArgRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_re_arg_fixed_components
      hMainRe hMainIm
      Q3.PSDpd.Step33.step33Shift16DigammaLogRe_abs hArg
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_component_abs
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_arg_fixed_components
      hMainRe hMainIm
      Q3.PSDpd.Step33.step33Shift16DigammaArg_abs
      hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm
    (hMain :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hLogPiLower :
      primaryFiniteRow0Parent0Split100Sub0LogPiLower <= Real.log Real.pi)
    (hLogPiUpper :
      Real.log Real.pi <= primaryFiniteRow0Parent0Split100Sub0LogPiUpper) := by
  have hComp :=
    Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_component_abs_of_norm
      hMain
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_component_abs
      hComp.1 hComp.2 hLogPiLower hLogPiUpper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_component_abs_closedLogPi
    (hMainRe :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_component_abs
      hMainRe hMainIm
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm_closedLogPi
    (hMain :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm
      hMain
      primaryFiniteRow0Parent0Split100Sub0LogPiLower_le
      primaryFiniteRow0Parent0Split100Sub0LogPi_le_upper

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_expanded_asymptotic_bound_closedLogPi
    (hExpanded :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
        hExpanded)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_first_omitted_term_bound_closedLogPi
    (hFirstOmitted :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (‖Q3.PSDpd.Step33.step33Shift16DigammaPoint‖⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_first_omitted_term_bound
        hFirstOmitted)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
    (hReFirstOmitted :
      ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
          (let z : Complex := Q3.PSDpd.Step33.step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound
        hReFirstOmitted)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_integral_remainder_bound_closedLogPi
    (hIntegral :
      Q3.digammaM6IntegralRemainderBound
        Q3.PSDpd.Step33.step33Shift16DigammaPoint) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
        hIntegral)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_closedLogPi
    (N : Nat) (shiftRad defectRad : Real)
    (hShift :
      ‖Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex))‖ <=
        shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
        N shiftRad defectRad hShift hDefects hTotal)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
    (payload : Q3.PSDpd.Step33.Step33Shift16M6FiniteTelescopeScalarPayload) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_scalar_payload
        payload)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shifted_integral_remainder_and_defect_sum_closedLogPi
    (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shifted_integral_remainder_and_defect_sum
        shiftRad defectRad hShiftIntegral hShiftRad hDefects hTotal)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum_closedLogPi
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (n : Complex))‖) <=
        defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
        seriesN gammaN shiftRad defectRad shiftReRad shiftImRad tailRadius
        digammaReLower digammaReUpper digammaImLower digammaImUpper
        mainReLower mainReUpper mainImLower mainImUpper
        hTailNorm hReLower hReUpper hImLower hImUpper
        hMainReLower hMainReUpper hMainImLower hMainImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefects hTotal)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_term_payload_closedLogPi
    (payload : Q3.PSDpd.Step33.Step33Shift16M6FiniteTelescopeTermPayload) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
      payload.toScalarPayload

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shifted_integral_remainder_component_interval_defects_closedLogPi
    (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects
        shiftRad defectRad
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad
        hShiftIntegral hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects_closedLogPi
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
        seriesN gammaN shiftRad defectRad shiftReRad shiftImRad tailRadius
        digammaReLower digammaReUpper digammaImLower digammaImUpper
        mainReLower mainReUpper mainImLower mainImUpper
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad hTailNorm hReLower hReUpper hImLower
        hImUpper hMainReLower hMainReUpper hMainImLower hMainImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (errorReLower errorReUpper errorImLower errorImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hErrorReLower :
      errorReLower <=
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re)
    (hErrorReUpper :
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).re <=
      errorReUpper)
    (hErrorImLower :
      errorImLower <=
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im)
    (hErrorImUpper :
        (Q3.digamma (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (16 : Complex))).im <=
      errorImUpper)
    (hShiftReLower : -shiftReRad <= errorReLower)
    (hShiftReUpper : errorReUpper <= shiftReRad)
    (hShiftImLower : -shiftImRad <= errorImLower)
    (hShiftImUpper : errorImUpper <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14) := by
  exact
    primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_term_payload_closedLogPi
      (Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects
        shiftRad defectRad shiftReRad shiftImRad
        errorReLower errorReUpper errorImLower errorImUpper
        termReLower termReUpper termImLower termImUpper
        termReRad termImRad termRad
        hErrorReLower hErrorReUpper hErrorImLower hErrorImUpper
        hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
        hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
        hReLowerContain hReUpperContain hImLowerContain hImUpperContain
        hTermRad hDefectSum hTotal)

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
