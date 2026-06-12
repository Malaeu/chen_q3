import Q3.Proofs.PSD_CenteredCoeffBaseAHboxImport
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import
import Q3.DigammaRemainder
import Q3.Proofs.PrimeCert.IntervalLemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory
open Filter Asymptotics
open scoped BigOperators Topology

namespace Q3
namespace PSDpd
namespace CenteredCoeffAnalyticABoundsBackend

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffPenaltyImport
open CenteredCoeffRadiusFloorImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffBaseHboxImport
open CenteredCoeffCertifiedBlockImport
open CenteredCoeffGramRadiusImport
open CenteredCoeffPenaltyRadiusDominanceImport
open CenteredCoeffQRowImport

/-!
Step33 A-profile finite/tail backend.

The active A-side hbox gate needs proof-producing Arch profile bounds, not
manual scalar replay.  This module isolates the reusable analytic receiver:
split the concrete `centeredBSplineArchKernelProfile` integral into a compact
finite window and its tail, then turn finite-window and tail bounds into the
same lower/upper interval shape consumed by the generated base hbox layer.
-/

def centeredBSplineArchKernelProfileIntegrand (k : Nat) (ell x t : Real) : Real :=
  Q3.a_star t *
    (ell * Real.cos (t * x) *
      (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)

/-- Generator-facing source for the active Step33A centered Arch chunk
payloads.  This intentionally names the Lean receiver integrand itself, rather
than the raw Step22 positive-axis Omega producer, so generated chunk bounds
target the exact folded receiver surface. -/
def step33A_centeredArchGeneratorIntegrand (k : Nat) (ell x t : Real) : Real :=
  centeredBSplineArchKernelProfileIntegrand k ell x t

theorem step33A_centeredArchGeneratorIntegrand_eq_receiverIntegrand
    (k : Nat) (ell x t : Real) :
    step33A_centeredArchGeneratorIntegrand k ell x t =
      centeredBSplineArchKernelProfileIntegrand k ell x t := by
  rfl

def step22OmegaArchWeight (eta : Real) : Real :=
  (Q3.digamma ((1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex)))).re -
    Real.log Real.pi

/-- Stieltjes main term for the raw Step22 Omega weight at `eta`.

This is a proof-engine helper for endpoint payloads: generated rows can prove
rational enclosures for this elementary expression, while Lean supplies the
digamma remainder bridge. -/
def step22OmegaArchWeightStieltjesMain (eta : Real) : Real :=
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2) - Real.log Real.pi

/-- Stieltjes remainder radius for the raw Step22 Omega weight at `eta`. -/
def step22OmegaArchWeightStieltjesErr (eta : Real) : Real :=
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  1 / (4 * ‖z‖ ^ 2)

/-- Convert the checked Stieltjes digamma remainder into a raw Omega anchor
interval bound.

This does not prove any generated endpoint row by itself; it is the reusable
Omega anchor engine below `rawOmegaEndpointClosedFormBounds_generated`. -/
theorem step22OmegaArchWeight_anchor_bounds_from_stieltjes
    (eta lower upper : Real)
    (hLower :
      lower <=
        step22OmegaArchWeightStieltjesMain eta -
          step22OmegaArchWeightStieltjesErr eta)
    (hUpper :
      step22OmegaArchWeightStieltjesMain eta +
          step22OmegaArchWeightStieltjesErr eta <= upper) :
    lower <= step22OmegaArchWeight eta ∧
      step22OmegaArchWeight eta <= upper := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hz : 0 < z.re := by
    norm_num [z]
  have hrem := Q3.re_digamma_remainder_bound_stieltjes z hz
  have hrem' :
      |(Q3.digamma z).re -
          (Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2))| <=
        1 / (4 * ‖z‖ ^ 2) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
  have hleft := (abs_le.mp hrem').1
  have hright := (abs_le.mp hrem').2
  have homega_lower :
      Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2) -
          1 / (4 * ‖z‖ ^ 2) <=
        (Q3.digamma z).re := by
    linarith
  have homega_upper :
      (Q3.digamma z).re <=
        Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2) +
          1 / (4 * ‖z‖ ^ 2) := by
    linarith
  constructor
  · have hLower' :
        lower <=
          Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2) -
              Real.log Real.pi -
            1 / (4 * ‖z‖ ^ 2) := by
      simpa [step22OmegaArchWeightStieltjesMain,
        step22OmegaArchWeightStieltjesErr, z, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using hLower
    have :
        lower <= (Q3.digamma z).re - Real.log Real.pi := by
      linarith
    simpa [step22OmegaArchWeight, z]
  · have hUpper' :
        Real.log ‖z‖ - z.re / (2 * ‖z‖ ^ 2) -
              Real.log Real.pi +
            1 / (4 * ‖z‖ ^ 2) <= upper := by
      simpa [step22OmegaArchWeightStieltjesMain,
        step22OmegaArchWeightStieltjesErr, z, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using hUpper
    have :
        (Q3.digamma z).re - Real.log Real.pi <= upper := by
      linarith
    simpa [step22OmegaArchWeight, z]

/-- Raw Step22 positive-axis Omega Arch integrand.

This names the source used by the Step22 Arch payload producer:
`(ell / pi) * Omega(eta) * E(k, ell, eta)^2 * cos(eta * x)` on `eta > 0`.
It is deliberately separate from `centeredBSplineArchKernelProfileIntegrand`;
route S must prove the assembler/sign theorem before this source can feed the
active Step33A hbox receiver. -/
def step22PositiveAxisOmegaAIntegrand
    (k : Nat) (ell x eta : Real) : Real :=
  (ell / Real.pi) * step22OmegaArchWeight eta *
    (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 *
      Real.cos (eta * x)

/-- Raw Step22 positive-axis Omega Arch profile. -/
def step22PositiveAxisOmegaAProfile
    (k : Nat) (ell x : Real) : Real :=
  ∫ eta in Set.Ioi (0 : Real), step22PositiveAxisOmegaAIntegrand k ell x eta

theorem step22PositiveAxisOmegaAProfile_even
    (k : Nat) (ell x : Real) :
    step22PositiveAxisOmegaAProfile k ell (-x) =
      step22PositiveAxisOmegaAProfile k ell x := by
  unfold step22PositiveAxisOmegaAProfile step22PositiveAxisOmegaAIntegrand
  apply MeasureTheory.integral_congr_ae
  filter_upwards with eta
  have harg : eta * (-x) = -(eta * x) := by
    ring
  rw [harg, Real.cos_neg]

/-- Raw Step22 finite positive-axis Omega Arch window. -/
def step22PositiveAxisOmegaAFinitePart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ eta in Set.Ioc (0 : Real) T, step22PositiveAxisOmegaAIntegrand k ell x eta

/-- Raw Step22 positive-axis Omega Arch tail after `T`. -/
def step22PositiveAxisOmegaATailPart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ eta in Set.Ioi T, step22PositiveAxisOmegaAIntegrand k ell x eta

/-- Raw Step22 positive-axis Omega Arch tail window `(T, U]`. -/
def step22PositiveAxisOmegaATailWindowPart
    (k : Nat) (ell x T U : Real) : Real :=
  ∫ eta in Set.Ioc T U, step22PositiveAxisOmegaAIntegrand k ell x eta

/-- Split the raw Step22 positive-axis Omega tail `(T,∞)` into a finite tail
window `(T,U]` and the remaining tail `(U,∞)`. -/
theorem step22PositiveAxisOmegaATailPart_eq_tailWindow_add_tailPart
    (k : Nat) (ell x T U : Real)
    (hTU : T <= U)
    (hint :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioi T)) :
    step22PositiveAxisOmegaATailPart k ell x T =
      step22PositiveAxisOmegaATailWindowPart k ell x T U +
        step22PositiveAxisOmegaATailPart k ell x U := by
  let f : Real → Real := step22PositiveAxisOmegaAIntegrand k ell x
  have hcover : Set.Ioi T = Set.Ioc T U ∪ Set.Ioi U := by
    ext eta
    constructor
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      by_cases hle : eta <= U
      · exact Or.inl ⟨heta, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      rcases heta with hwin | htail
      · exact hwin.1
      · exact lt_of_le_of_lt hTU htail
  have hdisj : Disjoint (Set.Ioc T U) (Set.Ioi U) := by
    rw [Set.disjoint_left]
    intro eta hwin htail
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hwin htail
    exact not_lt_of_ge hwin.2 htail
  have hwindowSub : Set.Ioc T U ⊆ Set.Ioi T := by
    intro eta heta
    exact heta.1
  have htailSub : Set.Ioi U ⊆ Set.Ioi T := by
    intro eta heta
    exact lt_of_le_of_lt hTU heta
  have hwindowInt : IntegrableOn f (Set.Ioc T U) := by
    exact hint.mono_set hwindowSub
  have htailInt : IntegrableOn f (Set.Ioi U) := by
    exact hint.mono_set htailSub
  unfold step22PositiveAxisOmegaATailPart step22PositiveAxisOmegaATailWindowPart
  rw [hcover]
  rw [setIntegral_union hdisj measurableSet_Ioi hwindowInt htailInt]

/-- Split the raw Step22 positive-axis Omega profile into its finite positive
window `(0,T]` and positive tail `(T,∞)`. -/
theorem step22PositiveAxisOmegaAProfile_eq_finitePart_add_tailPart
    (k : Nat) (ell x T : Real)
    (hT : 0 <= T)
    (hint :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x)
        (Set.Ioi (0 : Real))) :
    step22PositiveAxisOmegaAProfile k ell x =
      step22PositiveAxisOmegaAFinitePart k ell x T +
        step22PositiveAxisOmegaATailPart k ell x T := by
  let f : Real → Real := step22PositiveAxisOmegaAIntegrand k ell x
  have hcover : Set.Ioi (0 : Real) = Set.Ioc (0 : Real) T ∪ Set.Ioi T := by
    ext eta
    constructor
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      by_cases hle : eta <= T
      · exact Or.inl ⟨heta, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      rcases heta with hwin | htail
      · exact hwin.1
      · exact lt_of_le_of_lt hT htail
  have hdisj : Disjoint (Set.Ioc (0 : Real) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro eta hwin htail
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hwin htail
    exact not_lt_of_ge hwin.2 htail
  have hfiniteSub : Set.Ioc (0 : Real) T ⊆ Set.Ioi (0 : Real) := by
    intro eta heta
    exact heta.1
  have htailSub : Set.Ioi T ⊆ Set.Ioi (0 : Real) := by
    intro eta heta
    exact lt_of_le_of_lt hT heta
  have hfiniteInt : IntegrableOn f (Set.Ioc (0 : Real) T) := by
    exact hint.mono_set hfiniteSub
  have htailInt : IntegrableOn f (Set.Ioi T) := by
    exact hint.mono_set htailSub
  unfold step22PositiveAxisOmegaAProfile step22PositiveAxisOmegaAFinitePart
    step22PositiveAxisOmegaATailPart
  rw [hcover]
  rw [setIntegral_union hdisj measurableSet_Ioi hfiniteInt htailInt]

/-- Raw Step22 positive-axis Omega finite/tail interval certificate.  It
separates analytic interval work from arithmetic containment in the imported
payload box. -/
structure step22PositiveAxisOmegaAFiniteTailIntervalCert
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real) :
    Prop where
  hFiniteLower :
    finiteLower <= step22PositiveAxisOmegaAFinitePart k ell x T
  hFiniteUpper :
    step22PositiveAxisOmegaAFinitePart k ell x T <= finiteUpper
  hTail :
    |step22PositiveAxisOmegaATailPart k ell x T| <= tailRadius
  hLower : lower <= finiteLower - tailRadius
  hUpper : finiteUpper + tailRadius <= upper

theorem step22PositiveAxisOmegaAProfile_bounds_of_finiteTailIntervalCert
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (hT : 0 <= T)
    (hint :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x)
        (Set.Ioi (0 : Real)))
    (cert : step22PositiveAxisOmegaAFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius) :
    lower <= step22PositiveAxisOmegaAProfile k ell x ∧
      step22PositiveAxisOmegaAProfile k ell x <= upper := by
  constructor
  · rw [step22PositiveAxisOmegaAProfile_eq_finitePart_add_tailPart
      k ell x T hT hint]
    have hTailLower :
        -tailRadius <= step22PositiveAxisOmegaATailPart k ell x T :=
      (abs_le.mp cert.hTail).1
    linarith [cert.hLower, cert.hFiniteLower, hTailLower]
  · rw [step22PositiveAxisOmegaAProfile_eq_finitePart_add_tailPart
      k ell x T hT hint]
    have hTailUpper :
      step22PositiveAxisOmegaATailPart k ell x T <= tailRadius :=
      (abs_le.mp cert.hTail).2
    linarith [cert.hUpper, cert.hFiniteUpper, hTailUpper]

/-- Raw Step22 positive-axis Omega finite-window bounds from comparison
integrals on `(0,T]`.  This is the proof-side receiver that generated
finite-window payloads should target; arithmetic-only payloads are not enough
to prove these hypotheses. -/
theorem step22PositiveAxisOmegaAFinitePart_bounds_of_comparison_integrals
    (k : Nat) (ell x T finiteLower finiteUpper : Real)
    (lowerF upperF : Real → Real)
    (hProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x)
        (Set.Ioc (0 : Real) T))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc (0 : Real) T))
    (hUpperInt : IntegrableOn upperF (Set.Ioc (0 : Real) T))
    (hLower : ∀ eta ∈ Set.Ioc (0 : Real) T,
      lowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hUpper : ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= upperF eta)
    (hFiniteLower : finiteLower <= ∫ eta in Set.Ioc (0 : Real) T, lowerF eta)
    (hFiniteUpper : ∫ eta in Set.Ioc (0 : Real) T, upperF eta <= finiteUpper) :
    finiteLower <= step22PositiveAxisOmegaAFinitePart k ell x T ∧
      step22PositiveAxisOmegaAFinitePart k ell x T <= finiteUpper := by
  constructor
  · calc
      finiteLower <= ∫ eta in Set.Ioc (0 : Real) T, lowerF eta :=
        hFiniteLower
      _ <= ∫ eta in Set.Ioc (0 : Real) T,
          step22PositiveAxisOmegaAIntegrand k ell x eta := by
            exact setIntegral_mono_on hLowerInt hProfileInt measurableSet_Ioc hLower
      _ = step22PositiveAxisOmegaAFinitePart k ell x T := by
            rfl
  · calc
      step22PositiveAxisOmegaAFinitePart k ell x T =
          ∫ eta in Set.Ioc (0 : Real) T,
            step22PositiveAxisOmegaAIntegrand k ell x eta := by
            rfl
      _ <= ∫ eta in Set.Ioc (0 : Real) T, upperF eta := by
            exact setIntegral_mono_on hProfileInt hUpperInt measurableSet_Ioc hUpper
      _ <= finiteUpper := hFiniteUpper

/-- Build a raw Step22 positive-axis Omega finite/tail interval certificate
from finite-window comparison integrals, a tail absolute bound, and the
arithmetic containment into the target payload interval. -/
theorem step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tail_bound
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (lowerF upperF : Real → Real)
    (hProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x)
        (Set.Ioc (0 : Real) T))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc (0 : Real) T))
    (hUpperInt : IntegrableOn upperF (Set.Ioc (0 : Real) T))
    (hLower : ∀ eta ∈ Set.Ioc (0 : Real) T,
      lowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hUpper : ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= upperF eta)
    (hFiniteLower : finiteLower <= ∫ eta in Set.Ioc (0 : Real) T, lowerF eta)
    (hFiniteUpper : ∫ eta in Set.Ioc (0 : Real) T, upperF eta <= finiteUpper)
    (hTail : |step22PositiveAxisOmegaATailPart k ell x T| <= tailRadius)
    (hLowerArith : lower <= finiteLower - tailRadius)
    (hUpperArith : finiteUpper + tailRadius <= upper) :
    step22PositiveAxisOmegaAFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  have hFinite :=
    step22PositiveAxisOmegaAFinitePart_bounds_of_comparison_integrals
      k ell x T finiteLower finiteUpper lowerF upperF hProfileInt
      hLowerInt hUpperInt hLower hUpper hFiniteLower hFiniteUpper
  exact
    { hFiniteLower := hFinite.1
      hFiniteUpper := hFinite.2
      hTail := hTail
      hLower := hLowerArith
      hUpper := hUpperArith }

/-- Raw Step22 positive-axis Omega tail-window bounds from comparison
integrals on `(T,U]`. -/
theorem step22PositiveAxisOmegaATailWindowPart_bounds_of_comparison_integrals
    (k : Nat) (ell x T U windowLower windowUpper : Real)
    (lowerF upperF : Real → Real)
    (hProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioc T U))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc T U))
    (hUpperInt : IntegrableOn upperF (Set.Ioc T U))
    (hLower : ∀ eta ∈ Set.Ioc T U,
      lowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hUpper : ∀ eta ∈ Set.Ioc T U,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= upperF eta)
    (hWindowLower : windowLower <= ∫ eta in Set.Ioc T U, lowerF eta)
    (hWindowUpper : ∫ eta in Set.Ioc T U, upperF eta <= windowUpper) :
    windowLower <= step22PositiveAxisOmegaATailWindowPart k ell x T U ∧
      step22PositiveAxisOmegaATailWindowPart k ell x T U <= windowUpper := by
  constructor
  · calc
      windowLower <= ∫ eta in Set.Ioc T U, lowerF eta := hWindowLower
      _ <= ∫ eta in Set.Ioc T U,
          step22PositiveAxisOmegaAIntegrand k ell x eta := by
            exact setIntegral_mono_on hLowerInt hProfileInt measurableSet_Ioc hLower
      _ = step22PositiveAxisOmegaATailWindowPart k ell x T U := by
            rfl
  · calc
      step22PositiveAxisOmegaATailWindowPart k ell x T U =
          ∫ eta in Set.Ioc T U,
            step22PositiveAxisOmegaAIntegrand k ell x eta := by
            rfl
      _ <= ∫ eta in Set.Ioc T U, upperF eta := by
            exact setIntegral_mono_on hProfileInt hUpperInt measurableSet_Ioc hUpper
      _ <= windowUpper := hWindowUpper

/-- Raw Step22 positive-axis Omega tail-window interval certificate. -/
structure step22PositiveAxisOmegaATailWindowIntervalCert
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real) :
    Prop where
  hWindowLower :
    windowLower <= step22PositiveAxisOmegaATailWindowPart k ell x T U
  hWindowUpper :
    step22PositiveAxisOmegaATailWindowPart k ell x T U <= windowUpper
  hRemainder :
    |step22PositiveAxisOmegaATailPart k ell x U| <= remainderRadius

theorem step22PositiveAxisOmegaATailWindowIntervalCert_of_comparison_integrals
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real)
    (lowerF upperF : Real → Real)
    (hProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioc T U))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc T U))
    (hUpperInt : IntegrableOn upperF (Set.Ioc T U))
    (hLower : ∀ eta ∈ Set.Ioc T U,
      lowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hUpper : ∀ eta ∈ Set.Ioc T U,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= upperF eta)
    (hWindowLower : windowLower <= ∫ eta in Set.Ioc T U, lowerF eta)
    (hWindowUpper : ∫ eta in Set.Ioc T U, upperF eta <= windowUpper)
    (hRemainder :
      |step22PositiveAxisOmegaATailPart k ell x U| <= remainderRadius) :
    step22PositiveAxisOmegaATailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius := by
  have hWindow :=
    step22PositiveAxisOmegaATailWindowPart_bounds_of_comparison_integrals
      k ell x T U windowLower windowUpper lowerF upperF hProfileInt
      hLowerInt hUpperInt hLower hUpper hWindowLower hWindowUpper
  exact
    { hWindowLower := hWindow.1
      hWindowUpper := hWindow.2
      hRemainder := hRemainder }

theorem step22PositiveAxisOmegaATail_abs_le_of_tailWindowIntervalCert
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius
      tailRadius : Real)
    (hTU : T <= U)
    (hint :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioi T))
    (cert : step22PositiveAxisOmegaATailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius)
    (hTailLower : -tailRadius <= windowLower - remainderRadius)
    (hTailUpper : windowUpper + remainderRadius <= tailRadius) :
    |step22PositiveAxisOmegaATailPart k ell x T| <= tailRadius := by
  rw [abs_le]
  have hsplit :=
    step22PositiveAxisOmegaATailPart_eq_tailWindow_add_tailPart
      k ell x T U hTU hint
  have hrem := abs_le.mp cert.hRemainder
  constructor
  · rw [hsplit]
    linarith [cert.hWindowLower, hrem.1, hTailLower]
  · rw [hsplit]
    linarith [cert.hWindowUpper, hrem.2, hTailUpper]

theorem step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tailWindow
    (k : Nat) (ell x T U lower upper finiteLower finiteUpper
      tailWindowLower tailWindowUpper tailRemainderRadius tailRadius : Real)
    (finiteLowerF finiteUpperF tailLowerF tailUpperF : Real → Real)
    (hTailWindow : T <= U)
    (hFiniteProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x)
        (Set.Ioc (0 : Real) T))
    (hTailProfileInt :
      IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioi T))
    (hFiniteLowerInt :
      IntegrableOn finiteLowerF (Set.Ioc (0 : Real) T))
    (hFiniteUpperInt :
      IntegrableOn finiteUpperF (Set.Ioc (0 : Real) T))
    (hFiniteLower : ∀ eta ∈ Set.Ioc (0 : Real) T,
      finiteLowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hFiniteUpper : ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= finiteUpperF eta)
    (hFiniteLowerBound :
      finiteLower <= ∫ eta in Set.Ioc (0 : Real) T, finiteLowerF eta)
    (hFiniteUpperBound :
      ∫ eta in Set.Ioc (0 : Real) T, finiteUpperF eta <= finiteUpper)
    (hTailLowerInt : IntegrableOn tailLowerF (Set.Ioc T U))
    (hTailUpperInt : IntegrableOn tailUpperF (Set.Ioc T U))
    (hTailLower : ∀ eta ∈ Set.Ioc T U,
      tailLowerF eta <= step22PositiveAxisOmegaAIntegrand k ell x eta)
    (hTailUpper : ∀ eta ∈ Set.Ioc T U,
      step22PositiveAxisOmegaAIntegrand k ell x eta <= tailUpperF eta)
    (hTailWindowLower :
      tailWindowLower <= ∫ eta in Set.Ioc T U, tailLowerF eta)
    (hTailWindowUpper :
      ∫ eta in Set.Ioc T U, tailUpperF eta <= tailWindowUpper)
    (hTailRemainder :
      |step22PositiveAxisOmegaATailPart k ell x U| <= tailRemainderRadius)
    (hTailLowerArith : -tailRadius <= tailWindowLower - tailRemainderRadius)
    (hTailUpperArith : tailWindowUpper + tailRemainderRadius <= tailRadius)
    (hLowerArith : lower <= finiteLower - tailRadius)
    (hUpperArith : finiteUpper + tailRadius <= upper) :
    step22PositiveAxisOmegaAFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  have hFinite :=
    step22PositiveAxisOmegaAFinitePart_bounds_of_comparison_integrals
      k ell x T finiteLower finiteUpper finiteLowerF finiteUpperF
      hFiniteProfileInt hFiniteLowerInt hFiniteUpperInt hFiniteLower
      hFiniteUpper hFiniteLowerBound hFiniteUpperBound
  have hTailWindowCert :
      step22PositiveAxisOmegaATailWindowIntervalCert
        k ell x T U tailWindowLower tailWindowUpper tailRemainderRadius :=
    step22PositiveAxisOmegaATailWindowIntervalCert_of_comparison_integrals
      k ell x T U tailWindowLower tailWindowUpper tailRemainderRadius
      tailLowerF tailUpperF
      (hTailProfileInt.mono_set (by intro eta heta; exact heta.1))
      hTailLowerInt hTailUpperInt hTailLower hTailUpper
      hTailWindowLower hTailWindowUpper hTailRemainder
  have hTail :=
    step22PositiveAxisOmegaATail_abs_le_of_tailWindowIntervalCert
      k ell x T U tailWindowLower tailWindowUpper tailRemainderRadius
      tailRadius hTailWindow hTailProfileInt hTailWindowCert
      hTailLowerArith hTailUpperArith
  exact
    { hFiniteLower := hFinite.1
      hFiniteUpper := hFinite.2
      hTail := hTail
      hLower := hLowerArith
      hUpper := hUpperArith }

/-- Candidate C-level profile for route S: raw Step22 Omega Arch minus the
finite prime profile.  This is only a named target for the semantic assembler
route; it does not retarget the active Step33 receiver by itself. -/
def step22PositiveAxisOmegaCProfile
    {ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (weight shift : ν → Real) (x : Real) : Real :=
  step22PositiveAxisOmegaAProfile k ell x -
    centeredBSplineFinitePrimeKernelProfile k ell weight shift x

theorem step22PositiveAxisOmegaCProfile_eq_step22PositiveAxisOmega_sub_primeProfile
    {ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (weight shift : ν → Real) (x : Real) :
    step22PositiveAxisOmegaCProfile k ell weight shift x =
      step22PositiveAxisOmegaAProfile k ell x -
        centeredBSplineFinitePrimeKernelProfile k ell weight shift x := by
  rfl

/-- The current centered finite Weil C profile induced by the existing
centered coefficient assembler. -/
def centeredBSplineFiniteWeilCProfile
    {ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (weight shift : ν → Real) (x : Real) : Real :=
  centeredBSplineArchKernelProfile k ell x -
    centeredBSplineFinitePrimeKernelProfile k ell weight shift x

theorem centeredBSplineFiniteWeilCProfile_eq_centeredArch_sub_primeProfile
    {ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (weight shift : ν → Real) (x : Real) :
    centeredBSplineFiniteWeilCProfile k ell weight shift x =
      centeredBSplineArchKernelProfile k ell x -
        centeredBSplineFinitePrimeKernelProfile k ell weight shift x := by
  rfl

/-- On the current centered assembler, the desired raw-Step22 C-profile
identity is exactly the local Arch-profile identity.  Route S therefore needs
a genuine upstream assembler retarget, not a local C-level rewrite. -/
theorem centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmegaCProfile_iff_archProfile_eq
    {ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (weight shift : ν → Real) (x : Real) :
    centeredBSplineFiniteWeilCProfile k ell weight shift x =
        step22PositiveAxisOmegaCProfile k ell weight shift x ↔
      centeredBSplineArchKernelProfile k ell x =
        step22PositiveAxisOmegaAProfile k ell x := by
  unfold centeredBSplineFiniteWeilCProfile step22PositiveAxisOmegaCProfile
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Raw Step22 positive-axis Omega Arch matrix over packet centers. -/
def step22PositiveAxisOmegaAMatrix
    {ι : Type*}
    (k : Nat) (ell : Real) (center : ι → Real) : Matrix ι ι Real :=
  fun i j => step22PositiveAxisOmegaAProfile k ell (center j - center i)

/-- Raw Step22 positive-axis Omega Arch pairing on coefficient packets.

Unlike `step22PositiveAxisOmegaArchMatrixShadowForm`, this is sourced from the
analytic raw-Omega profile, not from the target matrix object. -/
noncomputable def step22PositiveAxisOmegaArchPacketCoeffPairing
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real)
    (x y : ι → Complex) : Real :=
  ∑ i, ∑ j,
    ((x j) * star (y i)).re *
      step22PositiveAxisOmegaAProfile k ell (center j - center i)

/-- Left additivity of the raw-Omega Arch coefficient pairing. -/
theorem step22PositiveAxisOmegaArchPacketCoeffPairing_add_left
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) (x y z : ι → Complex) :
    step22PositiveAxisOmegaArchPacketCoeffPairing k ell center (x + y) z =
      step22PositiveAxisOmegaArchPacketCoeffPairing k ell center x z +
        step22PositiveAxisOmegaArchPacketCoeffPairing k ell center y z := by
  unfold step22PositiveAxisOmegaArchPacketCoeffPairing
  simp only [Pi.add_apply, add_mul, Complex.add_re]
  simp only [Finset.sum_add_distrib]

/-- Left real homogeneity of the raw-Omega Arch coefficient pairing. -/
theorem step22PositiveAxisOmegaArchPacketCoeffPairing_smul_left
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell c : Real) (center : ι → Real) (x z : ι → Complex) :
    step22PositiveAxisOmegaArchPacketCoeffPairing k ell center (c • x) z =
      c * step22PositiveAxisOmegaArchPacketCoeffPairing k ell center x z := by
  unfold step22PositiveAxisOmegaArchPacketCoeffPairing
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp
  ring_nf

/-- Right additivity of the raw-Omega Arch coefficient pairing. -/
theorem step22PositiveAxisOmegaArchPacketCoeffPairing_add_right
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) (x y z : ι → Complex) :
    step22PositiveAxisOmegaArchPacketCoeffPairing k ell center z (x + y) =
      step22PositiveAxisOmegaArchPacketCoeffPairing k ell center z x +
        step22PositiveAxisOmegaArchPacketCoeffPairing k ell center z y := by
  unfold step22PositiveAxisOmegaArchPacketCoeffPairing
  simp only [Pi.add_apply, star_add, mul_add, Complex.add_re, add_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]

/-- Right real homogeneity of the raw-Omega Arch coefficient pairing. -/
theorem step22PositiveAxisOmegaArchPacketCoeffPairing_smul_right
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell c : Real) (center : ι → Real) (x z : ι → Complex) :
    step22PositiveAxisOmegaArchPacketCoeffPairing k ell center z (c • x) =
      c * step22PositiveAxisOmegaArchPacketCoeffPairing k ell center z x := by
  unfold step22PositiveAxisOmegaArchPacketCoeffPairing
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp
  ring_nf

/-- Basis entries of the raw-Omega Arch coefficient pairing are exactly the
raw Step22 positive-axis Omega Arch profile. -/
theorem step22PositiveAxisOmegaArchPacketCoeffPairing_basis_closed
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) (i j : ι) :
    step22PositiveAxisOmegaArchPacketCoeffPairing k ell center
      (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i) =
      step22PositiveAxisOmegaAProfile k ell (center j - center i) := by
  classical
  unfold step22PositiveAxisOmegaArchPacketCoeffPairing centeredBSplineCoeffBasis
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _hj' hj'
      simp [hj']
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  · intro i' _hi' hi'
    simp [hi']
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- Real-bilinear raw-Omega Arch form on coefficient packets, sourced from the
raw Step22 positive-axis Omega profile. -/
noncomputable def step22PositiveAxisOmegaArchPacketCoeffBilinearForm
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) :
    (ι → Complex) →ₗ[Real] (ι → Complex) →ₗ[Real] Real :=
  realBilinearFormOfPairing
    (step22PositiveAxisOmegaArchPacketCoeffPairing k ell center)
    (fun x y z =>
      step22PositiveAxisOmegaArchPacketCoeffPairing_add_left
        k ell center x y z)
    (fun c x z =>
      step22PositiveAxisOmegaArchPacketCoeffPairing_smul_left
        k ell c center x z)
    (fun x y z =>
      step22PositiveAxisOmegaArchPacketCoeffPairing_add_right
        k ell center y z x)
    (fun c x y =>
      step22PositiveAxisOmegaArchPacketCoeffPairing_smul_right
        k ell c center y x)

/-- Raw-Omega Arch packet-kernel data induced by the Step22 positive-axis
Omega profile. -/
noncomputable def step22PositiveAxisOmegaArchPacketCoeffKernelData
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) :
    PacketKernelPairingData ι (ι → Complex) where
  basisExpansion := centeredBSplineCoeffBasisExpansion
  form := step22PositiveAxisOmegaArchPacketCoeffBilinearForm k ell center
  kernel := fun i j => step22PositiveAxisOmegaAProfile k ell (center j - center i)
  pairing_ident := by
    intro i j
    dsimp [centeredBSplineCoeffBasisExpansion]
    change step22PositiveAxisOmegaAProfile k ell (center j - center i) =
      step22PositiveAxisOmegaArchPacketCoeffPairing k ell center
        (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i)
    rw [step22PositiveAxisOmegaArchPacketCoeffPairing_basis_closed]

/-- The raw-Omega Arch kernel-data matrix is the raw Step22 positive-axis
Omega Arch matrix. -/
theorem step22PositiveAxisOmegaArchPacketCoeffKernelData_matrix_eq_AMatrix
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) :
    (step22PositiveAxisOmegaArchPacketCoeffKernelData k ell center).matrix =
      step22PositiveAxisOmegaAMatrix k ell center := by
  rfl

/-- The profile-sourced raw-Omega Arch coefficient form expands to the raw
Step22 positive-axis Omega Arch matrix quadratic form. -/
theorem step22PositiveAxisOmegaArchPacketCoeffBilinearForm_synth_eq_quadForm
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) (v : ι → Real) :
    (step22PositiveAxisOmegaArchPacketCoeffBilinearForm k ell center)
        (centeredBSplineCoeffBasisExpansion.synth v)
        (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (step22PositiveAxisOmegaAMatrix k ell center) v := by
  rw [← step22PositiveAxisOmegaArchPacketCoeffKernelData_matrix_eq_AMatrix
    k ell center]
  exact (step22PositiveAxisOmegaArchPacketCoeffKernelData
    k ell center).form_synth_eq_quadForm v

/-- Finite Prime matrix over packet centers, using the existing centered prime
profile. -/
def centeredBSplineFinitePrimeProfileMatrix
    {ι ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    Matrix ι ι Real :=
  fun i j => centeredBSplineFinitePrimeKernelProfile k ell weight shift
    (center j - center i)

/-- Raw Step22 positive-axis Omega finite Weil C matrix over packet centers. -/
def step22PositiveAxisOmegaCMatrix
    {ι ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    Matrix ι ι Real :=
  fun i j => step22PositiveAxisOmegaCProfile k ell weight shift
    (center j - center i)

theorem step22PositiveAxisOmegaCMatrix_entry
    {ι ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real)
    (i j : ι) :
    step22PositiveAxisOmegaCMatrix k ell center weight shift i j =
      step22PositiveAxisOmegaCProfile k ell weight shift
        (center j - center i) := by
  rfl

/-- Matrix-level raw-Omega finite C assembler:
`C = A_rawStep22Omega - P`. -/
theorem step22PositiveAxisOmegaCMatrix_eq_matrixSub
    {ι ν : Type*} [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    step22PositiveAxisOmegaCMatrix k ell center weight shift =
      matrixSub
        (step22PositiveAxisOmegaAMatrix k ell center)
        (centeredBSplineFinitePrimeProfileMatrix k ell center weight shift) := by
  funext i j
  unfold step22PositiveAxisOmegaCMatrix step22PositiveAxisOmegaCProfile
    step22PositiveAxisOmegaAMatrix centeredBSplineFinitePrimeProfileMatrix
    matrixSub
  rfl

theorem step22PositiveAxisOmegaCMatrix_quadForm_eq_arch_sub_prime
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real)
    (v : ι → Real) :
    Q3.Proofs.quadForm
        (step22PositiveAxisOmegaCMatrix k ell center weight shift) v =
      Q3.Proofs.quadForm
          (step22PositiveAxisOmegaAMatrix k ell center) v -
        Q3.Proofs.quadForm
          (centeredBSplineFinitePrimeProfileMatrix k ell center weight shift) v := by
  rw [step22PositiveAxisOmegaCMatrix_eq_matrixSub k ell center weight shift]
  exact quadForm_matrixSub
    (step22PositiveAxisOmegaAMatrix k ell center)
    (centeredBSplineFinitePrimeProfileMatrix k ell center weight shift)
    v

theorem matrixSub_eq_matrixSub_same_right_iff_left_eq
    {ι : Type*} (A A' P : Matrix ι ι Real) :
    matrixSub A P = matrixSub A' P ↔ A = A' := by
  constructor
  · intro h
    ext i j
    have hij := congrFun (congrFun h i) j
    unfold matrixSub at hij
    linarith
  · intro h
    rw [h]

theorem matrixSub_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
    {ι ν : Type*} [Fintype ν]
    (A : Matrix ι ι Real)
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    matrixSub A (centeredBSplineFinitePrimeProfileMatrix k ell center weight shift) =
        step22PositiveAxisOmegaCMatrix k ell center weight shift ↔
      A = step22PositiveAxisOmegaAMatrix k ell center := by
  rw [step22PositiveAxisOmegaCMatrix_eq_matrixSub k ell center weight shift]
  exact matrixSub_eq_matrixSub_same_right_iff_left_eq
    A
    (step22PositiveAxisOmegaAMatrix k ell center)
    (centeredBSplineFinitePrimeProfileMatrix k ell center weight shift)

theorem centeredBSplineFinitePrimeProfileMatrix_eq_packetCoeffMatrix
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    centeredBSplineFinitePrimeProfileMatrix k ell center weight shift =
      (centeredBSplineFinitePrimePacketCoeffKernelData
        k ell center weight shift).matrix := by
  rfl

theorem centeredBSplineCoeffFormulaContractC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real)
    (hk : 0 < k) (hell : 0 < ell) :
    (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.C =
        step22PositiveAxisOmegaCMatrix k ell center weight shift ↔
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.A =
        step22PositiveAxisOmegaAMatrix k ell center := by
  change
    matrixSub
        (centeredBSplineArchPacketCoeffKernelData k ell center hk hell).matrix
        (centeredBSplineFinitePrimePacketCoeffKernelData
          k ell center weight shift).matrix =
        step22PositiveAxisOmegaCMatrix k ell center weight shift ↔
      (centeredBSplineArchPacketCoeffKernelData k ell center hk hell).matrix =
        step22PositiveAxisOmegaAMatrix k ell center
  rw [← centeredBSplineFinitePrimeProfileMatrix_eq_packetCoeffMatrix
    k ell center weight shift]
  exact matrixSub_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
    (centeredBSplineArchPacketCoeffKernelData k ell center hk hell).matrix
    k ell center weight shift

theorem primaryK11AnalyticC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq :
    primaryK11AnalyticC =
        step22PositiveAxisOmegaCMatrix
          11 primaryK11Ell primaryK11Center primaryK11PrimeWeight
          primaryK11PrimeShift ↔
      primaryK11CoeffAnalyticKernelContract.toFormulaContract.A =
        step22PositiveAxisOmegaAMatrix 11 primaryK11Ell primaryK11Center := by
  simpa [primaryK11AnalyticC, primaryK11CoeffAnalyticKernelContract] using
    (centeredBSplineCoeffFormulaContractC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight
      primaryK11PrimeShift primaryK11_hk primaryK11_hell)

theorem controlK9AnalyticC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq :
    controlK9AnalyticC =
        step22PositiveAxisOmegaCMatrix
          9 controlK9Ell controlK9Center controlK9PrimeWeight
          controlK9PrimeShift ↔
      controlK9CoeffAnalyticKernelContract.toFormulaContract.A =
        step22PositiveAxisOmegaAMatrix 9 controlK9Ell controlK9Center := by
  simpa [controlK9AnalyticC, controlK9CoeffAnalyticKernelContract] using
    (centeredBSplineCoeffFormulaContractC_eq_step22PositiveAxisOmegaCMatrix_iff_archMatrix_eq
      9 controlK9Ell controlK9Center controlK9PrimeWeight
      controlK9PrimeShift controlK9_hk controlK9_hell)

theorem step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real)
    (rawOmegaArchForm weilForm : (ι → Complex) → Real)
    (hArch : ∀ v : ι → Real,
      rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) =
        Q3.Proofs.quadForm
          (step22PositiveAxisOmegaAMatrix k ell center) v)
    (hWeilSplit : ∀ v : ι → Real,
      weilForm (centeredBSplineCoeffBasisExpansion.synth v) =
        rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) -
          (centeredBSplineFinitePrimePacketCoeffBilinearForm
            k ell center weight shift)
            (centeredBSplineCoeffBasisExpansion.synth v)
            (centeredBSplineCoeffBasisExpansion.synth v))
    (v : ι → Real) :
    weilForm (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (step22PositiveAxisOmegaCMatrix k ell center weight shift) v := by
  calc
    weilForm (centeredBSplineCoeffBasisExpansion.synth v)
        =
          rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) -
            (centeredBSplineFinitePrimePacketCoeffBilinearForm
              k ell center weight shift)
              (centeredBSplineCoeffBasisExpansion.synth v)
              (centeredBSplineCoeffBasisExpansion.synth v) := by
            exact hWeilSplit v
    _ =
          Q3.Proofs.quadForm
              (step22PositiveAxisOmegaAMatrix k ell center) v -
            Q3.Proofs.quadForm
              (centeredBSplineFinitePrimePacketCoeffKernelData
                k ell center weight shift).matrix v := by
            rw [hArch v]
            rw [centeredBSplineFinitePrimePacketCoeffBilinearForm_synth_eq_quadForm
              k ell center weight shift v]
    _ =
          Q3.Proofs.quadForm
              (step22PositiveAxisOmegaAMatrix k ell center) v -
            Q3.Proofs.quadForm
              (centeredBSplineFinitePrimeProfileMatrix
                k ell center weight shift) v := by
            rw [centeredBSplineFinitePrimeProfileMatrix_eq_packetCoeffMatrix
              k ell center weight shift]
    _ =
        Q3.Proofs.quadForm
          (step22PositiveAxisOmegaCMatrix k ell center weight shift) v := by
          rw [← step22PositiveAxisOmegaCMatrix_quadForm_eq_arch_sub_prime
            k ell center weight shift v]

noncomputable def step22PositiveAxisOmegaFiniteWeilMatrixModel_of_rawOmegaArchReceiver
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real)
    (hk : 0 < k) (hell : 0 < ell)
    (rawOmegaArchForm weilForm : (ι → Complex) → Real)
    (hArch : ∀ v : ι → Real,
      rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) =
        Q3.Proofs.quadForm
          (step22PositiveAxisOmegaAMatrix k ell center) v)
    (hWeilSplit : ∀ v : ι → Real,
      weilForm (centeredBSplineCoeffBasisExpansion.synth v) =
        rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) -
          (centeredBSplineFinitePrimePacketCoeffBilinearForm
            k ell center weight shift)
            (centeredBSplineCoeffBasisExpansion.synth v)
            (centeredBSplineCoeffBasisExpansion.synth v)) :
    FiniteWeilMatrixModel
      (V := ι → Complex)
      (step22PositiveAxisOmegaCMatrix k ell center weight shift)
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q where
  synth := centeredBSplineCoeffBasisExpansion.synth
  weilForm := weilForm
  boundary := centeredBSplineCoeffBoundaryPair center
  weil_ident := by
    intro v
    exact
      step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
        k ell center weight shift rawOmegaArchForm weilForm hArch hWeilSplit v
  analyticBoundary_to_matrixBoundary := by
    intro v hplus hminus
    exact
      (centeredBSplineCoeffFiniteWeilMatrixModel
        k ell center weight shift hk hell).analyticBoundary_to_matrixBoundary
          v hplus hminus

/-- The exact upstream raw-Omega Arch receiver still missing in route S.

This record is deliberately semantic: it asks for a real Arch form on the
coefficient packet space and its quadratic-form identification with the raw
Step22 positive-axis Omega Arch matrix.  It is not a numeric payload shortcut. -/
structure Step22PositiveAxisOmegaRawArchReceiver
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) where
  rawOmegaArchForm : (ι → Complex) → Real
  arch_ident :
    ∀ v : ι → Real,
      rawOmegaArchForm (centeredBSplineCoeffBasisExpansion.synth v) =
        Q3.Proofs.quadForm
          (step22PositiveAxisOmegaAMatrix k ell center) v

/-- Diagnostic-only coordinate shadow of the raw-Omega Arch form.

This form is built from the target matrix itself by reading real coordinates
out of the coefficient packet.  It proves that the matrix identity alone is
too weak to be the Step33 semantic receiver: the real route still needs an
independently defined Arch form and an analytic theorem identifying it with
`step22PositiveAxisOmegaAMatrix`. -/
noncomputable def step22PositiveAxisOmegaArchMatrixShadowForm
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) :
    (ι → Complex) → Real :=
  fun z =>
    Q3.Proofs.quadForm (step22PositiveAxisOmegaAMatrix k ell center)
      (fun i => (z i).re)

/-- The diagnostic matrix shadow satisfies the raw-Omega Arch matrix identity
on synthesized real packets by construction.

This theorem is intentionally named `Shadow`: it is a guardrail against a fake
Step33 close, not the missing semantic raw-Omega Arch receiver. -/
theorem step22PositiveAxisOmegaArchMatrixShadowForm_synth_eq_quadForm
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) (v : ι → Real) :
    step22PositiveAxisOmegaArchMatrixShadowForm k ell center
        (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (step22PositiveAxisOmegaAMatrix k ell center) v := by
  unfold step22PositiveAxisOmegaArchMatrixShadowForm
  have hcoeff :
      (fun i : ι =>
          ((centeredBSplineCoeffBasisExpansion.synth v) i).re) = v := by
    funext i
    simp [centeredBSplineCoeffBasisExpansion]
  rw [hcoeff]

/-- Profile-sourced raw-Omega Arch receiver for route S.

This is the non-shadow receiver: its form is the raw Step22 positive-axis
Omega packet coefficient form induced by `step22PositiveAxisOmegaAProfile`. -/
noncomputable def step22PositiveAxisOmegaRawArchKernelReceiver
    {ι : Type*} [Fintype ι]
    (k : Nat) (ell : Real) (center : ι → Real) :
    Step22PositiveAxisOmegaRawArchReceiver k ell center where
  rawOmegaArchForm := fun z =>
    (step22PositiveAxisOmegaArchPacketCoeffBilinearForm k ell center) z z
  arch_ident := by
    intro v
    exact step22PositiveAxisOmegaArchPacketCoeffBilinearForm_synth_eq_quadForm
      k ell center v

/-- Route-S finite Weil receiver over raw-Omega `C`.

The receiver carries the missing raw-Omega Arch receiver plus the honest
Weil split against the existing centered finite Prime form. -/
structure Step22PositiveAxisOmegaFiniteWeilReceiver
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) where
  archReceiver : Step22PositiveAxisOmegaRawArchReceiver k ell center
  weilForm : (ι → Complex) → Real
  weil_split :
    ∀ v : ι → Real,
      weilForm (centeredBSplineCoeffBasisExpansion.synth v) =
        archReceiver.rawOmegaArchForm
          (centeredBSplineCoeffBasisExpansion.synth v) -
          (centeredBSplineFinitePrimePacketCoeffBilinearForm
            k ell center weight shift)
            (centeredBSplineCoeffBasisExpansion.synth v)
            (centeredBSplineCoeffBasisExpansion.synth v)

/-- Profile-sourced raw-Omega finite Weil quadratic form:
raw positive-axis Omega Arch minus the existing centered finite Prime form. -/
noncomputable def step22PositiveAxisOmegaFiniteWeilPacketCoeffForm
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    (ι → Complex) → Real :=
  fun z =>
    (step22PositiveAxisOmegaArchPacketCoeffBilinearForm k ell center) z z -
      (centeredBSplineFinitePrimePacketCoeffBilinearForm
        k ell center weight shift) z z

/-- Profile-sourced raw-Omega finite Weil receiver over `step22PositiveAxisOmegaCMatrix`. -/
noncomputable def step22PositiveAxisOmegaFiniteWeilKernelReceiver
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : Nat) (ell : Real) (center : ι → Real) (weight shift : ν → Real) :
    Step22PositiveAxisOmegaFiniteWeilReceiver k ell center weight shift where
  archReceiver := step22PositiveAxisOmegaRawArchKernelReceiver k ell center
  weilForm := step22PositiveAxisOmegaFiniteWeilPacketCoeffForm
    k ell center weight shift
  weil_split := by
    intro v
    rfl

namespace Step22PositiveAxisOmegaFiniteWeilReceiver

theorem weil_ident
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : Nat} {ell : Real} {center : ι → Real} {weight shift : ν → Real}
    (R : Step22PositiveAxisOmegaFiniteWeilReceiver k ell center weight shift)
    (v : ι → Real) :
    R.weilForm (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (step22PositiveAxisOmegaCMatrix k ell center weight shift) v :=
  step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
    k ell center weight shift R.archReceiver.rawOmegaArchForm R.weilForm
    R.archReceiver.arch_ident R.weil_split v

noncomputable def toFiniteWeilMatrixModel
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : Nat} {ell : Real} {center : ι → Real} {weight shift : ν → Real}
    (R : Step22PositiveAxisOmegaFiniteWeilReceiver k ell center weight shift)
    (hk : 0 < k) (hell : 0 < ell) :
    FiniteWeilMatrixModel
      (V := ι → Complex)
      (step22PositiveAxisOmegaCMatrix k ell center weight shift)
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q :=
  step22PositiveAxisOmegaFiniteWeilMatrixModel_of_rawOmegaArchReceiver
    k ell center weight shift hk hell R.archReceiver.rawOmegaArchForm
    R.weilForm R.archReceiver.arch_ident R.weil_split

end Step22PositiveAxisOmegaFiniteWeilReceiver

def primaryK11RawOmegaAnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub
    (step22PositiveAxisOmegaCMatrix
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift)
    R primaryK11Theta

theorem primaryK11RawOmegaAnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm
          (step22PositiveAxisOmegaCMatrix
            11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift) v =
        Q3.Proofs.quadForm (primaryK11RawOmegaAnalyticDFromR R) v +
          primaryK11Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold primaryK11RawOmegaAnalyticDFromR
  exact
    quadForm_scaled_sub_split
      (step22PositiveAxisOmegaCMatrix
        11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift)
      R primaryK11Theta v

noncomputable def primaryK11RawOmegaFiniteWeilMatrixModel :
    FiniteWeilMatrixModel
      (V := CoeffIndex23 -> Complex)
      (step22PositiveAxisOmegaCMatrix
        11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift)
      primaryK11AnalyticQ :=
  (step22PositiveAxisOmegaFiniteWeilKernelReceiver
    11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      ).toFiniteWeilMatrixModel primaryK11_hk primaryK11_hell

theorem primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
    (R : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hDbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (primaryK11RawOmegaAnalyticDFromR R) primaryK11AnalyticQ
        primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q primaryK11TauD)
      primaryK11DPenaltyRadius)
    (hRbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ primaryK11TauR)
      (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q primaryK11TauR)
      primaryK11RPenaltyRadius) :
    ∀ v : CoeffIndex23 -> Real,
      primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
        0 ≤ primaryK11RawOmegaFiniteWeilMatrixModel.weilForm
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) :=
  primaryK11RawOmegaFiniteWeilMatrixModel.weil_nonneg_on_analyticBoundary
    (primaryK11FinitePenaltyCert_of_penalty_boxes
      (primaryK11RawOmegaAnalyticDFromR R) R primaryK11AnalyticQ hDbox hRbox)
    (primaryK11RawOmegaAnalyticSplitFromR R)
    primaryK11Theta_nonneg

def controlK9RawOmegaAnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub
    (step22PositiveAxisOmegaCMatrix
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift)
    R controlK9Theta

theorem controlK9RawOmegaAnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm
          (step22PositiveAxisOmegaCMatrix
            9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift) v =
        Q3.Proofs.quadForm (controlK9RawOmegaAnalyticDFromR R) v +
          controlK9Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold controlK9RawOmegaAnalyticDFromR
  exact
    quadForm_scaled_sub_split
      (step22PositiveAxisOmegaCMatrix
        9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift)
      R controlK9Theta v

noncomputable def controlK9RawOmegaFiniteWeilMatrixModel :
    FiniteWeilMatrixModel
      (V := CoeffIndex23 -> Complex)
      (step22PositiveAxisOmegaCMatrix
        9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift)
      controlK9AnalyticQ :=
  (step22PositiveAxisOmegaFiniteWeilKernelReceiver
    9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      ).toFiniteWeilMatrixModel controlK9_hk controlK9_hell

theorem controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
    (R : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hDbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (controlK9RawOmegaAnalyticDFromR R) controlK9AnalyticQ
        controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q controlK9TauD)
      controlK9DPenaltyRadius)
    (hRbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ controlK9TauR)
      (Q3.Proofs.penaltyMatrix controlK9R controlK9Q controlK9TauR)
      controlK9RPenaltyRadius) :
    ∀ v : CoeffIndex23 -> Real,
      controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
        0 ≤ controlK9RawOmegaFiniteWeilMatrixModel.weilForm
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) :=
  controlK9RawOmegaFiniteWeilMatrixModel.weil_nonneg_on_analyticBoundary
    (controlK9FinitePenaltyCert_of_penalty_boxes
      (controlK9RawOmegaAnalyticDFromR R) R controlK9AnalyticQ hDbox hRbox)
    (controlK9RawOmegaAnalyticSplitFromR R)
    controlK9Theta_nonneg

def primaryK11RawOmegaAnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  step22PositiveAxisOmegaAMatrix 11 primaryK11Ell primaryK11Center

private theorem rawOmegaCoeffAbsDistanceNat_lt_23 (i j : CoeffIndex23) :
    natAbsDiff i.1 j.1 < 23 := by
  unfold natAbsDiff
  by_cases h : i.1 ≤ j.1
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le j.1 i.1) j.2
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le i.1 j.1) i.2

private def rawOmegaCoeffAbsDistanceFin (i j : CoeffIndex23) : CoeffIndex23 :=
  ⟨natAbsDiff i.1 j.1, rawOmegaCoeffAbsDistanceNat_lt_23 i j⟩

private theorem rawOmega_abs_sub_le_of_lower_upper
    (x mid rad : Real)
    (hLower : mid - rad <= x)
    (hUpper : x <= mid + rad) :
    |x - mid| <= rad := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

structure primaryK11RawOmegaAAbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |step22PositiveAxisOmegaAProfile 11 primaryK11Ell ((n.1 : Real) / 4) -
      (primaryK11AAbsDistanceEntryRat n.1 : Real)| ≤
        (primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)

def primaryK11RawOmegaAAbsDistanceLower (n : CoeffIndex23) : Real :=
  (primaryK11AAbsDistanceEntryRat n.1 : Real) -
    (primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)

def primaryK11RawOmegaAAbsDistanceUpper (n : CoeffIndex23) : Real :=
  (primaryK11AAbsDistanceEntryRat n.1 : Real) +
    (primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)

structure primaryK11RawOmegaAAbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAAbsDistanceLower n ≤
      step22PositiveAxisOmegaAProfile 11 primaryK11Ell ((n.1 : Real) / 4)
  hUpper : ∀ n : CoeffIndex23,
    step22PositiveAxisOmegaAProfile 11 primaryK11Ell ((n.1 : Real) / 4) ≤
      primaryK11RawOmegaAAbsDistanceUpper n

theorem primaryK11RawOmegaAAbsDistanceHboxCert_of_interval_cert
    (cert : primaryK11RawOmegaAAbsDistanceIntervalCert) :
    primaryK11RawOmegaAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact rawOmega_abs_sub_le_of_lower_upper
    (step22PositiveAxisOmegaAProfile 11 primaryK11Ell ((n.1 : Real) / 4))
    (primaryK11AAbsDistanceEntryRat n.1 : Real)
    (primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)
    (by simpa [primaryK11RawOmegaAAbsDistanceLower] using cert.hLower n)
    (by simpa [primaryK11RawOmegaAAbsDistanceUpper] using cert.hUpper n)

abbrev primaryK11RawOmegaAFiniteTailIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  step22PositiveAxisOmegaAFiniteTailIntervalCert
    11 primaryK11Ell ((n.1 : Real) / 4) T
    (primaryK11RawOmegaAAbsDistanceLower n)
    (primaryK11RawOmegaAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

structure primaryK11RawOmegaAFiniteTailBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) :
    Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11RawOmegaAFiniteTailIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

/-- Primary raw-Omega finite/tail bounds receiver from generated comparison
integrals and tail bounds.  This keeps the generator target at distance level:
23 finite-window comparison payloads plus 23 tail absolute bounds and
arithmetic containments. -/
theorem primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailBounds
    {T : Real}
    {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T))
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Ioc (0 : Real) T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Ioc (0 : Real) T))
    (hLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      lowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        upperF n eta)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ eta in Set.Ioc (0 : Real) T, lowerF n eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) T, upperF n eta) <= finiteUpper n)
    (hTail : ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) T| <= tailRadius n)
    (hLowerArith : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAAbsDistanceLower n <= finiteLower n - tailRadius n)
    (hUpperArith : ∀ n : CoeffIndex23,
      finiteUpper n + tailRadius n <= primaryK11RawOmegaAAbsDistanceUpper n) :
    primaryK11RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tail_bound
      11 primaryK11Ell ((n.1 : Real) / 4) T
      (primaryK11RawOmegaAAbsDistanceLower n)
      (primaryK11RawOmegaAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (lowerF n) (upperF n)
      (hProfileInt n) (hLowerInt n) (hUpperInt n)
      (hLower n) (hUpper n) (hFiniteLower n) (hFiniteUpper n)
      (hTail n) (hLowerArith n) (hUpperArith n)

/-- Primary raw-Omega finite/tail bounds receiver from finite-window
comparison integrals plus a finite tail window and a remainder bound. -/
theorem primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
    {T U : Real}
    {finiteLower finiteUpper tailWindowLower tailWindowUpper
      tailRemainderRadius tailRadius : CoeffIndex23 → Real}
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hTailWindow : T <= U)
    (hFiniteProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T))
    (hTailProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi T))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) T))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) T))
    (hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      finiteLowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ eta in Set.Ioc (0 : Real) T, finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) T, finiteUpperF n eta) <= finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n) (Set.Ioc T U))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n) (Set.Ioc T U))
    (hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc T U,
      tailLowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc T U,
      step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4) eta <=
        tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      tailWindowLower n <= ∫ eta in Set.Ioc T U, tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc T U, tailUpperF n eta) <= tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) U| <= tailRemainderRadius n)
    (hTailLowerArith : ∀ n : CoeffIndex23,
      -tailRadius n <= tailWindowLower n - tailRemainderRadius n)
    (hTailUpperArith : ∀ n : CoeffIndex23,
      tailWindowUpper n + tailRemainderRadius n <= tailRadius n)
    (hLowerArith : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAAbsDistanceLower n <= finiteLower n - tailRadius n)
    (hUpperArith : ∀ n : CoeffIndex23,
      finiteUpper n + tailRadius n <= primaryK11RawOmegaAAbsDistanceUpper n) :
    primaryK11RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tailWindow
      11 primaryK11Ell ((n.1 : Real) / 4) T U
      (primaryK11RawOmegaAAbsDistanceLower n)
      (primaryK11RawOmegaAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n)
      (tailWindowLower n) (tailWindowUpper n)
      (tailRemainderRadius n) (tailRadius n)
      (finiteLowerF n) (finiteUpperF n) (tailLowerF n) (tailUpperF n)
      hTailWindow
      (hFiniteProfileInt n) (hTailProfileInt n)
      (hFiniteLowerInt n) (hFiniteUpperInt n)
      (hFiniteLower n) (hFiniteUpper n)
      (hFiniteLowerBound n) (hFiniteUpperBound n)
      (hTailLowerInt n) (hTailUpperInt n)
      (hTailLower n) (hTailUpper n)
      (hTailWindowLower n) (hTailWindowUpper n)
      (hTailRemainder n) (hTailLowerArith n) (hTailUpperArith n)
      (hLowerArith n) (hUpperArith n)

theorem primaryK11RawOmegaAAbsDistanceIntervalCert_of_finiteTailBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (hint : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (cert : primaryK11RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius) :
    primaryK11RawOmegaAAbsDistanceIntervalCert := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (step22PositiveAxisOmegaAProfile_bounds_of_finiteTailIntervalCert
        11 primaryK11Ell ((n.1 : Real) / 4) T
        (primaryK11RawOmegaAAbsDistanceLower n)
        (primaryK11RawOmegaAAbsDistanceUpper n)
        (finiteLower n) (finiteUpper n) (tailRadius n)
        hT (hint n) (cert.h n)).1
  · intro n
    exact
      (step22PositiveAxisOmegaAProfile_bounds_of_finiteTailIntervalCert
        11 primaryK11Ell ((n.1 : Real) / 4) T
        (primaryK11RawOmegaAAbsDistanceLower n)
        (primaryK11RawOmegaAAbsDistanceUpper n)
        (finiteLower n) (finiteUpper n) (tailRadius n)
        hT (hint n) (cert.h n)).2

private theorem primaryK11A_entry_from_rawOmega_abs_distance
    (i j : CoeffIndex23) :
    primaryK11A i j =
      (primaryK11AAbsDistanceEntryRat (rawOmegaCoeffAbsDistanceFin i j).1 :
        Real) := by
  rfl

private theorem primaryK11ARadius_entry_from_rawOmega_abs_distance
    (i j : CoeffIndex23) :
    primaryK11ARadius i j =
      (primaryK11ARadiusAbsDistanceEntryRat
        (rawOmegaCoeffAbsDistanceFin i j).1 : Real) := by
  rfl

private theorem primaryK11RawOmegaAnalyticA_entry_from_abs_distance
    (i j : CoeffIndex23) :
    primaryK11RawOmegaAnalyticA i j =
      step22PositiveAxisOmegaAProfile 11 primaryK11Ell
        (((rawOmegaCoeffAbsDistanceFin i j).1 : Real) / 4) := by
  by_cases h : i.1 ≤ j.1
  · have hcast :
        ((j.1 - i.1 : Nat) : Real) = (j.1 : Real) - (i.1 : Real) :=
      Nat.cast_sub h
    simp [primaryK11RawOmegaAnalyticA, step22PositiveAxisOmegaAMatrix,
      primaryK11Center_sub_eq_index_delta, rawOmegaCoeffAbsDistanceFin,
      natAbsDiff, h, hcast]
  · have hlt : j.1 < i.1 := Nat.lt_of_not_ge h
    have hle : j.1 ≤ i.1 := Nat.le_of_lt hlt
    have hcast :
        ((i.1 - j.1 : Nat) : Real) = (i.1 : Real) - (j.1 : Real) :=
      Nat.cast_sub hle
    have hneg :
        ((j.1 : Real) - (i.1 : Real)) / 4 =
          -(((i.1 - j.1 : Nat) : Real) / 4) := by
      rw [hcast]
      ring
    simp [primaryK11RawOmegaAnalyticA, step22PositiveAxisOmegaAMatrix,
      primaryK11Center_sub_eq_index_delta, rawOmegaCoeffAbsDistanceFin,
      natAbsDiff, h, hneg, step22PositiveAxisOmegaAProfile_even]

theorem primaryK11RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
    (cert : primaryK11RawOmegaAAbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius := by
  intro i j
  have hcert := cert.h (rawOmegaCoeffAbsDistanceFin i j)
  simpa [primaryK11RawOmegaAnalyticA_entry_from_abs_distance i j,
    primaryK11A_entry_from_rawOmega_abs_distance i j,
    primaryK11ARadius_entry_from_rawOmega_abs_distance i j] using hcert

def primaryK11RawOmegaAnalyticR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa primaryK11RawOmegaAnalyticA primaryK11AnalyticP0 primaryK11Kappa

def primaryK11RawOmegaAnalyticDtheta : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta primaryK11RawOmegaAnalyticA primaryK11AnalyticP primaryK11AnalyticP0
    primaryK11Kappa primaryK11Theta

theorem primaryK11RawOmegaPrimeProfileMatrix_eq_analyticP :
    centeredBSplineFinitePrimeProfileMatrix
        11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift =
      primaryK11AnalyticP := by
  simpa [primaryK11AnalyticP, primaryK11CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion]
    using
      (centeredBSplineFinitePrimeProfileMatrix_eq_packetCoeffMatrix
        11 primaryK11Ell primaryK11Center primaryK11PrimeWeight
        primaryK11PrimeShift)

theorem primaryK11RawOmegaAnalyticDFromR_eq_Dtheta :
    primaryK11RawOmegaAnalyticDFromR primaryK11RawOmegaAnalyticR =
      primaryK11RawOmegaAnalyticDtheta := by
  ext i j
  simp [primaryK11RawOmegaAnalyticDFromR, primaryK11RawOmegaAnalyticR,
    primaryK11RawOmegaAnalyticDtheta, primaryK11RawOmegaAnalyticA,
    step22PositiveAxisOmegaCMatrix_eq_matrixSub,
    primaryK11RawOmegaPrimeProfileMatrix_eq_analyticP,
    matrixRkappa, matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem primaryK11RawOmegaAnalyticR_hbox_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticR primaryK11R primaryK11RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11AnalyticP0 primaryK11P0
      primaryK11ARadius primaryK11P0Radius primaryK11Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [primaryK11RawOmegaAnalyticR, primaryK11RawOmegaAnalyticA,
    primaryK11R, primaryK11RRat, primaryK11A, primaryK11ARat,
    primaryK11P0, primaryK11P0Rat, primaryK11RBaseRadius,
    primaryK11RBaseRadiusRat, primaryK11Kappa, primaryK11KappaRat,
    matrixRkappa, matrixScaledSub, matrixScaledSubRat, Rat.cast_abs] using hij

theorem primaryK11RawOmegaAnalyticDtheta_hbox_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticDtheta primaryK11D primaryK11DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11AnalyticP primaryK11P
      primaryK11AnalyticP0 primaryK11P0 primaryK11ARadius primaryK11PRadius
      primaryK11P0Radius primaryK11Kappa primaryK11Theta
      primaryK11Theta_nonneg primaryK11Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  have hDentry :
      primaryK11D i j =
        (1 - primaryK11Theta) * primaryK11A i j -
          primaryK11P i j +
            primaryK11Theta * primaryK11Kappa * primaryK11P0 i j := by
    simp [primaryK11D, primaryK11DRat, primaryK11CRat,
      primaryK11RRat, primaryK11A, primaryK11ARat,
      primaryK11P, primaryK11PRat, primaryK11P0, primaryK11P0Rat,
      primaryK11Theta, primaryK11ThetaRat, primaryK11Kappa, primaryK11KappaRat,
      matrixScaledSubRat, matrixSubRat]
    ring
  rw [hDentry]
  simpa [primaryK11RawOmegaAnalyticDtheta, primaryK11RawOmegaAnalyticA,
    primaryK11D, primaryK11DRat, primaryK11A, primaryK11ARat,
    primaryK11P, primaryK11PRat, primaryK11P0, primaryK11P0Rat,
    primaryK11DBaseRadius, primaryK11DBaseRadiusRat,
    primaryK11ARadius, primaryK11ARadiusRat, primaryK11PRadius,
    primaryK11PRadiusRat, primaryK11P0Radius, primaryK11P0RadiusRat,
    primaryK11Kappa, primaryK11KappaRat, primaryK11Theta,
    primaryK11ThetaRat, matrixDtheta, matrixScaledSubRat, Rat.cast_abs] using hij

theorem primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
    (M MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe M primaryK11D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |primaryK11TauD| * GR i j ≤ primaryK11DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix M primaryK11AnalyticQ primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q primaryK11TauD)
      primaryK11DPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix M primaryK11AnalyticQ primaryK11TauD)
    (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q primaryK11TauD)
    (fun i j => MR i j + |primaryK11TauD| * GR i j)
    primaryK11DPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      M primaryK11D MR primaryK11AnalyticQ primaryK11Q GR primaryK11TauD hM
      (primaryK11BoundaryGramBox_of_importedQRadius GR hQ hGRad))
    hRad

theorem primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
    (M MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe M primaryK11D MR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |primaryK11TauD| * GR i j ≤ primaryK11DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix M primaryK11AnalyticQ primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q primaryK11TauD)
      primaryK11DPenaltyRadius :=
  primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
    M MR GR hM primaryK11QRadius_hbox hGRad hRad

theorem primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    ∀ v : CoeffIndex23 -> Real,
      primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
        0 ≤ primaryK11RawOmegaFiniteWeilMatrixModel.weilForm
          (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) := by
  refine
    primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
      primaryK11RawOmegaAnalyticR ?_ ?_
  · rw [primaryK11RawOmegaAnalyticDFromR_eq_Dtheta]
    exact
      primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
        primaryK11RawOmegaAnalyticDtheta primaryK11DBaseRadius
        primaryK11BoundaryGramRadius
        (primaryK11RawOmegaAnalyticDtheta_hbox_of_base_hboxes hA hP hP0)
        primaryK11BoundaryGramRadius_dominance
        primaryK11DBaseRadius_penaltyRadius_dominance
  · exact
      primaryK11RPenaltyBox_of_matrix_and_importedQRadius
        primaryK11RawOmegaAnalyticR primaryK11RBaseRadius
        primaryK11BoundaryGramRadius
        (primaryK11RawOmegaAnalyticR_hbox_of_base_hboxes hA hP0)
        primaryK11QRadius_hbox primaryK11BoundaryGramRadius_dominance
        primaryK11RBaseRadius_penaltyRadius_dominance

def controlK9RawOmegaAnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  step22PositiveAxisOmegaAMatrix 9 controlK9Ell controlK9Center

structure controlK9RawOmegaAAbsDistanceHboxCert : Prop where
  h : ∀ n : CoeffIndex23,
    |step22PositiveAxisOmegaAProfile 9 controlK9Ell ((n.1 : Real) / 4) -
      (controlK9AAbsDistanceEntryRat n.1 : Real)| ≤
        (controlK9ARadiusAbsDistanceEntryRat n.1 : Real)

def controlK9RawOmegaAAbsDistanceLower (n : CoeffIndex23) : Real :=
  (controlK9AAbsDistanceEntryRat n.1 : Real) -
    (controlK9ARadiusAbsDistanceEntryRat n.1 : Real)

def controlK9RawOmegaAAbsDistanceUpper (n : CoeffIndex23) : Real :=
  (controlK9AAbsDistanceEntryRat n.1 : Real) +
    (controlK9ARadiusAbsDistanceEntryRat n.1 : Real)

structure controlK9RawOmegaAAbsDistanceIntervalCert : Prop where
  hLower : ∀ n : CoeffIndex23,
    controlK9RawOmegaAAbsDistanceLower n ≤
      step22PositiveAxisOmegaAProfile 9 controlK9Ell ((n.1 : Real) / 4)
  hUpper : ∀ n : CoeffIndex23,
    step22PositiveAxisOmegaAProfile 9 controlK9Ell ((n.1 : Real) / 4) ≤
      controlK9RawOmegaAAbsDistanceUpper n

theorem controlK9RawOmegaAAbsDistanceHboxCert_of_interval_cert
    (cert : controlK9RawOmegaAAbsDistanceIntervalCert) :
    controlK9RawOmegaAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  exact rawOmega_abs_sub_le_of_lower_upper
    (step22PositiveAxisOmegaAProfile 9 controlK9Ell ((n.1 : Real) / 4))
    (controlK9AAbsDistanceEntryRat n.1 : Real)
    (controlK9ARadiusAbsDistanceEntryRat n.1 : Real)
    (by simpa [controlK9RawOmegaAAbsDistanceLower] using cert.hLower n)
    (by simpa [controlK9RawOmegaAAbsDistanceUpper] using cert.hUpper n)

abbrev controlK9RawOmegaAFiniteTailIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  step22PositiveAxisOmegaAFiniteTailIntervalCert
    9 controlK9Ell ((n.1 : Real) / 4) T
    (controlK9RawOmegaAAbsDistanceLower n)
    (controlK9RawOmegaAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

structure controlK9RawOmegaAFiniteTailBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) :
    Prop where
  h : ∀ n : CoeffIndex23,
    controlK9RawOmegaAFiniteTailIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

/-- Control raw-Omega finite/tail bounds receiver from generated comparison
integrals and tail bounds.  This is the `k=9` twin of the primary receiver. -/
theorem controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailBounds
    {T : Real}
    {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T))
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Ioc (0 : Real) T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Ioc (0 : Real) T))
    (hLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      lowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        upperF n eta)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ eta in Set.Ioc (0 : Real) T, lowerF n eta)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) T, upperF n eta) <= finiteUpper n)
    (hTail : ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) T| <= tailRadius n)
    (hLowerArith : ∀ n : CoeffIndex23,
      controlK9RawOmegaAAbsDistanceLower n <= finiteLower n - tailRadius n)
    (hUpperArith : ∀ n : CoeffIndex23,
      finiteUpper n + tailRadius n <= controlK9RawOmegaAAbsDistanceUpper n) :
    controlK9RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tail_bound
      9 controlK9Ell ((n.1 : Real) / 4) T
      (controlK9RawOmegaAAbsDistanceLower n)
      (controlK9RawOmegaAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (lowerF n) (upperF n)
      (hProfileInt n) (hLowerInt n) (hUpperInt n)
      (hLower n) (hUpper n) (hFiniteLower n) (hFiniteUpper n)
      (hTail n) (hLowerArith n) (hUpperArith n)

/-- Control raw-Omega finite/tail bounds receiver from finite-window
comparison integrals plus a finite tail window and a remainder bound. -/
theorem controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
    {T U : Real}
    {finiteLower finiteUpper tailWindowLower tailWindowUpper
      tailRemainderRadius tailRadius : CoeffIndex23 → Real}
    (finiteLowerF finiteUpperF tailLowerF tailUpperF :
      CoeffIndex23 → Real → Real)
    (hTailWindow : T <= U)
    (hFiniteProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T))
    (hTailProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi T))
    (hFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteLowerF n) (Set.Ioc (0 : Real) T))
    (hFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (finiteUpperF n) (Set.Ioc (0 : Real) T))
    (hFiniteLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      finiteLowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hFiniteUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc (0 : Real) T,
      step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        finiteUpperF n eta)
    (hFiniteLowerBound : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ eta in Set.Ioc (0 : Real) T, finiteLowerF n eta)
    (hFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) T, finiteUpperF n eta) <= finiteUpper n)
    (hTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailLowerF n) (Set.Ioc T U))
    (hTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (tailUpperF n) (Set.Ioc T U))
    (hTailLower : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc T U,
      tailLowerF n eta <=
        step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hTailUpper : ∀ n : CoeffIndex23, ∀ eta ∈ Set.Ioc T U,
      step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4) eta <=
        tailUpperF n eta)
    (hTailWindowLower : ∀ n : CoeffIndex23,
      tailWindowLower n <= ∫ eta in Set.Ioc T U, tailLowerF n eta)
    (hTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc T U, tailUpperF n eta) <= tailWindowUpper n)
    (hTailRemainder : ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) U| <= tailRemainderRadius n)
    (hTailLowerArith : ∀ n : CoeffIndex23,
      -tailRadius n <= tailWindowLower n - tailRemainderRadius n)
    (hTailUpperArith : ∀ n : CoeffIndex23,
      tailWindowUpper n + tailRemainderRadius n <= tailRadius n)
    (hLowerArith : ∀ n : CoeffIndex23,
      controlK9RawOmegaAAbsDistanceLower n <= finiteLower n - tailRadius n)
    (hUpperArith : ∀ n : CoeffIndex23,
      finiteUpper n + tailRadius n <= controlK9RawOmegaAAbsDistanceUpper n) :
    controlK9RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    step22PositiveAxisOmegaAFiniteTailIntervalCert_of_comparison_integrals_and_tailWindow
      9 controlK9Ell ((n.1 : Real) / 4) T U
      (controlK9RawOmegaAAbsDistanceLower n)
      (controlK9RawOmegaAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n)
      (tailWindowLower n) (tailWindowUpper n)
      (tailRemainderRadius n) (tailRadius n)
      (finiteLowerF n) (finiteUpperF n) (tailLowerF n) (tailUpperF n)
      hTailWindow
      (hFiniteProfileInt n) (hTailProfileInt n)
      (hFiniteLowerInt n) (hFiniteUpperInt n)
      (hFiniteLower n) (hFiniteUpper n)
      (hFiniteLowerBound n) (hFiniteUpperBound n)
      (hTailLowerInt n) (hTailUpperInt n)
      (hTailLower n) (hTailUpper n)
      (hTailWindowLower n) (hTailWindowUpper n)
      (hTailRemainder n) (hTailLowerArith n) (hTailUpperArith n)
      (hLowerArith n) (hUpperArith n)

theorem controlK9RawOmegaAAbsDistanceIntervalCert_of_finiteTailBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (hint : ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (cert : controlK9RawOmegaAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius) :
    controlK9RawOmegaAAbsDistanceIntervalCert := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (step22PositiveAxisOmegaAProfile_bounds_of_finiteTailIntervalCert
        9 controlK9Ell ((n.1 : Real) / 4) T
        (controlK9RawOmegaAAbsDistanceLower n)
        (controlK9RawOmegaAAbsDistanceUpper n)
        (finiteLower n) (finiteUpper n) (tailRadius n)
        hT (hint n) (cert.h n)).1
  · intro n
    exact
      (step22PositiveAxisOmegaAProfile_bounds_of_finiteTailIntervalCert
        9 controlK9Ell ((n.1 : Real) / 4) T
        (controlK9RawOmegaAAbsDistanceLower n)
        (controlK9RawOmegaAAbsDistanceUpper n)
        (finiteLower n) (finiteUpper n) (tailRadius n)
        hT (hint n) (cert.h n)).2

private theorem controlK9A_entry_from_rawOmega_abs_distance
    (i j : CoeffIndex23) :
    controlK9A i j =
      (controlK9AAbsDistanceEntryRat (rawOmegaCoeffAbsDistanceFin i j).1 :
        Real) := by
  rfl

private theorem controlK9ARadius_entry_from_rawOmega_abs_distance
    (i j : CoeffIndex23) :
    controlK9ARadius i j =
      (controlK9ARadiusAbsDistanceEntryRat
        (rawOmegaCoeffAbsDistanceFin i j).1 : Real) := by
  rfl

private theorem controlK9RawOmegaAnalyticA_entry_from_abs_distance
    (i j : CoeffIndex23) :
    controlK9RawOmegaAnalyticA i j =
      step22PositiveAxisOmegaAProfile 9 controlK9Ell
        (((rawOmegaCoeffAbsDistanceFin i j).1 : Real) / 4) := by
  by_cases h : i.1 ≤ j.1
  · have hcast :
        ((j.1 - i.1 : Nat) : Real) = (j.1 : Real) - (i.1 : Real) :=
      Nat.cast_sub h
    simp [controlK9RawOmegaAnalyticA, step22PositiveAxisOmegaAMatrix,
      controlK9Center_sub_eq_index_delta, rawOmegaCoeffAbsDistanceFin,
      natAbsDiff, h, hcast]
  · have hlt : j.1 < i.1 := Nat.lt_of_not_ge h
    have hle : j.1 ≤ i.1 := Nat.le_of_lt hlt
    have hcast :
        ((i.1 - j.1 : Nat) : Real) = (i.1 : Real) - (j.1 : Real) :=
      Nat.cast_sub hle
    have hneg :
        ((j.1 : Real) - (i.1 : Real)) / 4 =
          -(((i.1 - j.1 : Nat) : Real) / 4) := by
      rw [hcast]
      ring
    simp [controlK9RawOmegaAnalyticA, step22PositiveAxisOmegaAMatrix,
      controlK9Center_sub_eq_index_delta, rawOmegaCoeffAbsDistanceFin,
      natAbsDiff, h, hneg, step22PositiveAxisOmegaAProfile_even]

theorem controlK9RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
    (cert : controlK9RawOmegaAAbsDistanceHboxCert) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticA controlK9A controlK9ARadius := by
  intro i j
  have hcert := cert.h (rawOmegaCoeffAbsDistanceFin i j)
  simpa [controlK9RawOmegaAnalyticA_entry_from_abs_distance i j,
    controlK9A_entry_from_rawOmega_abs_distance i j,
    controlK9ARadius_entry_from_rawOmega_abs_distance i j] using hcert

def controlK9RawOmegaAnalyticR : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa controlK9RawOmegaAnalyticA controlK9AnalyticP0 controlK9Kappa

def controlK9RawOmegaAnalyticDtheta : Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta controlK9RawOmegaAnalyticA controlK9AnalyticP controlK9AnalyticP0
    controlK9Kappa controlK9Theta

theorem controlK9RawOmegaPrimeProfileMatrix_eq_analyticP :
    centeredBSplineFinitePrimeProfileMatrix
        9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift =
      controlK9AnalyticP := by
  simpa [controlK9AnalyticP, controlK9CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion]
    using
      (centeredBSplineFinitePrimeProfileMatrix_eq_packetCoeffMatrix
        9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift)

theorem controlK9RawOmegaAnalyticDFromR_eq_Dtheta :
    controlK9RawOmegaAnalyticDFromR controlK9RawOmegaAnalyticR =
      controlK9RawOmegaAnalyticDtheta := by
  ext i j
  simp [controlK9RawOmegaAnalyticDFromR, controlK9RawOmegaAnalyticR,
    controlK9RawOmegaAnalyticDtheta, controlK9RawOmegaAnalyticA,
    step22PositiveAxisOmegaCMatrix_eq_matrixSub,
    controlK9RawOmegaPrimeProfileMatrix_eq_analyticP,
    matrixRkappa, matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem controlK9RawOmegaAnalyticR_hbox_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticA controlK9A controlK9ARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticR controlK9R controlK9RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      controlK9RawOmegaAnalyticA controlK9A controlK9AnalyticP0 controlK9P0
      controlK9ARadius controlK9P0Radius controlK9Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [controlK9RawOmegaAnalyticR, controlK9RawOmegaAnalyticA,
    controlK9R, controlK9RRat, controlK9A, controlK9ARat,
    controlK9P0, controlK9P0Rat, controlK9RBaseRadius,
    controlK9RBaseRadiusRat, controlK9Kappa, controlK9KappaRat,
    matrixRkappa, matrixScaledSub, matrixScaledSubRat, Rat.cast_abs] using hij

theorem controlK9RawOmegaAnalyticDtheta_hbox_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticA controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticDtheta controlK9D controlK9DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      controlK9RawOmegaAnalyticA controlK9A controlK9AnalyticP controlK9P
      controlK9AnalyticP0 controlK9P0 controlK9ARadius controlK9PRadius
      controlK9P0Radius controlK9Kappa controlK9Theta
      controlK9Theta_nonneg controlK9Theta_le_one hA hP hP0
  intro i j
  have hij := h i j
  have hDentry :
      controlK9D i j =
        (1 - controlK9Theta) * controlK9A i j -
          controlK9P i j +
            controlK9Theta * controlK9Kappa * controlK9P0 i j := by
    simp [controlK9D, controlK9DRat, controlK9CRat,
      controlK9RRat, controlK9A, controlK9ARat,
      controlK9P, controlK9PRat, controlK9P0, controlK9P0Rat,
      controlK9Theta, controlK9ThetaRat, controlK9Kappa, controlK9KappaRat,
      matrixScaledSubRat, matrixSubRat]
    ring
  rw [hDentry]
  simpa [controlK9RawOmegaAnalyticDtheta, controlK9RawOmegaAnalyticA,
    controlK9D, controlK9DRat, controlK9A, controlK9ARat,
    controlK9P, controlK9PRat, controlK9P0, controlK9P0Rat,
    controlK9DBaseRadius, controlK9DBaseRadiusRat,
    controlK9ARadius, controlK9ARadiusRat, controlK9PRadius,
    controlK9PRadiusRat, controlK9P0Radius, controlK9P0RadiusRat,
    controlK9Kappa, controlK9KappaRat, controlK9Theta,
    controlK9ThetaRat, matrixDtheta, matrixScaledSubRat, Rat.cast_abs] using hij

theorem controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
    (M MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe M controlK9D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |controlK9TauD| * GR i j ≤ controlK9DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix M controlK9AnalyticQ controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q controlK9TauD)
      controlK9DPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix M controlK9AnalyticQ controlK9TauD)
    (Q3.Proofs.penaltyMatrix controlK9D controlK9Q controlK9TauD)
    (fun i j => MR i j + |controlK9TauD| * GR i j)
    controlK9DPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      M controlK9D MR controlK9AnalyticQ controlK9Q GR controlK9TauD hM
      (controlK9BoundaryGramBox_of_importedQRadius GR hQ hGRad))
    hRad

theorem controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
    (M MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe M controlK9D MR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |controlK9TauD| * GR i j ≤ controlK9DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix M controlK9AnalyticQ controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q controlK9TauD)
      controlK9DPenaltyRadius :=
  controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius
    M MR GR hM controlK9QRadius_hbox hGRad hRad

theorem controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticA controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    ∀ v : CoeffIndex23 -> Real,
      controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
        0 ≤ controlK9RawOmegaFiniteWeilMatrixModel.weilForm
          (controlK9RawOmegaFiniteWeilMatrixModel.synth v) := by
  refine
    controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_penalty_boxes
      controlK9RawOmegaAnalyticR ?_ ?_
  · rw [controlK9RawOmegaAnalyticDFromR_eq_Dtheta]
    exact
      controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
        controlK9RawOmegaAnalyticDtheta controlK9DBaseRadius
        controlK9BoundaryGramRadius
        (controlK9RawOmegaAnalyticDtheta_hbox_of_base_hboxes hA hP hP0)
        controlK9BoundaryGramRadius_dominance
        controlK9DBaseRadius_penaltyRadius_dominance
  · exact
      controlK9RPenaltyBox_of_matrix_and_importedQRadius
        controlK9RawOmegaAnalyticR controlK9RBaseRadius
        controlK9BoundaryGramRadius
        (controlK9RawOmegaAnalyticR_hbox_of_base_hboxes hA hP0)
      controlK9QRadius_hbox controlK9BoundaryGramRadius_dominance
      controlK9RBaseRadius_penaltyRadius_dominance

/-- Primary raw-Omega base hbox package.

This mirrors `PrimaryK11BaseEntryHboxCert`, but its Arch `A` field targets the
raw Step22 positive-axis Omega receiver instead of the centered Arch receiver. -/
structure PrimaryK11RawOmegaBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP primaryK11P primaryK11PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius

/-- Control raw-Omega base hbox package. -/
structure ControlK9RawOmegaBaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9RawOmegaAnalyticA controlK9A controlK9ARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP controlK9P controlK9PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP0 controlK9P0 controlK9P0Radius

/-- Active primary/control raw-Omega entry hbox package for route S. -/
structure ActiveRawOmegaCoeffEntryHboxCert : Prop where
  primary : PrimaryK11RawOmegaBaseEntryHboxCert
  control : ControlK9RawOmegaBaseEntryHboxCert

/-- Expose a certified finite Weil model as the generic finite-certificate
ledger row used by the directed-family shell.  The analytic identity remains
in the `CertifiedFiniteWeilModel`; this adapter only remembers finite matrices
and the interval-backed `FinitePenaltyCert`. -/
noncomputable def certifiedFiniteBlock_of_certifiedFiniteWeilModel
    {ρ ι V : Type} [Fintype ρ] [Fintype ι]
    [AddCommGroup V] [Module Real V]
    (label : FiniteSpaceLabel)
    (B : CertifiedFiniteWeilModel ρ ι V) :
    CertifiedFiniteBlock where
  label := label
  rho := ρ
  iota := ι
  rhoFinite := inferInstance
  iotaFinite := inferInstance
  D := B.D
  R := B.R
  Q := B.Q
  cert := B.cert

/-- Primary raw-Omega certified finite Weil model from the raw-Omega hbox
package. -/
noncomputable def primaryK11RawOmegaCertifiedFiniteWeilModel_of_entryHboxCert
    (cert : PrimaryK11RawOmegaBaseEntryHboxCert) :
    CertifiedFiniteWeilModel (Fin 2) CoeffIndex23 (CoeffIndex23 -> Complex) where
  C :=
    step22PositiveAxisOmegaCMatrix
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
  D := primaryK11RawOmegaAnalyticDtheta
  R := primaryK11RawOmegaAnalyticR
  Q := primaryK11AnalyticQ
  theta := primaryK11Theta
  theta_nonneg := primaryK11Theta_nonneg
  cert :=
    primaryK11FinitePenaltyCert_of_penalty_boxes
      primaryK11RawOmegaAnalyticDtheta primaryK11RawOmegaAnalyticR
      primaryK11AnalyticQ
      (primaryK11RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
        primaryK11RawOmegaAnalyticDtheta primaryK11DBaseRadius
        primaryK11BoundaryGramRadius
        (primaryK11RawOmegaAnalyticDtheta_hbox_of_base_hboxes
          cert.hA cert.hP cert.hP0)
        primaryK11BoundaryGramRadius_dominance
        primaryK11DBaseRadius_penaltyRadius_dominance)
      (primaryK11RPenaltyBox_of_matrix_and_importedQRadius
        primaryK11RawOmegaAnalyticR primaryK11RBaseRadius
        primaryK11BoundaryGramRadius
        (primaryK11RawOmegaAnalyticR_hbox_of_base_hboxes cert.hA cert.hP0)
        primaryK11QRadius_hbox primaryK11BoundaryGramRadius_dominance
        primaryK11RBaseRadius_penaltyRadius_dominance)
  split := by
    intro v
    rw [← primaryK11RawOmegaAnalyticDFromR_eq_Dtheta]
    exact primaryK11RawOmegaAnalyticSplitFromR primaryK11RawOmegaAnalyticR v
  model := primaryK11RawOmegaFiniteWeilMatrixModel

/-- Control raw-Omega certified finite Weil model from the raw-Omega hbox
package. -/
noncomputable def controlK9RawOmegaCertifiedFiniteWeilModel_of_entryHboxCert
    (cert : ControlK9RawOmegaBaseEntryHboxCert) :
    CertifiedFiniteWeilModel (Fin 2) CoeffIndex23 (CoeffIndex23 -> Complex) where
  C :=
    step22PositiveAxisOmegaCMatrix
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
  D := controlK9RawOmegaAnalyticDtheta
  R := controlK9RawOmegaAnalyticR
  Q := controlK9AnalyticQ
  theta := controlK9Theta
  theta_nonneg := controlK9Theta_nonneg
  cert :=
    controlK9FinitePenaltyCert_of_penalty_boxes
      controlK9RawOmegaAnalyticDtheta controlK9RawOmegaAnalyticR
      controlK9AnalyticQ
      (controlK9RawOmegaDPenaltyBox_of_matrix_and_importedQRadius_hbox
        controlK9RawOmegaAnalyticDtheta controlK9DBaseRadius
        controlK9BoundaryGramRadius
        (controlK9RawOmegaAnalyticDtheta_hbox_of_base_hboxes
          cert.hA cert.hP cert.hP0)
        controlK9BoundaryGramRadius_dominance
        controlK9DBaseRadius_penaltyRadius_dominance)
      (controlK9RPenaltyBox_of_matrix_and_importedQRadius
        controlK9RawOmegaAnalyticR controlK9RBaseRadius
        controlK9BoundaryGramRadius
        (controlK9RawOmegaAnalyticR_hbox_of_base_hboxes cert.hA cert.hP0)
        controlK9QRadius_hbox controlK9BoundaryGramRadius_dominance
        controlK9RBaseRadius_penaltyRadius_dominance)
  split := by
    intro v
    rw [← controlK9RawOmegaAnalyticDFromR_eq_Dtheta]
    exact controlK9RawOmegaAnalyticSplitFromR controlK9RawOmegaAnalyticR v
  model := controlK9RawOmegaFiniteWeilMatrixModel

noncomputable def primaryK11RawOmegaFiniteBlock_of_entryHboxCert
    (cert : PrimaryK11RawOmegaBaseEntryHboxCert) :
    CertifiedFiniteBlock :=
  certifiedFiniteBlock_of_certifiedFiniteWeilModel
    CenteredBSplineCoeffManifestLabel.primaryK11L3Ell030Delta025Theta1e4
    (primaryK11RawOmegaCertifiedFiniteWeilModel_of_entryHboxCert cert)

noncomputable def controlK9RawOmegaFiniteBlock_of_entryHboxCert
    (cert : ControlK9RawOmegaBaseEntryHboxCert) :
    CertifiedFiniteBlock :=
  certifiedFiniteBlock_of_certifiedFiniteWeilModel
    CenteredBSplineCoeffManifestLabel.controlK9L3Ell030Delta025Theta1e5
    (controlK9RawOmegaCertifiedFiniteWeilModel_of_entryHboxCert cert)

noncomputable def primaryK11RawOmegaSingletonDirectedCertFamily_of_entryHboxCert
    (cert : PrimaryK11RawOmegaBaseEntryHboxCert) :
    DirectedCertFamily :=
  (primaryK11RawOmegaFiniteBlock_of_entryHboxCert cert).singletonDirectedFamily

noncomputable def controlK9RawOmegaSingletonDirectedCertFamily_of_entryHboxCert
    (cert : ControlK9RawOmegaBaseEntryHboxCert) :
    DirectedCertFamily :=
  (controlK9RawOmegaFiniteBlock_of_entryHboxCert cert).singletonDirectedFamily

def PsdStep33RawOmegaSingletonDirectedFamilyHandoff
    (cert : ActiveRawOmegaCoeffEntryHboxCert) : Prop :=
  ∃ primaryFamily controlFamily : DirectedCertFamily,
    primaryFamily =
      primaryK11RawOmegaSingletonDirectedCertFamily_of_entryHboxCert cert.primary ∧
    controlFamily =
      controlK9RawOmegaSingletonDirectedCertFamily_of_entryHboxCert cert.control

/-- Raw-Omega Step33B-level finite analytic positivity for primary and control.

This is the raw Step22 positive-axis Omega analogue of the ordinary
`PsdStep33FiniteAnalyticPositivity` surface.  It deliberately does not claim an
`ActiveCenteredCoeffEntryHboxCert`, because the raw-Omega finite matrix model is
parallel to the older centered positive-A certified block. -/
def PsdStep33RawOmegaFiniteAnalyticPositivity : Prop :=
  (∀ v : CoeffIndex23 -> Real,
    primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
        (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
    primaryK11RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
        (primaryK11RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      0 ≤ primaryK11RawOmegaFiniteWeilMatrixModel.weilForm
        (primaryK11RawOmegaFiniteWeilMatrixModel.synth v)) ∧
  (∀ v : CoeffIndex23 -> Real,
    controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalPlus
        (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
    controlK9RawOmegaFiniteWeilMatrixModel.boundary.evalMinus
        (controlK9RawOmegaFiniteWeilMatrixModel.synth v) = 0 ->
      0 ≤ controlK9RawOmegaFiniteWeilMatrixModel.weilForm
        (controlK9RawOmegaFiniteWeilMatrixModel.synth v))

theorem psd_step33_rawOmega_finite_analytic_weil_positivity_of_base_hboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11RawOmegaAnalyticA primaryK11A primaryK11ARadius)
    (primary_hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9RawOmegaAnalyticA controlK9A controlK9ARadius)
    (control_hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    PsdStep33RawOmegaFiniteAnalyticPositivity := by
  exact ⟨
    primaryK11RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
      primary_hA primary_hP primary_hP0,
    controlK9RawOmega_weil_nonneg_on_analyticBoundary_of_base_hboxes
      control_hA control_hP control_hP0⟩

theorem psd_step33_rawOmega_finite_analytic_weil_positivity_of_entryHboxCert
    (cert : ActiveRawOmegaCoeffEntryHboxCert) :
    PsdStep33RawOmegaFiniteAnalyticPositivity :=
  psd_step33_rawOmega_finite_analytic_weil_positivity_of_base_hboxes
    cert.primary.hA cert.primary.hP cert.primary.hP0
    cert.control.hA cert.control.hP cert.control.hP0

theorem psd_step33_rawOmega_singleton_directed_family_handoff_of_entryHboxCert
    (cert : ActiveRawOmegaCoeffEntryHboxCert) :
    PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact ⟨
    primaryK11RawOmegaSingletonDirectedCertFamily_of_entryHboxCert cert.primary,
    controlK9RawOmegaSingletonDirectedCertFamily_of_entryHboxCert cert.control,
    rfl, rfl⟩

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
    (cert : ActiveRawOmegaCoeffEntryHboxCert) :
    PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact ⟨
    psd_step33_rawOmega_finite_analytic_weil_positivity_of_entryHboxCert cert,
    psd_step33_rawOmega_singleton_directed_family_handoff_of_entryHboxCert cert⟩

theorem a_star_eq_neg_twoPi_step22OmegaArchWeight (xi : Real) :
    Q3.a_star xi = -(2 * Real.pi) * step22OmegaArchWeight (2 * Real.pi * xi) := by
  unfold Q3.a_star Q3.a step22OmegaArchWeight
  have harg :
      ((1 / 4 : Complex) + Complex.I * ((((2 * Real.pi * xi) / 2 : Real) : Complex))) =
        ((1 / 4 : Complex) + Complex.I * (((Real.pi * xi : Real) : Complex))) := by
    congr 1
    norm_num
    ring
  have harg2 :
      ((1 / 4 : Complex) + Complex.I * (Real.pi : Complex) * (xi : Complex)) =
        ((1 / 4 : Complex) + Complex.I * (((Real.pi * xi : Real) : Complex))) := by
    norm_num
    ring
  rw [harg, harg2]
  ring

theorem step22OmegaArchWeight_eq_neg_inv_twoPi_aStar (eta : Real) :
    step22OmegaArchWeight eta =
      -((2 * Real.pi)⁻¹) * Q3.a_star (eta / (2 * Real.pi)) := by
  have htwo : (2 * Real.pi) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  have harg : 2 * Real.pi * (eta / (2 * Real.pi)) = eta := by
    field_simp [htwo]
  have h := a_star_eq_neg_twoPi_step22OmegaArchWeight (eta / (2 * Real.pi))
  rw [harg] at h
  calc
    step22OmegaArchWeight eta =
        -((2 * Real.pi)⁻¹) * (-(2 * Real.pi) * step22OmegaArchWeight eta) := by
          field_simp [htwo]
    _ = -((2 * Real.pi)⁻¹) * Q3.a_star (eta / (2 * Real.pi)) := by
          rw [← h]

theorem step22OmegaArchWeight_continuous :
    Continuous step22OmegaArchWeight := by
  have hfun :
      step22OmegaArchWeight =
        fun eta : Real =>
          -((2 * Real.pi)⁻¹) * Q3.a_star (eta / (2 * Real.pi)) := by
    funext eta
    exact step22OmegaArchWeight_eq_neg_inv_twoPi_aStar eta
  rw [hfun]
  exact continuous_const.mul
    (Q3.a_star_continuous.comp (by continuity))

theorem digamma_differentiableAt_of_re_pos {z : Complex} (hz : 0 < z.re) :
    DifferentiableAt Complex Q3.digamma z := by
  unfold Q3.digamma
  refine DifferentiableAt.div ?hnum ?hden ?hne
  · have hS_open : IsOpen {z : Complex | 0 < z.re} := by
      simpa using isOpen_lt continuous_const Complex.continuous_re
    have hdiffOn :
        DifferentiableOn Complex (deriv Complex.Gamma)
          {z : Complex | 0 < z.re} := by
      exact DifferentiableOn.deriv Q3.Gamma_differentiableOn_right_half_plane hS_open
    exact (hdiffOn z hz).differentiableAt (hS_open.mem_nhds hz)
  · exact Complex.differentiableAt_Gamma z (by
      intro m h
      have hm0 : (0 : Real) <= (m : Real) := by exact_mod_cast Nat.zero_le m
      have hre : z.re = -(m : Real) := by
        simpa using congrArg Complex.re h
      nlinarith)
  · exact Complex.Gamma_ne_zero_of_re_pos hz

@[fun_prop]
theorem step22OmegaArchWeight_differentiableAt (eta : Real) :
    DifferentiableAt Real step22OmegaArchWeight eta := by
  unfold step22OmegaArchWeight
  let z : Real → Complex :=
    fun t : Real =>
      (1 / 4 : Complex) + Complex.I * (((t / 2 : Real) : Complex))
  have hzDiff : DifferentiableAt Real z eta := by
    have hdiv : DifferentiableAt Real (fun t : Real => t / 2) eta := by
      fun_prop
    have hcast :
        DifferentiableAt Real (fun t : Real => (((t / 2 : Real) : Real) : Complex))
          eta :=
      Complex.ofRealCLM.differentiableAt.comp eta hdiv
    dsimp [z]
    fun_prop
  have hzPos : 0 < (z eta).re := by
    dsimp [z]
    norm_num [Complex.add_re, Complex.mul_re]
  have hDigamma :
      DifferentiableAt Real (fun t : Real => Q3.digamma (z t)) eta :=
    (digamma_differentiableAt_of_re_pos hzPos).restrictScalars Real |>.comp eta hzDiff
  have hRealPart :
      DifferentiableAt Real (fun t : Real => (Q3.digamma (z t)).re) eta :=
    Complex.reCLM.differentiableAt.comp eta hDigamma
  simpa [z] using hRealPart.sub (differentiableAt_const (Real.log Real.pi))

@[fun_prop]
theorem realSinc_differentiableAt (eta : Real) :
    DifferentiableAt Real realSinc eta := by
  rw [realSinc_eq_sinc, Real.sinc_eq_dslope]
  by_cases heta : eta = 0
  · subst eta
    rcases (Real.analyticAt_sin (x := 0)) with ⟨p, hp⟩
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp).differentiableAt
  · exact
      (differentiableAt_dslope_of_ne (f := Real.sin) (a := 0) (b := eta) heta).2
        Real.differentiableAt_sin

@[fun_prop]
theorem centeredBSplineImagTransformRealClosedForm_differentiableAt
    (k : Nat) (ell eta : Real) :
    DifferentiableAt Real
      (fun t : Real => centeredBSplineImagTransformRealClosedForm k ell t) eta := by
  unfold centeredBSplineImagTransformRealClosedForm
  fun_prop

@[fun_prop]
theorem step22PositiveAxisOmegaAIntegrand_differentiableAt
    (k : Nat) (ell x eta : Real) :
    DifferentiableAt Real
      (fun t : Real => step22PositiveAxisOmegaAIntegrand k ell x t) eta := by
  unfold step22PositiveAxisOmegaAIntegrand
  fun_prop

theorem step22PositiveAxisOmegaAIntegrand_continuous
    (k : Nat) (ell x : Real) :
    Continuous (fun eta : Real => step22PositiveAxisOmegaAIntegrand k ell x eta) := by
  unfold step22PositiveAxisOmegaAIntegrand
  exact (((continuous_const.mul step22OmegaArchWeight_continuous).mul
    ((centeredBSplineImagTransformRealClosedForm_continuous k ell).pow 2)).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)))

theorem step22OmegaArchWeight_linear_growth :
    ∃ C0 C1 : Real, 0 <= C0 ∧ 0 <= C1 ∧
      ∀ eta : Real, |step22OmegaArchWeight eta| <= C0 + C1 * |eta| := by
  rcases Q3.a_star_linear_growth with ⟨C0, C1, hC0, hC1, hgrowth⟩
  let invTwoPiAbs : Real := |(2 * Real.pi)⁻¹|
  refine ⟨invTwoPiAbs * C0, invTwoPiAbs * C1 * invTwoPiAbs, ?_, ?_, ?_⟩
  · exact mul_nonneg (abs_nonneg _) hC0
  · exact mul_nonneg (mul_nonneg (abs_nonneg _) hC1) (abs_nonneg _)
  · intro eta
    have harg :
        |eta / (2 * Real.pi)| = |eta| * invTwoPiAbs := by
      have hrewrite : eta / (2 * Real.pi) = eta * (2 * Real.pi)⁻¹ := by
        ring
      rw [hrewrite, abs_mul]
    calc
      |step22OmegaArchWeight eta| =
          invTwoPiAbs * |Q3.a_star (eta / (2 * Real.pi))| := by
            rw [step22OmegaArchWeight_eq_neg_inv_twoPi_aStar, abs_mul,
              abs_neg]
      _ <= invTwoPiAbs *
          (C0 + C1 * |eta / (2 * Real.pi)|) := by
            exact mul_le_mul_of_nonneg_left
              (hgrowth (eta / (2 * Real.pi))) (abs_nonneg _)
      _ = invTwoPiAbs * C0 + (invTwoPiAbs * C1 * invTwoPiAbs) * |eta| := by
            rw [harg]
            ring
      _ = invTwoPiAbs * C0 +
          (invTwoPiAbs * C1 * invTwoPiAbs) * |eta| := rfl

def step22OmegaEtaTransformedIntegrandWithArchSign
    (k : Nat) (ell x eta : Real) : Real :=
  -step22OmegaArchWeight eta *
    (ell * Real.cos ((eta / (2 * Real.pi)) * x) *
      (centeredBSplineImagTransformRealClosedForm k ell (eta / (2 * Real.pi))) ^ 2)

def step22OmegaEtaTransformedProfileWithArchSign
    (k : Nat) (ell x : Real) : Real :=
  ∫ eta : Real, step22OmegaEtaTransformedIntegrandWithArchSign k ell x eta

theorem centeredBSplineArchKernelProfileIntegrand_eq_twoPi_mul_step22OmegaEtaTransformedIntegrandWithArchSign_comp
    (k : Nat) (ell x xi : Real) :
    centeredBSplineArchKernelProfileIntegrand k ell x xi =
      (2 * Real.pi) *
        step22OmegaEtaTransformedIntegrandWithArchSign k ell x (2 * Real.pi * xi) := by
  unfold centeredBSplineArchKernelProfileIntegrand
    step22OmegaEtaTransformedIntegrandWithArchSign
  rw [a_star_eq_neg_twoPi_step22OmegaArchWeight xi]
  have hscale : (2 * Real.pi * xi) / (2 * Real.pi) = xi := by
    field_simp [Real.pi_ne_zero]
  rw [hscale]
  ring

theorem centeredBSplineArchKernelProfile_eq_step22OmegaEtaTransformedProfileWithArchSign
    (k : Nat) (ell x : Real) :
    centeredBSplineArchKernelProfile k ell x =
      step22OmegaEtaTransformedProfileWithArchSign k ell x := by
  let G : Real → Real := fun eta =>
    step22OmegaEtaTransformedIntegrandWithArchSign k ell x eta
  have hpoint :
      (fun xi : Real => centeredBSplineArchKernelProfileIntegrand k ell x xi) =
        (fun xi : Real => (2 * Real.pi) * G (2 * Real.pi * xi)) := by
    funext xi
    simpa [G] using
      centeredBSplineArchKernelProfileIntegrand_eq_twoPi_mul_step22OmegaEtaTransformedIntegrandWithArchSign_comp
        k ell x xi
  have hcomp :
      (∫ xi : Real, G (2 * Real.pi * xi)) =
        |(2 * Real.pi)⁻¹| * ∫ eta : Real, G eta := by
    simpa using MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)
  have hscale : (2 * Real.pi) * |(2 * Real.pi)⁻¹| = 1 := by
    have hpos : 0 < 2 * Real.pi := by positivity
    rw [abs_of_pos (inv_pos.mpr hpos)]
    field_simp [hpos.ne']
  calc
    centeredBSplineArchKernelProfile k ell x
        = ∫ xi : Real, centeredBSplineArchKernelProfileIntegrand k ell x xi := by
            rfl
    _ = ∫ xi : Real, (2 * Real.pi) * G (2 * Real.pi * xi) := by
            rw [hpoint]
    _ = (2 * Real.pi) * ∫ xi : Real, G (2 * Real.pi * xi) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi) * (|(2 * Real.pi)⁻¹| * ∫ eta : Real, G eta) := by
            rw [hcomp]
    _ = ∫ eta : Real, G eta := by
            rw [← mul_assoc, hscale, one_mul]
    _ = step22OmegaEtaTransformedProfileWithArchSign k ell x := by
            rfl

theorem centeredBSplineArchKernelProfile_eq_integral_integrand
    (k : Nat) (ell x : Real) :
    centeredBSplineArchKernelProfile k ell x =
      ∫ t : Real, centeredBSplineArchKernelProfileIntegrand k ell x t := by
  rfl

lemma bounds_div_two_of_two_mul_bounds
    {x L U : Real}
    (hL : L <= 2 * x)
    (hU : 2 * x <= U) :
    L / 2 <= x ∧ x <= U / 2 := by
  constructor <;> nlinarith

theorem centeredBSplineArchKernelProfileIntegrand_neg
    (k : Nat) (ell x t : Real) :
    centeredBSplineArchKernelProfileIntegrand k ell x (-t) =
      centeredBSplineArchKernelProfileIntegrand k ell x t := by
  unfold centeredBSplineArchKernelProfileIntegrand
  have harg : (-t) * x = -(t * x) := by ring
  rw [Q3.a_star_even t]
  rw [harg, Real.cos_neg]
  rw [centeredBSplineImagTransformRealClosedForm_neg]

theorem centeredBSplineArchKernelProfileIntegrand_continuous
    (k : Nat) (ell x : Real) :
    Continuous (fun t : Real => centeredBSplineArchKernelProfileIntegrand k ell x t) := by
  unfold centeredBSplineArchKernelProfileIntegrand
  exact Q3.a_star_continuous.mul
    (((continuous_const.mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))).mul
      ((centeredBSplineImagTransformRealClosedForm_continuous k ell).pow 2)))

theorem centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
    (k : Nat) (ell x : Real) (hk : 0 < k) (hell : 0 < ell) :
    Integrable (fun t : Real => centeredBSplineArchKernelProfileIntegrand k ell x t) := by
  let g : Real → Real := fun t =>
    Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2
  have hg : Integrable g := by
    simpa [g] using
      a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
        k ell hk hell
  have hboundInt : Integrable (fun t : Real => |ell| * ‖g t‖) := by
    simpa using hg.norm.const_mul |ell|
  refine hboundInt.mono'
    (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).aestronglyMeasurable ?_
  filter_upwards with t
  have hcos : |Real.cos (t * x)| <= 1 := Real.abs_cos_le_one (t * x)
  have hmain :
      |Q3.a_star t * (ell * Real.cos (t * x) *
          (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)| <=
        |ell| * |Q3.a_star t *
          (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2| := by
    have hcosmul :
        |Real.cos (t * x)| *
            (|Q3.a_star t| *
              |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) <=
          1 *
            (|Q3.a_star t| *
              |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) := by
      exact mul_le_mul_of_nonneg_right hcos
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc
      |Q3.a_star t * (ell * Real.cos (t * x) *
          (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)|
          = |ell| * |Real.cos (t * x)| *
              (|Q3.a_star t| *
                |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) := by
            simp only [abs_mul]
            ring_nf
      _ = |ell| * (|Real.cos (t * x)| *
              (|Q3.a_star t| *
                |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|)) := by
            ring
      _ <= |ell| * (1 *
              (|Q3.a_star t| *
                |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|)) := by
            exact mul_le_mul_of_nonneg_left hcosmul (abs_nonneg ell)
      _ = |ell| * |Q3.a_star t *
              (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2| := by
            simp only [abs_mul]
            ring_nf
  simpa [centeredBSplineArchKernelProfileIntegrand, g, Real.norm_eq_abs] using hmain

theorem linearGrowthWeight_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound
    (k : Nat) (ell t w C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : |w| <= C0 + C1 * |t|) (ht : 1 <= t) :
    ‖w * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2‖ <=
      ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
        (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
  let D : Real := (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹
  let c : Real := ell / (2 * bsplineScale k)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc_ne : c ≠ 0 := by
    unfold c
    exact div_ne_zero hell.ne'
      (mul_ne_zero (by norm_num) (bsplineScale_ne_zero k))
  have harg :
      ell * t / (2 * bsplineScale k) = c * t := by
    unfold c
    ring
  have hsinc4 :
      |realSinc (c * t)| ^ 4 <= (|c|⁻¹) ^ 4 * t ^ (-4 : ℝ) := by
    have hct : c * t ≠ 0 := mul_ne_zero hc_ne htpos.ne'
    have hsinc := realSinc_abs_le_inv_abs hct
    have hpow :
        |realSinc (c * t)| ^ 4 <= (|c * t|⁻¹) ^ 4 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hsinc 4
    calc
      |realSinc (c * t)| ^ 4 <= (|c * t|⁻¹) ^ 4 := hpow
      _ = (|c|⁻¹) ^ 4 * t ^ (-4 : ℝ) := by
        rw [abs_mul, abs_of_pos htpos]
        have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc_ne
        have htne : t ≠ 0 := htpos.ne'
        rw [Real.rpow_neg (le_of_lt htpos)]
        field_simp [hcabs, htne]
        norm_num [Real.rpow_natCast]
  have hsincpow_le :
      |realSinc (c * t)| ^ (2 * (k + 1)) <=
        |realSinc (c * t)| ^ 4 := by
    have hx0 : 0 <= |realSinc (c * t)| := abs_nonneg _
    have hx1 : |realSinc (c * t)| <= 1 := realSinc_abs_le_one _
    have hpow : 4 <= 2 * (k + 1) := by
      have hk1 : 2 <= k + 1 := Nat.succ_le_succ hk
      nlinarith
    exact pow_le_pow_of_le_one hx0 hx1 hpow
  have hEabs :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        |D| ^ 2 * |realSinc (c * t)| ^ (2 * (k + 1)) := by
    apply le_of_eq
    unfold centeredBSplineImagTransformRealClosedForm D
    rw [harg]
    rw [abs_mul]
    rw [abs_pow]
    rw [mul_pow]
    ring_nf
  have hEabs4 :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        |D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ)) := by
    calc
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
          |D| ^ 2 * |realSinc (c * t)| ^ (2 * (k + 1)) := hEabs
      _ <= |D| ^ 2 * |realSinc (c * t)| ^ 4 := by
        exact mul_le_mul_of_nonneg_left hsincpow_le (sq_nonneg |D|)
      _ <= |D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsinc4 (sq_nonneg |D|)
  have hw : |w| <= (C0 + C1) * t := by
    calc
      |w| <= C0 + C1 * |t| := hgrowth
      _ = C0 + C1 * t := by rw [abs_of_pos htpos]
      _ <= (C0 + C1) * t := by
        nlinarith [hC0, hC1, ht]
  have ht_rpow :
      t * t ^ (-4 : ℝ) = t ^ (-3 : ℝ) := by
    calc
      t * t ^ (-4 : ℝ) =
          t ^ (1 : ℝ) * t ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-4 : ℝ)) := by rw [Real.rpow_add htpos]
      _ = t ^ (-3 : ℝ) := by norm_num
  have hmain :
      |w| *
          |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
    calc
      |w| *
          |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        ((C0 + C1) * t) *
          (|D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ))) := by
            exact mul_le_mul hw hEabs4 (sq_nonneg _) (by positivity)
      _ = ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
        rw [← ht_rpow]
        ring
  calc
    ‖w * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2‖
        = |w| *
            |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
    _ <= ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := hmain
    _ = ((C0 + C1) *
          |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
        (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
          simp [D, c]

theorem step22PositiveAxisOmegaAIntegrand_tail_bound
    (k : Nat) (ell x eta C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : |step22OmegaArchWeight eta| <= C0 + C1 * |eta|)
    (heta : 1 <= eta) :
    ‖step22PositiveAxisOmegaAIntegrand k ell x eta‖ <=
      |ell / Real.pi| *
        (((C0 + C1) *
          |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * eta ^ (-3 : ℝ)) := by
  have hbase :=
    linearGrowthWeight_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound
      k ell eta (step22OmegaArchWeight eta) C0 C1 hk hell hC0 hC1 hgrowth heta
  have hprofile :
      ‖step22PositiveAxisOmegaAIntegrand k ell x eta‖ <=
        |ell / Real.pi| *
          ‖step22OmegaArchWeight eta *
            (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2‖ := by
    have hcos : |Real.cos (eta * x)| <= 1 := Real.abs_cos_le_one (eta * x)
    have hmain :
        |(ell / Real.pi) * step22OmegaArchWeight eta *
            (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 *
            Real.cos (eta * x)| <=
          |ell / Real.pi| *
            |step22OmegaArchWeight eta *
              (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2| := by
      have hcosmul :
          |Real.cos (eta * x)| *
              (|step22OmegaArchWeight eta| *
                |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2|) <=
            1 *
              (|step22OmegaArchWeight eta| *
                |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2|) := by
        exact mul_le_mul_of_nonneg_right hcos
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      calc
        |(ell / Real.pi) * step22OmegaArchWeight eta *
            (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2 *
            Real.cos (eta * x)|
            = |ell / Real.pi| * |Real.cos (eta * x)| *
                (|step22OmegaArchWeight eta| *
                  |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2|) := by
              simp only [abs_mul]
              ring_nf
        _ = |ell / Real.pi| * (|Real.cos (eta * x)| *
                (|step22OmegaArchWeight eta| *
                  |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2|)) := by
              ring
        _ <= |ell / Real.pi| * (1 *
                (|step22OmegaArchWeight eta| *
                  |(centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2|)) := by
              exact mul_le_mul_of_nonneg_left hcosmul (abs_nonneg _)
        _ = |ell / Real.pi| *
              |step22OmegaArchWeight eta *
                (centeredBSplineImagTransformRealClosedForm k ell eta) ^ 2| := by
              simp only [abs_mul]
              ring_nf
    simpa [step22PositiveAxisOmegaAIntegrand, Real.norm_eq_abs, abs_div] using hmain
  exact le_trans hprofile
    (mul_le_mul_of_nonneg_left hbase (abs_nonneg _))

theorem step22PositiveAxisOmegaAIntegrand_integrableOn_Ioi_of_pos_degree
    (k : Nat) (ell x : Real) (hk : 0 < k) (hell : 0 < ell) :
    IntegrableOn (step22PositiveAxisOmegaAIntegrand k ell x) (Set.Ioi (0 : Real)) := by
  let f : Real → Real := step22PositiveAxisOmegaAIntegrand k ell x
  rcases step22OmegaArchWeight_linear_growth with ⟨C0, C1, hC0, hC1, hgrowth⟩
  let M : Real := |ell / Real.pi| *
    ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
      (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)
  have hcont : Continuous f := by
    simpa [f] using step22PositiveAxisOmegaAIntegrand_continuous k ell x
  have htail_bound :
      ∀ eta ∈ Set.Ioi (1 : Real), ‖f eta‖ <= M * eta ^ (-3 : ℝ) := by
    intro eta heta
    have h :=
      step22PositiveAxisOmegaAIntegrand_tail_bound
        k ell x eta C0 C1 hk hell hC0 hC1 (hgrowth eta)
        (le_of_lt (show (1 : Real) < eta from heta))
    calc
      ‖f eta‖ =
          ‖step22PositiveAxisOmegaAIntegrand k ell x eta‖ := by rfl
      _ <= |ell / Real.pi| *
          (((C0 + C1) *
            |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
            (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) *
            eta ^ (-3 : ℝ)) := h
      _ = M * eta ^ (-3 : ℝ) := by
            unfold M
            ring
  have htail_majorant :
      Integrable (fun eta : Real => M * eta ^ (-3 : ℝ))
        (volume.restrict (Set.Ioi (1 : Real))) := by
    have h :
        IntegrableOn (fun eta : Real => M * eta ^ (-3 : ℝ))
          (Set.Ioi (1 : Real)) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-3 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul M
    simpa [IntegrableOn] using h
  have htail : IntegrableOn f (Set.Ioi (1 : Real)) := by
    have hf_meas : AEStronglyMeasurable f
        (volume.restrict (Set.Ioi (1 : Real))) :=
      hcont.aestronglyMeasurable
    have htail_int : Integrable f (volume.restrict (Set.Ioi (1 : Real))) := by
      refine htail_majorant.mono' hf_meas ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro eta heta
      exact htail_bound eta heta
    simpa [IntegrableOn] using htail_int
  have hcompact : IntegrableOn f (Set.Ioc (0 : Real) 1) := by
    exact ((hcont.integrableOn_Icc (a := (0 : Real)) (b := 1)).mono_set
      Set.Ioc_subset_Icc_self)
  have hcover :
      Set.Ioi (0 : Real) = Set.Ioc (0 : Real) 1 ∪ Set.Ioi (1 : Real) := by
    ext eta
    constructor
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      by_cases hle : eta <= 1
      · exact Or.inl ⟨heta, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    · intro heta
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at heta ⊢
      rcases heta with hwin | htail'
      · exact hwin.1
      · exact lt_trans zero_lt_one htail'
  have hpos : IntegrableOn f (Set.Ioc (0 : Real) 1 ∪ Set.Ioi (1 : Real)) :=
    hcompact.union htail
  change IntegrableOn f (Set.Ioi (0 : Real))
  rw [hcover]
  exact hpos

theorem primaryK11RawOmegaAIntegrand_integrableOn_Ioi :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)) := by
  intro n
  exact step22PositiveAxisOmegaAIntegrand_integrableOn_Ioi_of_pos_degree
    11 primaryK11Ell ((n.1 : Real) / 4)
    (by norm_num)
    (by norm_num [primaryK11Ell, primaryK11EllRat])

theorem controlK9RawOmegaAIntegrand_integrableOn_Ioi :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)) := by
  intro n
  exact step22PositiveAxisOmegaAIntegrand_integrableOn_Ioi_of_pos_degree
    9 controlK9Ell ((n.1 : Real) / 4)
    (by norm_num)
    (by norm_num [controlK9Ell, controlK9EllRat])

theorem primaryK11RawOmegaAIntegrand_integrableOn_Ioc_zero
    (T : Real) :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T) := by
  intro n
  exact (primaryK11RawOmegaAIntegrand_integrableOn_Ioi n).mono_set
    (by intro eta heta; exact heta.1)

theorem controlK9RawOmegaAIntegrand_integrableOn_Ioc_zero
    (T : Real) :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioc (0 : Real) T) := by
  intro n
  exact (controlK9RawOmegaAIntegrand_integrableOn_Ioi n).mono_set
    (by intro eta heta; exact heta.1)

theorem primaryK11RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
    (T : Real) (hT : 0 <= T) :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi T) := by
  intro n
  exact (primaryK11RawOmegaAIntegrand_integrableOn_Ioi n).mono_set
    (by intro eta heta; exact lt_of_le_of_lt hT heta)

theorem controlK9RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg
    (T : Real) (hT : 0 <= T) :
    ∀ n : CoeffIndex23,
      IntegrableOn
        (step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi T) := by
  intro n
  exact (controlK9RawOmegaAIntegrand_integrableOn_Ioi n).mono_set
    (by intro eta heta; exact lt_of_le_of_lt hT heta)

theorem step22PositiveAxisOmegaATail_abs_le_of_linear_growth
    (k : Nat) (ell x T C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ eta : Real, |step22OmegaArchWeight eta| <= C0 + C1 * |eta|)
    (hT : 1 <= T) :
    |step22PositiveAxisOmegaATailPart k ell x T| <=
      (|ell / Real.pi| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2) := by
  let f : Real → Real := step22PositiveAxisOmegaAIntegrand k ell x
  let M : Real := |ell / Real.pi| *
    ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
      (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTnonneg : 0 <= T := le_trans zero_le_one hT
  have hbaseInt :
      IntegrableOn f (Set.Ioi (0 : Real)) := by
    simpa [f] using
      step22PositiveAxisOmegaAIntegrand_integrableOn_Ioi_of_pos_degree
        k ell x hk hell
  have htailIntOn : IntegrableOn f (Set.Ioi T) := by
    exact hbaseInt.mono_set (by intro eta heta; exact lt_of_le_of_lt hTnonneg heta)
  have hfint : Integrable f (volume.restrict (Set.Ioi T)) := by
    simpa [IntegrableOn] using htailIntOn
  have habsint : Integrable (fun eta : Real => |f eta|)
      (volume.restrict (Set.Ioi T)) := by
    simpa [Real.norm_eq_abs] using hfint.norm
  have hmajint :
      Integrable (fun eta : Real => M * eta ^ (-3 : ℝ))
        (volume.restrict (Set.Ioi T)) := by
    have h : IntegrableOn (fun eta : Real => M * eta ^ (-3 : ℝ)) (Set.Ioi T) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-3 : ℝ) < -1) hTpos).const_mul M
    simpa [IntegrableOn] using h
  have hmono :
      ∫ eta in Set.Ioi T, |f eta| <=
        ∫ eta in Set.Ioi T, M * eta ^ (-3 : ℝ) := by
    refine integral_mono_ae habsint hmajint ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro eta heta
    have heta1 : 1 <= eta := le_trans hT (le_of_lt heta)
    have htail :=
      step22PositiveAxisOmegaAIntegrand_tail_bound
        k ell x eta C0 C1 hk hell hC0 hC1 (hgrowth eta) heta1
    calc
      |f eta| = ‖f eta‖ := by rw [Real.norm_eq_abs]
      _ <= |ell / Real.pi| *
          (((C0 + C1) *
            |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
            (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) *
            eta ^ (-3 : ℝ)) := by
              simpa [f] using htail
      _ = M * eta ^ (-3 : ℝ) := by
            unfold M
            ring
  have hmaj_eq :
      ∫ eta in Set.Ioi T, M * eta ^ (-3 : ℝ) = M * (T ^ (-2 : ℝ) / 2) := by
    rw [integral_const_mul]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hTpos]
    ring_nf
  calc
    |step22PositiveAxisOmegaATailPart k ell x T|
        = |∫ eta in Set.Ioi T, f eta| := by rfl
    _ <= ∫ eta in Set.Ioi T, |f eta| := by
          simpa using
            (abs_integral_le_integral_abs
              (μ := volume.restrict (Set.Ioi T)) (f := f))
    _ <= ∫ eta in Set.Ioi T, M * eta ^ (-3 : ℝ) := hmono
    _ = M * (T ^ (-2 : ℝ) / 2) := hmaj_eq
    _ = (|ell / Real.pi| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2) := by rfl

theorem primaryK11RawOmegaATailRemainder_abs_le_of_linear_growth
    (U C0 C1 : Real)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ eta : Real, |step22OmegaArchWeight eta| <= C0 + C1 * |eta|)
    (hU : 1 <= U)
    (remainderRadius : CoeffIndex23 → Real)
    (hRadius : ∀ n : CoeffIndex23,
      (|primaryK11Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (bsplineScale 11 * bsplineAutocorrNorm 11))⁻¹| ^ 2 *
          (|(primaryK11Ell / (2 * bsplineScale 11))|⁻¹) ^ 4)) *
        (U ^ (-2 : ℝ) / 2) <= remainderRadius n) :
    ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) U| <= remainderRadius n := by
  intro n
  exact le_trans
    (step22PositiveAxisOmegaATail_abs_le_of_linear_growth
      11 primaryK11Ell ((n.1 : Real) / 4) U C0 C1
      (by norm_num) (by norm_num [primaryK11Ell, primaryK11EllRat])
      hC0 hC1 hgrowth hU)
    (hRadius n)

theorem controlK9RawOmegaATailRemainder_abs_le_of_linear_growth
    (U C0 C1 : Real)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ eta : Real, |step22OmegaArchWeight eta| <= C0 + C1 * |eta|)
    (hU : 1 <= U)
    (remainderRadius : CoeffIndex23 → Real)
    (hRadius : ∀ n : CoeffIndex23,
      (|controlK9Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (bsplineScale 9 * bsplineAutocorrNorm 9))⁻¹| ^ 2 *
          (|(controlK9Ell / (2 * bsplineScale 9))|⁻¹) ^ 4)) *
        (U ^ (-2 : ℝ) / 2) <= remainderRadius n) :
    ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) U| <= remainderRadius n := by
  intro n
  exact le_trans
    (step22PositiveAxisOmegaATail_abs_le_of_linear_growth
      9 controlK9Ell ((n.1 : Real) / 4) U C0 C1
      (by norm_num) (by norm_num [controlK9Ell, controlK9EllRat])
      hC0 hC1 hgrowth hU)
    (hRadius n)

theorem centeredBSplineArchKernelProfileIntegrand_tail_bound
    (k : Nat) (ell x t C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : |Q3.a_star t| <= C0 + C1 * |t|) (ht : 1 <= t) :
    ‖centeredBSplineArchKernelProfileIntegrand k ell x t‖ <=
      |ell| *
        (((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * t ^ (-3 : ℝ)) := by
  have hbase :=
    a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound
      k ell t C0 C1 hk hell hC0 hC1 hgrowth ht
  have hprofile :
      ‖centeredBSplineArchKernelProfileIntegrand k ell x t‖ <=
        |ell| * ‖Q3.a_star t *
          (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2‖ := by
    have hcos : |Real.cos (t * x)| <= 1 := Real.abs_cos_le_one (t * x)
    have hmain :
        |Q3.a_star t * (ell * Real.cos (t * x) *
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)| <=
          |ell| * |Q3.a_star t *
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2| := by
      have hcosmul :
          |Real.cos (t * x)| *
              (|Q3.a_star t| *
                |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) <=
            1 *
              (|Q3.a_star t| *
                |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) := by
        exact mul_le_mul_of_nonneg_right hcos
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      calc
        |Q3.a_star t * (ell * Real.cos (t * x) *
            (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)|
            = |ell| * |Real.cos (t * x)| *
                (|Q3.a_star t| *
                  |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|) := by
              simp only [abs_mul]
              ring_nf
        _ = |ell| * (|Real.cos (t * x)| *
                (|Q3.a_star t| *
                  |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|)) := by
              ring
        _ <= |ell| * (1 *
                (|Q3.a_star t| *
                  |(centeredBSplineImagTransformRealClosedForm k ell t) ^ 2|)) := by
              exact mul_le_mul_of_nonneg_left hcosmul (abs_nonneg ell)
        _ = |ell| * |Q3.a_star t *
                (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2| := by
              simp only [abs_mul]
              ring_nf
    simpa [centeredBSplineArchKernelProfileIntegrand, Real.norm_eq_abs] using hmain
  exact le_trans hprofile (mul_le_mul_of_nonneg_left hbase (abs_nonneg ell))

def centeredBSplineArchKernelProfilePositiveTailPart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ t in Set.Ioi T, centeredBSplineArchKernelProfileIntegrand k ell x t

def centeredBSplineArchKernelProfilePositiveTailWindowPart
    (k : Nat) (ell x T U : Real) : Real :=
  ∫ t in Set.Ioc T U, centeredBSplineArchKernelProfileIntegrand k ell x t

theorem centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_pointwise_bounds
    (k : Nat) (ell x T U lower upper : Real)
    (hTU : T <= U)
    (hLower : ∀ t ∈ Set.Ioc T U,
      lower <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upper) :
    (U - T) * lower <=
        centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U ∧
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U <=
        (U - T) * upper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hvol : volume.real (Set.Ioc T U) = U - T := by
    exact Real.volume_real_Ioc_of_le hTU
  have hfintOn : IntegrableOn f (Set.Ioc T U) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := T) (b := U)).mono_set Set.Ioc_subset_Icc_self
  have hlowerIntOn : IntegrableOn (fun _ : Real => lower) (Set.Ioc T U) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hupperIntOn : IntegrableOn (fun _ : Real => upper) (Set.Ioc T U) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  constructor
  · calc
      (U - T) * lower = ∫ t in Set.Ioc T U, lower := by
        rw [setIntegral_const, smul_eq_mul, hvol]
      _ <= ∫ t in Set.Ioc T U, f t := by
        exact setIntegral_mono_on hlowerIntOn hfintOn measurableSet_Ioc hLower
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U := by
        rfl
  · calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U =
          ∫ t in Set.Ioc T U, f t := by
            rfl
      _ <= ∫ t in Set.Ioc T U, upper := by
        exact setIntegral_mono_on hfintOn hupperIntOn measurableSet_Ioc hUpper
      _ = (U - T) * upper := by
        rw [setIntegral_const, smul_eq_mul, hvol]

theorem centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_two_piece_pointwise_bounds
    (k : Nat) (ell x T U c lowerLeft upperLeft lowerRight upperRight : Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeft : ∀ t ∈ Set.Ioc T c,
      lowerLeft <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft)
    (hLowerRight : ∀ t ∈ Set.Ioc c U,
      lowerRight <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight) :
    (c - T) * lowerLeft + (U - c) * lowerRight <=
        centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U ∧
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U <=
        (c - T) * upperLeft + (U - c) * upperRight := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Ioc T U = Set.Ioc T c ∪ Set.Ioc c U := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      by_cases hyc : y <= c
      · exact Or.inl ⟨hy.1, hyc⟩
      · exact Or.inr ⟨lt_of_not_ge hyc, hy.2⟩
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      rcases hy with hleftMem | hrightMem
      · exact ⟨hleftMem.1, le_trans hleftMem.2 hRight⟩
      · exact ⟨lt_of_le_of_lt hLeft hrightMem.1, hrightMem.2⟩
  have hdisj : Disjoint (Set.Ioc T c) (Set.Ioc c U) := by
    rw [Set.disjoint_left]
    intro y hyleft hyright
    simp only [Set.mem_Ioc] at hyleft hyright
    exact not_lt_of_ge hyleft.2 hyright.1
  have hvolLeft : volume.real (Set.Ioc T c) = c - T := by
    exact Real.volume_real_Ioc_of_le hLeft
  have hvolRight : volume.real (Set.Ioc c U) = U - c := by
    exact Real.volume_real_Ioc_of_le hRight
  have hfintLeft : IntegrableOn f (Set.Ioc T c) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := T) (b := c)).mono_set Set.Ioc_subset_Icc_self
  have hfintRight : IntegrableOn f (Set.Ioc c U) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := c) (b := U)).mono_set Set.Ioc_subset_Icc_self
  have hLowerLeftInt : IntegrableOn (fun _ : Real => lowerLeft) (Set.Ioc T c) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hUpperLeftInt : IntegrableOn (fun _ : Real => upperLeft) (Set.Ioc T c) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hLowerRightInt : IntegrableOn (fun _ : Real => lowerRight) (Set.Ioc c U) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hUpperRightInt : IntegrableOn (fun _ : Real => upperRight) (Set.Ioc c U) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  constructor
  · have hLeftBound :
        (∫ t in Set.Ioc T c, lowerLeft) <=
          ∫ t in Set.Ioc T c, f t := by
      exact setIntegral_mono_on hLowerLeftInt hfintLeft measurableSet_Ioc hLowerLeft
    have hRightBound :
        (∫ t in Set.Ioc c U, lowerRight) <=
          ∫ t in Set.Ioc c U, f t := by
      exact setIntegral_mono_on hLowerRightInt hfintRight measurableSet_Ioc hLowerRight
    calc
      (c - T) * lowerLeft + (U - c) * lowerRight =
          (∫ t in Set.Ioc T c, lowerLeft) +
            ∫ t in Set.Ioc c U, lowerRight := by
            rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
              hvolLeft, hvolRight]
      _ <= (∫ t in Set.Ioc T c, f t) + ∫ t in Set.Ioc c U, f t := by
            exact add_le_add hLeftBound hRightBound
      _ = ∫ t in Set.Ioc T c ∪ Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U := by
            rw [← hcover]
            rfl
  · have hLeftBound :
        (∫ t in Set.Ioc T c, f t) <=
          ∫ t in Set.Ioc T c, upperLeft := by
      exact setIntegral_mono_on hfintLeft hUpperLeftInt measurableSet_Ioc hUpperLeft
    have hRightBound :
        (∫ t in Set.Ioc c U, f t) <=
          ∫ t in Set.Ioc c U, upperRight := by
      exact setIntegral_mono_on hfintRight hUpperRightInt measurableSet_Ioc hUpperRight
    calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U =
          ∫ t in Set.Ioc T c ∪ Set.Ioc c U, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Ioc T c, f t) + ∫ t in Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ <= (∫ t in Set.Ioc T c, upperLeft) + ∫ t in Set.Ioc c U, upperRight := by
            exact add_le_add hLeftBound hRightBound
      _ = (c - T) * upperLeft + (U - c) * upperRight := by
            rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
              hvolLeft, hvolRight]

theorem centeredBSplineArchKernelProfilePositiveTail_abs_le_of_integral_majorant
    (k : Nat) (ell x U remainderRadius : Real)
    (majorant : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hMajorantInt : Integrable majorant (volume.restrict (Set.Ioi U)))
    (hMajorant : ∀ t ∈ Set.Ioi U,
      |centeredBSplineArchKernelProfileIntegrand k ell x t| <= majorant t)
    (hIntegral : ∫ t in Set.Ioi U, majorant t <= remainderRadius) :
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
      remainderRadius := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hfint : Integrable f (volume.restrict (Set.Ioi U)) := by
    exact hint.restrict
  have habsint : Integrable (fun t : Real => |f t|)
      (volume.restrict (Set.Ioi U)) := by
    simpa [Real.norm_eq_abs] using hfint.norm
  have hmono :
      ∫ t in Set.Ioi U, |f t| <= ∫ t in Set.Ioi U, majorant t := by
    refine integral_mono_ae habsint hMajorantInt ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    simpa [f] using hMajorant t ht
  calc
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x U|
        = |∫ t in Set.Ioi U, f t| := by rfl
    _ <= ∫ t in Set.Ioi U, |f t| := by
      simpa using
        (abs_integral_le_integral_abs
          (μ := volume.restrict (Set.Ioi U)) (f := f))
    _ <= ∫ t in Set.Ioi U, majorant t := hmono
    _ <= remainderRadius := hIntegral

theorem centeredBSplineArchKernelProfileIntegrand_abs_le_of_aStar_and_transform_sq_majorants
    (k : Nat) (ell x t omegaMajorant transformSqMajorant : Real)
    (hOmega : |Q3.a_star t| <= omegaMajorant)
    (hTransform :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        transformSqMajorant) :
    |centeredBSplineArchKernelProfileIntegrand k ell x t| <=
      |ell| * omegaMajorant * transformSqMajorant := by
  have hOmegaNonneg : 0 <= omegaMajorant :=
    le_trans (abs_nonneg _) hOmega
  have hAE :
      |Q3.a_star t| *
          |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        omegaMajorant * transformSqMajorant := by
    exact mul_le_mul hOmega hTransform
      (sq_nonneg |centeredBSplineImagTransformRealClosedForm k ell t|)
      hOmegaNonneg
  have hcos : |Real.cos (t * x)| <= 1 :=
    Real.abs_cos_le_one (t * x)
  have hcosAE :
      |Real.cos (t * x)| *
          (|Q3.a_star t| *
            |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2) <=
        1 * (omegaMajorant * transformSqMajorant) := by
    exact mul_le_mul hcos hAE
      (mul_nonneg (abs_nonneg _)
        (sq_nonneg |centeredBSplineImagTransformRealClosedForm k ell t|))
      (by norm_num)
  calc
    |centeredBSplineArchKernelProfileIntegrand k ell x t|
        = |ell| * (|Real.cos (t * x)| *
            (|Q3.a_star t| *
              |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2)) := by
          simp only [centeredBSplineArchKernelProfileIntegrand, abs_mul,
            abs_pow]
          ring
    _ <= |ell| * (1 * (omegaMajorant * transformSqMajorant)) := by
          exact mul_le_mul_of_nonneg_left hcosAE (abs_nonneg ell)
    _ = |ell| * omegaMajorant * transformSqMajorant := by ring

/-- The fixed digamma argument used in the Arch density `a_star`. -/
def aStarTailArg (t : Real) : Complex :=
  (1 / 4 : Complex) + Complex.I * (Real.pi : Complex) * (t : Complex)

/-- Stieltjes/Euler-Maclaurin log envelope for the Arch density. -/
def aStarStieltjesLogEnvelope (t : Real) : Real :=
  let z : Complex := aStarTailArg t
  2 * Real.pi *
    (|Real.log Real.pi - Real.log ‖z‖| +
      |z.re / (2 * ‖z‖ ^ 2)| +
      1 / (4 * ‖z‖ ^ 2))

theorem a_star_abs_le_stieltjesLogEnvelope (t : Real) :
    |Q3.a_star t| <= aStarStieltjesLogEnvelope t := by
  let z : Complex := aStarTailArg t
  have hz : 0 < z.re := by
    simp [z, aStarTailArg]
  have hrem := Q3.re_digamma_remainder_bound_stieltjes z hz
  let A : Real := Real.log Real.pi - Real.log ‖z‖
  let B : Real := z.re / (2 * ‖z‖ ^ 2)
  let E : Real := (Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖ ^ 2)
  have hdecomp : Real.log Real.pi - (Q3.digamma z).re = A + B - E := by
    unfold A B E
    ring
  have hbase :
      |Real.log Real.pi - (Q3.digamma z).re| <=
        |Real.log Real.pi - Real.log ‖z‖| +
          |z.re / (2 * ‖z‖ ^ 2)| +
          1 / (4 * ‖z‖ ^ 2) := by
    calc
      |Real.log Real.pi - (Q3.digamma z).re| = |A + B - E| := by rw [hdecomp]
      _ <= |A + B| + |E| := by
            simpa [sub_eq_add_neg] using (abs_sub (A + B) E)
      _ <= (|A| + |B|) + |E| := by
            have h := abs_sub A (-B)
            simpa [sub_eq_add_neg, abs_neg] using add_le_add_right h |E|
      _ <= (|A| + |B|) + 1 / (4 * ‖z‖ ^ 2) := by
            have hremE : |E| <= 1 / (4 * ‖z‖ ^ 2) := by
              simpa [E] using hrem
            exact add_le_add_right hremE (|A| + |B|)
      _ = |Real.log Real.pi - Real.log ‖z‖| +
            |z.re / (2 * ‖z‖ ^ 2)| +
            1 / (4 * ‖z‖ ^ 2) := by
            unfold A B
            ring
  have ha :
      Q3.a_star t = 2 * Real.pi * (Real.log Real.pi - (Q3.digamma z).re) := by
    simp [Q3.a_star, Q3.a, z, aStarTailArg]
  rw [ha]
  rw [abs_mul]
  have htwo_pi_abs : |2 * Real.pi| = 2 * Real.pi := by
    exact abs_of_pos (mul_pos (by norm_num) Real.pi_pos)
  rw [htwo_pi_abs]
  have htwo_pi_nonneg : 0 <= 2 * Real.pi := le_of_lt (mul_pos (by norm_num) Real.pi_pos)
  exact
    (mul_le_mul_of_nonneg_left hbase htwo_pi_nonneg).trans_eq
      (by simp [aStarStieltjesLogEnvelope, z])

theorem a_star_abs_le_logOmega_of_stieltjesLogEnvelope
    {U omegaFactor : Real}
    (hEnvelope : ∀ t ∈ Set.Ioi U,
      aStarStieltjesLogEnvelope t <= omegaFactor * Real.log (3 * t)) :
    ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaFactor * Real.log (3 * t) := by
  intro t ht
  exact le_trans (a_star_abs_le_stieltjesLogEnvelope t) (hEnvelope t ht)

theorem aStarStieltjesLogEnvelope_le_ten_log_after_one
    {t : Real} (ht : (1 : Real) < t) :
    aStarStieltjesLogEnvelope t <= 10 * Real.log (3 * t) := by
  let z : Complex := aStarTailArg t
  let L : Real := Real.log (3 * t)
  have ht0 : 0 < t := by linarith
  have ht1 : 1 <= t := by linarith
  have hpit_pos : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have hpit_nonneg : 0 <= Real.pi * t := le_of_lt hpit_pos
  have hz_im : z.im = Real.pi * t := by
    simp [z, aStarTailArg, mul_assoc]
  have hnorm_ge_pit : Real.pi * t <= ‖z‖ := by
    have him_le : |z.im| <= ‖z‖ := by
      simpa using (RCLike.abs_im_le_norm z)
    simpa [hz_im, abs_of_nonneg hpit_nonneg] using him_le
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hpit_pos hnorm_ge_pit
  have hnorm_ge_one : (1 : Real) <= ‖z‖ := by
    have hpi_ge_one : (1 : Real) <= Real.pi := by nlinarith [Real.pi_gt_three]
    have : (1 : Real) <= Real.pi * t := by
      nlinarith [hpi_ge_one, ht1, Real.pi_pos]
    exact le_trans this hnorm_ge_pit
  have hnorm_sq_ge_one : (1 : Real) <= ‖z‖ ^ 2 := by
    nlinarith [hnorm_ge_one, sq_nonneg (‖z‖ - 1)]
  have hnorm_le_two_pi_t : ‖z‖ <= 2 * Real.pi * t := by
    have htri :
        ‖(1 / 4 : Complex) + Complex.I * (Real.pi : Complex) * (t : Complex)‖ <=
          ‖(1 / 4 : Complex)‖ + ‖Complex.I * (Real.pi : Complex) * (t : Complex)‖ :=
      norm_add_le _ _
    have hnorm_i : ‖Complex.I * (Real.pi : Complex) * (t : Complex)‖ = Real.pi * t := by
      calc
        ‖Complex.I * (Real.pi : Complex) * (t : Complex)‖ =
            ‖Complex.I‖ * ‖(Real.pi : Complex)‖ * ‖(t : Complex)‖ := by
              simp [mul_assoc]
        _ = Real.pi * t := by
              simp [abs_of_pos Real.pi_pos, abs_of_pos ht0]
    have hnorm_quarter : ‖(1 / 4 : Complex)‖ = (1 / 4 : Real) := by
      norm_num
    calc
      ‖z‖ = ‖(1 / 4 : Complex) + Complex.I * (Real.pi : Complex) * (t : Complex)‖ := by
            simp [z, aStarTailArg, mul_assoc]
      _ <= ‖(1 / 4 : Complex)‖ + ‖Complex.I * (Real.pi : Complex) * (t : Complex)‖ := htri
      _ = (1 / 4 : Real) + Real.pi * t := by
            rw [hnorm_quarter, hnorm_i]
      _ <= 2 * Real.pi * t := by
            nlinarith [hpit_pos, Real.pi_gt_three, ht1]
  have hnorm_div_le : ‖z‖ / Real.pi <= 3 * t := by
    have hdiv : ‖z‖ / Real.pi <= (2 * Real.pi * t) / Real.pi := by
      exact div_le_div_of_nonneg_right hnorm_le_two_pi_t Real.pi_pos.le
    have htwo : (2 * Real.pi * t) / Real.pi = 2 * t := by
      field_simp [Real.pi_ne_zero]
    calc
      ‖z‖ / Real.pi <= (2 * Real.pi * t) / Real.pi := hdiv
      _ = 2 * t := htwo
      _ <= 3 * t := by nlinarith [ht0]
  have hratio_pos : 0 < ‖z‖ / Real.pi := div_pos hnorm_pos Real.pi_pos
  have hthree_t_pos : 0 < 3 * t := by positivity
  have hlog_ratio :
      Real.log ‖z‖ - Real.log Real.pi <= L := by
    have hlog_div : Real.log (‖z‖ / Real.pi) = Real.log ‖z‖ - Real.log Real.pi := by
      simpa using (Real.log_div (ne_of_gt hnorm_pos) Real.pi_ne_zero)
    have hle := Real.log_le_log hratio_pos hnorm_div_le
    simpa [L, hlog_div] using hle
  have hlog_pi_le_norm : Real.log Real.pi <= Real.log ‖z‖ := by
    have hpi_le_norm : Real.pi <= ‖z‖ := by
      have : Real.pi <= Real.pi * t := by nlinarith [Real.pi_pos, ht1]
      exact le_trans this hnorm_ge_pit
    exact Real.log_le_log Real.pi_pos hpi_le_norm
  have hlog_abs :
      |Real.log Real.pi - Real.log ‖z‖| <= L := by
    have habs :
        |Real.log Real.pi - Real.log ‖z‖| =
          Real.log ‖z‖ - Real.log Real.pi := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    simpa [habs] using hlog_ratio
  have hterm2 :
      |z.re / (2 * ‖z‖ ^ 2)| <= (1 / 8 : Real) := by
    have hzre : z.re = (1 / 4 : Real) := by
      simp [z, aStarTailArg]
    have hden_pos : 0 < 2 * ‖z‖ ^ 2 := by positivity
    have hnonneg : 0 <= z.re / (2 * ‖z‖ ^ 2) := by
      rw [hzre]
      positivity
    rw [abs_of_nonneg hnonneg, hzre]
    have hden_ge : (8 : Real) <= 8 * ‖z‖ ^ 2 := by
      nlinarith [hnorm_sq_ge_one]
    have hpos8 : (0 : Real) < 8 := by norm_num
    calc
      (1 / 4 : Real) / (2 * ‖z‖ ^ 2) = (1 : Real) / (8 * ‖z‖ ^ 2) := by
            field_simp [hden_pos.ne']
            ring
      _ <= 1 / 8 := one_div_le_one_div_of_le hpos8 hden_ge
  have hterm3 :
      1 / (4 * ‖z‖ ^ 2) <= (1 / 4 : Real) := by
    have hden_ge : (4 : Real) <= 4 * ‖z‖ ^ 2 := by
      nlinarith [hnorm_sq_ge_one]
    have hpos4 : (0 : Real) < 4 := by norm_num
    exact one_div_le_one_div_of_le hpos4 hden_ge
  have hsmall :
      |z.re / (2 * ‖z‖ ^ 2)| + 1 / (4 * ‖z‖ ^ 2) <= (3 / 8 : Real) := by
    nlinarith [hterm2, hterm3]
  have hinside :
      |Real.log Real.pi - Real.log ‖z‖| +
          |z.re / (2 * ‖z‖ ^ 2)| +
          1 / (4 * ‖z‖ ^ 2) <= L + (3 / 8 : Real) := by
    nlinarith [hlog_abs, hsmall]
  have hinside_nonneg :
      0 <= |Real.log Real.pi - Real.log ‖z‖| +
          |z.re / (2 * ‖z‖ ^ 2)| +
          1 / (4 * ‖z‖ ^ 2) := by
    have hterm3_nonneg : 0 <= 1 / (4 * ‖z‖ ^ 2) := by positivity
    positivity
  have hL_ge_one : (1 : Real) <= L := by
    have hexp : Real.exp 1 <= 3 * t := by
      have he3 : Real.exp 1 <= (3 : Real) := by
        exact (le_of_lt Real.exp_one_lt_d9).trans (by norm_num)
      nlinarith [he3, ht1]
    exact (Real.le_log_iff_exp_le hthree_t_pos).2 hexp
  have htwo_pi_le_seven : 2 * Real.pi <= (7 : Real) := by
    nlinarith [Real.pi_lt_d2]
  calc
    aStarStieltjesLogEnvelope t =
        2 * Real.pi *
          (|Real.log Real.pi - Real.log ‖z‖| +
            |z.re / (2 * ‖z‖ ^ 2)| +
            1 / (4 * ‖z‖ ^ 2)) := by
          simp [aStarStieltjesLogEnvelope, z]
    _ <= 7 *
          (|Real.log Real.pi - Real.log ‖z‖| +
            |z.re / (2 * ‖z‖ ^ 2)| +
            1 / (4 * ‖z‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_right htwo_pi_le_seven hinside_nonneg
    _ <= 7 * (L + (3 / 8 : Real)) := by
          exact mul_le_mul_of_nonneg_left hinside (by norm_num)
    _ <= 10 * L := by
          nlinarith [hL_ge_one]

theorem aStarStieltjesLogEnvelope_le_ten_log_after_260
    {t : Real} (ht : (260 : Real) < t) :
    aStarStieltjesLogEnvelope t <= 10 * Real.log (3 * t) := by
  exact aStarStieltjesLogEnvelope_le_ten_log_after_one (by linarith)

theorem aStarStieltjesLogEnvelope_le_ten_log_after_520
    {t : Real} (ht : (520 : Real) < t) :
    aStarStieltjesLogEnvelope t <= 10 * Real.log (3 * t) := by
  exact aStarStieltjesLogEnvelope_le_ten_log_after_one (by linarith)

theorem a_star_abs_le_ten_logOmega_after_260 :
    ∀ t ∈ Set.Ioi (260 : Real), |Q3.a_star t| <= 10 * Real.log (3 * t) := by
  exact a_star_abs_le_logOmega_of_stieltjesLogEnvelope
    (U := (260 : Real)) (omegaFactor := 10)
    (fun t ht => aStarStieltjesLogEnvelope_le_ten_log_after_260 ht)

theorem a_star_abs_le_ten_logOmega_after_520 :
    ∀ t ∈ Set.Ioi (520 : Real), |Q3.a_star t| <= 10 * Real.log (3 * t) := by
  exact a_star_abs_le_logOmega_of_stieltjesLogEnvelope
    (U := (520 : Real)) (omegaFactor := 10)
    (fun t ht => aStarStieltjesLogEnvelope_le_ten_log_after_520 ht)

theorem step22OmegaArchWeight_abs_le_ten_logOmega_after_520 :
    ∀ eta ∈ Set.Ioi (520 : Real),
      |step22OmegaArchWeight eta| <= 10 * Real.log (3 * eta) := by
  intro eta heta
  let xi : Real := eta / (2 * Real.pi)
  have htwoPi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have heta_gt : (520 : Real) < eta := by
    simpa [Set.mem_Ioi] using heta
  have heta_pos : 0 < eta := by linarith
  have hxi_gt_one : (1 : Real) < xi := by
    rw [show xi = eta / (2 * Real.pi) by rfl]
    rw [lt_div_iff₀ htwoPi_pos]
    nlinarith [heta_gt, Real.pi_lt_d2]
  have hxi_pos : 0 < xi := lt_trans zero_lt_one hxi_gt_one
  have hxi_le_eta : xi <= eta := by
    rw [show xi = eta / (2 * Real.pi) by rfl]
    rw [div_le_iff₀ htwoPi_pos]
    nlinarith [heta_pos, Real.pi_gt_three]
  have hA :
      |Q3.a_star xi| <= 10 * Real.log (3 * xi) := by
    exact le_trans (a_star_abs_le_stieltjesLogEnvelope xi)
      (aStarStieltjesLogEnvelope_le_ten_log_after_one hxi_gt_one)
  have hlog_nonneg : 0 <= 10 * Real.log (3 * xi) := by
    have hthree_xi_ge_one : (1 : Real) <= 3 * xi := by nlinarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg hthree_xi_ge_one)
  have hlog_mono : Real.log (3 * xi) <= Real.log (3 * eta) := by
    have hthree_xi_pos : 0 < 3 * xi := by positivity
    have hthree_le : 3 * xi <= 3 * eta := by nlinarith
    exact Real.log_le_log hthree_xi_pos hthree_le
  have hinv_le_one : |(2 * Real.pi)⁻¹| <= 1 := by
    rw [abs_of_pos (inv_pos.mpr htwoPi_pos)]
    calc
      (2 * Real.pi)⁻¹ = (1 : Real) / (2 * Real.pi) := by
        ring
      _ <= (1 : Real) / 1 := by
        exact one_div_le_one_div_of_le zero_lt_one (by nlinarith [Real.pi_gt_three])
      _ = 1 := by norm_num
  calc
    |step22OmegaArchWeight eta| =
        |(2 * Real.pi)⁻¹| * |Q3.a_star xi| := by
          rw [step22OmegaArchWeight_eq_neg_inv_twoPi_aStar eta]
          simp [xi, abs_mul, abs_neg]
    _ <= 1 * (10 * Real.log (3 * xi)) := by
          exact mul_le_mul hinv_le_one hA (abs_nonneg _) (by norm_num)
    _ = 10 * Real.log (3 * xi) := by ring
    _ <= 10 * Real.log (3 * eta) := by
          exact mul_le_mul_of_nonneg_left hlog_mono (by norm_num)

def centeredBSplineImagTransformSqTailMajorant
    (k : Nat) (ell t : Real) : Real :=
  |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
    (|(ell / (2 * bsplineScale k))|⁻¹) ^ (2 * (k + 1)) *
      t ^ (-(2 * (k + 1) : Real))

theorem centeredBSplineImagTransformRealClosedForm_sq_abs_le_full_tail
    (k : Nat) (ell t : Real) (hell : 0 < ell) (ht : 0 < t) :
    |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
      centeredBSplineImagTransformSqTailMajorant k ell t := by
  let D : Real := (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹
  let c : Real := ell / (2 * bsplineScale k)
  let q : Nat := 2 * (k + 1)
  have hc_ne : c ≠ 0 := by
    unfold c
    exact div_ne_zero hell.ne'
      (mul_ne_zero (by norm_num) (bsplineScale_ne_zero k))
  have harg :
      ell * t / (2 * bsplineScale k) = c * t := by
    unfold c
    ring
  have hct : c * t ≠ 0 := mul_ne_zero hc_ne ht.ne'
  have hsinc := realSinc_abs_le_inv_abs hct
  have hpow :
      |realSinc (c * t)| ^ q <= (|c * t|⁻¹) ^ q := by
    exact pow_le_pow_left₀ (abs_nonneg _) hsinc q
  have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc_ne
  have htne : t ≠ 0 := ht.ne'
  have hpow_tail :
      (|c * t|⁻¹) ^ q = (|c|⁻¹) ^ q * t ^ (-(q : Real)) := by
    have h_abs_inv : |c * t|⁻¹ = |c|⁻¹ * t⁻¹ := by
      rw [abs_mul, abs_of_pos ht]
      field_simp [hcabs, htne]
    have h_t_inv_pow : t⁻¹ ^ q = t ^ (-(q : Real)) := by
      rw [Real.rpow_neg (le_of_lt ht)]
      rw [Real.rpow_natCast]
      rw [inv_pow]
    calc
      (|c * t|⁻¹) ^ q = (|c|⁻¹ * t⁻¹) ^ q := by rw [h_abs_inv]
      _ = (|c|⁻¹) ^ q * t⁻¹ ^ q := by rw [mul_pow]
      _ = (|c|⁻¹) ^ q * t ^ (-(q : Real)) := by rw [h_t_inv_pow]
  have hEabs :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 =
        |D| ^ 2 * |realSinc (c * t)| ^ q := by
    unfold centeredBSplineImagTransformRealClosedForm D q
    rw [harg]
    rw [abs_mul]
    rw [abs_pow]
    rw [mul_pow]
    ring_nf
  calc
    |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 =
        |D| ^ 2 * |realSinc (c * t)| ^ q := hEabs
    _ <= |D| ^ 2 * ((|c|⁻¹) ^ q * t ^ (-(q : Real))) := by
          rw [← hpow_tail]
          exact mul_le_mul_of_nonneg_left hpow (sq_nonneg |D|)
    _ = centeredBSplineImagTransformSqTailMajorant k ell t := by
          have hqexp : -(q : Real) = -2 - (k : Real) * 2 := by
            unfold q
            norm_num
            ring
          rw [hqexp]
          unfold centeredBSplineImagTransformSqTailMajorant D c q
          ring_nf

private def primaryK11RawOmegaATailLogMajorantDominatingConstant : Real :=
  9 *
    (|(Real.sqrt
        (bsplineScale 11 *
          bsplineAutocorrNorm 11))⁻¹| ^ 2 *
      (|(primaryK11Ell /
        (2 * bsplineScale 11))|⁻¹) ^
          (2 * (11 + 1)))

private def controlK9RawOmegaATailLogMajorantDominatingConstant : Real :=
  9 *
    (|(Real.sqrt
        (bsplineScale 9 *
          bsplineAutocorrNorm 9))⁻¹| ^ 2 *
      (|(controlK9Ell /
        (2 * bsplineScale 9))|⁻¹) ^
          (2 * (9 + 1)))

private theorem primaryK11RawOmegaATailLogMajorant_after520
    (eta : Real) (heta : eta ∈ Set.Ioi (520 : Real)) :
    ‖|primaryK11Ell / Real.pi| *
        ((10 : Real) * Real.log (3 * eta)) *
        centeredBSplineImagTransformSqTailMajorant 11 primaryK11Ell eta‖ <=
      primaryK11RawOmegaATailLogMajorantDominatingConstant *
        eta ^ (-23 : Real) := by
  have heta520 : (520 : Real) < eta := by
    simpa [Set.mem_Ioi] using heta
  have hetapos : 0 < eta := by linarith
  have heta3pos : 0 < 3 * eta := by positivity
  have hlog : Real.log (3 * eta) <= 3 * eta :=
    Real.log_le_self (le_of_lt heta3pos)
  have hlog_nonneg : 0 <= Real.log (3 * eta) :=
    Real.log_nonneg (by nlinarith)
  have hpow_nonneg : 0 <= eta ^ (-24 : Real) :=
    Real.rpow_nonneg hetapos.le _
  let C : Real :=
    |(Real.sqrt
        (bsplineScale 11 *
          bsplineAutocorrNorm 11))⁻¹| ^ 2 *
      (|(primaryK11Ell /
        (2 * bsplineScale 11))|⁻¹) ^
          (2 * (11 + 1))
  have hC_nonneg : 0 <= C := by
    unfold C
    positivity
  have hscale_le : |primaryK11Ell / Real.pi| <= |(3 : Real) / 10| := by
    have hpi_ge_one : (1 : Real) <= Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hinv_le_one : Real.pi⁻¹ <= (1 : Real) := by
      calc
        Real.pi⁻¹ = (1 : Real) / Real.pi := by
          ring
        _ <= (1 : Real) / 1 := by
          exact one_div_le_one_div_of_le zero_lt_one hpi_ge_one
        _ = 1 := by norm_num
    calc
      |primaryK11Ell / Real.pi| =
          |primaryK11Ell| * Real.pi⁻¹ := by
            rw [abs_div, abs_of_pos Real.pi_pos]
            rw [div_eq_mul_inv]
      _ <= |primaryK11Ell| * 1 := by
            exact mul_le_mul_of_nonneg_left hinv_le_one (abs_nonneg _)
      _ = |primaryK11Ell| := by ring
      _ = |(3 : Real) / 10| := by
            norm_num [primaryK11Ell, primaryK11EllRat]
  have hmaj_eq :
      centeredBSplineImagTransformSqTailMajorant
          11 primaryK11Ell eta =
        C * eta ^ (-24 : Real) := by
    unfold centeredBSplineImagTransformSqTailMajorant C
    norm_num
  have hrpow : eta * eta ^ (-24 : Real) = eta ^ (-23 : Real) := by
    calc
      eta * eta ^ (-24 : Real) =
          eta ^ (1 : Real) * eta ^ (-24 : Real) := by rw [Real.rpow_one]
      _ = eta ^ ((1 : Real) + (-24 : Real)) := by
          rw [← Real.rpow_add hetapos]
      _ = eta ^ (-23 : Real) := by norm_num
  rw [hmaj_eq]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · calc
      |primaryK11Ell / Real.pi| * (10 * Real.log (3 * eta)) *
          (C * eta ^ (-24 : Real))
          <= |primaryK11Ell / Real.pi| * (10 * (3 * eta)) *
            (C * eta ^ (-24 : Real)) := by
              gcongr
      _ <= |(3 : Real) / 10| * (10 * (3 * eta)) *
            (C * eta ^ (-24 : Real)) := by
              gcongr
      _ = primaryK11RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-23 : Real) := by
              unfold primaryK11RawOmegaATailLogMajorantDominatingConstant C
              rw [abs_of_pos (by norm_num : (0 : Real) < 3 / 10)]
              rw [← hrpow]
              ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num) hlog_nonneg))
      (mul_nonneg hC_nonneg hpow_nonneg)

private theorem controlK9RawOmegaATailLogMajorant_after520
    (eta : Real) (heta : eta ∈ Set.Ioi (520 : Real)) :
    ‖|controlK9Ell / Real.pi| *
        ((10 : Real) * Real.log (3 * eta)) *
        centeredBSplineImagTransformSqTailMajorant 9 controlK9Ell eta‖ <=
      controlK9RawOmegaATailLogMajorantDominatingConstant *
        eta ^ (-19 : Real) := by
  have heta520 : (520 : Real) < eta := by
    simpa [Set.mem_Ioi] using heta
  have hetapos : 0 < eta := by linarith
  have heta3pos : 0 < 3 * eta := by positivity
  have hlog : Real.log (3 * eta) <= 3 * eta :=
    Real.log_le_self (le_of_lt heta3pos)
  have hlog_nonneg : 0 <= Real.log (3 * eta) :=
    Real.log_nonneg (by nlinarith)
  have hpow_nonneg : 0 <= eta ^ (-20 : Real) :=
    Real.rpow_nonneg hetapos.le _
  let C : Real :=
    |(Real.sqrt
        (bsplineScale 9 *
          bsplineAutocorrNorm 9))⁻¹| ^ 2 *
      (|(controlK9Ell /
        (2 * bsplineScale 9))|⁻¹) ^
          (2 * (9 + 1))
  have hC_nonneg : 0 <= C := by
    unfold C
    positivity
  have hscale_le : |controlK9Ell / Real.pi| <= |(3 : Real) / 10| := by
    have hpi_ge_one : (1 : Real) <= Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hinv_le_one : Real.pi⁻¹ <= (1 : Real) := by
      calc
        Real.pi⁻¹ = (1 : Real) / Real.pi := by
          ring
        _ <= (1 : Real) / 1 := by
          exact one_div_le_one_div_of_le zero_lt_one hpi_ge_one
        _ = 1 := by norm_num
    calc
      |controlK9Ell / Real.pi| =
          |controlK9Ell| * Real.pi⁻¹ := by
            rw [abs_div, abs_of_pos Real.pi_pos]
            rw [div_eq_mul_inv]
      _ <= |controlK9Ell| * 1 := by
            exact mul_le_mul_of_nonneg_left hinv_le_one (abs_nonneg _)
      _ = |controlK9Ell| := by ring
      _ = |(3 : Real) / 10| := by
            norm_num [controlK9Ell, controlK9EllRat]
  have hmaj_eq :
      centeredBSplineImagTransformSqTailMajorant
          9 controlK9Ell eta =
        C * eta ^ (-20 : Real) := by
    unfold centeredBSplineImagTransformSqTailMajorant C
    norm_num
  have hrpow : eta * eta ^ (-20 : Real) = eta ^ (-19 : Real) := by
    calc
      eta * eta ^ (-20 : Real) =
          eta ^ (1 : Real) * eta ^ (-20 : Real) := by rw [Real.rpow_one]
      _ = eta ^ ((1 : Real) + (-20 : Real)) := by
          rw [← Real.rpow_add hetapos]
      _ = eta ^ (-19 : Real) := by norm_num
  rw [hmaj_eq]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · calc
      |controlK9Ell / Real.pi| * (10 * Real.log (3 * eta)) *
          (C * eta ^ (-20 : Real))
          <= |controlK9Ell / Real.pi| * (10 * (3 * eta)) *
            (C * eta ^ (-20 : Real)) := by
              gcongr
      _ <= |(3 : Real) / 10| * (10 * (3 * eta)) *
            (C * eta ^ (-20 : Real)) := by
              gcongr
      _ = controlK9RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-19 : Real) := by
              unfold controlK9RawOmegaATailLogMajorantDominatingConstant C
              rw [abs_of_pos (by norm_num : (0 : Real) < 3 / 10)]
              rw [← hrpow]
              ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num) hlog_nonneg))
      (mul_nonneg hC_nonneg hpow_nonneg)

private theorem primaryK11RawOmegaATailLogMajorantContinuous_after520 :
    ContinuousOn
      (fun eta : Real =>
        |primaryK11Ell / Real.pi| *
          ((10 : Real) * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant
            11 primaryK11Ell eta)
      (Set.Ioi (520 : Real)) := by
  have hlog : ContinuousOn (fun eta : Real => Real.log (3 * eta))
      (Set.Ioi (520 : Real)) := by
    have hmul : ContinuousOn (fun eta : Real => (3 : Real) * eta)
        (Set.Ioi (520 : Real)) := by
      simpa using ((continuousOn_const : ContinuousOn (fun _ : Real => (3 : Real))
        (Set.Ioi (520 : Real))).mul continuousOn_id)
    exact hmul.log (by
      intro eta heta
      have heta520 : (520 : Real) < eta := by
        simpa [Set.mem_Ioi] using heta
      nlinarith)
  have hrpow : ContinuousOn (fun eta : Real => eta ^ (-(2 * (11 + 1) : Real)))
      (Set.Ioi (520 : Real)) := by
    exact continuousOn_id.rpow_const (by
      intro eta heta
      left
      change eta ≠ 0
      have heta520 : (520 : Real) < eta := by
        simpa [Set.mem_Ioi] using heta
      nlinarith)
  unfold centeredBSplineImagTransformSqTailMajorant
  fun_prop

private theorem controlK9RawOmegaATailLogMajorantContinuous_after520 :
    ContinuousOn
      (fun eta : Real =>
        |controlK9Ell / Real.pi| *
          ((10 : Real) * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant
            9 controlK9Ell eta)
      (Set.Ioi (520 : Real)) := by
  have hlog : ContinuousOn (fun eta : Real => Real.log (3 * eta))
      (Set.Ioi (520 : Real)) := by
    have hmul : ContinuousOn (fun eta : Real => (3 : Real) * eta)
        (Set.Ioi (520 : Real)) := by
      simpa using ((continuousOn_const : ContinuousOn (fun _ : Real => (3 : Real))
        (Set.Ioi (520 : Real))).mul continuousOn_id)
    exact hmul.log (by
      intro eta heta
      have heta520 : (520 : Real) < eta := by
        simpa [Set.mem_Ioi] using heta
      nlinarith)
  have hrpow : ContinuousOn (fun eta : Real => eta ^ (-(2 * (9 + 1) : Real)))
      (Set.Ioi (520 : Real)) := by
    exact continuousOn_id.rpow_const (by
      intro eta heta
      left
      change eta ≠ 0
      have heta520 : (520 : Real) < eta := by
        simpa [Set.mem_Ioi] using heta
      nlinarith)
  unfold centeredBSplineImagTransformSqTailMajorant
  fun_prop

theorem primaryK11RawOmegaATailLogMajorant_integrable_after_520 :
    ∀ _n : CoeffIndex23,
      Integrable
        (fun eta : Real =>
          |primaryK11Ell / Real.pi| *
            ((10 : Real) * Real.log (3 * eta)) *
            centeredBSplineImagTransformSqTailMajorant
              11 primaryK11Ell eta)
        (volume.restrict (Set.Ioi (520 : Real))) := by
  intro _n
  have hdom :
      Integrable (fun eta : Real =>
          primaryK11RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-23 : Real))
        (volume.restrict (Set.Ioi (520 : Real))) := by
    have hOn : IntegrableOn (fun eta : Real =>
          primaryK11RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-23 : Real))
        (Set.Ioi (520 : Real)) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-23 : Real) < -1)
        (by norm_num : (0 : Real) < 520)).const_mul
            primaryK11RawOmegaATailLogMajorantDominatingConstant
    simpa [IntegrableOn] using hOn
  refine hdom.mono'
    (ContinuousOn.aestronglyMeasurable
      primaryK11RawOmegaATailLogMajorantContinuous_after520 measurableSet_Ioi) ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono
    (fun eta heta => primaryK11RawOmegaATailLogMajorant_after520 eta heta)

theorem controlK9RawOmegaATailLogMajorant_integrable_after_520 :
    ∀ _n : CoeffIndex23,
      Integrable
        (fun eta : Real =>
          |controlK9Ell / Real.pi| *
            ((10 : Real) * Real.log (3 * eta)) *
            centeredBSplineImagTransformSqTailMajorant
              9 controlK9Ell eta)
        (volume.restrict (Set.Ioi (520 : Real))) := by
  intro _n
  have hdom :
      Integrable (fun eta : Real =>
          controlK9RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-19 : Real))
        (volume.restrict (Set.Ioi (520 : Real))) := by
    have hOn : IntegrableOn (fun eta : Real =>
          controlK9RawOmegaATailLogMajorantDominatingConstant *
            eta ^ (-19 : Real))
        (Set.Ioi (520 : Real)) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-19 : Real) < -1)
        (by norm_num : (0 : Real) < 520)).const_mul
            controlK9RawOmegaATailLogMajorantDominatingConstant
    simpa [IntegrableOn] using hOn
  refine hdom.mono'
    (ContinuousOn.aestronglyMeasurable
      controlK9RawOmegaATailLogMajorantContinuous_after520 measurableSet_Ioi) ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono
    (fun eta heta => controlK9RawOmegaATailLogMajorant_after520 eta heta)

def rawOmegaLog1560Upper : Real :=
  (7352441100243583 : Real) / (10 : Real) ^ 15

theorem rawOmega_log_1560_le_upper :
    Real.log (1560 : Real) <= rawOmegaLog1560Upper := by
  have hnle : (1560 : Real) <= Real.exp rawOmegaLog1560Upper := by
    have hx0 : 0 <= rawOmegaLog1560Upper := by
      norm_num [rawOmegaLog1560Upper]
    have hsum :
        (1560 : Real) <=
          ∑ m ∈ Finset.range 39,
            rawOmegaLog1560Upper ^ m / (Nat.factorial m) := by
      norm_num [rawOmegaLog1560Upper]
    have hle :
        (∑ m ∈ Finset.range 39,
            rawOmegaLog1560Upper ^ m / (Nat.factorial m)) <=
          Real.exp rawOmegaLog1560Upper := by
      simpa using (Real.sum_le_exp_of_nonneg hx0 39)
    exact le_trans hsum hle
  exact Q3.Proofs.PrimeCert.log_nat_le_of_le_exp
    (n := 1560) (by norm_num) hnle

def rawOmegaPiLower : Real :=
  (314159265358979323846 : Real) / (10 : Real) ^ 20

theorem rawOmegaPiLower_le_pi : rawOmegaPiLower <= Real.pi := by
  have h : rawOmegaPiLower = (3.14159265358979323846 : Real) := by
    norm_num [rawOmegaPiLower]
  rw [h]
  exact le_of_lt Real.pi_gt_d20

private theorem rawOmega_log_rpow_tendsto_zero
    (p : Real) (hp : 1 < p) :
    Tendsto (fun x : Real => Real.log x * x ^ (-p)) atTop (𝓝 0) := by
  have hLittle :
      (fun x : Real => Real.log x * x ^ (-p)) =o[atTop]
        (fun x : Real => x ^ (1 : Real) * x ^ (-p)) := by
    exact (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1)).mul_isBigO
      (isBigO_refl (fun x : Real => x ^ (-p)) atTop)
  have htarget :
      Tendsto (fun x : Real => x ^ (1 : Real) * x ^ (-p)) atTop (𝓝 0) := by
    have hp1 : 0 < p - 1 := by linarith
    have hbase : Tendsto (fun x : Real => x ^ (-(p - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hp1
    have heq :
        (fun x : Real => x ^ (-(p - 1))) =ᶠ[atTop]
          (fun x : Real => x ^ (1 : Real) * x ^ (-p)) := by
      refine (eventually_gt_atTop (0 : Real)).mono ?_
      intro x hx
      calc
        x ^ (-(p - 1)) = x ^ ((1 : Real) + (-p)) := by ring_nf
        _ = x ^ (1 : Real) * x ^ (-p) := by rw [Real.rpow_add hx]
    exact Filter.Tendsto.congr' heq hbase
  exact hLittle.trans_tendsto htarget

private theorem rawOmega_log_three_mul_rpow_tendsto_zero
    (p : Real) (hp : 1 < p) :
    Tendsto (fun x : Real => Real.log (3 * x) * x ^ (-p)) atTop (𝓝 0) := by
  have hlogx : Tendsto (fun x : Real => Real.log x * x ^ (-p)) atTop (𝓝 0) :=
    rawOmega_log_rpow_tendsto_zero p hp
  have hconst :
      Tendsto (fun x : Real => Real.log (3 : Real) * x ^ (-p)) atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_neg_atTop (by linarith : (0 : Real) < p)).const_mul
        (Real.log (3 : Real))
  have hsum : Tendsto
      (fun x : Real =>
        Real.log (3 : Real) * x ^ (-p) + Real.log x * x ^ (-p))
      atTop (𝓝 0) := by
    simpa using hconst.add hlogx
  have heq :
      (fun x : Real => Real.log (3 * x) * x ^ (-p)) =ᶠ[atTop]
        (fun x : Real =>
          Real.log (3 : Real) * x ^ (-p) + Real.log x * x ^ (-p)) := by
    refine (eventually_gt_atTop (0 : Real)).mono ?_
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have h3ne : (3 : Real) ≠ 0 := by norm_num
    dsimp
    rw [Real.log_mul h3ne hxne]
    ring
  exact Filter.Tendsto.congr' heq.symm hsum

theorem rawOmega_integral_Ioi_log_three_mul_rpow_neg24_after_520 :
    ∫ eta in Set.Ioi (520 : Real),
      Real.log (3 * eta) * eta ^ (-24 : Real) =
    (520 : Real) ^ (-23 : Real) *
      (Real.log (1560 : Real) / 23 + 1 / ((23 : Real) ^ 2)) := by
  let g : Real → Real := fun x =>
    x ^ (-23 : Real) *
      (Real.log (3 * x) / (-23 : Real) - 1 / ((-23 : Real) ^ 2))
  let g' : Real → Real := fun x =>
    Real.log (3 * x) * x ^ (-24 : Real)
  have hderiv : ∀ x ∈ Set.Ici (520 : Real), HasDerivAt g (g' x) x := by
    intro t ht
    have htpos : 0 < t := by
      have h : (520 : Real) <= t := by simpa [Set.mem_Ici] using ht
      nlinarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have h3ne : 3 * t ≠ 0 := by nlinarith
    have hpow : HasDerivAt (fun x : Real => x ^ (-23 : Real))
        ((-23 : Real) * t ^ ((-23 : Real) - 1)) t := by
      exact Real.hasDerivAt_rpow_const (x := t) (p := (-23 : Real)) (Or.inl htne)
    have hlog : HasDerivAt (fun x : Real => Real.log (3 * x)) (t⁻¹) t := by
      have hmul : HasDerivAt (fun x : Real => 3 * x) 3 t := by
        simpa using (hasDerivAt_id t).const_mul (3 : Real)
      have hlog0 : HasDerivAt Real.log (3 * t)⁻¹ (3 * t) :=
        Real.hasDerivAt_log h3ne
      convert hlog0.comp t hmul using 1
      field_simp [htne]
    have hsecond : HasDerivAt
        (fun x : Real =>
          Real.log (3 * x) / (-23 : Real) - 1 / ((-23 : Real) ^ 2))
        (t⁻¹ / (-23 : Real) - 0) t := by
      exact (hlog.div_const (-23 : Real)).sub
        (hasDerivAt_const t (1 / ((-23 : Real) ^ 2)))
    have hprod := hpow.mul hsecond
    convert hprod using 1
    dsimp [g']
    field_simp [htne]
    norm_num
    field_simp [htne]
    ring
  have g'pos : ∀ x ∈ Set.Ioi (520 : Real), 0 <= g' x := by
    intro x hx
    have hx520 : (520 : Real) < x := by simpa [Set.mem_Ioi] using hx
    have hxpos : 0 < x := by nlinarith
    have hlog : 0 <= Real.log (3 * x) := by
      exact Real.log_nonneg (by nlinarith : (1 : Real) <= 3 * x)
    have hrpow : 0 <= x ^ (-24 : Real) := Real.rpow_nonneg hxpos.le _
    exact mul_nonneg hlog hrpow
  have hlim : Tendsto g atTop (𝓝 (0 : Real)) := by
    have hlogprod :
        Tendsto (fun x : Real => Real.log (3 * x) * x ^ (-23 : Real))
          atTop (𝓝 0) :=
      rawOmega_log_three_mul_rpow_tendsto_zero 23 (by norm_num)
    have hrpow : Tendsto (fun x : Real => x ^ (-23 : Real)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 23)
    have hcombo0 := ((hlogprod.const_mul (1 / (-23 : Real))).sub
      (hrpow.const_mul (((23 : Real) ^ 2)⁻¹)))
    have hcombo : Tendsto
        (fun x : Real =>
          (1 / (-23 : Real)) * (Real.log (3 * x) * x ^ (-23 : Real)) -
            (((23 : Real) ^ 2)⁻¹) * x ^ (-23 : Real))
        atTop (𝓝 0) := by
      simpa using hcombo0
    have heq : g =ᶠ[atTop]
        (fun x : Real =>
          (1 / (-23 : Real)) * (Real.log (3 * x) * x ^ (-23 : Real)) -
            (((23 : Real) ^ 2)⁻¹) * x ^ (-23 : Real)) := by
      exact Eventually.of_forall (by
        intro x
        dsimp [g]
        ring)
    exact Filter.Tendsto.congr' heq.symm hcombo
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (520 : Real)) hderiv g'pos hlim
  calc
    ∫ eta in Set.Ioi (520 : Real),
      Real.log (3 * eta) * eta ^ (-24 : Real) =
        ∫ eta in Set.Ioi (520 : Real), g' eta := by rfl
    _ = (0 : Real) - g (520 : Real) := hmain
    _ = (520 : Real) ^ (-23 : Real) *
      (Real.log (1560 : Real) / 23 + 1 / ((23 : Real) ^ 2)) := by
        dsimp [g]
        norm_num
        ring_nf

theorem rawOmega_integral_Ioi_log_three_mul_rpow_neg20_after_520 :
    ∫ eta in Set.Ioi (520 : Real),
      Real.log (3 * eta) * eta ^ (-20 : Real) =
    (520 : Real) ^ (-19 : Real) *
      (Real.log (1560 : Real) / 19 + 1 / ((19 : Real) ^ 2)) := by
  let g : Real → Real := fun x =>
    x ^ (-19 : Real) *
      (Real.log (3 * x) / (-19 : Real) - 1 / ((-19 : Real) ^ 2))
  let g' : Real → Real := fun x =>
    Real.log (3 * x) * x ^ (-20 : Real)
  have hderiv : ∀ x ∈ Set.Ici (520 : Real), HasDerivAt g (g' x) x := by
    intro t ht
    have htpos : 0 < t := by
      have h : (520 : Real) <= t := by simpa [Set.mem_Ici] using ht
      nlinarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have h3ne : 3 * t ≠ 0 := by nlinarith
    have hpow : HasDerivAt (fun x : Real => x ^ (-19 : Real))
        ((-19 : Real) * t ^ ((-19 : Real) - 1)) t := by
      exact Real.hasDerivAt_rpow_const (x := t) (p := (-19 : Real)) (Or.inl htne)
    have hlog : HasDerivAt (fun x : Real => Real.log (3 * x)) (t⁻¹) t := by
      have hmul : HasDerivAt (fun x : Real => 3 * x) 3 t := by
        simpa using (hasDerivAt_id t).const_mul (3 : Real)
      have hlog0 : HasDerivAt Real.log (3 * t)⁻¹ (3 * t) :=
        Real.hasDerivAt_log h3ne
      convert hlog0.comp t hmul using 1
      field_simp [htne]
    have hsecond : HasDerivAt
        (fun x : Real =>
          Real.log (3 * x) / (-19 : Real) - 1 / ((-19 : Real) ^ 2))
        (t⁻¹ / (-19 : Real) - 0) t := by
      exact (hlog.div_const (-19 : Real)).sub
        (hasDerivAt_const t (1 / ((-19 : Real) ^ 2)))
    have hprod := hpow.mul hsecond
    convert hprod using 1
    dsimp [g']
    field_simp [htne]
    norm_num
    field_simp [htne]
    ring
  have g'pos : ∀ x ∈ Set.Ioi (520 : Real), 0 <= g' x := by
    intro x hx
    have hx520 : (520 : Real) < x := by simpa [Set.mem_Ioi] using hx
    have hxpos : 0 < x := by nlinarith
    have hlog : 0 <= Real.log (3 * x) := by
      exact Real.log_nonneg (by nlinarith : (1 : Real) <= 3 * x)
    have hrpow : 0 <= x ^ (-20 : Real) := Real.rpow_nonneg hxpos.le _
    exact mul_nonneg hlog hrpow
  have hlim : Tendsto g atTop (𝓝 (0 : Real)) := by
    have hlogprod :
        Tendsto (fun x : Real => Real.log (3 * x) * x ^ (-19 : Real))
          atTop (𝓝 0) :=
      rawOmega_log_three_mul_rpow_tendsto_zero 19 (by norm_num)
    have hrpow : Tendsto (fun x : Real => x ^ (-19 : Real)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 19)
    have hcombo0 := ((hlogprod.const_mul (1 / (-19 : Real))).sub
      (hrpow.const_mul (((19 : Real) ^ 2)⁻¹)))
    have hcombo : Tendsto
        (fun x : Real =>
          (1 / (-19 : Real)) * (Real.log (3 * x) * x ^ (-19 : Real)) -
            (((19 : Real) ^ 2)⁻¹) * x ^ (-19 : Real))
        atTop (𝓝 0) := by
      simpa using hcombo0
    have heq : g =ᶠ[atTop]
        (fun x : Real =>
          (1 / (-19 : Real)) * (Real.log (3 * x) * x ^ (-19 : Real)) -
            (((19 : Real) ^ 2)⁻¹) * x ^ (-19 : Real)) := by
      exact Eventually.of_forall (by
        intro x
        dsimp [g]
        ring)
    exact Filter.Tendsto.congr' heq.symm hcombo
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (520 : Real)) hderiv g'pos hlim
  calc
    ∫ eta in Set.Ioi (520 : Real),
      Real.log (3 * eta) * eta ^ (-20 : Real) =
        ∫ eta in Set.Ioi (520 : Real), g' eta := by rfl
    _ = (0 : Real) - g (520 : Real) := hmain
    _ = (520 : Real) ^ (-19 : Real) *
      (Real.log (1560 : Real) / 19 + 1 / ((19 : Real) ^ 2)) := by
        dsimp [g]
        norm_num
        ring_nf

theorem centeredBSplineArchKernelProfileIntegrand_abs_le_logOmegaFullTransformTailMajorant
    (k : Nat) (ell x t omegaFactor : Real)
    (hell : 0 < ell) (ht : 0 < t)
    (hOmega : |Q3.a_star t| <= omegaFactor * Real.log (3 * t)) :
    |centeredBSplineArchKernelProfileIntegrand k ell x t| <=
      |ell| * (omegaFactor * Real.log (3 * t)) *
        centeredBSplineImagTransformSqTailMajorant k ell t := by
  exact
    centeredBSplineArchKernelProfileIntegrand_abs_le_of_aStar_and_transform_sq_majorants
      k ell x t (omegaFactor * Real.log (3 * t))
      (centeredBSplineImagTransformSqTailMajorant k ell t)
      hOmega
      (centeredBSplineImagTransformRealClosedForm_sq_abs_le_full_tail
        k ell t hell ht)

theorem centeredBSplineArchKernelProfileIntegrand_bounds_of_logOmegaFullTransformTailMajorant
    (k : Nat) (ell x t omegaFactor lower upper : Real)
    (hell : 0 < ell) (ht : 0 < t)
    (hOmega : |Q3.a_star t| <= omegaFactor * Real.log (3 * t))
    (hLower :
      lower <=
        -(|ell| * (omegaFactor * Real.log (3 * t)) *
          centeredBSplineImagTransformSqTailMajorant k ell t))
    (hUpper :
      |ell| * (omegaFactor * Real.log (3 * t)) *
          centeredBSplineImagTransformSqTailMajorant k ell t <=
        upper) :
    lower <= centeredBSplineArchKernelProfileIntegrand k ell x t ∧
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upper := by
  have habs :=
    centeredBSplineArchKernelProfileIntegrand_abs_le_logOmegaFullTransformTailMajorant
      k ell x t omegaFactor hell ht hOmega
  exact ⟨le_trans hLower (abs_le.mp habs).1,
    le_trans (abs_le.mp habs).2 hUpper⟩

theorem step22PositiveAxisOmegaAIntegrand_abs_le_of_omega_and_transform_sq_majorants
    (k : Nat) (ell x eta omegaMajorant transformSqMajorant : Real)
    (hOmega : |step22OmegaArchWeight eta| <= omegaMajorant)
    (hTransform :
      |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 <=
        transformSqMajorant) :
    |step22PositiveAxisOmegaAIntegrand k ell x eta| <=
      |ell / Real.pi| * omegaMajorant * transformSqMajorant := by
  have hcos : |Real.cos (eta * x)| <= 1 := Real.abs_cos_le_one _
  have hOmegaNonneg : 0 <= omegaMajorant :=
    le_trans (abs_nonneg _) hOmega
  have hTransformNonneg : 0 <= transformSqMajorant :=
    le_trans (sq_nonneg _) hTransform
  have hProduct :
      |step22OmegaArchWeight eta| *
          |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 *
            |Real.cos (eta * x)| <=
        omegaMajorant * transformSqMajorant := by
    have hBase :
        |step22OmegaArchWeight eta| *
            |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 <=
          omegaMajorant * transformSqMajorant :=
      mul_le_mul hOmega hTransform (sq_nonneg _) hOmegaNonneg
    calc
      |step22OmegaArchWeight eta| *
          |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 *
            |Real.cos (eta * x)| <=
        (omegaMajorant * transformSqMajorant) * 1 := by
          exact mul_le_mul hBase hcos (abs_nonneg _)
            (mul_nonneg hOmegaNonneg hTransformNonneg)
      _ = omegaMajorant * transformSqMajorant := by ring
  calc
    |step22PositiveAxisOmegaAIntegrand k ell x eta| =
        |ell / Real.pi| *
          |step22OmegaArchWeight eta| *
            |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 *
              |Real.cos (eta * x)| := by
          simp [step22PositiveAxisOmegaAIntegrand, abs_mul, abs_pow]
    _ = |ell / Real.pi| *
        (|step22OmegaArchWeight eta| *
          |centeredBSplineImagTransformRealClosedForm k ell eta| ^ 2 *
            |Real.cos (eta * x)|) := by ring
    _ <= |ell / Real.pi| * (omegaMajorant * transformSqMajorant) := by
          exact mul_le_mul_of_nonneg_left hProduct (abs_nonneg _)
    _ = |ell / Real.pi| * omegaMajorant * transformSqMajorant := by ring

theorem step22PositiveAxisOmegaAIntegrand_abs_le_logOmegaFullTransformTailMajorant
    (k : Nat) (ell x eta omegaFactor : Real)
    (hell : 0 < ell) (heta : 0 < eta)
    (hOmega : |step22OmegaArchWeight eta| <= omegaFactor * Real.log (3 * eta)) :
    |step22PositiveAxisOmegaAIntegrand k ell x eta| <=
      |ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
        centeredBSplineImagTransformSqTailMajorant k ell eta := by
  exact
    step22PositiveAxisOmegaAIntegrand_abs_le_of_omega_and_transform_sq_majorants
      k ell x eta (omegaFactor * Real.log (3 * eta))
      (centeredBSplineImagTransformSqTailMajorant k ell eta)
      hOmega
      (centeredBSplineImagTransformRealClosedForm_sq_abs_le_full_tail
        k ell eta hell heta)

theorem step22PositiveAxisOmegaATail_abs_le_of_integral_majorant
    (k : Nat) (ell x U remainderRadius : Real)
    (majorant : Real → Real)
    (hint :
      Integrable (fun eta : Real => step22PositiveAxisOmegaAIntegrand k ell x eta)
        (volume.restrict (Set.Ioi U)))
    (hMajorantInt :
      Integrable majorant (volume.restrict (Set.Ioi U)))
    (hMajorant : ∀ eta ∈ Set.Ioi U,
      |step22PositiveAxisOmegaAIntegrand k ell x eta| <= majorant eta)
    (hIntegral :
      ∫ eta in Set.Ioi U, majorant eta <= remainderRadius) :
    |step22PositiveAxisOmegaATailPart k ell x U| <= remainderRadius := by
  have habsint :
      Integrable
        (fun eta : Real => |step22PositiveAxisOmegaAIntegrand k ell x eta|)
        (volume.restrict (Set.Ioi U)) := by
    simpa [Real.norm_eq_abs] using hint.norm
  have hmono :
      ∫ eta in Set.Ioi U,
          |step22PositiveAxisOmegaAIntegrand k ell x eta| <=
        ∫ eta in Set.Ioi U, majorant eta := by
    refine integral_mono_ae habsint hMajorantInt ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro eta heta
    exact hMajorant eta heta
  calc
    |step22PositiveAxisOmegaATailPart k ell x U| =
        |∫ eta in Set.Ioi U, step22PositiveAxisOmegaAIntegrand k ell x eta| := by rfl
    _ <=
        ∫ eta in Set.Ioi U,
          |step22PositiveAxisOmegaAIntegrand k ell x eta| := by
          simpa using
            (abs_integral_le_integral_abs
              (μ := volume.restrict (Set.Ioi U))
              (f := fun eta : Real =>
                step22PositiveAxisOmegaAIntegrand k ell x eta))
    _ <= ∫ eta in Set.Ioi U, majorant eta := hmono
    _ <= remainderRadius := hIntegral

theorem step22PositiveAxisOmegaATail_abs_le_of_logOmegaFullTransformTailMajorant
    (k : Nat) (ell x U omegaFactor remainderRadius : Real)
    (hell : 0 < ell) (hU0 : 0 <= U)
    (hint :
      Integrable (fun eta : Real => step22PositiveAxisOmegaAIntegrand k ell x eta)
        (volume.restrict (Set.Ioi U)))
    (hMajorantInt :
      Integrable
        (fun eta : Real =>
          |ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
            centeredBSplineImagTransformSqTailMajorant k ell eta)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ eta ∈ Set.Ioi U,
      |step22OmegaArchWeight eta| <= omegaFactor * Real.log (3 * eta))
    (hIntegral :
      ∫ eta in Set.Ioi U,
        |ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant k ell eta <=
        remainderRadius) :
    |step22PositiveAxisOmegaATailPart k ell x U| <= remainderRadius := by
  refine
    step22PositiveAxisOmegaATail_abs_le_of_integral_majorant
      k ell x U remainderRadius
      (fun eta : Real =>
        |ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant k ell eta)
      hint hMajorantInt ?_ hIntegral
  intro eta heta
  exact
    step22PositiveAxisOmegaAIntegrand_abs_le_logOmegaFullTransformTailMajorant
      k ell x eta omegaFactor hell (lt_of_le_of_lt hU0 heta)
      (hOmega eta heta)

theorem primaryK11RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
    {U omegaFactor : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun eta : Real =>
          |primaryK11Ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
            centeredBSplineImagTransformSqTailMajorant 11 primaryK11Ell eta)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ eta ∈ Set.Ioi U,
      |step22OmegaArchWeight eta| <= omegaFactor * Real.log (3 * eta))
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ eta in Set.Ioi U,
        |primaryK11Ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant 11 primaryK11Ell eta <=
        remainderRadius n) :
    ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) U| <= remainderRadius n := by
  intro n
  exact
    step22PositiveAxisOmegaATail_abs_le_of_logOmegaFullTransformTailMajorant
      11 primaryK11Ell ((n.1 : Real) / 4) U omegaFactor
      (remainderRadius n)
      (by norm_num [primaryK11Ell, primaryK11EllRat])
      hU0
      (by
        simpa [IntegrableOn] using
          primaryK11RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg U hU0 n)
      (hMajorantInt n) hOmega (hIntegral n)

theorem controlK9RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant
    {U omegaFactor : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun eta : Real =>
          |controlK9Ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
            centeredBSplineImagTransformSqTailMajorant 9 controlK9Ell eta)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ eta ∈ Set.Ioi U,
      |step22OmegaArchWeight eta| <= omegaFactor * Real.log (3 * eta))
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ eta in Set.Ioi U,
        |controlK9Ell / Real.pi| * (omegaFactor * Real.log (3 * eta)) *
          centeredBSplineImagTransformSqTailMajorant 9 controlK9Ell eta <=
        remainderRadius n) :
    ∀ n : CoeffIndex23,
      |step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) U| <= remainderRadius n := by
  intro n
  exact
    step22PositiveAxisOmegaATail_abs_le_of_logOmegaFullTransformTailMajorant
      9 controlK9Ell ((n.1 : Real) / 4) U omegaFactor
      (remainderRadius n)
      (by norm_num [controlK9Ell, controlK9EllRat])
      hU0
      (by
        simpa [IntegrableOn] using
          controlK9RawOmegaAIntegrand_integrableOn_Ioi_of_nonneg U hU0 n)
      (hMajorantInt n) hOmega (hIntegral n)

theorem centeredBSplineArchKernelProfilePositiveTail_abs_le_of_aStar_transform_integral_majorants
    (k : Nat) (ell x U remainderRadius : Real)
    (omegaMajorant transformSqMajorant : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hMajorantInt : Integrable
      (fun t : Real => |ell| * omegaMajorant t * transformSqMajorant t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaMajorant t)
    (hTransform : ∀ t ∈ Set.Ioi U,
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 <=
        transformSqMajorant t)
    (hIntegral :
      ∫ t in Set.Ioi U, |ell| * omegaMajorant t * transformSqMajorant t <=
        remainderRadius) :
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
      remainderRadius := by
  exact
    centeredBSplineArchKernelProfilePositiveTail_abs_le_of_integral_majorant
      k ell x U remainderRadius
      (fun t : Real => |ell| * omegaMajorant t * transformSqMajorant t)
      hint hMajorantInt
      (fun t ht =>
        centeredBSplineArchKernelProfileIntegrand_abs_le_of_aStar_and_transform_sq_majorants
          k ell x t (omegaMajorant t) (transformSqMajorant t)
          (hOmega t ht) (hTransform t ht))
      hIntegral

theorem centeredBSplineArchKernelProfilePositiveTail_abs_le
    (k : Nat) (ell x T C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (hT : 1 <= T) :
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x T| <=
      (|ell| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2) := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  let M : Real := |ell| *
    ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
      (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hfint : Integrable f (volume.restrict (Set.Ioi T)) := by
    exact (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
      k ell x hk hell).restrict
  have habsint : Integrable (fun t : Real => |f t|) (volume.restrict (Set.Ioi T)) := by
    simpa [Real.norm_eq_abs] using hfint.norm
  have hmajint :
      Integrable (fun t : Real => M * t ^ (-3 : ℝ)) (volume.restrict (Set.Ioi T)) := by
    have h : IntegrableOn (fun t : Real => M * t ^ (-3 : ℝ)) (Set.Ioi T) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-3 : ℝ) < -1) hTpos).const_mul M
    simpa [IntegrableOn] using h
  have hmono :
      ∫ t in Set.Ioi T, |f t| <= ∫ t in Set.Ioi T, M * t ^ (-3 : ℝ) := by
    refine integral_mono_ae habsint hmajint ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have ht1 : 1 <= t := le_trans hT (le_of_lt ht)
    have htail := centeredBSplineArchKernelProfileIntegrand_tail_bound
      k ell x t C0 C1 hk hell hC0 hC1 (hgrowth t) ht1
    simpa [f, M, Real.norm_eq_abs, mul_assoc] using htail
  have hmaj_eq :
      ∫ t in Set.Ioi T, M * t ^ (-3 : ℝ) = M * (T ^ (-2 : ℝ) / 2) := by
    rw [integral_const_mul]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hTpos]
    ring_nf
  calc
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x T|
        = |∫ t in Set.Ioi T, f t| := by rfl
    _ <= ∫ t in Set.Ioi T, |f t| := by
      simpa using (abs_integral_le_integral_abs (μ := volume.restrict (Set.Ioi T)) (f := f))
    _ <= ∫ t in Set.Ioi T, M * t ^ (-3 : ℝ) := hmono
    _ = M * (T ^ (-2 : ℝ) / 2) := hmaj_eq
    _ = (|ell| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2) := by rfl

def centeredBSplineArchKernelProfileFinitePart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ t in Set.Icc (-T) T, centeredBSplineArchKernelProfileIntegrand k ell x t

def centeredBSplineArchKernelProfilePositiveFinitePart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ t in Set.Ioc 0 T, centeredBSplineArchKernelProfileIntegrand k ell x t

def centeredBSplineArchKernelProfileTailPart
    (k : Nat) (ell x T : Real) : Real :=
  ∫ t in (Set.Icc (-T) T)ᶜ, centeredBSplineArchKernelProfileIntegrand k ell x t

theorem centeredBSplineArchKernelProfileFinitePart_eq_two_positiveFinitePart
    (k : Nat) (ell x T : Real) (hT : 0 <= T) :
    centeredBSplineArchKernelProfileFinitePart k ell x T =
      2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hnegT : -T <= 0 := by linarith
  have hcover :
      Set.Icc (-T) T = Set.Icc (-T) 0 ∪ Set.Ioc 0 T := by
    exact (Set.Icc_union_Ioc_eq_Icc hnegT hT).symm
  have hdisj : Disjoint (Set.Icc (-T) 0) (Set.Ioc 0 T) := by
    exact (Set.Iic_disjoint_Ioc (a := (0 : Real)) (b := 0) (c := T) le_rfl).mono
      Set.Icc_subset_Iic_self le_rfl
  have hleftint : IntegrableOn f (Set.Icc (-T) 0) := by
    simpa [f] using
      (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
  have hrightint : IntegrableOn f (Set.Ioc 0 T) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self
  have hneg :
      ∫ t in Set.Icc (-T) 0, f t = ∫ t in Set.Ioc 0 T, f t := by
    calc
      ∫ t in Set.Icc (-T) 0, f t = ∫ t in Set.Ioc (-T) 0, f t := by
        exact integral_Icc_eq_integral_Ioc
      _ = ∫ t in (-T)..0, f t := by
        exact (intervalIntegral.integral_of_le hnegT).symm
      _ = ∫ t in 0..T, f (-t) := by
        simp
      _ = ∫ t in 0..T, f t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp [f]
        exact centeredBSplineArchKernelProfileIntegrand_neg k ell x t
      _ = ∫ t in Set.Ioc 0 T, f t := by
        exact intervalIntegral.integral_of_le hT
  unfold centeredBSplineArchKernelProfileFinitePart
    centeredBSplineArchKernelProfilePositiveFinitePart
  rw [hcover]
  rw [setIntegral_union hdisj measurableSet_Ioc hleftint hrightint]
  rw [hneg]
  ring

theorem centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_comparison_integrals
    (k : Nat) (ell x T positiveLower positiveUpper : Real)
    (lowerF upperF : Real → Real)
    (hLowerInt : IntegrableOn lowerF (Set.Ioc 0 T))
    (hUpperInt : IntegrableOn upperF (Set.Ioc 0 T))
    (hLower : ∀ t ∈ Set.Ioc 0 T,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc 0 T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hPositiveLower : positiveLower <= ∫ t in Set.Ioc 0 T, lowerF t)
    (hPositiveUpper : ∫ t in Set.Ioc 0 T, upperF t <= positiveUpper) :
    positiveLower <=
        centeredBSplineArchKernelProfilePositiveFinitePart k ell x T ∧
      centeredBSplineArchKernelProfilePositiveFinitePart k ell x T <=
        positiveUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hfintOn : IntegrableOn f (Set.Ioc 0 T) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self
  constructor
  · calc
      positiveLower <= ∫ t in Set.Ioc 0 T, lowerF t := hPositiveLower
      _ <= ∫ t in Set.Ioc 0 T, f t := by
            exact setIntegral_mono_on hLowerInt hfintOn measurableSet_Ioc hLower
      _ = centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            rfl
  · calc
      centeredBSplineArchKernelProfilePositiveFinitePart k ell x T =
          ∫ t in Set.Ioc 0 T, f t := by
            rfl
      _ <= ∫ t in Set.Ioc 0 T, upperF t := by
            exact setIntegral_mono_on hfintOn hUpperInt measurableSet_Ioc hUpper
      _ <= positiveUpper := hPositiveUpper

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals
    (k : Nat) (ell x T finiteLower finiteUpper : Real)
    (lowerF upperF : Real → Real)
    (hT : 0 <= T)
    (hLowerInt : IntegrableOn lowerF (Set.Ioc 0 T))
    (hUpperInt : IntegrableOn upperF (Set.Ioc 0 T))
    (hLower : ∀ t ∈ Set.Ioc 0 T,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc 0 T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hFiniteLower : finiteLower <= 2 * ∫ t in Set.Ioc 0 T, lowerF t)
    (hFiniteUpper : 2 * ∫ t in Set.Ioc 0 T, upperF t <= finiteUpper) :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  have hpositive :=
    centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_comparison_integrals
      k ell x T (∫ t in Set.Ioc 0 T, lowerF t)
      (∫ t in Set.Ioc 0 T, upperF t) lowerF upperF
      hLowerInt hUpperInt hLower hUpper le_rfl le_rfl
  have hfinite_eq :=
    centeredBSplineArchKernelProfileFinitePart_eq_two_positiveFinitePart
      k ell x T hT
  constructor
  · calc
      finiteLower <= 2 * ∫ t in Set.Ioc 0 T, lowerF t := hFiniteLower
      _ <= 2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            exact mul_le_mul_of_nonneg_left hpositive.1 (by norm_num)
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by
            rw [hfinite_eq]
  · calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            rw [hfinite_eq]
      _ <= 2 * ∫ t in Set.Ioc 0 T, upperF t := by
            exact mul_le_mul_of_nonneg_left hpositive.2 (by norm_num)
      _ <= finiteUpper := hFiniteUpper

theorem centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_two_piece_comparison_integrals
    (k : Nat) (ell x T c positiveLower positiveUpper : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real → Real)
    (hLeft : 0 <= c) (hRight : c <= T)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Ioc 0 c))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Ioc 0 c))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc c T))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc c T))
    (hLowerLeft : ∀ t ∈ Set.Ioc 0 c,
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc 0 c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : ∀ t ∈ Set.Ioc c T,
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hPositiveLower : positiveLower <=
      (∫ t in Set.Ioc 0 c, lowerLeft t) +
        ∫ t in Set.Ioc c T, lowerRight t)
    (hPositiveUpper :
      (∫ t in Set.Ioc 0 c, upperLeft t) +
        ∫ t in Set.Ioc c T, upperRight t <= positiveUpper) :
    positiveLower <=
        centeredBSplineArchKernelProfilePositiveFinitePart k ell x T ∧
      centeredBSplineArchKernelProfilePositiveFinitePart k ell x T <=
        positiveUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Ioc 0 T = Set.Ioc 0 c ∪ Set.Ioc c T := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      by_cases hyc : y <= c
      · exact Or.inl ⟨hy.1, hyc⟩
      · exact Or.inr ⟨lt_of_not_ge hyc, hy.2⟩
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      rcases hy with hleftMem | hrightMem
      · exact ⟨hleftMem.1, le_trans hleftMem.2 hRight⟩
      · exact ⟨lt_of_le_of_lt hLeft hrightMem.1, hrightMem.2⟩
  have hdisj : Disjoint (Set.Ioc 0 c) (Set.Ioc c T) := by
    rw [Set.disjoint_left]
    intro y hyleft hyright
    simp only [Set.mem_Ioc] at hyleft hyright
    exact not_lt_of_ge hyleft.2 hyright.1
  have hfintLeft : IntegrableOn f (Set.Ioc 0 c) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := 0) (b := c)).mono_set Set.Ioc_subset_Icc_self
  have hfintRight : IntegrableOn f (Set.Ioc c T) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := c) (b := T)).mono_set Set.Ioc_subset_Icc_self
  constructor
  · have hLeftBound :
        (∫ t in Set.Ioc 0 c, lowerLeft t) <=
          ∫ t in Set.Ioc 0 c, f t := by
      exact setIntegral_mono_on hLowerLeftInt hfintLeft measurableSet_Ioc hLowerLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, lowerRight t) <=
          ∫ t in Set.Ioc c T, f t := by
      exact setIntegral_mono_on hLowerRightInt hfintRight measurableSet_Ioc hLowerRight
    calc
      positiveLower <= (∫ t in Set.Ioc 0 c, lowerLeft t) +
          ∫ t in Set.Ioc c T, lowerRight t := hPositiveLower
      _ <= (∫ t in Set.Ioc 0 c, f t) + ∫ t in Set.Ioc c T, f t := by
            exact add_le_add hLeftBound hRightBound
      _ = ∫ t in Set.Ioc 0 c ∪ Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            rw [← hcover]
            rfl
  · have hLeftBound :
        (∫ t in Set.Ioc 0 c, f t) <=
          ∫ t in Set.Ioc 0 c, upperLeft t := by
      exact setIntegral_mono_on hfintLeft hUpperLeftInt measurableSet_Ioc hUpperLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, f t) <=
          ∫ t in Set.Ioc c T, upperRight t := by
      exact setIntegral_mono_on hfintRight hUpperRightInt measurableSet_Ioc hUpperRight
    calc
      centeredBSplineArchKernelProfilePositiveFinitePart k ell x T =
          ∫ t in Set.Ioc 0 c ∪ Set.Ioc c T, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Ioc 0 c, f t) + ∫ t in Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ <= (∫ t in Set.Ioc 0 c, upperLeft t) +
          ∫ t in Set.Ioc c T, upperRight t := by
            exact add_le_add hLeftBound hRightBound
      _ <= positiveUpper := hPositiveUpper

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals
    (k : Nat) (ell x T c finiteLower finiteUpper : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real → Real)
    (hT : 0 <= T) (hLeft : 0 <= c) (hRight : c <= T)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Ioc 0 c))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Ioc 0 c))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc c T))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc c T))
    (hLowerLeft : ∀ t ∈ Set.Ioc 0 c,
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc 0 c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : ∀ t ∈ Set.Ioc c T,
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hFiniteLower : finiteLower <=
      2 * ((∫ t in Set.Ioc 0 c, lowerLeft t) +
        ∫ t in Set.Ioc c T, lowerRight t))
    (hFiniteUpper :
      2 * ((∫ t in Set.Ioc 0 c, upperLeft t) +
        ∫ t in Set.Ioc c T, upperRight t) <= finiteUpper) :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  have hpositive :=
    centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_two_piece_comparison_integrals
      k ell x T c
      ((∫ t in Set.Ioc 0 c, lowerLeft t) +
        ∫ t in Set.Ioc c T, lowerRight t)
      ((∫ t in Set.Ioc 0 c, upperLeft t) +
        ∫ t in Set.Ioc c T, upperRight t)
      lowerLeft upperLeft lowerRight upperRight hLeft hRight
      hLowerLeftInt hUpperLeftInt hLowerRightInt hUpperRightInt
      hLowerLeft hUpperLeft hLowerRight hUpperRight le_rfl le_rfl
  have hfinite_eq :=
    centeredBSplineArchKernelProfileFinitePart_eq_two_positiveFinitePart
      k ell x T hT
  constructor
  · calc
      finiteLower <= 2 * ((∫ t in Set.Ioc 0 c, lowerLeft t) +
          ∫ t in Set.Ioc c T, lowerRight t) := hFiniteLower
      _ <= 2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            exact mul_le_mul_of_nonneg_left hpositive.1 (by norm_num)
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by
            rw [hfinite_eq]
  · calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            rw [hfinite_eq]
      _ <= 2 * ((∫ t in Set.Ioc 0 c, upperLeft t) +
          ∫ t in Set.Ioc c T, upperRight t) := by
            exact mul_le_mul_of_nonneg_left hpositive.2 (by norm_num)
      _ <= finiteUpper := hFiniteUpper

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
    (k : Nat) (ell x T lower upper : Real)
    (hT : 0 <= T)
    (hLower : ∀ t ∈ Set.Icc (-T) T,
      lower <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upper) :
    (2 * T) * lower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= (2 * T) * upper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hle : -T <= T := by linarith
  have hvol : volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [Real.volume_real_Icc_of_le hle]
    ring
  have hfintOn : IntegrableOn f (Set.Icc (-T) T) := by
    simpa [f] using
      (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
  have hlowerIntOn : IntegrableOn (fun _ : Real => lower) (Set.Icc (-T) T) := by
    exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hupperIntOn : IntegrableOn (fun _ : Real => upper) (Set.Icc (-T) T) := by
    exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  constructor
  · calc
      (2 * T) * lower = ∫ t in Set.Icc (-T) T, lower := by
        rw [setIntegral_const, smul_eq_mul, hvol]
      _ <= ∫ t in Set.Icc (-T) T, f t := by
        exact setIntegral_mono_on hlowerIntOn hfintOn measurableSet_Icc hLower
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by rfl
  · calc
      centeredBSplineArchKernelProfileFinitePart k ell x T = ∫ t in Set.Icc (-T) T, f t := by
        rfl
      _ <= ∫ t in Set.Icc (-T) T, upper := by
        exact setIntegral_mono_on hfintOn hupperIntOn measurableSet_Icc hUpper
      _ = (2 * T) * upper := by
        rw [setIntegral_const, smul_eq_mul, hvol]

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
    (k : Nat) (ell x T c lowerLeft upperLeft lowerRight upperRight : Real)
    (hLeft : -T <= c) (hRight : c <= T)
    (hLowerLeft : ∀ t ∈ Set.Icc (-T) c,
      lowerLeft <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Icc (-T) c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft)
    (hLowerRight : ∀ t ∈ Set.Ioc c T,
      lowerRight <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight) :
    (c + T) * lowerLeft + (T - c) * lowerRight <=
        centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <=
        (c + T) * upperLeft + (T - c) * upperRight := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Icc (-T) T = Set.Icc (-T) c ∪ Set.Ioc c T := by
    exact (Set.Icc_union_Ioc_eq_Icc hLeft hRight).symm
  have hdisj : Disjoint (Set.Icc (-T) c) (Set.Ioc c T) := by
    exact (Set.Iic_disjoint_Ioc (a := c) (b := c) (c := T) le_rfl).mono
      Set.Icc_subset_Iic_self le_rfl
  have hvolLeft : volume.real (Set.Icc (-T) c) = c + T := by
    rw [Real.volume_real_Icc_of_le hLeft]
    ring
  have hvolRight : volume.real (Set.Ioc c T) = T - c := by
    exact Real.volume_real_Ioc_of_le hRight
  have hfintLeft : IntegrableOn f (Set.Icc (-T) c) := by
    simpa [f] using
      (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
  have hfintRight : IntegrableOn f (Set.Ioc c T) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := c) (b := T)).mono_set Set.Ioc_subset_Icc_self
  have hLowerLeftInt : IntegrableOn (fun _ : Real => lowerLeft) (Set.Icc (-T) c) := by
    exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hUpperLeftInt : IntegrableOn (fun _ : Real => upperLeft) (Set.Icc (-T) c) := by
    exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hLowerRightInt : IntegrableOn (fun _ : Real => lowerRight) (Set.Ioc c T) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  have hUpperRightInt : IntegrableOn (fun _ : Real => upperRight) (Set.Ioc c T) := by
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne) (hC := ENNReal.coe_ne_top)
  constructor
  · have hLeftBound :
        (∫ t in Set.Icc (-T) c, lowerLeft) <=
          ∫ t in Set.Icc (-T) c, f t := by
      exact setIntegral_mono_on hLowerLeftInt hfintLeft measurableSet_Icc hLowerLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, lowerRight) <=
          ∫ t in Set.Ioc c T, f t := by
      exact setIntegral_mono_on hLowerRightInt hfintRight measurableSet_Ioc hLowerRight
    calc
      (c + T) * lowerLeft + (T - c) * lowerRight =
          (∫ t in Set.Icc (-T) c, lowerLeft) +
            ∫ t in Set.Ioc c T, lowerRight := by
            rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
              hvolLeft, hvolRight]
      _ <= (∫ t in Set.Icc (-T) c, f t) + ∫ t in Set.Ioc c T, f t := by
            exact add_le_add hLeftBound hRightBound
      _ = ∫ t in Set.Icc (-T) c ∪ Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by
            rw [← hcover]
            rfl
  · have hLeftBound :
        (∫ t in Set.Icc (-T) c, f t) <=
          ∫ t in Set.Icc (-T) c, upperLeft := by
      exact setIntegral_mono_on hfintLeft hUpperLeftInt measurableSet_Icc hUpperLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, f t) <=
          ∫ t in Set.Ioc c T, upperRight := by
      exact setIntegral_mono_on hfintRight hUpperRightInt measurableSet_Ioc hUpperRight
    calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          ∫ t in Set.Icc (-T) c ∪ Set.Ioc c T, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Icc (-T) c, f t) + ∫ t in Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ <= (∫ t in Set.Icc (-T) c, upperLeft) + ∫ t in Set.Ioc c T, upperRight := by
            exact add_le_add hLeftBound hRightBound
      _ = (c + T) * upperLeft + (T - c) * upperRight := by
            rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
              hvolLeft, hvolRight]

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
    (k : Nat) (ell x T finiteLower finiteUpper : Real)
    (lowerF upperF : Real → Real)
    (hLowerInt : IntegrableOn lowerF (Set.Icc (-T) T))
    (hUpperInt : IntegrableOn upperF (Set.Icc (-T) T))
    (hLower : ∀ t ∈ Set.Icc (-T) T,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hFiniteLower : finiteLower <= ∫ t in Set.Icc (-T) T, lowerF t)
    (hFiniteUpper : ∫ t in Set.Icc (-T) T, upperF t <= finiteUpper) :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hfintOn : IntegrableOn f (Set.Icc (-T) T) := by
    simpa [f] using
      (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
  constructor
  · calc
      finiteLower <= ∫ t in Set.Icc (-T) T, lowerF t := hFiniteLower
      _ <= ∫ t in Set.Icc (-T) T, f t := by
            exact setIntegral_mono_on hLowerInt hfintOn measurableSet_Icc hLower
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by rfl
  · calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          ∫ t in Set.Icc (-T) T, f t := by
            rfl
      _ <= ∫ t in Set.Icc (-T) T, upperF t := by
            exact setIntegral_mono_on hfintOn hUpperInt measurableSet_Icc hUpper
      _ <= finiteUpper := hFiniteUpper

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
    (k : Nat) (ell x T c finiteLower finiteUpper : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real → Real)
    (hLeft : -T <= c) (hRight : c <= T)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Icc (-T) c))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Icc (-T) c))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc c T))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc c T))
    (hLowerLeft : ∀ t ∈ Set.Icc (-T) c,
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Icc (-T) c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : ∀ t ∈ Set.Ioc c T,
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c T,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hFiniteLower : finiteLower <=
      (∫ t in Set.Icc (-T) c, lowerLeft t) +
        ∫ t in Set.Ioc c T, lowerRight t)
    (hFiniteUpper :
      (∫ t in Set.Icc (-T) c, upperLeft t) +
        ∫ t in Set.Ioc c T, upperRight t <= finiteUpper) :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Icc (-T) T = Set.Icc (-T) c ∪ Set.Ioc c T := by
    exact (Set.Icc_union_Ioc_eq_Icc hLeft hRight).symm
  have hdisj : Disjoint (Set.Icc (-T) c) (Set.Ioc c T) := by
    exact (Set.Iic_disjoint_Ioc (a := c) (b := c) (c := T) le_rfl).mono
      Set.Icc_subset_Iic_self le_rfl
  have hfintLeft : IntegrableOn f (Set.Icc (-T) c) := by
    simpa [f] using
      (centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
  have hfintRight : IntegrableOn f (Set.Ioc c T) := by
    exact ((centeredBSplineArchKernelProfileIntegrand_continuous k ell x).integrableOn_Icc
      (a := c) (b := T)).mono_set Set.Ioc_subset_Icc_self
  constructor
  · have hLeftBound :
        (∫ t in Set.Icc (-T) c, lowerLeft t) <=
          ∫ t in Set.Icc (-T) c, f t := by
      exact setIntegral_mono_on hLowerLeftInt hfintLeft measurableSet_Icc hLowerLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, lowerRight t) <=
          ∫ t in Set.Ioc c T, f t := by
      exact setIntegral_mono_on hLowerRightInt hfintRight measurableSet_Ioc hLowerRight
    calc
      finiteLower <= (∫ t in Set.Icc (-T) c, lowerLeft t) +
          ∫ t in Set.Ioc c T, lowerRight t := hFiniteLower
      _ <= (∫ t in Set.Icc (-T) c, f t) + ∫ t in Set.Ioc c T, f t := by
            exact add_le_add hLeftBound hRightBound
      _ = ∫ t in Set.Icc (-T) c ∪ Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by
            rw [← hcover]
            rfl
  · have hLeftBound :
        (∫ t in Set.Icc (-T) c, f t) <=
          ∫ t in Set.Icc (-T) c, upperLeft t := by
      exact setIntegral_mono_on hfintLeft hUpperLeftInt measurableSet_Icc hUpperLeft
    have hRightBound :
        (∫ t in Set.Ioc c T, f t) <=
          ∫ t in Set.Ioc c T, upperRight t := by
      exact setIntegral_mono_on hfintRight hUpperRightInt measurableSet_Ioc hUpperRight
    calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          ∫ t in Set.Icc (-T) c ∪ Set.Ioc c T, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Icc (-T) c, f t) + ∫ t in Set.Ioc c T, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ <= (∫ t in Set.Icc (-T) c, upperLeft t) +
          ∫ t in Set.Ioc c T, upperRight t := by
            exact add_le_add hLeftBound hRightBound
      _ <= finiteUpper := hFiniteUpper

theorem centeredBSplineArchKernelProfileTailPart_eq_two_positiveTailPart
    (k : Nat) (ell x T : Real) (hT : 0 <= T)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t)) :
    centeredBSplineArchKernelProfileTailPart k ell x T =
      2 * centeredBSplineArchKernelProfilePositiveTailPart k ell x T := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
        Set.mem_Iio, Set.mem_Ioi] at hy ⊢
      by_cases hleft : y < -T
      · exact Or.inl hleft
      · right
        have hyge : -T <= y := le_of_not_gt hleft
        by_contra hnot
        have hleT : y <= T := le_of_not_gt hnot
        exact hy ⟨hyge, hleT⟩
    · intro hy
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
        Set.mem_Iio, Set.mem_Ioi] at hy ⊢
      rcases hy with hleft | hright
      · intro hmem
        exact not_le_of_gt hleft hmem.1
      · intro hmem
        exact not_le_of_gt hright hmem.2
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro y hylt hygt
    simp only [Set.mem_Iio, Set.mem_Ioi] at hylt hygt
    linarith
  have hleftint : IntegrableOn f (Set.Iio (-T)) := hint.integrableOn
  have hrightint : IntegrableOn f (Set.Ioi T) := hint.integrableOn
  have hneg : ∫ t in Set.Iio (-T), f t = ∫ t in Set.Ioi T, f t := by
    calc
      ∫ t in Set.Iio (-T), f t = ∫ t in Set.Iic (-T), f t := by
        exact (integral_Iic_eq_integral_Iio (x := -T) (f := f)).symm
      _ = ∫ t in Set.Ioi T, f (-t) := by
        exact (integral_comp_neg_Ioi (c := T) (f := f)).symm
      _ = ∫ t in Set.Ioi T, f t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _ht
        dsimp [f]
        exact centeredBSplineArchKernelProfileIntegrand_neg k ell x t
  unfold centeredBSplineArchKernelProfileTailPart
    centeredBSplineArchKernelProfilePositiveTailPart
  rw [hcompl]
  rw [setIntegral_union hdisj measurableSet_Ioi hleftint hrightint]
  rw [hneg]
  ring

theorem centeredBSplineArchKernelProfilePositiveTailPart_eq_window_add_positiveTailPart
    (k : Nat) (ell x T U : Real) (hTU : T <= U)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t)) :
    centeredBSplineArchKernelProfilePositiveTailPart k ell x T =
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U +
        centeredBSplineArchKernelProfilePositiveTailPart k ell x U := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover : Set.Ioi T = Set.Ioc T U ∪ Set.Ioi U := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at hy ⊢
      by_cases hyU : y <= U
      · exact Or.inl ⟨hy, hyU⟩
      · exact Or.inr (lt_of_not_ge hyU)
    · intro hy
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc] at hy ⊢
      rcases hy with hwin | htail
      · exact hwin.1
      · exact lt_of_le_of_lt hTU htail
  have hdisj : Disjoint (Set.Ioc T U) (Set.Ioi U) := by
    rw [Set.disjoint_left]
    intro y hywin hytail
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hywin hytail
    exact not_lt_of_ge hywin.2 hytail
  have hwinint : IntegrableOn f (Set.Ioc T U) := hint.integrableOn
  have htailint : IntegrableOn f (Set.Ioi U) := hint.integrableOn
  unfold centeredBSplineArchKernelProfilePositiveTailPart
    centeredBSplineArchKernelProfilePositiveTailWindowPart
  rw [hcover]
  rw [setIntegral_union hdisj measurableSet_Ioi hwinint htailint]

theorem centeredBSplineArchKernelProfileTail_abs_le
    (k : Nat) (ell x T C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (hT : 1 <= T) :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <=
      2 * ((|ell| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2)) := by
  have hT0 : 0 <= T := le_trans zero_le_one hT
  have hint :=
    centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree k ell x hk hell
  have htail_eq :=
    centeredBSplineArchKernelProfileTailPart_eq_two_positiveTailPart
      k ell x T hT0 hint
  have hpos := centeredBSplineArchKernelProfilePositiveTail_abs_le
    k ell x T C0 C1 hk hell hC0 hC1 hgrowth hT
  rw [htail_eq]
  calc
    |2 * centeredBSplineArchKernelProfilePositiveTailPart k ell x T|
        = 2 * |centeredBSplineArchKernelProfilePositiveTailPart k ell x T| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    _ <= 2 * ((|ell| *
        ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
          (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
        (T ^ (-2 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hpos (by norm_num)

/-- Closed-form tail majorant produced by the checked `a_star` linear-growth
tail receiver.  It is independent of the profile center `x`. -/
def centeredBSplineArchKernelProfileTailGrowthBound
    (k : Nat) (ell T C0 C1 : Real) : Real :=
  2 * ((|ell| *
    ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
      (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4)) *
    (T ^ (-2 : ℝ) / 2))

theorem centeredBSplineArchKernelProfile_eq_finitePart_add_tailPart
    (k : Nat) (ell x T : Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t)) :
    centeredBSplineArchKernelProfile k ell x =
      centeredBSplineArchKernelProfileFinitePart k ell x T +
        centeredBSplineArchKernelProfileTailPart k ell x T := by
  rw [centeredBSplineArchKernelProfile_eq_integral_integrand]
  symm
  exact MeasureTheory.integral_add_compl (s := Set.Icc (-T) T) measurableSet_Icc hint

structure centeredBSplineArchKernelProfileFiniteTailIntervalCert
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real) : Prop where
  hFiniteLower :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T
  hFiniteUpper :
    centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper
  hTail :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius
  hLower : lower <= finiteLower - tailRadius
  hUpper : finiteUpper + tailRadius <= upper

structure centeredBSplineArchKernelProfileFiniteTailAnalyticCert
    (k : Nat) (ell x T finiteLower finiteUpper tailRadius : Real) : Prop where
  hFiniteLower :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T
  hFiniteUpper :
    centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper
  hTail :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius

structure centeredBSplineArchKernelProfileTailIntervalCert
    (k : Nat) (ell x T tailLower tailUpper : Real) : Prop where
  hTailLower :
    tailLower <= centeredBSplineArchKernelProfileTailPart k ell x T
  hTailUpper :
    centeredBSplineArchKernelProfileTailPart k ell x T <= tailUpper

structure centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real) :
    Prop where
  hWindowLower :
    windowLower <=
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U
  hWindowUpper :
    centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U <=
      windowUpper
  hRemainder :
    |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
      remainderRadius

theorem centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_comparison_integrals
    (k : Nat) (ell x T U windowLower windowUpper : Real)
    (lowerF upperF : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc T U))
    (hUpperInt : IntegrableOn upperF (Set.Ioc T U))
    (hLower : ∀ t ∈ Set.Ioc T U,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hWindowLower : windowLower <= ∫ t in Set.Ioc T U, lowerF t)
    (hWindowUpper : ∫ t in Set.Ioc T U, upperF t <= windowUpper) :
    windowLower <=
        centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U ∧
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U <=
        windowUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hfintOn : IntegrableOn f (Set.Ioc T U) := hint.integrableOn
  constructor
  · calc
      windowLower <= ∫ t in Set.Ioc T U, lowerF t := hWindowLower
      _ <= ∫ t in Set.Ioc T U, f t := by
            exact setIntegral_mono_on hLowerInt hfintOn measurableSet_Ioc hLower
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U := by
            rfl
  · calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U =
          ∫ t in Set.Ioc T U, f t := by
            rfl
      _ <= ∫ t in Set.Ioc T U, upperF t := by
            exact setIntegral_mono_on hfintOn hUpperInt measurableSet_Ioc hUpper
      _ <= windowUpper := hWindowUpper

theorem centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_two_piece_comparison_integrals
    (k : Nat) (ell x T U c windowLower windowUpper : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Ioc T c))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Ioc T c))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc c U))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc c U))
    (hLowerLeft : ∀ t ∈ Set.Ioc T c,
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : ∀ t ∈ Set.Ioc c U,
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hWindowLower : windowLower <=
      (∫ t in Set.Ioc T c, lowerLeft t) +
        ∫ t in Set.Ioc c U, lowerRight t)
    (hWindowUpper :
      (∫ t in Set.Ioc T c, upperLeft t) +
        ∫ t in Set.Ioc c U, upperRight t <= windowUpper) :
    windowLower <=
        centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U ∧
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U <=
        windowUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Ioc T U = Set.Ioc T c ∪ Set.Ioc c U := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      by_cases hyc : y <= c
      · exact Or.inl ⟨hy.1, hyc⟩
      · exact Or.inr ⟨lt_of_not_ge hyc, hy.2⟩
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      rcases hy with hleftMem | hrightMem
      · exact ⟨hleftMem.1, le_trans hleftMem.2 hRight⟩
      · exact ⟨lt_of_le_of_lt hLeft hrightMem.1, hrightMem.2⟩
  have hdisj : Disjoint (Set.Ioc T c) (Set.Ioc c U) := by
    rw [Set.disjoint_left]
    intro y hyleft hyright
    simp only [Set.mem_Ioc] at hyleft hyright
    exact not_lt_of_ge hyleft.2 hyright.1
  have hfintLeft : IntegrableOn f (Set.Ioc T c) := hint.integrableOn
  have hfintRight : IntegrableOn f (Set.Ioc c U) := hint.integrableOn
  constructor
  · have hLeftBound :
        (∫ t in Set.Ioc T c, lowerLeft t) <=
          ∫ t in Set.Ioc T c, f t := by
      exact setIntegral_mono_on hLowerLeftInt hfintLeft measurableSet_Ioc hLowerLeft
    have hRightBound :
        (∫ t in Set.Ioc c U, lowerRight t) <=
          ∫ t in Set.Ioc c U, f t := by
      exact setIntegral_mono_on hLowerRightInt hfintRight measurableSet_Ioc hLowerRight
    calc
      windowLower <= (∫ t in Set.Ioc T c, lowerLeft t) +
          ∫ t in Set.Ioc c U, lowerRight t := hWindowLower
      _ <= (∫ t in Set.Ioc T c, f t) + ∫ t in Set.Ioc c U, f t := by
            exact add_le_add hLeftBound hRightBound
      _ = ∫ t in Set.Ioc T c ∪ Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U := by
            rw [← hcover]
            rfl
  · have hLeftBound :
        (∫ t in Set.Ioc T c, f t) <=
          ∫ t in Set.Ioc T c, upperLeft t := by
      exact setIntegral_mono_on hfintLeft hUpperLeftInt measurableSet_Ioc hUpperLeft
    have hRightBound :
        (∫ t in Set.Ioc c U, f t) <=
          ∫ t in Set.Ioc c U, upperRight t := by
      exact setIntegral_mono_on hfintRight hUpperRightInt measurableSet_Ioc hUpperRight
    calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x T U =
          ∫ t in Set.Ioc T c ∪ Set.Ioc c U, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Ioc T c, f t) + ∫ t in Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ <= (∫ t in Set.Ioc T c, upperLeft t) +
          ∫ t in Set.Ioc c U, upperRight t := by
            exact add_le_add hLeftBound hRightBound
      _ <= windowUpper := hWindowUpper

structure centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
    (k : Nat) (ell x L U windowLower windowUpper : Real) : Prop where
  hWindowLower :
    windowLower <=
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U
  hWindowUpper :
    centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U <=
      windowUpper

theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
    (k : Nat) (ell x L U windowLower windowUpper : Real)
    (lowerF upperF : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc L U))
    (hUpperInt : IntegrableOn upperF (Set.Ioc L U))
    (hLower : ∀ t ∈ Set.Ioc L U,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc L U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hWindowLower : windowLower <= ∫ t in Set.Ioc L U, lowerF t)
    (hWindowUpper : ∫ t in Set.Ioc L U, upperF t <= windowUpper) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L U windowLower windowUpper := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_comparison_integrals
      k ell x L U windowLower windowUpper lowerF upperF hint hLowerInt
      hUpperInt hLower hUpper hWindowLower hWindowUpper
  exact
    { hWindowLower := hWindow.1
      hWindowUpper := hWindow.2 }

/-- Build a positive-window certificate from constant pointwise bounds on the
window and scalar comparisons against the requested window endpoints. -/
theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds
    (k : Nat) (ell x L U pointLower pointUpper windowLower windowUpper : Real)
    (hLU : L <= U)
    (hLower : ∀ t ∈ Set.Ioc L U,
      pointLower <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc L U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpper)
    (hWindowLower : windowLower <= (U - L) * pointLower)
    (hWindowUpper : (U - L) * pointUpper <= windowUpper) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L U windowLower windowUpper := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_pointwise_bounds
      k ell x L U pointLower pointUpper hLU hLower hUpper
  exact
    { hWindowLower := le_trans hWindowLower hWindow.1
      hWindowUpper := le_trans hWindow.2 hWindowUpper }

theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_glue_adjacent
    (k : Nat) (ell x L U c windowLower windowUpper
      leftLower leftUpper rightLower rightUpper : Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLeft : L <= c) (hRight : c <= U)
    (left :
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x L c leftLower leftUpper)
    (right :
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x c U rightLower rightUpper)
    (hWindowLower : windowLower <= leftLower + rightLower)
    (hWindowUpper : leftUpper + rightUpper <= windowUpper) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L U windowLower windowUpper := by
  let f : Real → Real := centeredBSplineArchKernelProfileIntegrand k ell x
  have hcover :
      Set.Ioc L U = Set.Ioc L c ∪ Set.Ioc c U := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      by_cases hyc : y <= c
      · exact Or.inl ⟨hy.1, hyc⟩
      · exact Or.inr ⟨lt_of_not_ge hyc, hy.2⟩
    · intro hy
      simp only [Set.mem_Ioc, Set.mem_union] at hy ⊢
      rcases hy with hleftMem | hrightMem
      · exact ⟨hleftMem.1, le_trans hleftMem.2 hRight⟩
      · exact ⟨lt_of_le_of_lt hLeft hrightMem.1, hrightMem.2⟩
  have hdisj : Disjoint (Set.Ioc L c) (Set.Ioc c U) := by
    rw [Set.disjoint_left]
    intro y hyleft hyright
    simp only [Set.mem_Ioc] at hyleft hyright
    exact not_lt_of_ge hyleft.2 hyright.1
  have hfintLeft : IntegrableOn f (Set.Ioc L c) := hint.integrableOn
  have hfintRight : IntegrableOn f (Set.Ioc c U) := hint.integrableOn
  have hsum :
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U =
        centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L c +
          centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x c U := by
    calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U =
          ∫ t in Set.Ioc L c ∪ Set.Ioc c U, f t := by
            rw [← hcover]
            rfl
      _ = (∫ t in Set.Ioc L c, f t) + ∫ t in Set.Ioc c U, f t := by
            rw [setIntegral_union hdisj measurableSet_Ioc hfintLeft hfintRight]
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L c +
          centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x c U := by
            rfl
  refine ⟨?_, ?_⟩
  · calc
      windowLower <= leftLower + rightLower := hWindowLower
      _ <= centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L c +
          centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x c U := by
            exact add_le_add left.hWindowLower right.hWindowLower
      _ = centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U := by
            rw [hsum]
  · calc
      centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L U =
          centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x L c +
            centeredBSplineArchKernelProfilePositiveTailWindowPart k ell x c U := hsum
      _ <= leftUpper + rightUpper := by
            exact add_le_add left.hWindowUpper right.hWindowUpper
      _ <= windowUpper := hWindowUpper

/-- Degenerate positive-window certificate on an empty adjacent interval. -/
theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_empty
    (k : Nat) (ell x L : Real) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L L 0 0 := by
  refine ⟨?_, ?_⟩
  · simp [centeredBSplineArchKernelProfilePositiveTailWindowPart]
  · simp [centeredBSplineArchKernelProfilePositiveTailWindowPart]

/-- Fold a finite adjacent chunk family into one positive-window certificate.
This is the structural receiver for generated Step33A `A` window payloads:
the generator supplies chunk certificates plus final lower/upper sum
comparisons, while this theorem handles the interval gluing. -/
theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat → Real)
    (N : Nat)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hstep : 0 <= step)
    (chunkCert : ∀ i < N,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x (L + step * (i : Real)) (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i)) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L (L + step * (N : Real))
      (∑ i ∈ Finset.range N, chunkLower i)
      (∑ i ∈ Finset.range N, chunkUpper i) := by
  induction N with
  | zero =>
      simpa using
        centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_empty
          k ell x L
  | succ N ih =>
      have hprefix :
          centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
            k ell x L (L + step * (N : Real))
            (∑ i ∈ Finset.range N, chunkLower i)
            (∑ i ∈ Finset.range N, chunkUpper i) := by
        exact ih (fun i hi => chunkCert i (Nat.lt_trans hi (Nat.lt_succ_self N)))
      have hlast :
          centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
            k ell x (L + step * (N : Real))
              (L + step * (((N + 1 : Nat) : Real)))
            (chunkLower N) (chunkUpper N) := by
        simpa using chunkCert N (Nat.lt_succ_self N)
      have hLeft : L <= L + step * (N : Real) := by
        have hN : (0 : Real) <= (N : Real) := by exact_mod_cast Nat.zero_le N
        nlinarith [mul_nonneg hstep hN]
      have hRight :
          L + step * (N : Real) <=
            L + step * (((N + 1 : Nat) : Real)) := by
        have hN : (N : Real) <= (((N + 1 : Nat) : Real)) := by
          exact_mod_cast Nat.le_succ N
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (mul_le_mul_of_nonneg_left hN hstep) L
      exact
        centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_glue_adjacent
          k ell x L (L + step * (((N + 1 : Nat) : Real)))
          (L + step * (N : Real))
          (∑ i ∈ Finset.range (N + 1), chunkLower i)
          (∑ i ∈ Finset.range (N + 1), chunkUpper i)
          (∑ i ∈ Finset.range N, chunkLower i)
          (∑ i ∈ Finset.range N, chunkUpper i)
          (chunkLower N) (chunkUpper N)
          hint hLeft hRight hprefix hlast
          (by rw [Finset.sum_range_succ])
          (by rw [Finset.sum_range_succ])

/-- Fold adjacent chunks and compare their endpoint sums to an enclosing target
window. Generated Step33A payloads prove chunk certificates plus these two
scalar comparisons; this receiver handles the interval gluing. -/
theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
    (k : Nat) (ell x L step : Real)
    (chunkLower chunkUpper : Nat → Real)
    (N : Nat) (windowLower windowUpper : Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hstep : 0 <= step)
    (chunkCert : ∀ i < N,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x (L + step * (i : Real)) (L + step * ((i + 1 : Nat) : Real))
        (chunkLower i) (chunkUpper i))
    (hWindowLower : windowLower <= ∑ i ∈ Finset.range N, chunkLower i)
    (hWindowUpper : (∑ i ∈ Finset.range N, chunkUpper i) <= windowUpper) :
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ell x L (L + step * (N : Real)) windowLower windowUpper := by
  have folded :=
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range
      k ell x L step chunkLower chunkUpper N hint hstep chunkCert
  exact
    { hWindowLower := le_trans hWindowLower folded.hWindowLower
      hWindowUpper := le_trans folded.hWindowUpper hWindowUpper }

theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert
    (k : Nat) (ell x T finiteLower finiteUpper positiveLower positiveUpper : Real)
    (hT : 0 <= T)
    (cert :
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x 0 T positiveLower positiveUpper)
    (hFiniteLower : finiteLower <= 2 * positiveLower)
    (hFiniteUpper : 2 * positiveUpper <= finiteUpper) :
    finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T ∧
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  have hfinite_eq :=
    centeredBSplineArchKernelProfileFinitePart_eq_two_positiveFinitePart
      k ell x T hT
  have hposLower :
      positiveLower <= centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
    simpa [centeredBSplineArchKernelProfilePositiveFinitePart,
      centeredBSplineArchKernelProfilePositiveTailWindowPart] using cert.hWindowLower
  have hposUpper :
      centeredBSplineArchKernelProfilePositiveFinitePart k ell x T <= positiveUpper := by
    simpa [centeredBSplineArchKernelProfilePositiveFinitePart,
      centeredBSplineArchKernelProfilePositiveTailWindowPart] using cert.hWindowUpper
  constructor
  · calc
      finiteLower <= 2 * positiveLower := hFiniteLower
      _ <= 2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            exact mul_le_mul_of_nonneg_left hposLower (by norm_num)
      _ = centeredBSplineArchKernelProfileFinitePart k ell x T := by
            rw [hfinite_eq]
  · calc
      centeredBSplineArchKernelProfileFinitePart k ell x T =
          2 * centeredBSplineArchKernelProfilePositiveFinitePart k ell x T := by
            rw [hfinite_eq]
      _ <= 2 * positiveUpper := by
            exact mul_le_mul_of_nonneg_left hposUpper (by norm_num)
      _ <= finiteUpper := hFiniteUpper

theorem centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_window_cert
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real)
    (cert :
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x T U windowLower windowUpper)
    (hRemainder :
      |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
        remainderRadius) :
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius :=
  { hWindowLower := cert.hWindowLower
    hWindowUpper := cert.hWindowUpper
    hRemainder := hRemainder }

theorem centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_comparison_integrals
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real)
    (lowerF upperF : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLowerInt : IntegrableOn lowerF (Set.Ioc T U))
    (hUpperInt : IntegrableOn upperF (Set.Ioc T U))
    (hLower : ∀ t ∈ Set.Ioc T U,
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hWindowLower : windowLower <= ∫ t in Set.Ioc T U, lowerF t)
    (hWindowUpper : ∫ t in Set.Ioc T U, upperF t <= windowUpper)
    (hRemainder :
      |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
        remainderRadius) :
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_comparison_integrals
      k ell x T U windowLower windowUpper lowerF upperF hint hLowerInt
      hUpperInt hLower hUpper hWindowLower hWindowUpper
  exact
    { hWindowLower := hWindow.1
      hWindowUpper := hWindow.2
      hRemainder := hRemainder }

theorem centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_comparison_integrals
    (k : Nat) (ell x T U c windowLower windowUpper remainderRadius : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real → Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Ioc T c))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Ioc T c))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc c U))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc c U))
    (hLowerLeft : ∀ t ∈ Set.Ioc T c,
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : ∀ t ∈ Set.Ioc c U,
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hWindowLower : windowLower <=
      (∫ t in Set.Ioc T c, lowerLeft t) +
        ∫ t in Set.Ioc c U, lowerRight t)
    (hWindowUpper :
      (∫ t in Set.Ioc T c, upperLeft t) +
        ∫ t in Set.Ioc c U, upperRight t <= windowUpper)
    (hRemainder :
      |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
        remainderRadius) :
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_two_piece_comparison_integrals
      k ell x T U c windowLower windowUpper lowerLeft upperLeft lowerRight
      upperRight hint hLeft hRight hLowerLeftInt hUpperLeftInt
      hLowerRightInt hUpperRightInt hLowerLeft hUpperLeft hLowerRight
      hUpperRight hWindowLower hWindowUpper
  exact
    { hWindowLower := hWindow.1
      hWindowUpper := hWindow.2
      hRemainder := hRemainder }

theorem centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_pointwise_bounds
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius
      pointLower pointUpper : Real)
    (hTU : T <= U)
    (hLower : ∀ t ∈ Set.Ioc T U,
      pointLower <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpper)
    (hWindowLower : windowLower <= (U - T) * pointLower)
    (hWindowUpper : (U - T) * pointUpper <= windowUpper)
    (hRemainder :
      |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
        remainderRadius) :
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_pointwise_bounds
      k ell x T U pointLower pointUpper hTU hLower hUpper
  exact
    { hWindowLower := le_trans hWindowLower hWindow.1
      hWindowUpper := le_trans hWindow.2 hWindowUpper
      hRemainder := hRemainder }

theorem centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_pointwise_bounds
    (k : Nat) (ell x T U c windowLower windowUpper remainderRadius
      pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight : Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeft : ∀ t ∈ Set.Ioc T c,
      pointLowerLeft <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpperLeft)
    (hLowerRight : ∀ t ∈ Set.Ioc c U,
      pointLowerRight <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpperRight)
    (hWindowLower :
      windowLower <=
        (c - T) * pointLowerLeft + (U - c) * pointLowerRight)
    (hWindowUpper :
      (c - T) * pointUpperLeft + (U - c) * pointUpperRight <=
        windowUpper)
    (hRemainder :
      |centeredBSplineArchKernelProfilePositiveTailPart k ell x U| <=
        remainderRadius) :
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius := by
  have hWindow :=
    centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_two_piece_pointwise_bounds
      k ell x T U c pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      hLeft hRight hLowerLeft hUpperLeft hLowerRight hUpperRight
  exact
    { hWindowLower := le_trans hWindowLower hWindow.1
      hWindowUpper := le_trans hWindow.2 hWindowUpper
      hRemainder := hRemainder }

theorem centeredBSplineArchKernelProfileTailIntervalCert_of_positiveTailWindowIntervalCert
    (k : Nat) (ell x T U windowLower windowUpper remainderRadius : Real)
    (hT : 0 <= T) (hTU : T <= U)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (cert : centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
      k ell x T U windowLower windowUpper remainderRadius) :
    centeredBSplineArchKernelProfileTailIntervalCert
      k ell x T
      (2 * (windowLower - remainderRadius))
      (2 * (windowUpper + remainderRadius)) := by
  have htail_eq :=
    centeredBSplineArchKernelProfileTailPart_eq_two_positiveTailPart
      k ell x T hT hint
  have hsplit :=
    centeredBSplineArchKernelProfilePositiveTailPart_eq_window_add_positiveTailPart
      k ell x T U hTU hint
  have hrem := abs_le.mp cert.hRemainder
  refine
    { hTailLower := ?_
      hTailUpper := ?_ }
  · rw [htail_eq, hsplit]
    nlinarith [cert.hWindowLower, hrem.1]
  · rw [htail_eq, hsplit]
    nlinarith [cert.hWindowUpper, hrem.2]

theorem centeredBSplineArchKernelProfile_tail_abs_le_of_tailIntervalCert
    (k : Nat) (ell x T tailLower tailUpper tailRadius : Real)
    (cert : centeredBSplineArchKernelProfileTailIntervalCert
      k ell x T tailLower tailUpper)
    (hLower : -tailRadius <= tailLower)
    (hUpper : tailUpper <= tailRadius) :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius := by
  rw [abs_le]
  exact ⟨le_trans hLower cert.hTailLower, le_trans cert.hTailUpper hUpper⟩

structure centeredBSplineArchKernelProfileFiniteTailArithmeticCert
    (lower upper finiteLower finiteUpper tailRadius : Real) : Prop where
  hLower : lower <= finiteLower - tailRadius
  hUpper : finiteUpper + tailRadius <= upper

theorem centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_parts
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (hFiniteLower :
      finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T)
    (hFiniteUpper :
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper)
    (hTail :
      |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius)
    (arith : centeredBSplineArchKernelProfileFiniteTailArithmeticCert
      lower upper finiteLower finiteUpper tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  exact
    { hFiniteLower := hFiniteLower
      hFiniteUpper := hFiniteUpper
      hTail := hTail
      hLower := arith.hLower
      hUpper := arith.hUpper }

theorem centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_analyticAndArithmeticCert
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (analytic : centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T finiteLower finiteUpper tailRadius)
    (arith : centeredBSplineArchKernelProfileFiniteTailArithmeticCert
      lower upper finiteLower finiteUpper tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_parts
      k ell x T lower upper finiteLower finiteUpper tailRadius
      analytic.hFiniteLower analytic.hFiniteUpper analytic.hTail arith

theorem centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailGrowthBound
    (k : Nat) (ell x T finiteLower finiteUpper tailRadius C0 C1 : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (hT : 1 <= T)
    (hFiniteLower :
      finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T)
    (hFiniteUpper :
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper)
    (hTailBound :
      centeredBSplineArchKernelProfileTailGrowthBound k ell T C0 C1 <=
        tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T finiteLower finiteUpper tailRadius := by
  refine
    { hFiniteLower := hFiniteLower
      hFiniteUpper := hFiniteUpper
      hTail := ?_ }
  exact le_trans
    (by
      simpa [centeredBSplineArchKernelProfileTailGrowthBound] using
        centeredBSplineArchKernelProfileTail_abs_le
          k ell x T C0 C1 hk hell hC0 hC1 hgrowth hT)
    hTailBound

theorem centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailIntervalCert
    (k : Nat) (ell x T finiteLower finiteUpper tailLower tailUpper tailRadius : Real)
    (hFiniteLower :
      finiteLower <= centeredBSplineArchKernelProfileFinitePart k ell x T)
    (hFiniteUpper :
      centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper)
    (tail : centeredBSplineArchKernelProfileTailIntervalCert
      k ell x T tailLower tailUpper)
    (hTailLower : -tailRadius <= tailLower)
    (hTailUpper : tailUpper <= tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T finiteLower finiteUpper tailRadius := by
  refine
    { hFiniteLower := hFiniteLower
      hFiniteUpper := hFiniteUpper
      hTail := ?_ }
  exact centeredBSplineArchKernelProfile_tail_abs_le_of_tailIntervalCert
    k ell x T tailLower tailUpper tailRadius tail hTailLower hTailUpper

/-- Widen the finite-window interval inside a finite-tail analytic certificate.

This is the local receiver needed by row-target refresh: generated refined
subchunk sums may produce a wider finite interval, while the tail analytic
bound is unchanged. -/
theorem centeredBSplineArchKernelProfileFiniteTailAnalyticCert_mono
    (k : Nat) (ell x T finiteLower finiteUpper finiteLower' finiteUpper'
      tailRadius : Real)
    (cert : centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T finiteLower finiteUpper tailRadius)
    (hLower : finiteLower' <= finiteLower)
    (hUpper : finiteUpper <= finiteUpper') :
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T finiteLower' finiteUpper' tailRadius := by
  exact
    { hFiniteLower := le_trans hLower cert.hFiniteLower
      hFiniteUpper := le_trans cert.hFiniteUpper hUpper
      hTail := cert.hTail }

structure centeredBSplineArchKernelProfilePointwiseFiniteTailIntervalCert
    (k : Nat) (ell x T lower upper pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real) : Prop where
  hT : 0 <= T
  hPointLower : ∀ t ∈ Set.Icc (-T) T,
    pointLower <= centeredBSplineArchKernelProfileIntegrand k ell x t
  hPointUpper : ∀ t ∈ Set.Icc (-T) T,
    centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpper
  hTail :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius
  hFiniteLower : finiteLower <= (2 * T) * pointLower
  hFiniteUpper : (2 * T) * pointUpper <= finiteUpper
  hLower : lower <= finiteLower - tailRadius
  hUpper : finiteUpper + tailRadius <= upper

structure centeredBSplineArchKernelProfileTwoPiecePointwiseFiniteTailIntervalCert
    (k : Nat) (ell x T c lower upper
      pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : Real) : Prop where
  hLeft : -T <= c
  hRight : c <= T
  hPointLowerLeft : ∀ t ∈ Set.Icc (-T) c,
    pointLowerLeft <= centeredBSplineArchKernelProfileIntegrand k ell x t
  hPointUpperLeft : ∀ t ∈ Set.Icc (-T) c,
    centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpperLeft
  hPointLowerRight : ∀ t ∈ Set.Ioc c T,
    pointLowerRight <= centeredBSplineArchKernelProfileIntegrand k ell x t
  hPointUpperRight : ∀ t ∈ Set.Ioc c T,
    centeredBSplineArchKernelProfileIntegrand k ell x t <= pointUpperRight
  hTail :
    |centeredBSplineArchKernelProfileTailPart k ell x T| <= tailRadius
  hFiniteLower :
    finiteLower <= (c + T) * pointLowerLeft + (T - c) * pointLowerRight
  hFiniteUpper :
    (c + T) * pointUpperLeft + (T - c) * pointUpperRight <= finiteUpper
  hLower : lower <= finiteLower - tailRadius
  hUpper : finiteUpper + tailRadius <= upper

theorem centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
    (k : Nat) (ell x T lower upper pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real)
    (cert : centeredBSplineArchKernelProfilePointwiseFiniteTailIntervalCert
      k ell x T lower upper pointLower pointUpper finiteLower finiteUpper tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  have hFinite :=
    centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
      k ell x T pointLower pointUpper cert.hT cert.hPointLower cert.hPointUpper
  exact
    { hFiniteLower := by linarith [cert.hFiniteLower, hFinite.1]
      hFiniteUpper := by linarith [cert.hFiniteUpper, hFinite.2]
      hTail := cert.hTail
      hLower := cert.hLower
      hUpper := cert.hUpper }

theorem centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
    (k : Nat) (ell x T c lower upper
      pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : Real)
    (cert : centeredBSplineArchKernelProfileTwoPiecePointwiseFiniteTailIntervalCert
      k ell x T c lower upper pointLowerLeft pointUpperLeft pointLowerRight
      pointUpperRight finiteLower finiteUpper tailRadius) :
    centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius := by
  have hFinite :=
    centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
      k ell x T c pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      cert.hLeft cert.hRight cert.hPointLowerLeft cert.hPointUpperLeft
      cert.hPointLowerRight cert.hPointUpperRight
  exact
    { hFiniteLower := by linarith [cert.hFiniteLower, hFinite.1]
      hFiniteUpper := by linarith [cert.hFiniteUpper, hFinite.2]
      hTail := cert.hTail
      hLower := cert.hLower
      hUpper := cert.hUpper }

theorem centeredBSplineArchKernelProfile_bounds_of_finiteTailIntervalCert
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (hint : Integrable (fun t : Real =>
      centeredBSplineArchKernelProfileIntegrand k ell x t))
    (cert : centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius) :
    lower <= centeredBSplineArchKernelProfile k ell x ∧
      centeredBSplineArchKernelProfile k ell x <= upper := by
  constructor
  · rw [centeredBSplineArchKernelProfile_eq_finitePart_add_tailPart k ell x T hint]
    have hTailLower :
        -tailRadius <= centeredBSplineArchKernelProfileTailPart k ell x T :=
      (abs_le.mp cert.hTail).1
    linarith [cert.hLower, cert.hFiniteLower, hTailLower]
  · rw [centeredBSplineArchKernelProfile_eq_finitePart_add_tailPart k ell x T hint]
    have hTailUpper :
        centeredBSplineArchKernelProfileTailPart k ell x T <= tailRadius :=
      (abs_le.mp cert.hTail).2
    linarith [cert.hUpper, cert.hFiniteUpper, hTailUpper]

theorem centeredBSplineArchKernelProfile_bounds_of_finiteTailIntervalCert_of_pos_degree
    (k : Nat) (ell x T lower upper finiteLower finiteUpper tailRadius : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (cert : centeredBSplineArchKernelProfileFiniteTailIntervalCert
      k ell x T lower upper finiteLower finiteUpper tailRadius) :
    lower <= centeredBSplineArchKernelProfile k ell x ∧
      centeredBSplineArchKernelProfile k ell x <= upper := by
  exact centeredBSplineArchKernelProfile_bounds_of_finiteTailIntervalCert
    k ell x T lower upper finiteLower finiteUpper tailRadius
    (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
      k ell x hk hell)
    cert

theorem abs_sub_le_of_recenter
    {x c C r R : Real}
    (hx : |x - c| <= r)
    (hR : r + |c - C| <= R) :
    |x - C| <= R := by
  have h : x - C = (x - c) + (c - C) := by ring
  rw [h]
  exact le_trans (abs_add_le _ _)
    (le_trans (add_le_add hx le_rfl) hR)

theorem centeredBSplineArchKernelProfile_abs_sub_mid_le_of_finiteTailAnalyticCert_of_pos_degree
    (k : Nat) (ell x T finiteMid finiteRadius tailRadius : Real)
    (hk : 0 < k) (hell : 0 < ell)
    (cert : centeredBSplineArchKernelProfileFiniteTailAnalyticCert
      k ell x T (finiteMid - finiteRadius) (finiteMid + finiteRadius)
      tailRadius) :
    |centeredBSplineArchKernelProfile k ell x - finiteMid| <=
      finiteRadius + tailRadius := by
  have hint :=
    centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
      k ell x hk hell
  rw [centeredBSplineArchKernelProfile_eq_finitePart_add_tailPart
    k ell x T hint]
  have hFinite :
      |centeredBSplineArchKernelProfileFinitePart k ell x T - finiteMid| <=
        finiteRadius := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [cert.hFiniteLower, cert.hFiniteUpper]
  have hdecomp :
      centeredBSplineArchKernelProfileFinitePart k ell x T +
          centeredBSplineArchKernelProfileTailPart k ell x T - finiteMid =
        (centeredBSplineArchKernelProfileFinitePart k ell x T - finiteMid) +
          centeredBSplineArchKernelProfileTailPart k ell x T := by
    ring
  rw [hdecomp]
  exact le_trans (abs_add_le _ _) (add_le_add hFinite cert.hTail)

abbrev primaryK11AnalyticAFiniteTailIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailIntervalCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

abbrev primaryK11AnalyticAFiniteTailAnalyticIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailAnalyticCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    finiteLower finiteUpper tailRadius

abbrev primaryK11AnalyticATailIntervalCert
    (n : CoeffIndex23) (T tailLower tailUpper : Real) : Prop :=
  centeredBSplineArchKernelProfileTailIntervalCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    tailLower tailUpper

abbrev primaryK11AnalyticAPositiveTailWindowIntervalCert
    (n : CoeffIndex23) (T U windowLower windowUpper remainderRadius : Real) :
    Prop :=
  centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
    windowLower windowUpper remainderRadius

abbrev primaryK11AnalyticAFiniteTailArithmeticIntervalCert
    (n : CoeffIndex23) (finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailArithmeticCert
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

abbrev primaryK11AnalyticAPointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfilePointwiseFiniteTailIntervalCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
    pointLower pointUpper finiteLower finiteUpper tailRadius

abbrev primaryK11AnalyticATwoPiecePointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T c pointLowerLeft pointUpperLeft
      pointLowerRight pointUpperRight finiteLower finiteUpper tailRadius : Real) :
    Prop :=
  centeredBSplineArchKernelProfileTwoPiecePointwiseFiniteTailIntervalCert
    11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T c
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
    pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    finiteLower finiteUpper tailRadius

theorem primaryK11AnalyticAFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real)
    (cert : primaryK11AnalyticAPointwiseFiniteTailIntervalCert
      n T pointLower pointUpper finiteLower finiteUpper tailRadius) :
    primaryK11AnalyticAFiniteTailIntervalCert
      n T finiteLower finiteUpper tailRadius := by
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
      pointLower pointUpper finiteLower finiteUpper tailRadius cert

theorem primaryK11AnalyticAFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T c pointLowerLeft pointUpperLeft
      pointLowerRight pointUpperRight finiteLower finiteUpper tailRadius : Real)
    (cert : primaryK11AnalyticATwoPiecePointwiseFiniteTailIntervalCert
      n T c pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius) :
    primaryK11AnalyticAFiniteTailIntervalCert
      n T finiteLower finiteUpper tailRadius := by
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T c
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
      pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius cert

structure primaryK11AnalyticAFiniteTailBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticAFiniteTailIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

structure primaryK11AnalyticAFiniteTailAnalyticBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticAFiniteTailAnalyticIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

/-- Widen primary k=11 finite-tail analytic bounds pointwise without changing
the tail radius. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_mono
    {T : Real}
    {finiteLower finiteUpper finiteLower' finiteUpper' tailRadius :
      CoeffIndex23 → Real}
    (cert : primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (hLower : ∀ n : CoeffIndex23, finiteLower' n <= finiteLower n)
    (hUpper : ∀ n : CoeffIndex23, finiteUpper n <= finiteUpper' n) :
    primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower' finiteUpper' tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_mono
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (finiteLower' n) (finiteUpper' n)
      (tailRadius n) (cert.h n) (hLower n) (hUpper n)

structure primaryK11AnalyticAFinitePartBoundsCert
    (T : Real) (finiteLower finiteUpper : CoeffIndex23 → Real) : Prop where
  hFiniteLower : ∀ n : CoeffIndex23,
    finiteLower n <=
      centeredBSplineArchKernelProfileFinitePart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
  hFiniteUpper : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfileFinitePart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T <=
      finiteUpper n

/-- Widen primary k=11 finite-window bounds pointwise. -/
theorem primaryK11AnalyticAFinitePartBoundsCert_mono
    {T : Real}
    {finiteLower finiteUpper finiteLower' finiteUpper' : CoeffIndex23 → Real}
    (cert : primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper)
    (hLower : ∀ n : CoeffIndex23, finiteLower' n <= finiteLower n)
    (hUpper : ∀ n : CoeffIndex23, finiteUpper n <= finiteUpper' n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower' finiteUpper' := by
  exact
    { hFiniteLower := fun n => le_trans (hLower n) (cert.hFiniteLower n)
      hFiniteUpper := fun n => le_trans (cert.hFiniteUpper n) (hUpper n) }

theorem primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Icc (-T) T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Icc (-T) T))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ t in Set.Icc (-T) T, lowerF n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-T) T, upperF n t <= finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem primaryK11AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Ioc 0 T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Ioc 0 T))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 T,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * ∫ t in Set.Ioc 0 T, lowerF n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * ∫ t in Set.Ioc 0 T, upperF n t <= finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        hT (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        hT (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem primaryK11AnalyticAFinitePartBoundsCert_of_positiveTwoPieceComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (cut : CoeffIndex23 → Real)
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : ∀ n : CoeffIndex23, 0 <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Ioc 0 (cut n)))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Ioc 0 (cut n)))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc (cut n) T))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc (cut n) T))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 (cut n),
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 (cut n),
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * ((∫ t in Set.Ioc 0 (cut n), lowerLeft n t) +
        ∫ t in Set.Ioc (cut n) T, lowerRight n t))
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * ((∫ t in Set.Ioc 0 (cut n), upperLeft n t) +
        ∫ t in Set.Ioc (cut n) T, upperRight n t) <= finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (finiteLower n) (finiteUpper n) (lowerLeft n) (upperLeft n)
        (lowerRight n) (upperRight n) hT (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n) (hLowerRightInt n)
        (hUpperRightInt n) (fun t ht => hLowerLeft n t ht)
        (fun t ht => hUpperLeft n t ht) (fun t ht => hLowerRight n t ht)
        (fun t ht => hUpperRight n t ht) (hFiniteLower n)
        (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (finiteLower n) (finiteUpper n) (lowerLeft n) (upperLeft n)
        (lowerRight n) (upperRight n) hT (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n) (hLowerRightInt n)
        (hUpperRightInt n) (fun t ht => hLowerLeft n t ht)
        (fun t ht => hUpperLeft n t ht) (fun t ht => hLowerRight n t ht)
        (fun t ht => hUpperRight n t ht) (hFiniteLower n)
        (hFiniteUpper n)).2

theorem primaryK11AnalyticAFinitePartBoundsCert_of_positiveWindowCert
    {T : Real} {finiteLower finiteUpper positiveLower positiveUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (window : ∀ n : CoeffIndex23,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 T (positiveLower n) (positiveUpper n))
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * positiveLower n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * positiveUpper n <= finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (positiveLower n) (positiveUpper n)
        hT (window n) (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (positiveLower n) (positiveUpper n)
        hT (window n) (hFiniteLower n) (hFiniteUpper n)).2

theorem primaryK11AnalyticAFinitePartBoundsCert_of_twoPieceComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (cut : CoeffIndex23 → Real)
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : ∀ n : CoeffIndex23, -T <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Icc (-T) (cut n)))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Icc (-T) (cut n)))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc (cut n) T))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc (cut n) T))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <=
        (∫ t in Set.Icc (-T) (cut n), lowerLeft n t) +
          ∫ t in Set.Ioc (cut n) T, lowerRight n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (∫ t in Set.Icc (-T) (cut n), upperLeft n t) +
          ∫ t in Set.Ioc (cut n) T, upperRight n t <=
        finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T (cut n)
        (finiteLower n) (finiteUpper n)
        (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
        (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n)
        (hLowerRightInt n) (hUpperRightInt n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T (cut n)
        (finiteLower n) (finiteUpper n)
        (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
        (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n)
        (hLowerRightInt n) (hUpperRightInt n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem primaryK11AnalyticAFinitePartBoundsCert_of_pointwiseBounds
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (pointLower pointUpper : CoeffIndex23 → Real)
    (hT : 0 <= T)
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      pointLower n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpper n)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= (2 * T) * pointLower n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (2 * T) * pointUpper n <= finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact le_trans (hFiniteLower n)
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (pointLower n) (pointUpper n) hT
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)).1
  · intro n
    exact le_trans
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (pointLower n) (pointUpper n) hT
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)).2
      (hFiniteUpper n)

theorem primaryK11AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hLeft : ∀ n : CoeffIndex23, -T <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      pointLowerLeft n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      pointLowerRight n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperRight n)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <=
        (cut n + T) * pointLowerLeft n + (T - cut n) * pointLowerRight n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (cut n + T) * pointUpperLeft n + (T - cut n) * pointUpperRight n <=
        finiteUpper n) :
    primaryK11AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact le_trans (hFiniteLower n)
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (pointLowerLeft n) (pointUpperLeft n)
        (pointLowerRight n) (pointUpperRight n)
        (hLeft n) (hRight n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)).1
  · intro n
    exact le_trans
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (pointLowerLeft n) (pointUpperLeft n)
        (pointLowerRight n) (pointUpperRight n)
        (hLeft n) (hRight n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)).2
      (hFiniteUpper n)

structure primaryK11AnalyticATailGrowthBoundsCert
    (T C0 C1 : Real) (tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfileTailGrowthBound
      11 ((3 : Real) / (10 : Real)) T C0 C1 <= tailRadius n

structure primaryK11AnalyticATailIntervalBoundsCert
    (T : Real) (tailLower tailUpper tailRadius : CoeffIndex23 → Real) : Prop where
  hTail : ∀ n : CoeffIndex23,
    primaryK11AnalyticATailIntervalCert n T (tailLower n) (tailUpper n)
  hLower : ∀ n : CoeffIndex23, -tailRadius n <= tailLower n
  hUpper : ∀ n : CoeffIndex23, tailUpper n <= tailRadius n

structure primaryK11AnalyticAPositiveTailWindowBoundsCert
    (T U : Real)
    (windowLower windowUpper remainderRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticAPositiveTailWindowIntervalCert
      n T U (windowLower n) (windowUpper n) (remainderRadius n)

structure primaryK11AnalyticAPositiveTailRemainderBoundsCert
    (U : Real) (remainderRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineArchKernelProfilePositiveTailPart
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
        remainderRadius n

theorem primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_integralMajorants
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (majorant : CoeffIndex23 → Real → Real)
    (hMajorantInt : ∀ n : CoeffIndex23,
      Integrable (majorant n) (volume.restrict (Set.Ioi U)))
    (hMajorant : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioi U,
      |centeredBSplineArchKernelProfileIntegrand
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t| <=
          majorant n t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U, majorant n t <= remainderRadius n) :
    primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTail_abs_le_of_integral_majorant
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U
      (remainderRadius n) (majorant n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hMajorantInt n) (fun t ht => hMajorant n t ht) (hIntegral n)

theorem primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_aStarTransformIntegralMajorants
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (omegaMajorant : Real → Real)
    (transformSqMajorant : CoeffIndex23 → Real → Real)
    (hMajorantInt : ∀ n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            omegaMajorant t * transformSqMajorant n t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaMajorant t)
    (hTransform : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioi U,
      |centeredBSplineImagTransformRealClosedForm
        11 ((3 : Real) / (10 : Real)) t| ^ 2 <=
          transformSqMajorant n t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| *
          omegaMajorant t * transformSqMajorant n t <=
        remainderRadius n) :
    primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTail_abs_le_of_aStar_transform_integral_majorants
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U
      (remainderRadius n) omegaMajorant (transformSqMajorant n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hMajorantInt n) hOmega (fun t ht => hTransform n t ht)
      (hIntegral n)

theorem primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_aStarFullTransformTailMajorant
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (omegaMajorant : Real → Real)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| * omegaMajorant t *
            centeredBSplineImagTransformSqTailMajorant
              11 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaMajorant t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| * omegaMajorant t *
          centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t <=
        remainderRadius n) :
    primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine
    primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_aStarTransformIntegralMajorants
      omegaMajorant
      (fun _n t =>
        centeredBSplineImagTransformSqTailMajorant
          11 ((3 : Real) / (10 : Real)) t)
      ?_ hOmega ?_ hIntegral
  · intro n
    exact hMajorantInt n
  · intro _n t ht
    exact
      centeredBSplineImagTransformRealClosedForm_sq_abs_le_full_tail
        11 ((3 : Real) / (10 : Real)) t
        (by norm_num) (lt_of_le_of_lt hU0 ht)

theorem primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
    {U omegaFactor : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            (omegaFactor * Real.log (3 * t)) *
            centeredBSplineImagTransformSqTailMajorant
              11 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U,
      |Q3.a_star t| <= omegaFactor * Real.log (3 * t))
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| *
          (omegaFactor * Real.log (3 * t)) *
          centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t <=
        remainderRadius n) :
    primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  exact
    primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_aStarFullTransformTailMajorant
      hU0 (fun t : Real => omegaFactor * Real.log (3 * t))
      hMajorantInt hOmega hIntegral

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23, IntegrableOn (lowerF n) (Set.Ioc T U))
    (hUpperInt : ∀ n : CoeffIndex23, IntegrableOn (upperF n) (Set.Ioc T U))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= ∫ t in Set.Ioc T U, lowerF n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc T U, upperF n t <= windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_comparison_integrals
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (lowerF n) (upperF n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hLowerInt n) (hUpperInt n)
      (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (window : ∀ n : CoeffIndex23,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        T U (windowLower n) (windowUpper n))
    (remainder :
      primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_window_cert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (window n) (remainder.h n)

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPieceComparisonIntegrals
    {T U c : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Ioc T c))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Ioc T c))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc c U))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc c U))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <=
        (∫ t in Set.Ioc T c, lowerLeft n t) +
          ∫ t in Set.Ioc c U, lowerRight n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (∫ t in Set.Ioc T c, upperLeft n t) +
          ∫ t in Set.Ioc c U, upperRight n t <=
        windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_comparison_integrals
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U c
      (windowLower n) (windowUpper n) (remainderRadius n)
      (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      hLeft hRight
      (hLowerLeftInt n) (hUpperLeftInt n)
      (hLowerRightInt n) (hUpperRightInt n)
      (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
      (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegralsAndRemainderCert
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23, IntegrableOn (lowerF n) (Set.Ioc T U))
    (hUpperInt : ∀ n : CoeffIndex23, IntegrableOn (upperF n) (Set.Ioc T U))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= ∫ t in Set.Ioc T U, lowerF n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc T U, upperF n t <= windowUpper n)
    (remainder :
      primaryK11AnalyticAPositiveTailRemainderBoundsCert U remainderRadius) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  exact
    primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
      lowerF upperF hLowerInt hUpperInt hLower hUpper hWindowLower hWindowUpper
      remainder.h

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (pointLower pointUpper : CoeffIndex23 → Real)
    (hTU : T <= U)
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      pointLower n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpper n)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= (U - T) * pointLower n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (U - T) * pointUpper n <= windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_pointwise_bounds
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (pointLower n) (pointUpper n) hTU
      (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseBounds
    {T U c : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      pointLowerLeft n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      pointLowerRight n <=
        centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <=
        (c - T) * pointLowerLeft n + (U - c) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (c - T) * pointUpperLeft n + (U - c) * pointUpperRight n <=
        windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_pointwise_bounds
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U c
      (windowLower n) (windowUpper n) (remainderRadius n)
      (pointLowerLeft n) (pointUpperLeft n)
      (pointLowerRight n) (pointUpperRight n)
      hLeft hRight
      (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
      (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem primaryK11AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
    {T U : Real}
    {windowLower windowUpper remainderRadius tailLower tailUpper tailRadius :
      CoeffIndex23 → Real}
    (hT : 0 <= T) (hTU : T <= U)
    (window : primaryK11AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius)
    (hTailLower :
      ∀ n : CoeffIndex23, tailLower n <= 2 * (windowLower n - remainderRadius n))
    (hTailUpper :
      ∀ n : CoeffIndex23, 2 * (windowUpper n + remainderRadius n) <= tailUpper n)
    (hLower : ∀ n : CoeffIndex23, -tailRadius n <= tailLower n)
    (hUpper : ∀ n : CoeffIndex23, tailUpper n <= tailRadius n) :
    primaryK11AnalyticATailIntervalBoundsCert T tailLower tailUpper tailRadius := by
  refine ⟨?_, hLower, hUpper⟩
  intro n
  have hTail :=
    centeredBSplineArchKernelProfileTailIntervalCert_of_positiveTailWindowIntervalCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      hT hTU
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (window.h n)
  exact
    { hTailLower := le_trans (hTailLower n) hTail.hTailLower
      hTailUpper := le_trans hTail.hTailUpper (hTailUpper n) }

structure primaryK11AnalyticAFiniteTailArithmeticBoundsCert
    (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticAFiniteTailArithmeticIntervalCert
      n (finiteLower n) (finiteUpper n) (tailRadius n)

theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailGrowthBounds
    {T C0 C1 : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (hT : 1 <= T)
    (finite : primaryK11AnalyticAFinitePartBoundsCert
      T finiteLower finiteUpper)
    (tail : primaryK11AnalyticATailGrowthBoundsCert
      T C0 C1 tailRadius) :
    primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailGrowthBound
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (tailRadius n) C0 C1
      (by norm_num) (by norm_num) hC0 hC1 hgrowth hT
      (finite.hFiniteLower n) (finite.hFiniteUpper n) (tail.h n)

theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
    {T : Real}
    {finiteLower finiteUpper tailLower tailUpper tailRadius : CoeffIndex23 → Real}
    (finite : primaryK11AnalyticAFinitePartBoundsCert
      T finiteLower finiteUpper)
    (tail : primaryK11AnalyticATailIntervalBoundsCert
      T tailLower tailUpper tailRadius) :
    primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailIntervalCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (tailLower n) (tailUpper n) (tailRadius n)
      (finite.hFiniteLower n) (finite.hFiniteUpper n)
      (tail.hTail n) (tail.hLower n) (tail.hUpper n)

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_analyticAndArithmeticBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (analytic : primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (arith : primaryK11AnalyticAFiniteTailArithmeticBoundsCert
      finiteLower finiteUpper tailRadius) :
    primaryK11AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_analyticAndArithmeticCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (analytic.h n) (arith.h n)

structure primaryK11AnalyticAPointwiseFiniteTailBoundsCert
    (T : Real) (pointLower pointUpper finiteLower finiteUpper tailRadius :
      CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticAPointwiseFiniteTailIntervalCert
      n T (pointLower n) (pointUpper n) (finiteLower n) (finiteUpper n)
      (tailRadius n)

structure primaryK11AnalyticATwoPiecePointwiseFiniteTailBoundsCert
    (T : Real) (cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    primaryK11AnalyticATwoPiecePointwiseFiniteTailIntervalCert
      n T (cut n) (pointLowerLeft n) (pointUpperLeft n)
      (pointLowerRight n) (pointUpperRight n) (finiteLower n)
      (finiteUpper n) (tailRadius n)

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
    {T : Real}
    {pointLower pointUpper finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : primaryK11AnalyticAPointwiseFiniteTailBoundsCert
      T pointLower pointUpper finiteLower finiteUpper tailRadius) :
    primaryK11AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact primaryK11AnalyticAFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
    n T (pointLower n) (pointUpper n) (finiteLower n) (finiteUpper n)
    (tailRadius n) (cert.h n)

theorem primaryK11AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
    {T : Real}
    {cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : primaryK11AnalyticATwoPiecePointwiseFiniteTailBoundsCert
      T cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius) :
    primaryK11AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact primaryK11AnalyticAFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
    n T (cut n) (pointLowerLeft n) (pointUpperLeft n) (pointLowerRight n)
    (pointUpperRight n) (finiteLower n) (finiteUpper n) (tailRadius n)
    (cert.h n)

theorem primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : primaryK11AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius) :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert := by
  have hBounds : ∀ n : CoeffIndex23,
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n <=
        centeredBSplineArchKernelProfile
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) ∧
      centeredBSplineArchKernelProfile
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) <=
        CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n := by
    intro n
    exact centeredBSplineArchKernelProfile_bounds_of_finiteTailIntervalCert_of_pos_degree
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (by norm_num) (by norm_num) (cert.h n)
  constructor <;>
    first
    | simpa using (hBounds (⟨0, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨0, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨1, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨1, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨2, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨2, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨3, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨3, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨4, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨4, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨5, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨5, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨6, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨6, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨7, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨7, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨8, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨8, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨9, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨9, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨10, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨10, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨11, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨11, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨12, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨12, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨13, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨13, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨14, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨14, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨15, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨15, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨16, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨16, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨17, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨17, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨18, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨18, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨19, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨19, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨20, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨20, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨21, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨21, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨22, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨22, by norm_num⟩ : CoeffIndex23)).2

theorem primaryK11AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
    {T : Real} {finiteMid finiteRadius tailRadius : CoeffIndex23 → Real}
    (analytic : primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T (fun n => finiteMid n - finiteRadius n)
        (fun n => finiteMid n + finiteRadius n) tailRadius)
    (hContain : ∀ n : CoeffIndex23,
      finiteRadius n + tailRadius n +
          |finiteMid n -
            (CenteredCoeffPayloadImport.primaryK11AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)) :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  have hx :=
    centeredBSplineArchKernelProfile_abs_sub_mid_le_of_finiteTailAnalyticCert_of_pos_degree
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteMid n) (finiteRadius n) (tailRadius n)
      (by norm_num) (by norm_num) (analytic.h n)
  exact abs_sub_le_of_recenter hx (hContain n)

/-- Recenter primary k=11 A hboxes from arbitrary finite-tail interval bounds.

This is the row-refresh receiver: generated refined row sums may define
`finiteLower`/`finiteUpper` directly, and the midpoint/radius used by local
recenter containment is recovered from that interval. -/
theorem primaryK11AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticIntervalRecenter
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (analytic : primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (hContain : ∀ n : CoeffIndex23,
      ((finiteUpper n - finiteLower n) / 2) + tailRadius n +
          |((finiteLower n + finiteUpper n) / 2) -
            (CenteredCoeffPayloadImport.primaryK11AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.primaryK11ARadiusAbsDistanceEntryRat n.1 : Real)) :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert := by
  let finiteMid : CoeffIndex23 → Real :=
    fun n => (finiteLower n + finiteUpper n) / 2
  let finiteRadius : CoeffIndex23 → Real :=
    fun n => (finiteUpper n - finiteLower n) / 2
  refine
    primaryK11AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
      (T := T) (finiteMid := finiteMid) (finiteRadius := finiteRadius)
      (tailRadius := tailRadius) ?_ ?_
  · refine ⟨?_⟩
    intro n
    have hLower :
        finiteMid n - finiteRadius n = finiteLower n := by
      simp [finiteMid, finiteRadius]
      ring
    have hUpper :
        finiteMid n + finiteRadius n = finiteUpper n := by
      simp [finiteMid, finiteRadius]
      ring
    simpa [hLower, hUpper] using analytic.h n
  · intro n
    simpa [finiteMid, finiteRadius] using hContain n

abbrev controlK9AnalyticAFiniteTailIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailIntervalCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

abbrev controlK9AnalyticAFiniteTailAnalyticIntervalCert
    (n : CoeffIndex23) (T finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailAnalyticCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    finiteLower finiteUpper tailRadius

abbrev controlK9AnalyticATailIntervalCert
    (n : CoeffIndex23) (T tailLower tailUpper : Real) : Prop :=
  centeredBSplineArchKernelProfileTailIntervalCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    tailLower tailUpper

abbrev controlK9AnalyticAPositiveTailWindowIntervalCert
    (n : CoeffIndex23) (T U windowLower windowUpper remainderRadius : Real) :
    Prop :=
  centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
    windowLower windowUpper remainderRadius

abbrev controlK9AnalyticAFiniteTailArithmeticIntervalCert
    (n : CoeffIndex23) (finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfileFiniteTailArithmeticCert
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
    finiteLower finiteUpper tailRadius

abbrev controlK9AnalyticAPointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real) : Prop :=
  centeredBSplineArchKernelProfilePointwiseFiniteTailIntervalCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
    pointLower pointUpper finiteLower finiteUpper tailRadius

abbrev controlK9AnalyticATwoPiecePointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T c pointLowerLeft pointUpperLeft
      pointLowerRight pointUpperRight finiteLower finiteUpper tailRadius : Real) :
    Prop :=
  centeredBSplineArchKernelProfileTwoPiecePointwiseFiniteTailIntervalCert
    9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T c
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
    (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
    pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    finiteLower finiteUpper tailRadius

theorem controlK9AnalyticAFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T pointLower pointUpper
      finiteLower finiteUpper tailRadius : Real)
    (cert : controlK9AnalyticAPointwiseFiniteTailIntervalCert
      n T pointLower pointUpper finiteLower finiteUpper tailRadius) :
    controlK9AnalyticAFiniteTailIntervalCert
      n T finiteLower finiteUpper tailRadius := by
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
      pointLower pointUpper finiteLower finiteUpper tailRadius cert

theorem controlK9AnalyticAFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
    (n : CoeffIndex23) (T c pointLowerLeft pointUpperLeft
      pointLowerRight pointUpperRight finiteLower finiteUpper tailRadius : Real)
    (cert : controlK9AnalyticATwoPiecePointwiseFiniteTailIntervalCert
      n T c pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius) :
    controlK9AnalyticAFiniteTailIntervalCert
      n T finiteLower finiteUpper tailRadius := by
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T c
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
      pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius cert

structure controlK9AnalyticAFiniteTailBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticAFiniteTailIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

structure controlK9AnalyticAFiniteTailAnalyticBoundsCert
    (T : Real) (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticAFiniteTailAnalyticIntervalCert
      n T (finiteLower n) (finiteUpper n) (tailRadius n)

/-- Widen control k=9 finite-tail analytic bounds pointwise without changing
the tail radius. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_mono
    {T : Real}
    {finiteLower finiteUpper finiteLower' finiteUpper' tailRadius :
      CoeffIndex23 → Real}
    (cert : controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (hLower : ∀ n : CoeffIndex23, finiteLower' n <= finiteLower n)
    (hUpper : ∀ n : CoeffIndex23, finiteUpper n <= finiteUpper' n) :
    controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower' finiteUpper' tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_mono
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (finiteLower' n) (finiteUpper' n)
      (tailRadius n) (cert.h n) (hLower n) (hUpper n)

structure controlK9AnalyticAFinitePartBoundsCert
    (T : Real) (finiteLower finiteUpper : CoeffIndex23 → Real) : Prop where
  hFiniteLower : ∀ n : CoeffIndex23,
    finiteLower n <=
      centeredBSplineArchKernelProfileFinitePart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
  hFiniteUpper : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfileFinitePart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T <=
      finiteUpper n

/-- Widen control k=9 finite-window bounds pointwise. -/
theorem controlK9AnalyticAFinitePartBoundsCert_mono
    {T : Real}
    {finiteLower finiteUpper finiteLower' finiteUpper' : CoeffIndex23 → Real}
    (cert : controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper)
    (hLower : ∀ n : CoeffIndex23, finiteLower' n <= finiteLower n)
    (hUpper : ∀ n : CoeffIndex23, finiteUpper n <= finiteUpper' n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower' finiteUpper' := by
  exact
    { hFiniteLower := fun n => le_trans (hLower n) (cert.hFiniteLower n)
      hFiniteUpper := fun n => le_trans (cert.hFiniteUpper n) (hUpper n) }

theorem controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Icc (-T) T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Icc (-T) T))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= ∫ t in Set.Icc (-T) T, lowerF n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-T) T, upperF n t <= finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem controlK9AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerF n) (Set.Ioc 0 T))
    (hUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperF n) (Set.Ioc 0 T))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 T,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * ∫ t in Set.Ioc 0 T, lowerF n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * ∫ t in Set.Ioc 0 T, upperF n t <= finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        hT (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (lowerF n) (upperF n)
        hT (hLowerInt n) (hUpperInt n)
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem controlK9AnalyticAFinitePartBoundsCert_of_positiveTwoPieceComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (cut : CoeffIndex23 → Real)
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : ∀ n : CoeffIndex23, 0 <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Ioc 0 (cut n)))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Ioc 0 (cut n)))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc (cut n) T))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc (cut n) T))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 (cut n),
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc 0 (cut n),
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * ((∫ t in Set.Ioc 0 (cut n), lowerLeft n t) +
        ∫ t in Set.Ioc (cut n) T, lowerRight n t))
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * ((∫ t in Set.Ioc 0 (cut n), upperLeft n t) +
        ∫ t in Set.Ioc (cut n) T, upperRight n t) <= finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (finiteLower n) (finiteUpper n) (lowerLeft n) (upperLeft n)
        (lowerRight n) (upperRight n) hT (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n) (hLowerRightInt n)
        (hUpperRightInt n) (fun t ht => hLowerLeft n t ht)
        (fun t ht => hUpperLeft n t ht) (fun t ht => hLowerRight n t ht)
        (fun t ht => hUpperRight n t ht) (hFiniteLower n)
        (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (finiteLower n) (finiteUpper n) (lowerLeft n) (upperLeft n)
        (lowerRight n) (upperRight n) hT (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n) (hLowerRightInt n)
        (hUpperRightInt n) (fun t ht => hLowerLeft n t ht)
        (fun t ht => hUpperLeft n t ht) (fun t ht => hLowerRight n t ht)
        (fun t ht => hUpperRight n t ht) (hFiniteLower n)
        (hFiniteUpper n)).2

theorem controlK9AnalyticAFinitePartBoundsCert_of_positiveWindowCert
    {T : Real} {finiteLower finiteUpper positiveLower positiveUpper : CoeffIndex23 → Real}
    (hT : 0 <= T)
    (window : ∀ n : CoeffIndex23,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 T (positiveLower n) (positiveUpper n))
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= 2 * positiveLower n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      2 * positiveUpper n <= finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (positiveLower n) (positiveUpper n)
        hT (window n) (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (finiteLower n) (finiteUpper n) (positiveLower n) (positiveUpper n)
        hT (window n) (hFiniteLower n) (hFiniteUpper n)).2

theorem controlK9AnalyticAFinitePartBoundsCert_of_twoPieceComparisonIntegrals
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (cut : CoeffIndex23 → Real)
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : ∀ n : CoeffIndex23, -T <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Icc (-T) (cut n)))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Icc (-T) (cut n)))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc (cut n) T))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc (cut n) T))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <=
        (∫ t in Set.Icc (-T) (cut n), lowerLeft n t) +
          ∫ t in Set.Ioc (cut n) T, lowerRight n t)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (∫ t in Set.Icc (-T) (cut n), upperLeft n t) +
          ∫ t in Set.Ioc (cut n) T, upperRight n t <=
        finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T (cut n)
        (finiteLower n) (finiteUpper n)
        (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
        (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n)
        (hLowerRightInt n) (hUpperRightInt n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
        (hFiniteLower n) (hFiniteUpper n)).1
  · intro n
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T (cut n)
        (finiteLower n) (finiteUpper n)
        (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
        (hLeft n) (hRight n)
        (hLowerLeftInt n) (hUpperLeftInt n)
        (hLowerRightInt n) (hUpperRightInt n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
        (hFiniteLower n) (hFiniteUpper n)).2

theorem controlK9AnalyticAFinitePartBoundsCert_of_pointwiseBounds
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (pointLower pointUpper : CoeffIndex23 → Real)
    (hT : 0 <= T)
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      pointLower n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpper n)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <= (2 * T) * pointLower n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (2 * T) * pointUpper n <= finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact le_trans (hFiniteLower n)
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (pointLower n) (pointUpper n) hT
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)).1
  · intro n
    exact le_trans
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_pointwise_bounds
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (pointLower n) (pointUpper n) hT
        (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)).2
      (hFiniteUpper n)

theorem controlK9AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
    {T : Real} {finiteLower finiteUpper : CoeffIndex23 → Real}
    (cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hLeft : ∀ n : CoeffIndex23, -T <= cut n)
    (hRight : ∀ n : CoeffIndex23, cut n <= T)
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      pointLowerLeft n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Icc (-T) (cut n),
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      pointLowerRight n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc (cut n) T,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperRight n)
    (hFiniteLower : ∀ n : CoeffIndex23,
      finiteLower n <=
        (cut n + T) * pointLowerLeft n + (T - cut n) * pointLowerRight n)
    (hFiniteUpper : ∀ n : CoeffIndex23,
      (cut n + T) * pointUpperLeft n + (T - cut n) * pointUpperRight n <=
        finiteUpper n) :
    controlK9AnalyticAFinitePartBoundsCert T finiteLower finiteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    exact le_trans (hFiniteLower n)
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (pointLowerLeft n) (pointUpperLeft n)
        (pointLowerRight n) (pointUpperRight n)
        (hLeft n) (hRight n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)).1
  · intro n
    exact le_trans
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
        (cut n) (pointLowerLeft n) (pointUpperLeft n)
        (pointLowerRight n) (pointUpperRight n)
        (hLeft n) (hRight n)
        (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
        (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)).2
      (hFiniteUpper n)

structure controlK9AnalyticATailGrowthBoundsCert
    (T C0 C1 : Real) (tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    centeredBSplineArchKernelProfileTailGrowthBound
      9 ((3 : Real) / (10 : Real)) T C0 C1 <= tailRadius n

structure controlK9AnalyticATailIntervalBoundsCert
    (T : Real) (tailLower tailUpper tailRadius : CoeffIndex23 → Real) : Prop where
  hTail : ∀ n : CoeffIndex23,
    controlK9AnalyticATailIntervalCert n T (tailLower n) (tailUpper n)
  hLower : ∀ n : CoeffIndex23, -tailRadius n <= tailLower n
  hUpper : ∀ n : CoeffIndex23, tailUpper n <= tailRadius n

structure controlK9AnalyticAPositiveTailWindowBoundsCert
    (T U : Real)
    (windowLower windowUpper remainderRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticAPositiveTailWindowIntervalCert
      n T U (windowLower n) (windowUpper n) (remainderRadius n)

structure controlK9AnalyticAPositiveTailRemainderBoundsCert
    (U : Real) (remainderRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    |centeredBSplineArchKernelProfilePositiveTailPart
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
        remainderRadius n

theorem controlK9AnalyticAPositiveTailRemainderBoundsCert_of_integralMajorants
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (majorant : CoeffIndex23 → Real → Real)
    (hMajorantInt : ∀ n : CoeffIndex23,
      Integrable (majorant n) (volume.restrict (Set.Ioi U)))
    (hMajorant : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioi U,
      |centeredBSplineArchKernelProfileIntegrand
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t| <=
          majorant n t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U, majorant n t <= remainderRadius n) :
    controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTail_abs_le_of_integral_majorant
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U
      (remainderRadius n) (majorant n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hMajorantInt n) (fun t ht => hMajorant n t ht) (hIntegral n)

theorem controlK9AnalyticAPositiveTailRemainderBoundsCert_of_aStarTransformIntegralMajorants
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (omegaMajorant : Real → Real)
    (transformSqMajorant : CoeffIndex23 → Real → Real)
    (hMajorantInt : ∀ n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            omegaMajorant t * transformSqMajorant n t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaMajorant t)
    (hTransform : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioi U,
      |centeredBSplineImagTransformRealClosedForm
        9 ((3 : Real) / (10 : Real)) t| ^ 2 <=
          transformSqMajorant n t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| *
          omegaMajorant t * transformSqMajorant n t <=
        remainderRadius n) :
    controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTail_abs_le_of_aStar_transform_integral_majorants
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U
      (remainderRadius n) omegaMajorant (transformSqMajorant n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hMajorantInt n) hOmega (fun t ht => hTransform n t ht)
      (hIntegral n)

theorem controlK9AnalyticAPositiveTailRemainderBoundsCert_of_aStarFullTransformTailMajorant
    {U : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (omegaMajorant : Real → Real)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| * omegaMajorant t *
            centeredBSplineImagTransformSqTailMajorant
              9 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U, |Q3.a_star t| <= omegaMajorant t)
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| * omegaMajorant t *
          centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t <=
        remainderRadius n) :
    controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  refine
    controlK9AnalyticAPositiveTailRemainderBoundsCert_of_aStarTransformIntegralMajorants
      omegaMajorant
      (fun _n t =>
        centeredBSplineImagTransformSqTailMajorant
          9 ((3 : Real) / (10 : Real)) t)
      ?_ hOmega ?_ hIntegral
  · intro n
    exact hMajorantInt n
  · intro _n t ht
    exact
      centeredBSplineImagTransformRealClosedForm_sq_abs_le_full_tail
        9 ((3 : Real) / (10 : Real)) t
        (by norm_num) (lt_of_le_of_lt hU0 ht)

theorem controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
    {U omegaFactor : Real} {remainderRadius : CoeffIndex23 → Real}
    (hU0 : 0 <= U)
    (hMajorantInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            (omegaFactor * Real.log (3 * t)) *
            centeredBSplineImagTransformSqTailMajorant
              9 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi U)))
    (hOmega : ∀ t ∈ Set.Ioi U,
      |Q3.a_star t| <= omegaFactor * Real.log (3 * t))
    (hIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi U,
        |((3 : Real) / (10 : Real))| *
          (omegaFactor * Real.log (3 * t)) *
          centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t <=
        remainderRadius n) :
    controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius := by
  exact
    controlK9AnalyticAPositiveTailRemainderBoundsCert_of_aStarFullTransformTailMajorant
      hU0 (fun t : Real => omegaFactor * Real.log (3 * t))
      hMajorantInt hOmega hIntegral

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23, IntegrableOn (lowerF n) (Set.Ioc T U))
    (hUpperInt : ∀ n : CoeffIndex23, IntegrableOn (upperF n) (Set.Ioc T U))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= ∫ t in Set.Ioc T U, lowerF n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc T U, upperF n t <= windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_comparison_integrals
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (lowerF n) (upperF n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (hLowerInt n) (hUpperInt n)
      (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (window : ∀ n : CoeffIndex23,
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        T U (windowLower n) (windowUpper n))
    (remainder :
      controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_window_cert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (window n) (remainder.h n)

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPieceComparisonIntegrals
    {T U c : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerLeft upperLeft lowerRight upperRight : CoeffIndex23 → Real → Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerLeft n) (Set.Ioc T c))
    (hUpperLeftInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperLeft n) (Set.Ioc T c))
    (hLowerRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (lowerRight n) (Set.Ioc c U))
    (hUpperRightInt : ∀ n : CoeffIndex23,
      IntegrableOn (upperRight n) (Set.Ioc c U))
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      lowerLeft n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperLeft n t)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      lowerRight n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperRight n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <=
        (∫ t in Set.Ioc T c, lowerLeft n t) +
          ∫ t in Set.Ioc c U, lowerRight n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (∫ t in Set.Ioc T c, upperLeft n t) +
          ∫ t in Set.Ioc c U, upperRight n t <=
        windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_comparison_integrals
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U c
      (windowLower n) (windowUpper n) (remainderRadius n)
      (lowerLeft n) (upperLeft n) (lowerRight n) (upperRight n)
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      hLeft hRight
      (hLowerLeftInt n) (hUpperLeftInt n)
      (hLowerRightInt n) (hUpperRightInt n)
      (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
      (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegralsAndRemainderCert
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (lowerF upperF : CoeffIndex23 → Real → Real)
    (hLowerInt : ∀ n : CoeffIndex23, IntegrableOn (lowerF n) (Set.Ioc T U))
    (hUpperInt : ∀ n : CoeffIndex23, IntegrableOn (upperF n) (Set.Ioc T U))
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      lowerF n t <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n t)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= ∫ t in Set.Ioc T U, lowerF n t)
    (hWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc T U, upperF n t <= windowUpper n)
    (remainder :
      controlK9AnalyticAPositiveTailRemainderBoundsCert U remainderRadius) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  exact
    controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
      lowerF upperF hLowerInt hUpperInt hLower hUpper hWindowLower hWindowUpper
      remainder.h

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
    {T U : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (pointLower pointUpper : CoeffIndex23 → Real)
    (hTU : T <= U)
    (hLower : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      pointLower n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpper : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T U,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpper n)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <= (U - T) * pointLower n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (U - T) * pointUpper n <= windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_pointwise_bounds
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      (pointLower n) (pointUpper n) hTU
      (fun t ht => hLower n t ht) (fun t ht => hUpper n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseBounds
    {T U c : Real}
    {windowLower windowUpper remainderRadius : CoeffIndex23 → Real}
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hLeft : T <= c) (hRight : c <= U)
    (hLowerLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      pointLowerLeft n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc T c,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      pointLowerRight n <=
        centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23, ∀ t ∈ Set.Ioc c U,
      centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      windowLower n <=
        (c - T) * pointLowerLeft n + (U - c) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (c - T) * pointUpperLeft n + (U - c) * pointUpperRight n <=
        windowUpper n)
    (hRemainder : ∀ n : CoeffIndex23,
      |centeredBSplineArchKernelProfilePositiveTailPart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) U| <=
          remainderRadius n) :
    controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_pointwise_bounds
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U c
      (windowLower n) (windowUpper n) (remainderRadius n)
      (pointLowerLeft n) (pointUpperLeft n)
      (pointLowerRight n) (pointUpperRight n)
      hLeft hRight
      (fun t ht => hLowerLeft n t ht) (fun t ht => hUpperLeft n t ht)
      (fun t ht => hLowerRight n t ht) (fun t ht => hUpperRight n t ht)
      (hWindowLower n) (hWindowUpper n) (hRemainder n)

theorem controlK9AnalyticATailIntervalBoundsCert_of_positiveTailWindowBoundsCert
    {T U : Real}
    {windowLower windowUpper remainderRadius tailLower tailUpper tailRadius :
      CoeffIndex23 → Real}
    (hT : 0 <= T) (hTU : T <= U)
    (window : controlK9AnalyticAPositiveTailWindowBoundsCert
      T U windowLower windowUpper remainderRadius)
    (hTailLower :
      ∀ n : CoeffIndex23, tailLower n <= 2 * (windowLower n - remainderRadius n))
    (hTailUpper :
      ∀ n : CoeffIndex23, 2 * (windowUpper n + remainderRadius n) <= tailUpper n)
    (hLower : ∀ n : CoeffIndex23, -tailRadius n <= tailLower n)
    (hUpper : ∀ n : CoeffIndex23, tailUpper n <= tailRadius n) :
    controlK9AnalyticATailIntervalBoundsCert T tailLower tailUpper tailRadius := by
  refine ⟨?_, hLower, hUpper⟩
  intro n
  have hTail :=
    centeredBSplineArchKernelProfileTailIntervalCert_of_positiveTailWindowIntervalCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T U
      (windowLower n) (windowUpper n) (remainderRadius n)
      hT hTU
      (centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        (by norm_num) (by norm_num))
      (window.h n)
  exact
    { hTailLower := le_trans (hTailLower n) hTail.hTailLower
      hTailUpper := le_trans hTail.hTailUpper (hTailUpper n) }

structure controlK9AnalyticAFiniteTailArithmeticBoundsCert
    (finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticAFiniteTailArithmeticIntervalCert
      n (finiteLower n) (finiteUpper n) (tailRadius n)

theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailGrowthBounds
    {T C0 C1 : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (hT : 1 <= T)
    (finite : controlK9AnalyticAFinitePartBoundsCert
      T finiteLower finiteUpper)
    (tail : controlK9AnalyticATailGrowthBoundsCert
      T C0 C1 tailRadius) :
    controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailGrowthBound
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (tailRadius n) C0 C1
      (by norm_num) (by norm_num) hC0 hC1 hgrowth hT
      (finite.hFiniteLower n) (finite.hFiniteUpper n) (tail.h n)

theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
    {T : Real}
    {finiteLower finiteUpper tailLower tailUpper tailRadius : CoeffIndex23 → Real}
    (finite : controlK9AnalyticAFinitePartBoundsCert
      T finiteLower finiteUpper)
    (tail : controlK9AnalyticATailIntervalBoundsCert
      T tailLower tailUpper tailRadius) :
    controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailAnalyticCert_of_finitePartBounds_and_tailIntervalCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteLower n) (finiteUpper n) (tailLower n) (tailUpper n) (tailRadius n)
      (finite.hFiniteLower n) (finite.hFiniteUpper n)
      (tail.hTail n) (tail.hLower n) (tail.hUpper n)

theorem controlK9AnalyticAFiniteTailBoundsCert_of_analyticAndArithmeticBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (analytic : controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (arith : controlK9AnalyticAFiniteTailArithmeticBoundsCert
      finiteLower finiteUpper tailRadius) :
    controlK9AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact
    centeredBSplineArchKernelProfileFiniteTailIntervalCert_of_analyticAndArithmeticCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (analytic.h n) (arith.h n)

structure controlK9AnalyticAPointwiseFiniteTailBoundsCert
    (T : Real) (pointLower pointUpper finiteLower finiteUpper tailRadius :
      CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticAPointwiseFiniteTailIntervalCert
      n T (pointLower n) (pointUpper n) (finiteLower n) (finiteUpper n)
      (tailRadius n)

structure controlK9AnalyticATwoPiecePointwiseFiniteTailBoundsCert
    (T : Real) (cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : CoeffIndex23 → Real) : Prop where
  h : ∀ n : CoeffIndex23,
    controlK9AnalyticATwoPiecePointwiseFiniteTailIntervalCert
      n T (cut n) (pointLowerLeft n) (pointUpperLeft n)
      (pointLowerRight n) (pointUpperRight n) (finiteLower n)
      (finiteUpper n) (tailRadius n)

theorem controlK9AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
    {T : Real}
    {pointLower pointUpper finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : controlK9AnalyticAPointwiseFiniteTailBoundsCert
      T pointLower pointUpper finiteLower finiteUpper tailRadius) :
    controlK9AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact controlK9AnalyticAFiniteTailIntervalCert_of_pointwiseFiniteTailIntervalCert
    n T (pointLower n) (pointUpper n) (finiteLower n) (finiteUpper n)
    (tailRadius n) (cert.h n)

theorem controlK9AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
    {T : Real}
    {cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : controlK9AnalyticATwoPiecePointwiseFiniteTailBoundsCert
      T cut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
      finiteLower finiteUpper tailRadius) :
    controlK9AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius := by
  refine ⟨?_⟩
  intro n
  exact controlK9AnalyticAFiniteTailIntervalCert_of_twoPiecePointwiseFiniteTailIntervalCert
    n T (cut n) (pointLowerLeft n) (pointUpperLeft n) (pointLowerRight n)
    (pointUpperRight n) (finiteLower n) (finiteUpper n) (tailRadius n)
    (cert.h n)

theorem controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (cert : controlK9AnalyticAFiniteTailBoundsCert
      T finiteLower finiteUpper tailRadius) :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert := by
  have hBounds : ∀ n : CoeffIndex23,
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n <=
        centeredBSplineArchKernelProfile
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) ∧
      centeredBSplineArchKernelProfile
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) <=
        CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n := by
    intro n
    exact centeredBSplineArchKernelProfile_bounds_of_finiteTailIntervalCert_of_pos_degree
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceLower n)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceUpper n)
      (finiteLower n) (finiteUpper n) (tailRadius n)
      (by norm_num) (by norm_num) (cert.h n)
  constructor <;>
    first
    | simpa using (hBounds (⟨0, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨0, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨1, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨1, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨2, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨2, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨3, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨3, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨4, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨4, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨5, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨5, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨6, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨6, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨7, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨7, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨8, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨8, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨9, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨9, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨10, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨10, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨11, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨11, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨12, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨12, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨13, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨13, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨14, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨14, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨15, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨15, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨16, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨16, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨17, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨17, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨18, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨18, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨19, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨19, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨20, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨20, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨21, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨21, by norm_num⟩ : CoeffIndex23)).2
    | simpa using (hBounds (⟨22, by norm_num⟩ : CoeffIndex23)).1
    | simpa using (hBounds (⟨22, by norm_num⟩ : CoeffIndex23)).2

theorem controlK9AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
    {T : Real} {finiteMid finiteRadius tailRadius : CoeffIndex23 → Real}
    (analytic : controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T (fun n => finiteMid n - finiteRadius n)
        (fun n => finiteMid n + finiteRadius n) tailRadius)
    (hContain : ∀ n : CoeffIndex23,
      finiteRadius n + tailRadius n +
          |finiteMid n -
            (CenteredCoeffPayloadImport.controlK9AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.controlK9ARadiusAbsDistanceEntryRat n.1 : Real)) :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert := by
  refine ⟨?_⟩
  intro n
  have hx :=
    centeredBSplineArchKernelProfile_abs_sub_mid_le_of_finiteTailAnalyticCert_of_pos_degree
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) T
      (finiteMid n) (finiteRadius n) (tailRadius n)
      (by norm_num) (by norm_num) (analytic.h n)
  exact abs_sub_le_of_recenter hx (hContain n)

/-- Recenter control k=9 A hboxes from arbitrary finite-tail interval bounds.

This is the row-refresh receiver: generated refined row sums may define
`finiteLower`/`finiteUpper` directly, and the midpoint/radius used by local
recenter containment is recovered from that interval. -/
theorem controlK9AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticIntervalRecenter
    {T : Real} {finiteLower finiteUpper tailRadius : CoeffIndex23 → Real}
    (analytic : controlK9AnalyticAFiniteTailAnalyticBoundsCert
      T finiteLower finiteUpper tailRadius)
    (hContain : ∀ n : CoeffIndex23,
      ((finiteUpper n - finiteLower n) / 2) + tailRadius n +
          |((finiteLower n + finiteUpper n) / 2) -
            (CenteredCoeffPayloadImport.controlK9AAbsDistanceEntryRat n.1 : Real)| <=
        (CenteredCoeffPayloadImport.controlK9ARadiusAbsDistanceEntryRat n.1 : Real)) :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert := by
  let finiteMid : CoeffIndex23 → Real :=
    fun n => (finiteLower n + finiteUpper n) / 2
  let finiteRadius : CoeffIndex23 → Real :=
    fun n => (finiteUpper n - finiteLower n) / 2
  refine
    controlK9AnalyticAAbsDistanceHboxCert_of_finiteTailAnalyticRecenter
      (T := T) (finiteMid := finiteMid) (finiteRadius := finiteRadius)
      (tailRadius := tailRadius) ?_ ?_
  · refine ⟨?_⟩
    intro n
    have hLower :
        finiteMid n - finiteRadius n = finiteLower n := by
      simp [finiteMid, finiteRadius]
      ring
    have hUpper :
        finiteMid n + finiteRadius n = finiteUpper n := by
      simp [finiteMid, finiteRadius]
      ring
    simpa [hLower, hUpper] using analytic.h n
  · intro n
    simpa [finiteMid, finiteRadius] using hContain n

end CenteredCoeffAnalyticABoundsBackend
end PSDpd
end Q3
