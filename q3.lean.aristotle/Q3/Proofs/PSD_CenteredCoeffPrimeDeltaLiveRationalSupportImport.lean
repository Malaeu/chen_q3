import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryMinusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryPlusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlMinusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlPlusImport
import Q3.Proofs.PSD_CenteredCoeffBaseP0HboxImport
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0BoundsImport
import Q3.Proofs.PSD_CenteredCoeffBaseAHboxImport
import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend
import Q3.Proofs.PSD_CenteredCoeffAnalyticAFiniteTailArithmeticImport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowGeneratedArithmeticHandoffSupport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B split-`R` declared-support closure surface.

The four side support proofs are split into separate modules so each side can be
checked and cached independently.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

/-- Generated primary minus-side full live split-`R` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRMinusHboxByDelta_generated :
    primaryK11RationalDeltaLiveRMinusHboxByDelta := by
  exact
    primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated

/-- Generated primary plus-side full live split-`R` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRPlusHboxByDelta_generated :
    primaryK11RationalDeltaLiveRPlusHboxByDelta := by
  exact
    primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated

/-- Generated control minus-side full live split-`R` hbox receiver. -/
theorem controlK9RationalDeltaLiveRMinusHboxByDelta_generated :
    controlK9RationalDeltaLiveRMinusHboxByDelta := by
  exact
    controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated

/-- Generated control plus-side full live split-`R` hbox receiver. -/
theorem controlK9RationalDeltaLiveRPlusHboxByDelta_generated :
    controlK9RationalDeltaLiveRPlusHboxByDelta := by
  exact
    controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated

/-- Generated primary `R_minus + R_plus` hbox bridge. -/
theorem primaryK11RationalDeltaLiveRPairHboxBridge_generated :
    primaryK11RationalDeltaLiveRPairHboxBridge
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad := by
  exact
    primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
      primaryK11RationalDeltaLiveRMinusHboxByDelta_generated
      primaryK11RationalDeltaLiveRPlusHboxByDelta_generated

/-- Generated control `R_minus + R_plus` hbox bridge. -/
theorem controlK9RationalDeltaLiveRPairHboxBridge_generated :
    controlK9RationalDeltaLiveRPairHboxBridge
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad := by
  exact
    controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
      controlK9RationalDeltaLiveRMinusHboxByDelta_generated
      controlK9RationalDeltaLiveRPlusHboxByDelta_generated

/-- Generated primary rational term hbox bridge from the JSON witnesses. -/
theorem primaryK11RationalDeltaLiveTermHboxBridge_generated :
    primaryK11RationalDeltaLiveTermHboxBridge := by
  exact
    primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
      (primaryK11RationalPrimeWeight_hbox_of_active
        activeL3RationalPrimeWeight_hbox_generated)
      primaryK11RationalDeltaLiveRPairHboxBridge_generated

/-- Generated control rational term hbox bridge from the JSON witnesses. -/
theorem controlK9RationalDeltaLiveTermHboxBridge_generated :
    controlK9RationalDeltaLiveTermHboxBridge := by
  exact
    controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
      (controlK9RationalPrimeWeight_hbox_of_active
        activeL3RationalPrimeWeight_hbox_generated)
      controlK9RationalDeltaLiveRPairHboxBridge_generated

/-- Concrete generated primary rational payload witness with center error. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
      primaryK11RationalDeltaLiveTermHboxBridge_generated

/-- Concrete generated control rational payload witness with center error. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
      controlK9RationalDeltaLiveTermHboxBridge_generated

/-- Option-B closure using the two concrete generated rational payload hboxes.
This is the explicit generated landing surface for
`psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError`. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedPayloadHboxesWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0

/-- Generated closure after the base `A/P0` matrix hboxes have been reduced to
compact absolute-distance scalar certificate structures.  This is the checked
Step33A.1 bridge from four `23`-distance scalar certs to the active generated
rational payload closure surface. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedAbsDistanceBaseCertsWithCenterError
    (primary_hA_cert :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert)
    (primary_hP0_cert :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert)
    (control_hA_cert :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert)
    (control_hP0_cert :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert) :
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedPayloadHboxesWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert)

/-- Generated closure after the base `A/P0` compact scalar certificates have
been shifted to lower/upper interval certificate structures.  This keeps the
remaining Step21/Step22 proof obligation in the natural interval-output shape
while still closing the active generated rational payload surface. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedIntervalBaseCertsWithCenterError
    (primary_hA_interval :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert)
    (primary_hP0_interval :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert)
    (control_hA_interval :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert)
    (control_hP0_interval :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert) :
    let primary_hA_cert :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval
    let control_hA_cert :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedAbsDistanceBaseCertsWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval)

/-- Generated closure after the base `A/P0` compact scalar interval facts have
been packaged as named distance-bound certificate structures.  This is the
intended landing surface for a proof-producing Step21/Step22 scalar backend:
one checked cert term per active primary/control `A/P0` block. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedDistanceBoundBaseCertsWithCenterError
    (primary_hA_bounds :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert)
    (primary_hP0_bounds :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceBoundsCert)
    (control_hA_bounds :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert)
    (control_hP0_bounds :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceBoundsCert) :
    let primary_hA_interval :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hA_bounds
    let primary_hP0_interval :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hP0_bounds
    let control_hA_interval :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        control_hA_bounds
    let control_hP0_interval :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        control_hP0_bounds
    let primary_hA_cert :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval
    let control_hA_cert :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedIntervalBaseCertsWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hA_bounds)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hP0_bounds)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        control_hA_bounds)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        control_hP0_bounds)

/-- One named base scalar gate for the active Step33A.1 `A/P0` layer.  This
packages the four primary/control `A/P0` distance-bound certificates without
changing the checked receiver theorem. -/
structure RationalDeltaLiveBaseScalarBoundsCert : Prop where
  primary_hA_bounds :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert
  primary_hP0_bounds :
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceBoundsCert
  control_hA_bounds :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert
  control_hP0_bounds :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceBoundsCert

/-- The closure proposition exposed by the one-cert Step33A.1 base scalar gate. -/
def RationalDeltaLiveBaseScalarBoundsClosure
    (base_bounds : RationalDeltaLiveBaseScalarBoundsCert) : Prop :=
  let primary_hA_interval :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.primary_hA_bounds
  let primary_hP0_interval :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.primary_hP0_bounds
  let control_hA_interval :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.control_hA_bounds
  let control_hP0_interval :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.control_hP0_bounds
  let primary_hA_cert :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
      primary_hA_interval
  let primary_hP0_cert :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
      primary_hP0_interval
  let control_hA_cert :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
      control_hA_interval
  let control_hP0_cert :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
      control_hP0_interval
  let primary_hA :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
      primary_hA_cert
  let primary_hP0 :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
      primary_hP0_cert
  let control_hA :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
      control_hA_cert
  let control_hP0 :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
      control_hP0_cert
  let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
    primary_hA
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
    primary_hP0
    control_hA
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
    control_hP0
  PsdStep33FiniteAnalyticPositivity cert ∧
    PsdStep33SingletonDirectedFamilyHandoff cert

/-- Generated one-cert closure bridge for the active Step33A.1 base scalar gate.
The remaining backend target is now one proof-producing
`RationalDeltaLiveBaseScalarBoundsCert` inhabitant. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedBaseScalarBoundsCertWithCenterError
    (base_bounds : RationalDeltaLiveBaseScalarBoundsCert) :
    RationalDeltaLiveBaseScalarBoundsClosure base_bounds := by
  rcases base_bounds with
    ⟨primary_hA_bounds, primary_hP0_bounds, control_hA_bounds, control_hP0_bounds⟩
  simpa [RationalDeltaLiveBaseScalarBoundsClosure] using
    psd_step33_closed_from_rationalDeltaLiveGeneratedDistanceBoundBaseCertsWithCenterError
      primary_hA_bounds
      primary_hP0_bounds
      control_hA_bounds
      control_hP0_bounds

/-- Generated-P0 closure bridge for the active Step33A.1 base scalar gate.
The P0 primary/control distance-bound certificates are now generated Lean
artifacts; the remaining base scalar obligations are the two A-side distance
bound certificate structures. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0BaseScalarBoundsCertWithCenterError
    (primary_hA_bounds :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert)
    (control_hA_bounds :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨primary_hA_bounds,
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        control_hA_bounds,
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedBaseScalarBoundsCertWithCenterError
      ⟨primary_hA_bounds,
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        control_hA_bounds,
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩

/-- Generated-P0 plus A finite/tail closure bridge for the active Step33A.1
base scalar gate.  The remaining proof-producing target is now exactly two
A-side finite/tail certificate terms, one for primary K11 and one for control
K9. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
    {primaryT controlT : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailRadius : CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailRadius : CoeffIndex23 → Real}
    (primary_hA_finite_tail :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert
        primaryT primaryFiniteLower primaryFiniteUpper primaryTailRadius)
    (control_hA_finite_tail :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert
        controlT controlFiniteLower controlFiniteUpper controlTailRadius) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          primary_hA_finite_tail,
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          control_hA_finite_tail,
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0BaseScalarBoundsCertWithCenterError
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
        primary_hA_finite_tail)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
        control_hA_finite_tail)

/-- Generated-P0 plus generated A finite/tail arithmetic closure bridge for
the active Step33A.1 base scalar gate.  The remaining inputs are only the
analytic finite-window and tail facts for the generated A payload functions. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailGeneratedArithmeticBaseScalarBoundsCertWithCenterError
    (primary_hA_analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper
        Q3.PSDpd.primaryK11AnalyticATailRadius)
    (control_hA_analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper
        Q3.PSDpd.controlK9AnalyticATailRadius) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
            primary_hA_analytic),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
            control_hA_analytic),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
      (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
        primary_hA_analytic)
      (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedArithmetic
        control_hA_analytic)

/-- Generated-P0 plus local A recenter closure bridge.  This keeps midpoint
offset synchronization local to the A hbox receiver instead of routing through
global radius-payload mutation. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailRecenterWithCenterError
    (primary_hA_analytic :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper
        Q3.PSDpd.primaryK11AnalyticATailRadius)
    (control_hA_analytic :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper
        Q3.PSDpd.controlK9AnalyticATailRadius) :
    let primary_hA_cert :=
      Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        primary_hA_analytic
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated)
    let control_hA_cert :=
      Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        control_hA_analytic
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated)
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedAbsDistanceBaseCertsWithCenterError
      (Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        primary_hA_analytic)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated))
      (Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        control_hA_analytic)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated))

/-- Generated-P0 plus local A recenter closure bridge whose remaining A inputs
are finite-window bounds and signed tail-interval certificates.  This is the
local replacement surface for the too-coarse global `TailGrowthBound` route. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    {primaryTailLower primaryTailUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real}
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primary_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailIntervalBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        primaryTailLower primaryTailUpper Q3.PSDpd.primaryK11AnalyticATailRadius)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (control_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailIntervalBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        controlTailLower controlTailUpper Q3.PSDpd.controlK9AnalyticATailRadius) :
    let primary_hA_analytic :=
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        primary_hA_finite primary_hA_tail
    let control_hA_analytic :=
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        control_hA_finite control_hA_tail
    let primary_hA_cert :=
      Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        primary_hA_analytic
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated)
    let control_hA_cert :=
      Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        control_hA_analytic
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated)
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailRecenterWithCenterError
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        primary_hA_finite primary_hA_tail)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        control_hA_finite control_hA_tail)

/-- Generated-P0 plus generated A tail-window arithmetic closure bridge.  The
remaining A tail input is the proof-producing positive-tail-window certificate;
the generated arithmetic import turns it into signed tail-interval bounds. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0APositiveTailWindowRecenterWithCenterError
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primary_hA_tailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailRemainderRadius)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (control_hA_tailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailRemainderRadius) :
    let primary_hA_tail :=
      Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
        primary_hA_tailWindow
    let control_hA_tail :=
      Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
        control_hA_tailWindow
    let primary_hA_analytic :=
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        primary_hA_finite primary_hA_tail
    let control_hA_analytic :=
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
        control_hA_finite control_hA_tail
    let primary_hA_cert :=
      Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        primary_hA_analytic
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated)
    let control_hA_cert :=
      Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
        control_hA_analytic
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated)
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
      primary_hA_finite
      (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
        primary_hA_tailWindow)
      control_hA_finite
      (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
        control_hA_tailWindow)

/-- Generated-P0 plus generated A positive-tail-window closure bridge using
comparison integrals for both the finite window and the positive tail window.
This is the proof-producing landing surface for a compact A generator: it
proves the finite-window certs and positive-tail-window certs, then reuses the
generated local recenter bridge. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AComparisonIntegralPositiveTailWindowRecenterWithCenterError
    (primaryFiniteLowerF primaryFiniteUpperF
      primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF
      controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailUpperF n t)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailLowerF n t)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailUpperF n t <= Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (primaryTailRemainder : ∀ n : CoeffIndex23,
      |CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveTailPart
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          Q3.PSDpd.archAPositiveTailWindowEnd| <=
        Q3.PSDpd.primaryK11AnalyticATailRemainderRadius n)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailUpperF n t)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailLowerF n t)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailUpperF n t <= Q3.PSDpd.controlK9AnalyticATailWindowUpper n)
    (controlTailRemainder : ∀ n : CoeffIndex23,
      |CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveTailPart
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          Q3.PSDpd.archAPositiveTailWindowEnd| <=
        Q3.PSDpd.controlK9AnalyticATailRemainderRadius n) :
    PsdStep33FiniteAnalyticPositivity
      (psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
        (CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
          (Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
            (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
              (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
                primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
                primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
              (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
                (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
                  primaryTailLowerF primaryTailUpperF primaryTailLowerInt primaryTailUpperInt
                  primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
                  primaryTailRemainder)))))
        primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
          (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
            (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
              Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated)))
        (CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
          (Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
            (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
              (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
                controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
                controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
              (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
                (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
                  controlTailLowerF controlTailUpperF controlTailLowerInt controlTailUpperInt
                  controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
                  controlTailRemainder)))))
        controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
          (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
            (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
              Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated)))) ∧
      PsdStep33SingletonDirectedFamilyHandoff
        (psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
          (CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
            (Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
              (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
                (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
                  primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
                  primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
                (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
                  (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
                    primaryTailLowerF primaryTailUpperF primaryTailLowerInt primaryTailUpperInt
                    primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
                    primaryTailRemainder)))))
          primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
          (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
            (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
              (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
                Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated)))
          (CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
            (Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
              (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds
                (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
                  controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
                  controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
                (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindow
                  (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
                    controlTailLowerF controlTailUpperF controlTailLowerInt controlTailUpperInt
                    controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
                    controlTailRemainder)))))
          controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
          (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
            (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
              (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
                Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated)))) := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0APositiveTailWindowRecenterWithCenterError
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
        primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
        primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        primaryTailLowerF primaryTailUpperF primaryTailLowerInt primaryTailUpperInt
        primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
        primaryTailRemainder)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
        controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
        controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        controlTailLowerF controlTailUpperF controlTailLowerInt controlTailUpperInt
        controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
        controlTailRemainder)

theorem a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd :
    ∀ t ∈ Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
      |Q3.a_star t| <= 10 * Real.log (3 * t) := by
  intro t ht
  exact CenteredCoeffAnalyticABoundsBackend.a_star_abs_le_ten_logOmega_after_520
    t (by simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht)

theorem a_star_abs_le_ten_logOmega_after_archAFiniteTailCutoff :
    ∀ t ∈ Set.Ioi Q3.PSDpd.archAFiniteTailCutoff,
      |Q3.a_star t| <= 10 * Real.log (3 * t) := by
  intro t ht
  exact CenteredCoeffAnalyticABoundsBackend.a_star_abs_le_ten_logOmega_after_260
    t (by simpa [Q3.PSDpd.archAFiniteTailCutoff] using ht)

/-- Pointwise full-transform log majorant used on the positive A tail window.
This is a local proof target, not an imported A-radius mutation. -/
def archALogOmegaFullTransformPointwiseMajorant (k : Nat) (t : Real) : Real :=
  |((3 : Real) / 10)| * (10 * Real.log (3 * t)) *
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
      k ((3 : Real) / 10) t

private theorem archA_integrand_bounds_of_logOmegaFullTransformMajorant
    (k : Nat) (x t lower upper : Real)
    (ht : t ∈ Set.Ioi Q3.PSDpd.archAFiniteTailCutoff)
    (hLower :
      lower <= -archALogOmegaFullTransformPointwiseMajorant k t)
    (hUpper :
      archALogOmegaFullTransformPointwiseMajorant k t <= upper) :
    lower <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / 10) x t ∧
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / 10) x t <= upper := by
  have htCut : Q3.PSDpd.archAFiniteTailCutoff < t := by
    simpa [Set.mem_Ioi] using ht
  have ht0 : 0 < t := by
    have hcut : (0 : Real) < Q3.PSDpd.archAFiniteTailCutoff := by
      norm_num [Q3.PSDpd.archAFiniteTailCutoff]
    exact lt_trans hcut htCut
  simpa [archALogOmegaFullTransformPointwiseMajorant] using
    (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_bounds_of_logOmegaFullTransformTailMajorant
        k ((3 : Real) / 10) x t 10 lower upper
        (by norm_num) ht0
        (a_star_abs_le_ten_logOmega_after_archAFiniteTailCutoff t ht)
        (by simpa [archALogOmegaFullTransformPointwiseMajorant] using hLower)
        (by simpa [archALogOmegaFullTransformPointwiseMajorant] using hUpper))

/-- Local primary post-window dominating constant for the log-omega tail
majorant.  This is proof-only slack; it does not mutate imported A radii. -/
def primaryK11AnalyticATailProofRemainderDominatingConstant : Real :=
  9 *
    (|(Real.sqrt
        (bsplineScale 11 *
          bsplineAutocorrNorm 11))⁻¹| ^ 2 *
      (|(((3 : Real) / 10) /
        (2 * bsplineScale 11))|⁻¹) ^
          (2 * (11 + 1)))

/-- Local control post-window dominating constant for the log-omega tail
majorant.  This is proof-only slack; it does not mutate imported A radii. -/
def controlK9AnalyticATailProofRemainderDominatingConstant : Real :=
  9 *
    (|(Real.sqrt
        (bsplineScale 9 *
          bsplineAutocorrNorm 9))⁻¹| ^ 2 *
      (|(((3 : Real) / 10) /
        (2 * bsplineScale 9))|⁻¹) ^
          (2 * (9 + 1)))

private theorem primaryK11AnalyticATailProofRemainderMajorant_after520
    (t : Real)
    (ht : t ∈ Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) :
    ‖|((3 : Real) / (10 : Real))| *
        ((10 : Real) * Real.log (3 * t)) *
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          11 ((3 : Real) / (10 : Real)) t‖ <=
      primaryK11AnalyticATailProofRemainderDominatingConstant *
        t ^ (-23 : Real) := by
  have ht520 : (520 : Real) < t := by
    simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
  have htpos : 0 < t := by nlinarith
  have ht3pos : 0 < 3 * t := by positivity
  have hlog : Real.log (3 * t) <= 3 * t :=
    Real.log_le_self (le_of_lt ht3pos)
  have hlog_nonneg : 0 <= Real.log (3 * t) :=
    Real.log_nonneg (by nlinarith)
  have hpow_nonneg : 0 <= t ^ (-24 : Real) :=
    Real.rpow_nonneg htpos.le _
  let C : Real :=
    |(Real.sqrt
        (bsplineScale 11 *
          bsplineAutocorrNorm 11))⁻¹| ^ 2 *
      (|(((3 : Real) / 10) /
        (2 * bsplineScale 11))|⁻¹) ^
          (2 * (11 + 1))
  have hC_nonneg : 0 <= C := by
    unfold C
    positivity
  have hmaj_eq :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          11 ((3 : Real) / (10 : Real)) t =
        C * t ^ (-24 : Real) := by
    unfold CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant C
    norm_num
  have hrpow : t * t ^ (-24 : Real) = t ^ (-23 : Real) := by
    calc
      t * t ^ (-24 : Real) =
          t ^ (1 : Real) * t ^ (-24 : Real) := by rw [Real.rpow_one]
      _ = t ^ ((1 : Real) + (-24 : Real)) := by
          rw [← Real.rpow_add htpos]
      _ = t ^ (-23 : Real) := by norm_num
  rw [hmaj_eq]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · calc
      |(3 : Real) / 10| * (10 * Real.log (3 * t)) *
          (C * t ^ (-24 : Real))
          <= |(3 : Real) / 10| * (10 * (3 * t)) *
            (C * t ^ (-24 : Real)) := by
              gcongr
      _ = primaryK11AnalyticATailProofRemainderDominatingConstant *
            t ^ (-23 : Real) := by
              unfold primaryK11AnalyticATailProofRemainderDominatingConstant C
              rw [abs_of_pos (by norm_num : (0 : Real) < 3 / 10)]
              rw [← hrpow]
              ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num) hlog_nonneg))
      (mul_nonneg hC_nonneg hpow_nonneg)

private theorem controlK9AnalyticATailProofRemainderMajorant_after520
    (t : Real)
    (ht : t ∈ Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) :
    ‖|((3 : Real) / (10 : Real))| *
        ((10 : Real) * Real.log (3 * t)) *
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          9 ((3 : Real) / (10 : Real)) t‖ <=
      controlK9AnalyticATailProofRemainderDominatingConstant *
        t ^ (-19 : Real) := by
  have ht520 : (520 : Real) < t := by
    simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
  have htpos : 0 < t := by nlinarith
  have ht3pos : 0 < 3 * t := by positivity
  have hlog : Real.log (3 * t) <= 3 * t :=
    Real.log_le_self (le_of_lt ht3pos)
  have hlog_nonneg : 0 <= Real.log (3 * t) :=
    Real.log_nonneg (by nlinarith)
  have hpow_nonneg : 0 <= t ^ (-20 : Real) :=
    Real.rpow_nonneg htpos.le _
  let C : Real :=
    |(Real.sqrt
        (bsplineScale 9 *
          bsplineAutocorrNorm 9))⁻¹| ^ 2 *
      (|(((3 : Real) / 10) /
        (2 * bsplineScale 9))|⁻¹) ^
          (2 * (9 + 1))
  have hC_nonneg : 0 <= C := by
    unfold C
    positivity
  have hmaj_eq :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
          9 ((3 : Real) / (10 : Real)) t =
        C * t ^ (-20 : Real) := by
    unfold CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant C
    norm_num
  have hrpow : t * t ^ (-20 : Real) = t ^ (-19 : Real) := by
    calc
      t * t ^ (-20 : Real) =
          t ^ (1 : Real) * t ^ (-20 : Real) := by rw [Real.rpow_one]
      _ = t ^ ((1 : Real) + (-20 : Real)) := by
          rw [← Real.rpow_add htpos]
      _ = t ^ (-19 : Real) := by norm_num
  rw [hmaj_eq]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · calc
      |(3 : Real) / 10| * (10 * Real.log (3 * t)) *
          (C * t ^ (-20 : Real))
          <= |(3 : Real) / 10| * (10 * (3 * t)) *
            (C * t ^ (-20 : Real)) := by
              gcongr
      _ = controlK9AnalyticATailProofRemainderDominatingConstant *
            t ^ (-19 : Real) := by
              unfold controlK9AnalyticATailProofRemainderDominatingConstant C
              rw [abs_of_pos (by norm_num : (0 : Real) < 3 / 10)]
              rw [← hrpow]
              ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num) hlog_nonneg))
      (mul_nonneg hC_nonneg hpow_nonneg)

private theorem primaryK11AnalyticATailProofRemainderContinuous_after520 :
    ContinuousOn
      (fun t : Real =>
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t)
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
  have hlog : ContinuousOn (fun t : Real => Real.log (3 * t))
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
    have hmul : ContinuousOn (fun t : Real => (3 : Real) * t)
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      simpa using ((continuousOn_const : ContinuousOn (fun _ : Real => (3 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)).mul continuousOn_id)
    exact hmul.log (by
      intro t ht
      have ht520 : (520 : Real) < t := by
        simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
      nlinarith)
  have hrpow : ContinuousOn (fun t : Real => t ^ (-(2 * (11 + 1) : Real)))
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
    exact continuousOn_id.rpow_const (by
      intro t ht
      left
      change t ≠ 0
      have ht520 : (520 : Real) < t := by
        simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
      nlinarith)
  unfold CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
  fun_prop

private theorem controlK9AnalyticATailProofRemainderContinuous_after520 :
    ContinuousOn
      (fun t : Real =>
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t)
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
  have hlog : ContinuousOn (fun t : Real => Real.log (3 * t))
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
    have hmul : ContinuousOn (fun t : Real => (3 : Real) * t)
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      simpa using ((continuousOn_const : ContinuousOn (fun _ : Real => (3 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)).mul continuousOn_id)
    exact hmul.log (by
      intro t ht
      have ht520 : (520 : Real) < t := by
        simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
      nlinarith)
  have hrpow : ContinuousOn (fun t : Real => t ^ (-(2 * (9 + 1) : Real)))
      (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
    exact continuousOn_id.rpow_const (by
      intro t ht
      left
      change t ≠ 0
      have ht520 : (520 : Real) < t := by
        simpa [Q3.PSDpd.archAPositiveTailWindowEnd] using ht
      nlinarith)
  unfold CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
  fun_prop

theorem primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520 :
    ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            ((10 : Real) * Real.log (3 * t)) *
            CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
              11 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
  intro _n
  have hdom :
      Integrable (fun t : Real =>
          primaryK11AnalyticATailProofRemainderDominatingConstant *
            t ^ (-23 : Real))
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
    have hOn : IntegrableOn (fun t : Real =>
          primaryK11AnalyticATailProofRemainderDominatingConstant *
            t ^ (-23 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-23 : Real) < -1)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
          (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)).const_mul
            primaryK11AnalyticATailProofRemainderDominatingConstant
    simpa [IntegrableOn] using hOn
  refine hdom.mono'
    (ContinuousOn.aestronglyMeasurable
      primaryK11AnalyticATailProofRemainderContinuous_after520 measurableSet_Ioi) ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono
    (fun t ht => primaryK11AnalyticATailProofRemainderMajorant_after520 t ht)

theorem controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520 :
    ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            ((10 : Real) * Real.log (3 * t)) *
            CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
              9 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
  intro _n
  have hdom :
      Integrable (fun t : Real =>
          controlK9AnalyticATailProofRemainderDominatingConstant *
            t ^ (-19 : Real))
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
    have hOn : IntegrableOn (fun t : Real =>
          controlK9AnalyticATailProofRemainderDominatingConstant *
            t ^ (-19 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-19 : Real) < -1)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
          (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)).const_mul
            controlK9AnalyticATailProofRemainderDominatingConstant
    simpa [IntegrableOn] using hOn
  refine hdom.mono'
    (ContinuousOn.aestronglyMeasurable
      controlK9AnalyticATailProofRemainderContinuous_after520 measurableSet_Ioi) ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono
    (fun t ht => controlK9AnalyticATailProofRemainderMajorant_after520 t ht)

theorem primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520 :
    ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t <=
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius n := by
  intro n
  have hdom :
      Integrable (fun t : Real =>
          primaryK11AnalyticATailProofRemainderDominatingConstant *
            t ^ (-23 : Real))
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
    have hOn : IntegrableOn (fun t : Real =>
          primaryK11AnalyticATailProofRemainderDominatingConstant *
            t ^ (-23 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-23 : Real) < -1)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
          (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)).const_mul
            primaryK11AnalyticATailProofRemainderDominatingConstant
    simpa [IntegrableOn] using hOn
  have hmono :
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t <=
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryK11AnalyticATailProofRemainderDominatingConstant *
          t ^ (-23 : Real) := by
    refine integral_mono_ae
      (primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520 n)
      hdom ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    exact le_trans (le_abs_self _)
      (by
        simpa [Real.norm_eq_abs] using
          primaryK11AnalyticATailProofRemainderMajorant_after520 t ht)
  have hdom_eq :
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryK11AnalyticATailProofRemainderDominatingConstant *
          t ^ (-23 : Real) =
      primaryK11AnalyticATailProofRemainderDominatingConstant *
        (Q3.PSDpd.archAPositiveTailWindowEnd ^ (-22 : Real) / 22) := by
    rw [integral_const_mul]
    rw [integral_Ioi_rpow_of_lt
      (by norm_num : (-23 : Real) < -1)
      (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
        (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)]
    ring_nf
  have harith :
      primaryK11AnalyticATailProofRemainderDominatingConstant *
        (Q3.PSDpd.archAPositiveTailWindowEnd ^ (-22 : Real) / 22) <=
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius n := by
    unfold primaryK11AnalyticATailProofRemainderDominatingConstant
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius
      Q3.PSDpd.archAPositiveTailWindowEnd
    rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos
        (bsplineScale_pos 11)
        (bsplineAutocorrNorm_pos 11))))]
    rw [inv_pow]
    rw [Real.sq_sqrt (le_of_lt
      (mul_pos
        (bsplineScale_pos 11)
        (bsplineAutocorrNorm_pos 11)))]
    norm_num [
      bsplineScale,
      bsplineAutocorrNorm,
      bsplineAutocorrDegree,
      centeredCardinalBSpline,
      positivePartPower,
      Finset.sum_range_succ,
      Nat.choose
    ]
  rw [hdom_eq] at hmono
  exact le_trans hmono harith

theorem controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520 :
    ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t <=
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius n := by
  intro n
  have hdom :
      Integrable (fun t : Real =>
          controlK9AnalyticATailProofRemainderDominatingConstant *
            t ^ (-19 : Real))
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)) := by
    have hOn : IntegrableOn (fun t : Real =>
          controlK9AnalyticATailProofRemainderDominatingConstant *
            t ^ (-19 : Real))
        (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-19 : Real) < -1)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
          (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)).const_mul
            controlK9AnalyticATailProofRemainderDominatingConstant
    simpa [IntegrableOn] using hOn
  have hmono :
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          ((10 : Real) * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t <=
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        controlK9AnalyticATailProofRemainderDominatingConstant *
          t ^ (-19 : Real) := by
    refine integral_mono_ae
      (controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520 n)
      hdom ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    exact le_trans (le_abs_self _)
      (by
        simpa [Real.norm_eq_abs] using
          controlK9AnalyticATailProofRemainderMajorant_after520 t ht)
  have hdom_eq :
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        controlK9AnalyticATailProofRemainderDominatingConstant *
          t ^ (-19 : Real) =
      controlK9AnalyticATailProofRemainderDominatingConstant *
        (Q3.PSDpd.archAPositiveTailWindowEnd ^ (-18 : Real) / 18) := by
    rw [integral_const_mul]
    rw [integral_Ioi_rpow_of_lt
      (by norm_num : (-19 : Real) < -1)
      (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd] :
        (0 : Real) < Q3.PSDpd.archAPositiveTailWindowEnd)]
    ring_nf
  have harith :
      controlK9AnalyticATailProofRemainderDominatingConstant *
        (Q3.PSDpd.archAPositiveTailWindowEnd ^ (-18 : Real) / 18) <=
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius n := by
    unfold controlK9AnalyticATailProofRemainderDominatingConstant
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius
      Q3.PSDpd.archAPositiveTailWindowEnd
    rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos
        (bsplineScale_pos 9)
        (bsplineAutocorrNorm_pos 9))))]
    rw [inv_pow]
    rw [Real.sq_sqrt (le_of_lt
      (mul_pos
        (bsplineScale_pos 9)
        (bsplineAutocorrNorm_pos 9)))]
    norm_num [
      bsplineScale,
      bsplineAutocorrNorm,
      bsplineAutocorrDegree,
      centeredCardinalBSpline,
      positivePartPower,
      Finset.sum_range_succ,
      Nat.choose
    ]
  rw [hdom_eq] at hmono
  exact le_trans hmono harith

/-- Generated-P0 plus generated A comparison-integral closure bridge whose
post-window remainders use the local proof slack and are proved from a
`log(3t)` omega bound and the checked full sinc-power transform tail majorant. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AComparisonIntegralPositiveTailWindowLogOmegaRecenterWithCenterError
    (omegaFactor : Real)
    (primaryFiniteLowerF primaryFiniteUpperF
      primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF
      controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailUpperF n t)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailLowerF n t)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailUpperF n t <= Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (primaryTailRemainderInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            (omegaFactor * Real.log (3 * t)) *
            CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
              11 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)))
    (tailOmegaBound : ∀ t ∈ Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
      |Q3.a_star t| <= omegaFactor * Real.log (3 * t))
    (primaryTailRemainderIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          (omegaFactor * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            11 ((3 : Real) / (10 : Real)) t <=
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius n)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailUpperF n t)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailLowerF n t)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailUpperF n t <= Q3.PSDpd.controlK9AnalyticATailWindowUpper n)
    (controlTailRemainderInt : ∀ _n : CoeffIndex23,
      Integrable
        (fun t : Real =>
          |((3 : Real) / (10 : Real))| *
            (omegaFactor * Real.log (3 * t)) *
            CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
              9 ((3 : Real) / (10 : Real)) t)
        (volume.restrict (Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd)))
    (controlTailRemainderIntegral : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioi Q3.PSDpd.archAPositiveTailWindowEnd,
        |((3 : Real) / (10 : Real))| *
          (omegaFactor * Real.log (3 * t)) *
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformSqTailMajorant
            9 ((3 : Real) / (10 : Real)) t <=
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
      primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
    (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        primaryTailLowerF primaryTailUpperF primaryTailLowerInt primaryTailUpperInt
        primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := omegaFactor)
          (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          primaryTailRemainderInt tailOmegaBound primaryTailRemainderIntegral).h))
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
      controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
    (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        controlTailLowerF controlTailUpperF controlTailLowerInt controlTailUpperInt
        controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := omegaFactor)
          (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          controlTailRemainderInt tailOmegaBound controlTailRemainderIntegral).h))

/-- Specialized local-log-tail closure bridge.  Compared with
`...LogOmegaRecenterWithCenterError`, this no longer asks callers for
post-520 remainder integrability or integral bounds; those are supplied by the
local proof-only tail lemmas above. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AComparisonIntegralPositiveTailWindowLocalLogTailRecenterWithCenterError
    (primaryFiniteLowerF primaryFiniteUpperF
      primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF
      controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailUpperF n t)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailLowerF n t)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailUpperF n t <= Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailUpperF n t)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailLowerF n t)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailUpperF n t <= Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AComparisonIntegralPositiveTailWindowLogOmegaRecenterWithCenterError
    (10 : Real)
    primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
    controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF
    primaryFiniteLowerInt primaryFiniteUpperInt
    primaryFiniteLower primaryFiniteUpper
    primaryFiniteLowerBound primaryFiniteUpperBound
    primaryTailLowerInt primaryTailUpperInt
    primaryTailLower primaryTailUpper
    primaryTailWindowLower primaryTailWindowUpper
    primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
    a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
    primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520
    controlFiniteLowerInt controlFiniteUpperInt
    controlFiniteLower controlFiniteUpper
    controlFiniteLowerBound controlFiniteUpperBound
    controlTailLowerInt controlTailUpperInt
    controlTailLower controlTailUpper
    controlTailWindowLower controlTailWindowUpper
    controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
    controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520

/-- Specialized positive-half finite-window closure bridge.  The finite-window
inputs live only on `Ioc 0 archAFiniteTailCutoff`; the checked Arch evenness
identity doubles those comparison integrals into the full symmetric finite
window before feeding the local-log-tail recenter route. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0APositiveFiniteComparisonIntegralPositiveTailWindowLocalLogTailRecenterWithCenterError
    (primaryFiniteLowerF primaryFiniteUpperF
      primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF
      controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailUpperF n t)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailLowerF n t)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          primaryTailUpperF n t <= Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n)
        (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd))
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailUpperF n t)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailLowerF n t)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
          controlTailUpperF n t <= Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
      primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
    (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        primaryTailLowerF primaryTailUpperF primaryTailLowerInt primaryTailUpperInt
        primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := (10 : Real))
          (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
          a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
          primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520).h))
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
      controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
    (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_comparisonIntegrals
        controlTailLowerF controlTailUpperF controlTailLowerInt controlTailUpperInt
        controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := (10 : Real))
          (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
          a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
          controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520).h))

/-- Named landing surface for the signed chunked comparison-integral `A`
payload.  A generated chunk backend should assemble finite-window and
positive-window lower/upper comparison functions, then feed the existing
local-log-tail comparison-integral receiver through this alias. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0ASignedChunkedComparisonIntegralPayloadRecenterWithCenterError :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0APositiveFiniteComparisonIntegralPositiveTailWindowLocalLogTailRecenterWithCenterError

/-- Single payload object for the signed chunked comparison-integral `A`
route.  A generated backend should define the lower/upper comparison functions
and prove these fields; this record then feeds the checked local recenter
receiver without exposing a 24-premise call site. -/
structure Step33ASignedChunkedComparisonIntegralPayload where
  primaryFiniteLowerF : CoeffIndex23 → Real → Real
  primaryFiniteUpperF : CoeffIndex23 → Real → Real
  primaryTailLowerF : CoeffIndex23 → Real → Real
  primaryTailUpperF : CoeffIndex23 → Real → Real
  controlFiniteLowerF : CoeffIndex23 → Real → Real
  controlFiniteUpperF : CoeffIndex23 → Real → Real
  controlTailLowerF : CoeffIndex23 → Real → Real
  controlTailUpperF : CoeffIndex23 → Real → Real
  primaryFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (primaryFiniteLowerF n)
      (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff)
  primaryFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (primaryFiniteUpperF n)
      (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff)
  primaryFiniteLower : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
      primaryFiniteLowerF n t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryFiniteUpper : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryFiniteUpperF n t
  primaryFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
      2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t
  primaryFiniteUpperBound : ∀ n : CoeffIndex23,
    2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n
  primaryTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (primaryTailLowerF n)
      (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd)
  primaryTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (primaryTailUpperF n)
      (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd)
  primaryTailLower : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
      primaryTailLowerF n t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryTailUpper : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryTailUpperF n t
  primaryTailWindowLower : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailLowerF n t
  primaryTailWindowUpper : ∀ n : CoeffIndex23,
    ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailUpperF n t <= Q3.PSDpd.primaryK11AnalyticATailWindowUpper n
  controlFiniteLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (controlFiniteLowerF n)
      (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff)
  controlFiniteUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (controlFiniteUpperF n)
      (Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff)
  controlFiniteLower : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
      controlFiniteLowerF n t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlFiniteUpper : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlFiniteUpperF n t
  controlFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
      2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t
  controlFiniteUpperBound : ∀ n : CoeffIndex23,
    2 * ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n
  controlTailLowerInt : ∀ n : CoeffIndex23,
    IntegrableOn (controlTailLowerF n)
      (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd)
  controlTailUpperInt : ∀ n : CoeffIndex23,
    IntegrableOn (controlTailUpperF n)
      (Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd)
  controlTailLower : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
      controlTailLowerF n t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlTailUpper : ∀ n : CoeffIndex23,
    ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlTailUpperF n t
  controlTailWindowLower : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
      ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailLowerF n t
  controlTailWindowUpper : ∀ n : CoeffIndex23,
    ∫ t in Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailUpperF n t <= Q3.PSDpd.controlK9AnalyticATailWindowUpper n

/-- Feed a generated signed chunked comparison-integral payload into the
checked A finite-tail recenter route.  This theorem intentionally leaves the
payload proof-producing obligations in one record. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0ASignedChunkedComparisonIntegralPayload
    (payload : Step33ASignedChunkedComparisonIntegralPayload) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0ASignedChunkedComparisonIntegralPayloadRecenterWithCenterError
    payload.primaryFiniteLowerF payload.primaryFiniteUpperF
    payload.primaryTailLowerF payload.primaryTailUpperF
    payload.controlFiniteLowerF payload.controlFiniteUpperF
    payload.controlTailLowerF payload.controlTailUpperF
    payload.primaryFiniteLowerInt payload.primaryFiniteUpperInt
    payload.primaryFiniteLower payload.primaryFiniteUpper
    payload.primaryFiniteLowerBound payload.primaryFiniteUpperBound
    payload.primaryTailLowerInt payload.primaryTailUpperInt
    payload.primaryTailLower payload.primaryTailUpper
    payload.primaryTailWindowLower payload.primaryTailWindowUpper
    payload.controlFiniteLowerInt payload.controlFiniteUpperInt
    payload.controlFiniteLower payload.controlFiniteUpper
    payload.controlFiniteLowerBound payload.controlFiniteUpperBound
    payload.controlTailLowerInt payload.controlTailUpperInt
    payload.controlTailLower payload.controlTailUpper
    payload.controlTailWindowLower payload.controlTailWindowUpper

/-- Local proof-remainder support bridge.  The positive-tail-window inputs are
already packaged certs against the local proof-only post-`520` radii, so this
surface can be fed by comparison-integral, whole-window pointwise, or
split-window pointwise payloads. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteComparisonPositiveTailWindowProofRemainderRecenterWithCenterError
    (primaryFiniteLowerF primaryFiniteUpperF
      controlFiniteLowerF controlFiniteUpperF :
        CoeffIndex23 → Real → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
      primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
    (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      primaryTailWindow)
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
      controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
    (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      controlTailWindow)

/-- Local proof-remainder support bridge with already-packaged finite-window
and positive-tail-window certs.  This is the shared target for pointwise,
two-piece pointwise, and comparison-integral A window generators. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primaryTailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (controlTailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    primary_hA_finite
    (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      primaryTailWindow)
    control_hA_finite
    (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      controlTailWindow)

/-- Same local proof-remainder bridge, routed through the explicit analytic
finite-tail cert assembly surface.  This names the Step33A.1-A gate before the
A hbox recenter receiver consumes it. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailFromPositiveTailWindowProofRemainderRecenterWithCenterError
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primaryTailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (controlTailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailRecenterWithCenterError
    (Q3.PSDpd.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      primary_hA_finite primaryTailWindow)
    (Q3.PSDpd.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      control_hA_finite controlTailWindow)

/-- Single payload object for the folded positive-window `A` route.  The
generated side only has to prove positive-window certificates and the final
finite arithmetic comparisons; this receiver adds the checked finite-window
doubling, tail proof-remainder, and local A recenter bridge. -/
structure Step33AFoldedWindowPayload where
  primaryFinitePositiveLower : CoeffIndex23 → Real
  primaryFinitePositiveUpper : CoeffIndex23 → Real
  controlFinitePositiveLower : CoeffIndex23 → Real
  controlFinitePositiveUpper : CoeffIndex23 → Real
  primaryFiniteWindow : ∀ n : CoeffIndex23,
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      0 Q3.PSDpd.archAFiniteTailCutoff
      (primaryFinitePositiveLower n) (primaryFinitePositiveUpper n)
  primaryFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
      2 * primaryFinitePositiveLower n
  primaryFiniteUpperBound : ∀ n : CoeffIndex23,
    2 * primaryFinitePositiveUpper n <=
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper n
  primaryTailWindow : ∀ n : CoeffIndex23,
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
      (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
      (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
  controlFiniteWindow : ∀ n : CoeffIndex23,
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      0 Q3.PSDpd.archAFiniteTailCutoff
      (controlFinitePositiveLower n) (controlFinitePositiveUpper n)
  controlFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
      2 * controlFinitePositiveLower n
  controlFiniteUpperBound : ∀ n : CoeffIndex23,
    2 * controlFinitePositiveUpper n <=
      Q3.PSDpd.controlK9AnalyticAFiniteUpper n
  controlTailWindow : ∀ n : CoeffIndex23,
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
      (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
      (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)

/-- Build the folded `A` payload from generated positive-window certificates.
The finite arithmetic fields are the exact positive-half targets generated by
`PSD_CenteredCoeffAnalyticAFiniteTailArithmeticImport`; only the four analytic
window certificate families remain. -/
def step33AFoldedWindowPayload_of_generatedAWindowCerts
    (primaryFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n))
    (primaryTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n))
    (controlFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n))
    (controlTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)) :
    Step33AFoldedWindowPayload :=
  { primaryFinitePositiveLower := Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
    primaryFinitePositiveUpper := Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper
    controlFinitePositiveLower := Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
    controlFinitePositiveUpper := Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper
    primaryFiniteWindow := primaryFiniteWindow
    primaryFiniteLowerBound := Q3.PSDpd.primaryK11AnalyticAFinitePositiveLowerBound_generated
    primaryFiniteUpperBound := Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpperBound_generated
    primaryTailWindow := primaryTailWindow
    controlFiniteWindow := controlFiniteWindow
    controlFiniteLowerBound := Q3.PSDpd.controlK9AnalyticAFinitePositiveLowerBound_generated
    controlFiniteUpperBound := Q3.PSDpd.controlK9AnalyticAFinitePositiveUpperBound_generated
    controlTailWindow := controlTailWindow }

/-- A lower-level signed comparison-integral payload also produces the folded
positive-window payload.  This keeps the folded surface as the canonical Step33
gate while preserving the existing signed-chunk generator contract. -/
def step33AFoldedWindowPayload_of_signedChunkedComparisonIntegralPayload
    (payload : Step33ASignedChunkedComparisonIntegralPayload) :
    Step33AFoldedWindowPayload := by
  refine
    { primaryFinitePositiveLower := fun n =>
        ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.primaryFiniteLowerF n t
      primaryFinitePositiveUpper := fun n =>
        ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.primaryFiniteUpperF n t
      controlFinitePositiveLower := fun n =>
        ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.controlFiniteLowerF n t
      controlFinitePositiveUpper := fun n =>
        ∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.controlFiniteUpperF n t
      primaryFiniteWindow := ?_
      primaryFiniteLowerBound := ?_
      primaryFiniteUpperBound := ?_
      primaryTailWindow := ?_
      controlFiniteWindow := ?_
      controlFiniteLowerBound := ?_
      controlFiniteUpperBound := ?_
      controlTailWindow := ?_ }
  · intro n
    exact
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.primaryFiniteLowerF n t)
        (∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.primaryFiniteUpperF n t)
        (payload.primaryFiniteLowerF n) (payload.primaryFiniteUpperF n)
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (by norm_num) (by norm_num))
        (payload.primaryFiniteLowerInt n)
        (payload.primaryFiniteUpperInt n)
        (fun t ht => payload.primaryFiniteLower n t ht)
        (fun t ht => payload.primaryFiniteUpper n t ht)
        (le_rfl)
        (le_rfl)
  · intro n
    exact payload.primaryFiniteLowerBound n
  · intro n
    exact payload.primaryFiniteUpperBound n
  · intro n
    exact
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
        (payload.primaryTailLowerF n) (payload.primaryTailUpperF n)
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (by norm_num) (by norm_num))
        (payload.primaryTailLowerInt n)
        (payload.primaryTailUpperInt n)
        (fun t ht => payload.primaryTailLower n t ht)
        (fun t ht => payload.primaryTailUpper n t ht)
        (payload.primaryTailWindowLower n)
        (payload.primaryTailWindowUpper n)
  · intro n
    exact
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.controlFiniteLowerF n t)
        (∫ t in Set.Ioc 0 Q3.PSDpd.archAFiniteTailCutoff,
          payload.controlFiniteUpperF n t)
        (payload.controlFiniteLowerF n) (payload.controlFiniteUpperF n)
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (by norm_num) (by norm_num))
        (payload.controlFiniteLowerInt n)
        (payload.controlFiniteUpperInt n)
        (fun t ht => payload.controlFiniteLower n t ht)
        (fun t ht => payload.controlFiniteUpper n t ht)
        (le_rfl)
        (le_rfl)
  · intro n
    exact payload.controlFiniteLowerBound n
  · intro n
    exact payload.controlFiniteUpperBound n
  · intro n
    exact
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)
        (payload.controlTailLowerF n) (payload.controlTailUpperF n)
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (by norm_num) (by norm_num))
        (payload.controlTailLowerInt n)
        (payload.controlTailUpperInt n)
        (fun t ht => payload.controlTailLower n t ht)
        (fun t ht => payload.controlTailUpper n t ht)
        (payload.controlTailWindowLower n)
        (payload.controlTailWindowUpper n)

/-- Primary finite-window cert extracted from a folded `A` payload. -/
theorem primaryK11AnalyticAFinitePartBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      payload.primaryFiniteWindow payload.primaryFiniteLowerBound
      payload.primaryFiniteUpperBound

/-- Primary positive-tail-window cert extracted from a folded `A` payload. -/
theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.primaryK11AnalyticATailWindowLower
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      payload.primaryTailWindow
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520)

/-- Primary finite-tail analytic cert extracted from a folded `A` payload. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper
      Q3.PSDpd.primaryK11AnalyticATailRadius := by
  exact
    Q3.PSDpd.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (primaryK11AnalyticAFinitePartBoundsCert_of_foldedWindowPayload payload)
      (primaryK11AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload payload)

/-- Primary A absolute-distance hbox cert extracted from a folded `A` payload. -/
theorem primaryK11AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert := by
  exact
    Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
      (primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload payload)

/-- Primary A matrix hbox extracted from a folded `A` payload. -/
theorem primaryK11AnalyticA_entry_hbox_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius := by
  exact
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
      (primaryK11AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload payload)

/-- Control finite-window cert extracted from a folded `A` payload. -/
theorem controlK9AnalyticAFinitePartBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      payload.controlFiniteWindow payload.controlFiniteLowerBound
      payload.controlFiniteUpperBound

/-- Control positive-tail-window cert extracted from a folded `A` payload. -/
theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.controlK9AnalyticATailWindowLower
      Q3.PSDpd.controlK9AnalyticATailWindowUpper
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      payload.controlTailWindow
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520)

/-- Control finite-tail analytic cert extracted from a folded `A` payload. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper
      Q3.PSDpd.controlK9AnalyticATailRadius := by
  exact
    Q3.PSDpd.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (controlK9AnalyticAFinitePartBoundsCert_of_foldedWindowPayload payload)
      (controlK9AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload payload)

/-- Control A absolute-distance hbox cert extracted from a folded `A` payload. -/
theorem controlK9AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert := by
  exact
    Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
      (controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload payload)

/-- Control A matrix hbox extracted from a folded `A` payload. -/
theorem controlK9AnalyticA_entry_hbox_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius := by
  exact
    CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
      (controlK9AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload payload)

/-- Generated primary P0 matrix hbox used by the folded A payload route. -/
theorem primaryK11AnalyticP0_entry_hbox_generated :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius := by
  exact
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated))

/-- Generated control P0 matrix hbox used by the folded A payload route. -/
theorem controlK9AnalyticP0_entry_hbox_generated :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius := by
  exact
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
          Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated))

/-- Step33A certificate extracted from a folded `A` payload plus the generated
P/P0 payloads.  This is the named 33A landing surface for the current A gate. -/
theorem activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      (primaryK11AnalyticA_entry_hbox_of_foldedWindowPayload payload)
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primaryK11AnalyticP0_entry_hbox_generated
      (controlK9AnalyticA_entry_hbox_of_foldedWindowPayload payload)
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      controlK9AnalyticP0_entry_hbox_generated

/-- Step33B finite analytic Weil positivity extracted from a folded `A`
payload through the named Step33A certificate. -/
theorem psd_step33_finite_analytic_weil_positivity_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload payload) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload payload)

/-- Step33C singleton directed-family handoff extracted from a folded `A`
payload through the named Step33A certificate. -/
theorem psd_step33_singleton_directed_family_handoff_of_foldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload payload) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload payload)

/-- Step33A certificate extracted from the four generated `A` window cert
families.  This is the narrow active remaining premise surface for the folded
payload route. -/
theorem activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts
    (primaryFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n))
    (primaryTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n))
    (controlFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n))
    (controlTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload
      (step33AFoldedWindowPayload_of_generatedAWindowCerts
        primaryFiniteWindow primaryTailWindow controlFiniteWindow controlTailWindow)

/-- Step33B from the four generated `A` window cert families. -/
theorem psd_step33_finite_analytic_weil_positivity_of_generatedAWindowCerts
    (primaryFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n))
    (primaryTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n))
    (controlFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n))
    (controlTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts
        primaryFiniteWindow primaryTailWindow controlFiniteWindow controlTailWindow) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts
        primaryFiniteWindow primaryTailWindow controlFiniteWindow controlTailWindow)

/-- Step33C from the four generated `A` window cert families. -/
theorem psd_step33_singleton_directed_family_handoff_of_generatedAWindowCerts
    (primaryFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n))
    (primaryTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n))
    (controlFiniteWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n))
    (controlTailWindow : ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts
        primaryFiniteWindow primaryTailWindow controlFiniteWindow controlTailWindow) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts
        primaryFiniteWindow primaryTailWindow controlFiniteWindow controlTailWindow)

/-- Generated chunk payload for the active Step33A.1-A route.  Each of the four
positive-window families is supplied as 26 adjacent chunks of length 10; this
receiver folds them into the existing folded-window payload without touching
global `A` radii or generated radius-floor data. -/
structure Step33AChunkedWindowPayload where
  primaryFiniteChunkLower : CoeffIndex23 → Nat → Real
  primaryFiniteChunkUpper : CoeffIndex23 → Nat → Real
  primaryTailChunkLower : CoeffIndex23 → Nat → Real
  primaryTailChunkUpper : CoeffIndex23 → Nat → Real
  controlFiniteChunkLower : CoeffIndex23 → Nat → Real
  controlFiniteChunkUpper : CoeffIndex23 → Nat → Real
  controlTailChunkLower : CoeffIndex23 → Nat → Real
  controlTailChunkUpper : CoeffIndex23 → Nat → Real
  primaryFiniteChunks : ∀ n : CoeffIndex23, ∀ (i : Nat), i < 26 →
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      (0 + (10 : Real) * (i : Real))
      (0 + (10 : Real) * ((i + 1 : Nat) : Real))
      (primaryFiniteChunkLower n i) (primaryFiniteChunkUpper n i)
  primaryFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => primaryFiniteChunkLower n i)
  primaryFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryFiniteChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n
  primaryTailChunks : ∀ n : CoeffIndex23, ∀ (i : Nat), i < 26 →
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (primaryTailChunkLower n i) (primaryTailChunkUpper n i)
  primaryTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => primaryTailChunkLower n i)
  primaryTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryTailChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper n
  controlFiniteChunks : ∀ n : CoeffIndex23, ∀ (i : Nat), i < 26 →
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      (0 + (10 : Real) * (i : Real))
      (0 + (10 : Real) * ((i + 1 : Nat) : Real))
      (controlFiniteChunkLower n i) (controlFiniteChunkUpper n i)
  controlFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => controlFiniteChunkLower n i)
  controlFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlFiniteChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n
  controlTailChunks : ∀ n : CoeffIndex23, ∀ (i : Nat), i < 26 →
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * ((i + 1 : Nat) : Real))
      (controlTailChunkLower n i) (controlTailChunkUpper n i)
  controlTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => controlTailChunkLower n i)
  controlTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlTailChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticATailWindowUpper n

private theorem step33A_chunk_left_le_right
    (L step : Real) (hstep : 0 <= step) (i : Nat) :
    L + step * (i : Real) <=
      L + step * (((i + 1 : Nat) : Real)) := by
  have hi : (i : Real) <= (((i + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.le_succ i
  have hmul : step * (i : Real) <=
      step * (((i + 1 : Nat) : Real)) :=
    mul_le_mul_of_nonneg_left hi hstep
  nlinarith

/-- Pointwise-constant version of the 26-chunk `A` window payload.  This is
the next proof-producing landing surface for generated Arch `A` bounds: each
10-wide chunk supplies constant pointwise lower/upper bounds, scalar
length-times-bound comparisons, and final chunk-sum comparisons. -/
structure Step33AChunkedPointwiseWindowPayload where
  primaryFiniteChunkLower : CoeffIndex23 → Nat → Real
  primaryFiniteChunkUpper : CoeffIndex23 → Nat → Real
  primaryFinitePointLower : CoeffIndex23 → Nat → Real
  primaryFinitePointUpper : CoeffIndex23 → Nat → Real
  primaryTailChunkLower : CoeffIndex23 → Nat → Real
  primaryTailChunkUpper : CoeffIndex23 → Nat → Real
  primaryTailPointLower : CoeffIndex23 → Nat → Real
  primaryTailPointUpper : CoeffIndex23 → Nat → Real
  controlFiniteChunkLower : CoeffIndex23 → Nat → Real
  controlFiniteChunkUpper : CoeffIndex23 → Nat → Real
  controlFinitePointLower : CoeffIndex23 → Nat → Real
  controlFinitePointUpper : CoeffIndex23 → Nat → Real
  controlTailChunkLower : CoeffIndex23 → Nat → Real
  controlTailChunkUpper : CoeffIndex23 → Nat → Real
  controlTailPointLower : CoeffIndex23 → Nat → Real
  controlTailPointUpper : CoeffIndex23 → Nat → Real
  primaryFinitePointLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryFinitePointLower n i <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryFinitePointUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryFinitePointUpper n i
  primaryFiniteChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    primaryFiniteChunkLower n i <=
      ((0 + (10 : Real) * ((i + 1 : Nat) : Real)) -
          (0 + (10 : Real) * (i : Real))) *
        primaryFinitePointLower n i
  primaryFiniteChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ((0 + (10 : Real) * ((i + 1 : Nat) : Real)) -
        (0 + (10 : Real) * (i : Real))) *
      primaryFinitePointUpper n i <= primaryFiniteChunkUpper n i
  primaryFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => primaryFiniteChunkLower n i)
  primaryFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryFiniteChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n
  primaryTailPointLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryTailPointLower n i <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryTailPointUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryTailPointUpper n i
  primaryTailChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    primaryTailChunkLower n i <=
      ((Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)) -
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))) *
        primaryTailPointLower n i
  primaryTailChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ((Q3.PSDpd.archAFiniteTailCutoff +
        (10 : Real) * ((i + 1 : Nat) : Real)) -
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))) *
      primaryTailPointUpper n i <= primaryTailChunkUpper n i
  primaryTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => primaryTailChunkLower n i)
  primaryTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryTailChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper n
  controlFinitePointLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      controlFinitePointLower n i <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlFinitePointUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlFinitePointUpper n i
  controlFiniteChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    controlFiniteChunkLower n i <=
      ((0 + (10 : Real) * ((i + 1 : Nat) : Real)) -
          (0 + (10 : Real) * (i : Real))) *
        controlFinitePointLower n i
  controlFiniteChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ((0 + (10 : Real) * ((i + 1 : Nat) : Real)) -
        (0 + (10 : Real) * (i : Real))) *
      controlFinitePointUpper n i <= controlFiniteChunkUpper n i
  controlFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => controlFiniteChunkLower n i)
  controlFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlFiniteChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n
  controlTailPointLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      controlTailPointLower n i <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlTailPointUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlTailPointUpper n i
  controlTailChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    controlTailChunkLower n i <=
      ((Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)) -
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))) *
        controlTailPointLower n i
  controlTailChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ((Q3.PSDpd.archAFiniteTailCutoff +
        (10 : Real) * ((i + 1 : Nat) : Real)) -
      (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))) *
      controlTailPointUpper n i <= controlTailChunkUpper n i
  controlTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => controlTailChunkLower n i)
  controlTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlTailChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticATailWindowUpper n

/-- Convert pointwise-constant chunk data into the canonical chunked window
payload. -/
def step33AChunkedWindowPayload_of_chunkedPointwiseWindowPayload
    (payload : Step33AChunkedPointwiseWindowPayload) :
    Step33AChunkedWindowPayload :=
  { primaryFiniteChunkLower := payload.primaryFiniteChunkLower
    primaryFiniteChunkUpper := payload.primaryFiniteChunkUpper
    primaryTailChunkLower := payload.primaryTailChunkLower
    primaryTailChunkUpper := payload.primaryTailChunkUpper
    controlFiniteChunkLower := payload.controlFiniteChunkLower
    controlFiniteChunkUpper := payload.controlFiniteChunkUpper
    controlTailChunkLower := payload.controlTailChunkLower
    controlTailChunkUpper := payload.controlTailChunkUpper
    primaryFiniteChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.primaryFinitePointLower n i)
          (payload.primaryFinitePointUpper n i)
          (payload.primaryFiniteChunkLower n i)
          (payload.primaryFiniteChunkUpper n i)
          (step33A_chunk_left_le_right 0 (10 : Real) (by norm_num) i)
          (payload.primaryFinitePointLowerBound n i hi)
          (payload.primaryFinitePointUpperBound n i hi)
          (payload.primaryFiniteChunkLowerBound n i hi)
          (payload.primaryFiniteChunkUpperBound n i hi)
    primaryFiniteLowerBound := payload.primaryFiniteLowerBound
    primaryFiniteUpperBound := payload.primaryFiniteUpperBound
    primaryTailChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.primaryTailPointLower n i)
          (payload.primaryTailPointUpper n i)
          (payload.primaryTailChunkLower n i)
          (payload.primaryTailChunkUpper n i)
          (step33A_chunk_left_le_right Q3.PSDpd.archAFiniteTailCutoff
            (10 : Real) (by norm_num) i)
          (payload.primaryTailPointLowerBound n i hi)
          (payload.primaryTailPointUpperBound n i hi)
          (payload.primaryTailChunkLowerBound n i hi)
          (payload.primaryTailChunkUpperBound n i hi)
    primaryTailLowerBound := payload.primaryTailLowerBound
    primaryTailUpperBound := payload.primaryTailUpperBound
    controlFiniteChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.controlFinitePointLower n i)
          (payload.controlFinitePointUpper n i)
          (payload.controlFiniteChunkLower n i)
          (payload.controlFiniteChunkUpper n i)
          (step33A_chunk_left_le_right 0 (10 : Real) (by norm_num) i)
          (payload.controlFinitePointLowerBound n i hi)
          (payload.controlFinitePointUpperBound n i hi)
          (payload.controlFiniteChunkLowerBound n i hi)
          (payload.controlFiniteChunkUpperBound n i hi)
    controlFiniteLowerBound := payload.controlFiniteLowerBound
    controlFiniteUpperBound := payload.controlFiniteUpperBound
    controlTailChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.controlTailPointLower n i)
          (payload.controlTailPointUpper n i)
          (payload.controlTailChunkLower n i)
          (payload.controlTailChunkUpper n i)
          (step33A_chunk_left_le_right Q3.PSDpd.archAFiniteTailCutoff
            (10 : Real) (by norm_num) i)
          (payload.controlTailPointLowerBound n i hi)
          (payload.controlTailPointUpperBound n i hi)
          (payload.controlTailChunkLowerBound n i hi)
          (payload.controlTailChunkUpperBound n i hi)
    controlTailLowerBound := payload.controlTailLowerBound
    controlTailUpperBound := payload.controlTailUpperBound }

/-- Chunked comparison-integral version of the `A` window payload.  This is the
active proof-producing surface after the pointwise-constant diagnostic: each
10-wide chunk supplies comparison functions with integrability, pointwise
dominance, and scalar integral comparisons. -/
structure Step33AChunkedComparisonIntegralPayload where
  primaryFiniteChunkLower : CoeffIndex23 → Nat → Real
  primaryFiniteChunkUpper : CoeffIndex23 → Nat → Real
  primaryFiniteLowerF : CoeffIndex23 → Nat → Real → Real
  primaryFiniteUpperF : CoeffIndex23 → Nat → Real → Real
  primaryTailChunkLower : CoeffIndex23 → Nat → Real
  primaryTailChunkUpper : CoeffIndex23 → Nat → Real
  primaryTailLowerF : CoeffIndex23 → Nat → Real → Real
  primaryTailUpperF : CoeffIndex23 → Nat → Real → Real
  controlFiniteChunkLower : CoeffIndex23 → Nat → Real
  controlFiniteChunkUpper : CoeffIndex23 → Nat → Real
  controlFiniteLowerF : CoeffIndex23 → Nat → Real → Real
  controlFiniteUpperF : CoeffIndex23 → Nat → Real → Real
  controlTailChunkLower : CoeffIndex23 → Nat → Real
  controlTailChunkUpper : CoeffIndex23 → Nat → Real
  controlTailLowerF : CoeffIndex23 → Nat → Real → Real
  controlTailUpperF : CoeffIndex23 → Nat → Real → Real
  primaryFiniteLowerInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (primaryFiniteLowerF n i)
      (Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)))
  primaryFiniteUpperInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (primaryFiniteUpperF n i)
      (Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)))
  primaryFiniteLower : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryFiniteLowerF n i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryFiniteUpper : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryFiniteUpperF n i t
  primaryFiniteChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    primaryFiniteChunkLower n i <=
      ∫ t in Set.Ioc (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
        primaryFiniteLowerF n i t
  primaryFiniteChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryFiniteUpperF n i t <= primaryFiniteChunkUpper n i
  primaryFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => primaryFiniteChunkLower n i)
  primaryFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryFiniteChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n
  primaryTailLowerInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (primaryTailLowerF n i)
      (Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)))
  primaryTailUpperInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (primaryTailUpperF n i)
      (Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)))
  primaryTailLower : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryTailLowerF n i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  primaryTailUpper : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        primaryTailUpperF n i t
  primaryTailChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    primaryTailChunkLower n i <=
      ∫ t in Set.Ioc
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real)),
        primaryTailLowerF n i t
  primaryTailChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      primaryTailUpperF n i t <= primaryTailChunkUpper n i
  primaryTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => primaryTailChunkLower n i)
  primaryTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => primaryTailChunkUpper n i) <=
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper n
  controlFiniteLowerInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (controlFiniteLowerF n i)
      (Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)))
  controlFiniteUpperInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (controlFiniteUpperF n i)
      (Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)))
  controlFiniteLower : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      controlFiniteLowerF n i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlFiniteUpper : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlFiniteUpperF n i t
  controlFiniteChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    controlFiniteChunkLower n i <=
      ∫ t in Set.Ioc (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
        controlFiniteLowerF n i t
  controlFiniteChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc (0 + (10 : Real) * (i : Real))
        (0 + (10 : Real) * ((i + 1 : Nat) : Real)),
      controlFiniteUpperF n i t <= controlFiniteChunkUpper n i
  controlFiniteLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n <=
      (Finset.range 26).sum (fun i => controlFiniteChunkLower n i)
  controlFiniteUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlFiniteChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n
  controlTailLowerInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (controlTailLowerF n i)
      (Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)))
  controlTailUpperInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (controlTailUpperF n i)
      (Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)))
  controlTailLower : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      controlTailLowerF n i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  controlTailUpper : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        controlTailUpperF n i t
  controlTailChunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    controlTailChunkLower n i <=
      ∫ t in Set.Ioc
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real)),
        controlTailLowerF n i t
  controlTailChunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc
        (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real)),
      controlTailUpperF n i t <= controlTailChunkUpper n i
  controlTailLowerBound : ∀ n : CoeffIndex23,
    Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
      (Finset.range 26).sum (fun i => controlTailChunkLower n i)
  controlTailUpperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => controlTailChunkUpper n i) <=
      Q3.PSDpd.controlK9AnalyticATailWindowUpper n

/-- One family of the chunked comparison-integral `A` window payload.  This
keeps the proof-producing surface decomposable into the four independent
families: primary finite, primary tail, control finite, and control tail. -/
structure Step33AChunkedComparisonIntegralFamilyPayload
    (k : Nat) (L U : Nat → Real)
    (targetLower targetUpper : CoeffIndex23 → Real) where
  chunkLower : CoeffIndex23 → Nat → Real
  chunkUpper : CoeffIndex23 → Nat → Real
  lowerF : CoeffIndex23 → Nat → Real → Real
  upperF : CoeffIndex23 → Nat → Real → Real
  lowerInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (lowerF n i) (Set.Ioc (L i) (U i))
  upperInt : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    IntegrableOn (upperF n i) (Set.Ioc (L i) (U i))
  lower : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (L i) (U i),
      lowerF n i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  upper : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (L i) (U i),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF n i t
  chunkLowerBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    chunkLower n i <= ∫ t in Set.Ioc (L i) (U i), lowerF n i t
  chunkUpperBound : ∀ n : CoeffIndex23, ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc (L i) (U i), upperF n i t <= chunkUpper n i
  lowerBound : ∀ n : CoeffIndex23,
    targetLower n <= (Finset.range 26).sum (fun i => chunkLower n i)
  upperBound : ∀ n : CoeffIndex23,
    (Finset.range 26).sum (fun i => chunkUpper n i) <= targetUpper n

/-- One distance row of the chunked comparison-integral `A` window payload.
This is the delta-compressed generator surface: a proof producer can emit one
record per distance and then assemble the family without touching entry rows. -/
structure Step33AChunkedComparisonIntegralDistancePayload
    (k : Nat) (L U : Nat → Real)
    (targetLower targetUpper : CoeffIndex23 → Real)
    (n : CoeffIndex23) where
  chunkLower : Nat → Real
  chunkUpper : Nat → Real
  lowerF : Nat → Real → Real
  upperF : Nat → Real → Real
  lowerInt : ∀ i : Nat, i < 26 →
    IntegrableOn (lowerF i) (Set.Ioc (L i) (U i))
  upperInt : ∀ i : Nat, i < 26 →
    IntegrableOn (upperF i) (Set.Ioc (L i) (U i))
  lower : ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (L i) (U i),
      lowerF i t <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
  upper : ∀ i : Nat, i < 26 →
    ∀ t ∈ Set.Ioc (L i) (U i),
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
        upperF i t
  chunkLowerBound : ∀ i : Nat, i < 26 →
    chunkLower i <= ∫ t in Set.Ioc (L i) (U i), lowerF i t
  chunkUpperBound : ∀ i : Nat, i < 26 →
    ∫ t in Set.Ioc (L i) (U i), upperF i t <= chunkUpper i
  lowerBound :
    targetLower n <= (Finset.range 26).sum (fun i => chunkLower i)
  upperBound :
    (Finset.range 26).sum (fun i => chunkUpper i) <= targetUpper n

/-- Build one distance row by using the analytic `A` integrand itself as both
comparison functions.  This keeps the generated payload focused on scalar chunk
integral enclosures and the final two row-sum comparisons. -/
def step33AChunkedComparisonIntegralDistancePayload_of_integrand_chunk_bounds
    {k : Nat} {L U : Nat → Real}
    {targetLower targetUpper : CoeffIndex23 → Real}
    (n : CoeffIndex23)
    (chunkLower chunkUpper : Nat → Real)
    (hk : 0 < k)
    (hChunkLower : ∀ i : Nat, i < 26 →
      chunkLower i <=
        ∫ t in Set.Ioc (L i) (U i),
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hChunkUpper : ∀ i : Nat, i < 26 →
      (∫ t in Set.Ioc (L i) (U i),
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t) <=
        chunkUpper i)
    (hLowerBound :
      targetLower n <= (Finset.range 26).sum (fun i => chunkLower i))
    (hUpperBound :
      (Finset.range 26).sum (fun i => chunkUpper i) <= targetUpper n) :
    Step33AChunkedComparisonIntegralDistancePayload
      k L U targetLower targetUpper n :=
  { chunkLower := chunkLower
    chunkUpper := chunkUpper
    lowerF := fun _ t =>
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
        k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
    upperF := fun _ t =>
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
        k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t
    lowerInt := by
      intro i hi
      exact
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          hk (by norm_num)).integrableOn
    upperInt := by
      intro i hi
      exact
        (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
          k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          hk (by norm_num)).integrableOn
    lower := by
      intro i hi t ht
      exact le_rfl
    upper := by
      intro i hi t ht
      exact le_rfl
    chunkLowerBound := by
      intro i hi
      simpa using hChunkLower i hi
    chunkUpperBound := by
      intro i hi
      simpa using hChunkUpper i hi
    lowerBound := hLowerBound
    upperBound := hUpperBound }

/-- Assemble 23 distance rows into one chunked comparison-integral family
payload. -/
def step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
    {k : Nat} {L U : Nat → Real}
    {targetLower targetUpper : CoeffIndex23 → Real}
    (payload : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        k L U targetLower targetUpper n) :
    Step33AChunkedComparisonIntegralFamilyPayload
      k L U targetLower targetUpper :=
  { chunkLower := fun n => (payload n).chunkLower
    chunkUpper := fun n => (payload n).chunkUpper
    lowerF := fun n => (payload n).lowerF
    upperF := fun n => (payload n).upperF
    lowerInt := fun n i hi => (payload n).lowerInt i hi
    upperInt := fun n i hi => (payload n).upperInt i hi
    lower := fun n i hi => (payload n).lower i hi
    upper := fun n i hi => (payload n).upper i hi
    chunkLowerBound := fun n i hi => (payload n).chunkLowerBound i hi
    chunkUpperBound := fun n i hi => (payload n).chunkUpperBound i hi
    lowerBound := fun n => (payload n).lowerBound
    upperBound := fun n => (payload n).upperBound }

/-- Assemble the four independent chunked comparison-integral families into
the monolithic payload consumed by the existing Step33A/B/C wrappers. -/
def step33AChunkedComparisonIntegralPayload_of_familyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper)
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    Step33AChunkedComparisonIntegralPayload :=
  { primaryFiniteChunkLower := primaryFinite.chunkLower
    primaryFiniteChunkUpper := primaryFinite.chunkUpper
    primaryFiniteLowerF := primaryFinite.lowerF
    primaryFiniteUpperF := primaryFinite.upperF
    primaryTailChunkLower := primaryTail.chunkLower
    primaryTailChunkUpper := primaryTail.chunkUpper
    primaryTailLowerF := primaryTail.lowerF
    primaryTailUpperF := primaryTail.upperF
    controlFiniteChunkLower := controlFinite.chunkLower
    controlFiniteChunkUpper := controlFinite.chunkUpper
    controlFiniteLowerF := controlFinite.lowerF
    controlFiniteUpperF := controlFinite.upperF
    controlTailChunkLower := controlTail.chunkLower
    controlTailChunkUpper := controlTail.chunkUpper
    controlTailLowerF := controlTail.lowerF
    controlTailUpperF := controlTail.upperF
    primaryFiniteLowerInt := primaryFinite.lowerInt
    primaryFiniteUpperInt := primaryFinite.upperInt
    primaryFiniteLower := primaryFinite.lower
    primaryFiniteUpper := primaryFinite.upper
    primaryFiniteChunkLowerBound := primaryFinite.chunkLowerBound
    primaryFiniteChunkUpperBound := primaryFinite.chunkUpperBound
    primaryFiniteLowerBound := primaryFinite.lowerBound
    primaryFiniteUpperBound := primaryFinite.upperBound
    primaryTailLowerInt := primaryTail.lowerInt
    primaryTailUpperInt := primaryTail.upperInt
    primaryTailLower := primaryTail.lower
    primaryTailUpper := primaryTail.upper
    primaryTailChunkLowerBound := primaryTail.chunkLowerBound
    primaryTailChunkUpperBound := primaryTail.chunkUpperBound
    primaryTailLowerBound := primaryTail.lowerBound
    primaryTailUpperBound := primaryTail.upperBound
    controlFiniteLowerInt := controlFinite.lowerInt
    controlFiniteUpperInt := controlFinite.upperInt
    controlFiniteLower := controlFinite.lower
    controlFiniteUpper := controlFinite.upper
    controlFiniteChunkLowerBound := controlFinite.chunkLowerBound
    controlFiniteChunkUpperBound := controlFinite.chunkUpperBound
    controlFiniteLowerBound := controlFinite.lowerBound
    controlFiniteUpperBound := controlFinite.upperBound
    controlTailLowerInt := controlTail.lowerInt
    controlTailUpperInt := controlTail.upperInt
    controlTailLower := controlTail.lower
    controlTailUpper := controlTail.upper
    controlTailChunkLowerBound := controlTail.chunkLowerBound
    controlTailChunkUpperBound := controlTail.chunkUpperBound
    controlTailLowerBound := controlTail.lowerBound
    controlTailUpperBound := controlTail.upperBound }

/-- Extract a positive-window certificate from one chunked comparison-integral
family.  This is the one-family proof-producing receiver: generated data prove
the 26 chunk comparison integrals and final sum bounds; Lean folds the adjacent
chunks into the requested window certificate. -/
theorem centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (k : Nat) (base step : Real)
    (targetLower targetUpper : CoeffIndex23 → Real)
    (payload :
      Step33AChunkedComparisonIntegralFamilyPayload
        k
        (fun i => base + step * (i : Real))
        (fun i => base + step * ((i + 1 : Nat) : Real))
        targetLower targetUpper)
    (hk : 0 < k)
    (hstep : 0 <= step)
    (n : CoeffIndex23) :
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
      k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      base (base + step * (26 : Real)) (targetLower n) (targetUpper n) := by
  exact
    CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
      k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
      base step (payload.chunkLower n) (payload.chunkUpper n) 26
      (targetLower n) (targetUpper n)
      (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
        k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        hk (by norm_num))
      hstep
      (by
        intro i hi
        exact
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
            k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (base + step * (i : Real))
            (base + step * ((i + 1 : Nat) : Real))
            (payload.chunkLower n i) (payload.chunkUpper n i)
            (payload.lowerF n i) (payload.upperF n i)
            (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
              k ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
              hk (by norm_num))
            (payload.lowerInt n i hi) (payload.upperInt n i hi)
            (payload.lower n i hi) (payload.upper n i hi)
            (payload.chunkLowerBound n i hi) (payload.chunkUpperBound n i hi))
      (by simpa using payload.lowerBound n)
      (by simpa using payload.upperBound n)

/-- Primary positive-half finite-window certificate extracted from its
chunked comparison-integral family. -/
theorem primaryK11AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper) :
    ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n) := by
  intro n
  have h :=
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
      11 0 (10 : Real)
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper
      primaryFinite (by norm_num) (by norm_num) n
  norm_num [Q3.PSDpd.archAFiniteTailCutoff] at h
  exact h

/-- Primary finite-window bounds certificate extracted from the positive-half
chunked comparison-integral family. -/
theorem primaryK11AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      (primaryK11AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        primaryFinite)
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveLowerBound_generated
      Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpperBound_generated

/-- Primary positive-tail-window part certificate extracted from its chunked
comparison-integral family. -/
theorem primaryK11AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper) :
    ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
        (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n) := by
  intro n
  have h :=
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
      11 Q3.PSDpd.archAFiniteTailCutoff (10 : Real)
      Q3.PSDpd.primaryK11AnalyticATailWindowLower
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper
      primaryTail (by norm_num) (by norm_num) n
  norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd] at h
  exact h

/-- Primary positive-tail-window bounds certificate extracted from the tail
chunked comparison-integral family, using the checked post-520 proof
remainder. -/
theorem primaryK11AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.primaryK11AnalyticATailWindowLower
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      (primaryK11AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        primaryTail)
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520)

/-- Primary finite-tail analytic bounds certificate extracted from the two
primary chunked comparison-integral families. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper
      Q3.PSDpd.primaryK11AnalyticATailRadius := by
  exact
    Q3.PSDpd.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (primaryK11AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        primaryFinite)
      (primaryK11AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        primaryTail)

/-- Control positive-half finite-window certificate extracted from its
chunked comparison-integral family. -/
theorem controlK9AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper) :
    ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        0 Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
        (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n) := by
  intro n
  have h :=
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
      9 0 (10 : Real)
      Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
      Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper
      controlFinite (by norm_num) (by norm_num) n
  norm_num [Q3.PSDpd.archAFiniteTailCutoff] at h
  exact h

/-- Control finite-window bounds certificate extracted from the positive-half
chunked comparison-integral family. -/
theorem controlK9AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      (controlK9AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        controlFinite)
      Q3.PSDpd.controlK9AnalyticAFinitePositiveLowerBound_generated
      Q3.PSDpd.controlK9AnalyticAFinitePositiveUpperBound_generated

/-- Control positive-tail-window part certificate extracted from its chunked
comparison-integral family. -/
theorem controlK9AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    ∀ n : CoeffIndex23,
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd
        (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
        (Q3.PSDpd.controlK9AnalyticATailWindowUpper n) := by
  intro n
  have h :=
    centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
      9 Q3.PSDpd.archAFiniteTailCutoff (10 : Real)
      Q3.PSDpd.controlK9AnalyticATailWindowLower
      Q3.PSDpd.controlK9AnalyticATailWindowUpper
      controlTail (by norm_num) (by norm_num) n
  norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd] at h
  exact h

/-- Control positive-tail-window bounds certificate extracted from the tail
chunked comparison-integral family, using the checked post-520 proof
remainder. -/
theorem controlK9AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.controlK9AnalyticATailWindowLower
      Q3.PSDpd.controlK9AnalyticATailWindowUpper
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius := by
  exact
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      (controlK9AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        controlTail)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520)

/-- Control finite-tail analytic bounds certificate extracted from the two
control chunked comparison-integral families. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper
      Q3.PSDpd.controlK9AnalyticATailRadius := by
  exact
    Q3.PSDpd.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (controlK9AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        controlFinite)
      (controlK9AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        controlTail)

/-- Primary finite-tail analytic bounds certificate extracted from
delta-compressed distance payloads. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper
      Q3.PSDpd.primaryK11AnalyticATailRadius := by
  exact
    primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryTail)

/-- Control finite-tail analytic bounds certificate extracted from
delta-compressed distance payloads. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralDistancePayloads
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper
      Q3.PSDpd.controlK9AnalyticATailRadius := by
  exact
    controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlTail)

/-- Convert chunked comparison-integral data into the canonical chunked window
payload. -/
def step33AChunkedWindowPayload_of_chunkedComparisonIntegralPayload
    (payload : Step33AChunkedComparisonIntegralPayload) :
    Step33AChunkedWindowPayload :=
  { primaryFiniteChunkLower := payload.primaryFiniteChunkLower
    primaryFiniteChunkUpper := payload.primaryFiniteChunkUpper
    primaryTailChunkLower := payload.primaryTailChunkLower
    primaryTailChunkUpper := payload.primaryTailChunkUpper
    controlFiniteChunkLower := payload.controlFiniteChunkLower
    controlFiniteChunkUpper := payload.controlFiniteChunkUpper
    controlTailChunkLower := payload.controlTailChunkLower
    controlTailChunkUpper := payload.controlTailChunkUpper
    primaryFiniteChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.primaryFiniteChunkLower n i)
          (payload.primaryFiniteChunkUpper n i)
          (payload.primaryFiniteLowerF n i)
          (payload.primaryFiniteUpperF n i)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (payload.primaryFiniteLowerInt n i hi)
          (payload.primaryFiniteUpperInt n i hi)
          (payload.primaryFiniteLower n i hi)
          (payload.primaryFiniteUpper n i hi)
          (payload.primaryFiniteChunkLowerBound n i hi)
          (payload.primaryFiniteChunkUpperBound n i hi)
    primaryFiniteLowerBound := payload.primaryFiniteLowerBound
    primaryFiniteUpperBound := payload.primaryFiniteUpperBound
    primaryTailChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.primaryTailChunkLower n i)
          (payload.primaryTailChunkUpper n i)
          (payload.primaryTailLowerF n i)
          (payload.primaryTailUpperF n i)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (payload.primaryTailLowerInt n i hi)
          (payload.primaryTailUpperInt n i hi)
          (payload.primaryTailLower n i hi)
          (payload.primaryTailUpper n i hi)
          (payload.primaryTailChunkLowerBound n i hi)
          (payload.primaryTailChunkUpperBound n i hi)
    primaryTailLowerBound := payload.primaryTailLowerBound
    primaryTailUpperBound := payload.primaryTailUpperBound
    controlFiniteChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (0 + (10 : Real) * (i : Real))
          (0 + (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.controlFiniteChunkLower n i)
          (payload.controlFiniteChunkUpper n i)
          (payload.controlFiniteLowerF n i)
          (payload.controlFiniteUpperF n i)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (payload.controlFiniteLowerInt n i hi)
          (payload.controlFiniteUpperInt n i hi)
          (payload.controlFiniteLower n i hi)
          (payload.controlFiniteUpper n i hi)
          (payload.controlFiniteChunkLowerBound n i hi)
          (payload.controlFiniteChunkUpperBound n i hi)
    controlFiniteLowerBound := payload.controlFiniteLowerBound
    controlFiniteUpperBound := payload.controlFiniteUpperBound
    controlTailChunks := by
      intro n i hi
      exact
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
          (Q3.PSDpd.archAFiniteTailCutoff +
            (10 : Real) * ((i + 1 : Nat) : Real))
          (payload.controlTailChunkLower n i)
          (payload.controlTailChunkUpper n i)
          (payload.controlTailLowerF n i)
          (payload.controlTailUpperF n i)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (payload.controlTailLowerInt n i hi)
          (payload.controlTailUpperInt n i hi)
          (payload.controlTailLower n i hi)
          (payload.controlTailUpper n i hi)
          (payload.controlTailChunkLowerBound n i hi)
          (payload.controlTailChunkUpperBound n i hi)
    controlTailLowerBound := payload.controlTailLowerBound
    controlTailUpperBound := payload.controlTailUpperBound }

/-- Fold the 26-chunk generated Step33A `A` payload into the canonical folded
window payload used by the local recenter route. -/
def step33AFoldedWindowPayload_of_chunkedWindowPayload
    (payload : Step33AChunkedWindowPayload) :
    Step33AFoldedWindowPayload :=
  { primaryFinitePositiveLower := Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
    primaryFinitePositiveUpper := Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper
    controlFinitePositiveLower := Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
    controlFinitePositiveUpper := Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper
    primaryFiniteWindow := by
      intro n
      have h :=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          0 (10 : Real)
          (payload.primaryFiniteChunkLower n) (payload.primaryFiniteChunkUpper n)
          26
          (Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower n)
          (Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (by norm_num)
          (payload.primaryFiniteChunks n)
          (payload.primaryFiniteLowerBound n)
          (payload.primaryFiniteUpperBound n)
      norm_num [Q3.PSDpd.archAFiniteTailCutoff] at h
      exact h
    primaryFiniteLowerBound := Q3.PSDpd.primaryK11AnalyticAFinitePositiveLowerBound_generated
    primaryFiniteUpperBound := Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpperBound_generated
    primaryTailWindow := by
      intro n
      have h :=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          Q3.PSDpd.archAFiniteTailCutoff (10 : Real)
          (payload.primaryTailChunkLower n) (payload.primaryTailChunkUpper n)
          26
          (Q3.PSDpd.primaryK11AnalyticATailWindowLower n)
          (Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (by norm_num)
          (payload.primaryTailChunks n)
          (payload.primaryTailLowerBound n)
          (payload.primaryTailUpperBound n)
      norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd] at h
      exact h
    controlFiniteWindow := by
      intro n
      have h :=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          0 (10 : Real)
          (payload.controlFiniteChunkLower n) (payload.controlFiniteChunkUpper n)
          26
          (Q3.PSDpd.controlK9AnalyticAFinitePositiveLower n)
          (Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (by norm_num)
          (payload.controlFiniteChunks n)
          (payload.controlFiniteLowerBound n)
          (payload.controlFiniteUpperBound n)
      norm_num [Q3.PSDpd.archAFiniteTailCutoff] at h
      exact h
    controlFiniteLowerBound := Q3.PSDpd.controlK9AnalyticAFinitePositiveLowerBound_generated
    controlFiniteUpperBound := Q3.PSDpd.controlK9AnalyticAFinitePositiveUpperBound_generated
    controlTailWindow := by
      intro n
      have h :=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          Q3.PSDpd.archAFiniteTailCutoff (10 : Real)
          (payload.controlTailChunkLower n) (payload.controlTailChunkUpper n)
          26
          (Q3.PSDpd.controlK9AnalyticATailWindowLower n)
          (Q3.PSDpd.controlK9AnalyticATailWindowUpper n)
          (CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand_integrable_of_pos_degree
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
            (by norm_num) (by norm_num))
          (by norm_num)
          (payload.controlTailChunks n)
          (payload.controlTailLowerBound n)
          (payload.controlTailUpperBound n)
      norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd] at h
      exact h }

/-- Step33A certificate extracted from the 26-chunk `A` window payload. -/
theorem activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload
    (payload : Step33AChunkedWindowPayload) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload
      (step33AFoldedWindowPayload_of_chunkedWindowPayload payload)

/-- Step33B finite analytic Weil positivity from the 26-chunk `A` payload. -/
theorem psd_step33_finite_analytic_weil_positivity_of_chunkedWindowPayload
    (payload : Step33AChunkedWindowPayload) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload payload) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload payload)

/-- Step33C singleton directed-family handoff from the 26-chunk `A` payload. -/
theorem psd_step33_singleton_directed_family_handoff_of_chunkedWindowPayload
    (payload : Step33AChunkedWindowPayload) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload payload) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload payload)

/-- Step33A certificate extracted from pointwise-constant chunk data. -/
theorem activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload
    (payload : Step33AChunkedPointwiseWindowPayload) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload
      (step33AChunkedWindowPayload_of_chunkedPointwiseWindowPayload payload)

/-- Step33B finite analytic Weil positivity from pointwise-constant chunk data. -/
theorem psd_step33_finite_analytic_weil_positivity_of_chunkedPointwiseWindowPayload
    (payload : Step33AChunkedPointwiseWindowPayload) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload payload) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload payload)

/-- Step33C singleton directed-family handoff from pointwise-constant chunk data. -/
theorem psd_step33_singleton_directed_family_handoff_of_chunkedPointwiseWindowPayload
    (payload : Step33AChunkedPointwiseWindowPayload) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload payload) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload payload)

/-- Step33A certificate extracted from chunked comparison-integral data. -/
theorem activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload
    (payload : Step33AChunkedComparisonIntegralPayload) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload
      (step33AChunkedWindowPayload_of_chunkedComparisonIntegralPayload payload)

/-- Step33B finite analytic Weil positivity from chunked comparison-integral data. -/
theorem psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralPayload
    (payload : Step33AChunkedComparisonIntegralPayload) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload payload) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload payload)

/-- Step33C singleton directed-family handoff from chunked comparison-integral data. -/
theorem psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralPayload
    (payload : Step33AChunkedComparisonIntegralPayload) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload payload) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload payload)

/-- Step33A certificate extracted from four independent chunked
comparison-integral families. -/
theorem activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper)
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload
      (step33AChunkedComparisonIntegralPayload_of_familyPayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33B finite analytic Weil positivity from four independent chunked
comparison-integral families. -/
theorem psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralFamilyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper)
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33C singleton directed-family handoff from four independent chunked
comparison-integral families. -/
theorem psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralFamilyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper)
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33A certificate extracted from delta-compressed distance payloads. -/
theorem activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryTail)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlTail)

/-- Step33B finite analytic Weil positivity from delta-compressed distance
payloads. -/
theorem psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33C singleton directed-family handoff from delta-compressed distance
payloads. -/
theorem psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveLower
        Q3.PSDpd.primaryK11AnalyticAFinitePositiveUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => 0 + (10 : Real) * (i : Real))
        (fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFinitePositiveLower
        Q3.PSDpd.controlK9AnalyticAFinitePositiveUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- A full-window `( -T, T ]` certificate is enough for the finite part:
the missing left endpoint is measure-zero, so the `Ioc` window integral equals
the `Icc` finite-window integral used by the analytic receiver. -/
theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_fullWindowCert
    (k : Nat) (ell x T lower upper : Real)
    (cert :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
        k ell x (-T) T lower upper) :
    lower <=
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFinitePart
          k ell x T ∧
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFinitePart
          k ell x T <= upper := by
  have hEq :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveTailWindowPart
          k ell x (-T) T =
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFinitePart
          k ell x T := by
    unfold CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveTailWindowPart
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFinitePart
    rw [integral_Icc_eq_integral_Ioc]
  constructor
  · exact le_trans cert.hWindowLower (le_of_eq hEq)
  · exact le_trans (le_of_eq hEq.symm) cert.hWindowUpper

/-- Primary finite-window bounds extracted from a direct full-window chunked
comparison-integral family.  This is the aligned finite receiver for
`FiniteLower/FiniteUpper`, avoiding the folded positive-half target mismatch. -/
theorem primaryK11AnalyticAFinitePartBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayload
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    have hwindow :=
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        11 (-Q3.PSDpd.archAFiniteTailCutoff) (20 : Real)
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper
        primaryFinite (by norm_num) (by norm_num) n
    norm_num [Q3.PSDpd.archAFiniteTailCutoff] at hwindow
    have hfull :
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff
          (Q3.PSDpd.primaryK11AnalyticAFiniteLower n)
          (Q3.PSDpd.primaryK11AnalyticAFiniteUpper n) := by
      simpa [Q3.PSDpd.archAFiniteTailCutoff] using hwindow
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_fullWindowCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFiniteLower n)
        (Q3.PSDpd.primaryK11AnalyticAFiniteUpper n) hfull).1
  · intro n
    have hwindow :=
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        11 (-Q3.PSDpd.archAFiniteTailCutoff) (20 : Real)
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper
        primaryFinite (by norm_num) (by norm_num) n
    norm_num [Q3.PSDpd.archAFiniteTailCutoff] at hwindow
    have hfull :
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
          11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff
          (Q3.PSDpd.primaryK11AnalyticAFiniteLower n)
          (Q3.PSDpd.primaryK11AnalyticAFiniteUpper n) := by
      simpa [Q3.PSDpd.archAFiniteTailCutoff] using hwindow
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_fullWindowCert
        11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.primaryK11AnalyticAFiniteLower n)
        (Q3.PSDpd.primaryK11AnalyticAFiniteUpper n) hfull).2

/-- Control finite-window bounds extracted from a direct full-window chunked
comparison-integral family. -/
theorem controlK9AnalyticAFinitePartBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayload
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper := by
  refine ⟨?_, ?_⟩
  · intro n
    have hwindow :=
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        9 (-Q3.PSDpd.archAFiniteTailCutoff) (20 : Real)
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper
        controlFinite (by norm_num) (by norm_num) n
    norm_num [Q3.PSDpd.archAFiniteTailCutoff] at hwindow
    have hfull :
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff
          (Q3.PSDpd.controlK9AnalyticAFiniteLower n)
          (Q3.PSDpd.controlK9AnalyticAFiniteUpper n) := by
      simpa [Q3.PSDpd.archAFiniteTailCutoff] using hwindow
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_fullWindowCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFiniteLower n)
        (Q3.PSDpd.controlK9AnalyticAFiniteUpper n) hfull).1
  · intro n
    have hwindow :=
      centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        9 (-Q3.PSDpd.archAFiniteTailCutoff) (20 : Real)
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper
        controlFinite (by norm_num) (by norm_num) n
    norm_num [Q3.PSDpd.archAFiniteTailCutoff] at hwindow
    have hfull :
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert
          9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
          (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff
          (Q3.PSDpd.controlK9AnalyticAFiniteLower n)
          (Q3.PSDpd.controlK9AnalyticAFiniteUpper n) := by
      simpa [Q3.PSDpd.archAFiniteTailCutoff] using hwindow
    exact
      (centeredBSplineArchKernelProfileFinitePart_bounds_of_fullWindowCert
        9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real))
        Q3.PSDpd.archAFiniteTailCutoff
        (Q3.PSDpd.controlK9AnalyticAFiniteLower n)
        (Q3.PSDpd.controlK9AnalyticAFiniteUpper n) hfull).2

/-- Primary finite-tail analytic bounds from direct finite chunks and the
existing positive-tail-window/proof-remainder route. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
    (primaryFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primaryTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper
      Q3.PSDpd.primaryK11AnalyticATailRadius := by
  exact
    Q3.PSDpd.primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (primaryK11AnalyticAFinitePartBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayload
        primaryFinite)
      (primaryK11AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        primaryTail)

/-- Control finite-tail analytic bounds from direct finite chunks and the
existing positive-tail-window/proof-remainder route. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
    (controlFinite :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (controlTail :
      Step33AChunkedComparisonIntegralFamilyPayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper
      Q3.PSDpd.controlK9AnalyticATailRadius := by
  exact
    Q3.PSDpd.controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder
      (controlK9AnalyticAFinitePartBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayload
        controlFinite)
      (controlK9AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload
        controlTail)

/-- Primary A finite-tail analytic cert extracted directly from
delta-compressed direct finite/tail distance payloads. -/
theorem primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.primaryK11AnalyticAFiniteLower
      Q3.PSDpd.primaryK11AnalyticAFiniteUpper
      Q3.PSDpd.primaryK11AnalyticATailRadius := by
  exact
    primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        primaryTail)

/-- Control A finite-tail analytic cert extracted directly from
delta-compressed direct finite/tail distance payloads. -/
theorem controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailAnalyticBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.controlK9AnalyticAFiniteLower
      Q3.PSDpd.controlK9AnalyticAFiniteUpper
      Q3.PSDpd.controlK9AnalyticATailRadius := by
  exact
    controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlFinite)
      (step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads
        controlTail)

/-- Step33A certificate from direct finite full-window distance payloads plus
the existing positive-tail distance payloads. -/
theorem activeCenteredCoeffEntryHboxCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    ActiveCenteredCoeffEntryHboxCert := by
  let primaryFiniteFamily :=
    step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads primaryFinite
  let primaryTailFamily :=
    step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads primaryTail
  let controlFiniteFamily :=
    step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads controlFinite
  let controlTailFamily :=
    step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads controlTail
  exact
    psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        (Q3.PSDpd.primaryK11AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
          (primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
            primaryFiniteFamily primaryTailFamily)))
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primaryK11AnalyticP0_entry_hbox_generated
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        (Q3.PSDpd.controlK9AnalyticAAbsDistanceHboxCert_of_delta_recenter_checks
          (controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_directFiniteChunkedComparisonIntegralFamilyPayloads
            controlFiniteFamily controlTailFamily)))
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      controlK9AnalyticP0_entry_hbox_generated

/-- Step33B finite analytic Weil positivity from the direct finite distance
payload route. -/
theorem psd_step33_finite_analytic_weil_positivity_of_directFiniteChunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33C singleton directed-family handoff from the direct finite distance
payload route. -/
theorem psd_step33_singleton_directed_family_handoff_of_directFiniteChunkedComparisonIntegralDistancePayloads
    (primaryFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        11
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinite : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff + (20 : Real) * (i : Real))
        (fun i => -Q3.PSDpd.archAFiniteTailCutoff +
          (20 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTail : ∀ n : CoeffIndex23,
      Step33AChunkedComparisonIntegralDistancePayload
        9
        (fun i => Q3.PSDpd.archAFiniteTailCutoff + (10 : Real) * (i : Real))
        (fun i => Q3.PSDpd.archAFiniteTailCutoff +
          (10 : Real) * ((i + 1 : Nat) : Real))
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_directFiniteChunkedComparisonIntegralDistancePayloads
        primaryFinite primaryTail controlFinite controlTail)

/-- Step33A certificate extracted from the lower-level signed chunk payload via
the folded payload bridge. -/
theorem activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload
    (payload : Step33ASignedChunkedComparisonIntegralPayload) :
    ActiveCenteredCoeffEntryHboxCert := by
  exact
    activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload
      (step33AFoldedWindowPayload_of_signedChunkedComparisonIntegralPayload payload)

/-- Step33B finite analytic Weil positivity extracted from the lower-level
signed chunk payload via the folded payload bridge. -/
theorem psd_step33_finite_analytic_weil_positivity_of_signedChunkedComparisonIntegralPayload
    (payload : Step33ASignedChunkedComparisonIntegralPayload) :
    PsdStep33FiniteAnalyticPositivity
      (activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload payload) := by
  exact
    psd_step33_finite_analytic_weil_positivity_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload payload)

/-- Step33C singleton directed-family handoff extracted from the lower-level
signed chunk payload via the folded payload bridge. -/
theorem psd_step33_singleton_directed_family_handoff_of_signedChunkedComparisonIntegralPayload
    (payload : Step33ASignedChunkedComparisonIntegralPayload) :
    PsdStep33SingletonDirectedFamilyHandoff
      (activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload payload) := by
  exact
    psd_step33_singleton_directed_family_handoff_of_activeEntryHboxCert
      (activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload payload)

/-- Feed a folded positive-window payload into the checked local A finite-tail
recenter route.  This is the compact generated target after adjacent chunk
certificates have been glued. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFoldedWindowPayload
    (payload : Step33AFoldedWindowPayload) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      payload.primaryFiniteWindow payload.primaryFiniteLowerBound
      payload.primaryFiniteUpperBound)
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      payload.primaryTailWindow
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520))
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_positiveWindowCert
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      payload.controlFiniteWindow payload.controlFiniteLowerBound
      payload.controlFiniteUpperBound)
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert
      payload.controlTailWindow
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := (10 : Real))
        (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520))

/-- Local proof-remainder support bridge with pointwise constant finite-window
payloads and packaged positive-tail-window certs. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePointwisePositiveTailWindowProofRemainderRecenterWithCenterError
    (primaryFinitePointLower primaryFinitePointUpper
      controlFinitePointLower controlFinitePointUpper :
        CoeffIndex23 → Real)
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpper n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointLower n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointUpper n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpper n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointLower n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointUpper n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_pointwiseBounds
      primaryFinitePointLower primaryFinitePointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
    primaryTailWindow
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_pointwiseBounds
      controlFinitePointLower controlFinitePointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
    controlTailWindow

/-- Local proof-remainder support bridge with two-piece pointwise finite-window
payloads and packaged positive-tail-window certs. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTwoPiecePointwisePositiveTailWindowProofRemainderRecenterWithCenterError
    (primaryFiniteCut primaryFinitePointLowerLeft primaryFinitePointUpperLeft
      primaryFinitePointLowerRight primaryFinitePointUpperRight
      controlFiniteCut controlFinitePointLowerLeft controlFinitePointUpperLeft
      controlFinitePointLowerRight controlFinitePointUpperRight :
        CoeffIndex23 → Real)
    (primaryFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= primaryFiniteCut n)
    (primaryFiniteCutRight : ∀ n : CoeffIndex23,
      primaryFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (primaryFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        primaryFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperLeft n)
    (primaryFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperRight n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointLowerRight n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailWindow :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.primaryK11AnalyticATailWindowLower
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper
        Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
    (controlFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= controlFiniteCut n)
    (controlFiniteCutRight : ∀ n : CoeffIndex23,
      controlFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (controlFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        controlFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperLeft n)
    (controlFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperRight n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointLowerRight n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailWindow :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.archAPositiveTailWindowEnd
        Q3.PSDpd.controlK9AnalyticATailWindowLower
        Q3.PSDpd.controlK9AnalyticATailWindowUpper
        Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
      primaryFiniteCut primaryFinitePointLowerLeft primaryFinitePointUpperLeft
      primaryFinitePointLowerRight primaryFinitePointUpperRight
      primaryFiniteCutLeft primaryFiniteCutRight
      primaryFiniteLowerLeft primaryFiniteUpperLeft
      primaryFiniteLowerRight primaryFiniteUpperRight
      primaryFiniteLowerBound primaryFiniteUpperBound)
    primaryTailWindow
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
      controlFiniteCut controlFinitePointLowerLeft controlFinitePointUpperLeft
      controlFinitePointLowerRight controlFinitePointUpperRight
      controlFiniteCutLeft controlFiniteCutRight
      controlFiniteLowerLeft controlFiniteUpperLeft
      controlFiniteLowerRight controlFiniteUpperRight
      controlFiniteLowerBound controlFiniteUpperBound)
    controlTailWindow

/-- Local-log-tail closure bridge with pointwise constant positive-tail-window
payloads.  Compared with
`...ComparisonIntegralPositiveTailWindowLocalLogTailRecenterWithCenterError`,
the positive-window generator now only has to provide constant pointwise
enclosures on `(260,520]` plus the corresponding arithmetic window
comparisons. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteComparisonPositiveTailPointwiseLocalLogTailRecenterWithCenterError
    (primaryFiniteLowerF primaryFiniteUpperF
      controlFiniteLowerF controlFiniteUpperF :
        CoeffIndex23 → Real → Real)
    (primaryTailPointLower primaryTailPointUpper
      controlTailPointLower controlTailPointUpper :
        CoeffIndex23 → Real)
    (primaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFiniteUpperF n t)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteLowerF n t)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryFiniteUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpper n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointLower n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointUpper n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFiniteLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFiniteUpperF n t)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteLowerF n t)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlFiniteUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpper n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointLower n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointUpper n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailIntervalRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      primaryFiniteLowerF primaryFiniteUpperF primaryFiniteLowerInt primaryFiniteUpperInt
      primaryFiniteLower primaryFiniteUpper primaryFiniteLowerBound primaryFiniteUpperBound)
    (Q3.PSDpd.primaryK11AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
        primaryTailPointLower primaryTailPointUpper
        (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := 10)
          (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
          a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
          primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520).h))
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
      controlFiniteLowerF controlFiniteUpperF controlFiniteLowerInt controlFiniteUpperInt
      controlFiniteLower controlFiniteUpper controlFiniteLowerBound controlFiniteUpperBound)
    (Q3.PSDpd.controlK9AnalyticATailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
        controlTailPointLower controlTailPointUpper
        (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
        controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
        (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
          (U := Q3.PSDpd.archAPositiveTailWindowEnd)
          (omegaFactor := 10)
          (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
          (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
          controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
          a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
          controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520).h))

/-- Local-log-tail closure bridge with pointwise constant finite-window and
positive-tail-window payloads.  This is the narrowest whole-window constant
surface: generated data only has to prove pointwise bounds and scalar window
comparisons on `[-260,260]` and `(260,520]`. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePointwisePositiveTailPointwiseLocalLogTailRecenterWithCenterError
    (primaryFinitePointLower primaryFinitePointUpper
      primaryTailPointLower primaryTailPointUpper
      controlFinitePointLower controlFinitePointUpper
      controlTailPointLower controlTailPointUpper :
        CoeffIndex23 → Real)
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpper n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointLower n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointUpper n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpper n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointLower n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointUpper n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpper n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointLower n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointUpper n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpper n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointLower n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointUpper n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePointwisePositiveTailWindowProofRemainderRecenterWithCenterError
    primaryFinitePointLower primaryFinitePointUpper
    controlFinitePointLower controlFinitePointUpper
    primaryFiniteLower primaryFiniteUpper
    primaryFiniteLowerBound primaryFiniteUpperBound
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
      primaryTailPointLower primaryTailPointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
      primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := 10)
        (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520).h)
    controlFiniteLower controlFiniteUpper
    controlFiniteLowerBound controlFiniteUpperBound
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
      controlTailPointLower controlTailPointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
      controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := 10)
        (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520).h)

/-- Local-log-tail closure bridge with two-piece pointwise finite-window
payloads and pointwise positive-tail-window payloads.  This is the current
preferred generated surface when a single finite-window constant is too coarse. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTwoPiecePointwisePositiveTailPointwiseLocalLogTailRecenterWithCenterError
    (primaryFiniteCut primaryFinitePointLowerLeft primaryFinitePointUpperLeft
      primaryFinitePointLowerRight primaryFinitePointUpperRight
      primaryTailPointLower primaryTailPointUpper
      controlFiniteCut controlFinitePointLowerLeft controlFinitePointUpperLeft
      controlFinitePointLowerRight controlFinitePointUpperRight
      controlTailPointLower controlTailPointUpper :
        CoeffIndex23 → Real)
    (primaryFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= primaryFiniteCut n)
    (primaryFiniteCutRight : ∀ n : CoeffIndex23,
      primaryFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (primaryFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        primaryFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperLeft n)
    (primaryFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperRight n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointLowerRight n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpper n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointLower n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          primaryTailPointUpper n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= controlFiniteCut n)
    (controlFiniteCutRight : ∀ n : CoeffIndex23,
      controlFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (controlFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        controlFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperLeft n)
    (controlFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperRight n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointLowerRight n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpper n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointLower n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (Q3.PSDpd.archAPositiveTailWindowEnd - Q3.PSDpd.archAFiniteTailCutoff) *
          controlTailPointUpper n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTwoPiecePointwisePositiveTailWindowProofRemainderRecenterWithCenterError
    primaryFiniteCut primaryFinitePointLowerLeft primaryFinitePointUpperLeft
    primaryFinitePointLowerRight primaryFinitePointUpperRight
    controlFiniteCut controlFinitePointLowerLeft controlFinitePointUpperLeft
    controlFinitePointLowerRight controlFinitePointUpperRight
    primaryFiniteCutLeft primaryFiniteCutRight
    primaryFiniteLowerLeft primaryFiniteUpperLeft
    primaryFiniteLowerRight primaryFiniteUpperRight
    primaryFiniteLowerBound primaryFiniteUpperBound
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
      primaryTailPointLower primaryTailPointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
      primaryTailLower primaryTailUpper primaryTailWindowLower primaryTailWindowUpper
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := 10)
        (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520).h)
    controlFiniteCutLeft controlFiniteCutRight
    controlFiniteLowerLeft controlFiniteUpperLeft
    controlFiniteLowerRight controlFiniteUpperRight
    controlFiniteLowerBound controlFiniteUpperBound
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_pointwiseBounds
      controlTailPointLower controlTailPointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff, Q3.PSDpd.archAPositiveTailWindowEnd])
      controlTailLower controlTailUpper controlTailWindowLower controlTailWindowUpper
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
        (U := Q3.PSDpd.archAPositiveTailWindowEnd)
        (omegaFactor := 10)
        (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
        (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
        controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
        a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
        controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520).h)

/-- Local-log-tail positive-window helper with a two-piece pointwise payload for
the primary Arch block. -/
def primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
    (tailCut : Real)
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= tailCut)
    (hCutRight : tailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (hLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        pointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        pointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.primaryK11AnalyticATailWindowLower
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius :=
  CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseBounds
    pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    hCutLeft hCutRight hLowerLeft hUpperLeft hLowerRight hUpperRight
    hWindowLower hWindowUpper
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
      (U := Q3.PSDpd.archAPositiveTailWindowEnd)
      (omegaFactor := 10)
      (remainderRadius := Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius)
      (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
      primaryK11AnalyticATailProofRemainderIntegrable_logOmegaAfter520
      a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
      primaryK11AnalyticATailProofRemainderIntegral_logOmegaAfter520).h

/-- Local-log-tail positive-window helper with a two-piece pointwise payload for
the control Arch block. -/
def controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
    (tailCut : Real)
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= tailCut)
    (hCutRight : tailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (hLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        pointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        pointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (hUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.controlK9AnalyticATailWindowLower
      Q3.PSDpd.controlK9AnalyticATailWindowUpper
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius :=
  CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseBounds
    pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    hCutLeft hCutRight hLowerLeft hUpperLeft hLowerRight hUpperRight
    hWindowLower hWindowUpper
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailRemainderBoundsCert_of_logOmegaFullTransformTailMajorant
      (U := Q3.PSDpd.archAPositiveTailWindowEnd)
      (omegaFactor := 10)
      (remainderRadius := Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius)
      (by norm_num [Q3.PSDpd.archAPositiveTailWindowEnd])
      controlK9AnalyticATailProofRemainderIntegrable_logOmegaAfter520
      a_star_abs_le_ten_logOmega_after_archAPositiveTailWindowEnd
      controlK9AnalyticATailProofRemainderIntegral_logOmegaAfter520).h

/-- Primary positive-window helper where the generator proves scalar domination
by the full-transform `10 * log(3t)` majorant instead of raw integrand
pointwise inequalities. -/
def primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPieceLogOmegaMajorantBounds
    (tailCut : Real)
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= tailCut)
    (hCutRight : tailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (hLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        pointLowerLeft n <= -archALogOmegaFullTransformPointwiseMajorant 11 t)
    (hUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        archALogOmegaFullTransformPointwiseMajorant 11 t <=
          pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        pointLowerRight n <= -archALogOmegaFullTransformPointwiseMajorant 11 t)
    (hUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        archALogOmegaFullTransformPointwiseMajorant 11 t <=
          pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.primaryK11AnalyticATailWindowLower
      Q3.PSDpd.primaryK11AnalyticATailWindowUpper
      Q3.PSDpd.primaryK11AnalyticATailProofRemainderRadius :=
  primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
    tailCut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    hCutLeft hCutRight
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        11 ((n.1 : Real) / 4) t (pointLowerLeft n) (pointUpperLeft n)
        (by simpa [Set.mem_Ioi] using ht.1)
        (hLowerLeft n t ht) (hUpperLeft n t ht)).1)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        11 ((n.1 : Real) / 4) t (pointLowerLeft n) (pointUpperLeft n)
        (by simpa [Set.mem_Ioi] using ht.1)
        (hLowerLeft n t ht) (hUpperLeft n t ht)).2)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        11 ((n.1 : Real) / 4) t (pointLowerRight n) (pointUpperRight n)
        (by
          have hcut : Q3.PSDpd.archAFiniteTailCutoff < t :=
            lt_of_le_of_lt hCutLeft ht.1
          simpa [Set.mem_Ioi] using hcut)
        (hLowerRight n t ht) (hUpperRight n t ht)).1)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        11 ((n.1 : Real) / 4) t (pointLowerRight n) (pointUpperRight n)
        (by
          have hcut : Q3.PSDpd.archAFiniteTailCutoff < t :=
            lt_of_le_of_lt hCutLeft ht.1
          simpa [Set.mem_Ioi] using hcut)
        (hLowerRight n t ht) (hUpperRight n t ht)).2)
    hWindowLower hWindowUpper

/-- Control positive-window helper with the same scalar log-majorant target as
the primary helper. -/
def controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPieceLogOmegaMajorantBounds
    (tailCut : Real)
    (pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight :
      CoeffIndex23 → Real)
    (hCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= tailCut)
    (hCutRight : tailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (hLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        pointLowerLeft n <= -archALogOmegaFullTransformPointwiseMajorant 9 t)
    (hUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff tailCut,
        archALogOmegaFullTransformPointwiseMajorant 9 t <=
          pointUpperLeft n)
    (hLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        pointLowerRight n <= -archALogOmegaFullTransformPointwiseMajorant 9 t)
    (hUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc tailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        archALogOmegaFullTransformPointwiseMajorant 9 t <=
          pointUpperRight n)
    (hWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointLowerRight n)
    (hWindowUpper : ∀ n : CoeffIndex23,
      (tailCut - Q3.PSDpd.archAFiniteTailCutoff) * pointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - tailCut) * pointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :
    CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPositiveTailWindowBoundsCert
      Q3.PSDpd.archAFiniteTailCutoff
      Q3.PSDpd.archAPositiveTailWindowEnd
      Q3.PSDpd.controlK9AnalyticATailWindowLower
      Q3.PSDpd.controlK9AnalyticATailWindowUpper
      Q3.PSDpd.controlK9AnalyticATailProofRemainderRadius :=
  controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
    tailCut pointLowerLeft pointUpperLeft pointLowerRight pointUpperRight
    hCutLeft hCutRight
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        9 ((n.1 : Real) / 4) t (pointLowerLeft n) (pointUpperLeft n)
        (by simpa [Set.mem_Ioi] using ht.1)
        (hLowerLeft n t ht) (hUpperLeft n t ht)).1)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        9 ((n.1 : Real) / 4) t (pointLowerLeft n) (pointUpperLeft n)
        (by simpa [Set.mem_Ioi] using ht.1)
        (hLowerLeft n t ht) (hUpperLeft n t ht)).2)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        9 ((n.1 : Real) / 4) t (pointLowerRight n) (pointUpperRight n)
        (by
          have hcut : Q3.PSDpd.archAFiniteTailCutoff < t :=
            lt_of_le_of_lt hCutLeft ht.1
          simpa [Set.mem_Ioi] using hcut)
        (hLowerRight n t ht) (hUpperRight n t ht)).1)
    (fun n t ht =>
      (archA_integrand_bounds_of_logOmegaFullTransformMajorant
        9 ((n.1 : Real) / 4) t (pointLowerRight n) (pointUpperRight n)
        (by
          have hcut : Q3.PSDpd.archAFiniteTailCutoff < t :=
            lt_of_le_of_lt hCutLeft ht.1
          simpa [Set.mem_Ioi] using hcut)
        (hLowerRight n t ht) (hUpperRight n t ht)).2)
    hWindowLower hWindowUpper

/-- Packaged finite-window bridge whose positive-window side only needs scalar
domination by the full-transform log majorant. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailTwoPieceLogOmegaMajorantRecenterWithCenterError
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primaryTailCut : Real)
    (primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight :
        CoeffIndex23 → Real)
    (primaryTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= primaryTailCut)
    (primaryTailCutRight : primaryTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (primaryTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        primaryTailPointLowerLeft n <=
          -archALogOmegaFullTransformPointwiseMajorant 11 t)
    (primaryTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        archALogOmegaFullTransformPointwiseMajorant 11 t <=
          primaryTailPointUpperLeft n)
    (primaryTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLowerRight n <=
          -archALogOmegaFullTransformPointwiseMajorant 11 t)
    (primaryTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        archALogOmegaFullTransformPointwiseMajorant 11 t <=
          primaryTailPointUpperRight n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointLowerRight n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (controlTailCut : Real)
    (controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight :
        CoeffIndex23 → Real)
    (controlTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= controlTailCut)
    (controlTailCutRight : controlTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (controlTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        controlTailPointLowerLeft n <=
          -archALogOmegaFullTransformPointwiseMajorant 9 t)
    (controlTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        archALogOmegaFullTransformPointwiseMajorant 9 t <=
          controlTailPointUpperLeft n)
    (controlTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLowerRight n <=
          -archALogOmegaFullTransformPointwiseMajorant 9 t)
    (controlTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        archALogOmegaFullTransformPointwiseMajorant 9 t <=
          controlTailPointUpperRight n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointLowerRight n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    primary_hA_finite
    (primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPieceLogOmegaMajorantBounds
      primaryTailCut
      primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight
      primaryTailCutLeft primaryTailCutRight
      primaryTailLowerLeft primaryTailUpperLeft
      primaryTailLowerRight primaryTailUpperRight
      primaryTailWindowLower primaryTailWindowUpper)
    control_hA_finite
    (controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPieceLogOmegaMajorantBounds
      controlTailCut
      controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight
      controlTailCutLeft controlTailCutRight
      controlTailLowerLeft controlTailUpperLeft
      controlTailLowerRight controlTailUpperRight
      controlTailWindowLower controlTailWindowUpper)

/-- Local-log-tail closure bridge with packaged finite-window certs and
two-piece pointwise positive-tail-window payloads.  Combine this with the
finite-window pointwise wrappers when the generated finite side is also
pointwise. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailTwoPiecePointwiseLocalLogTailRecenterWithCenterError
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primaryTailCut : Real)
    (primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight :
        CoeffIndex23 → Real)
    (primaryTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= primaryTailCut)
    (primaryTailCutRight : primaryTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (primaryTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        primaryTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperLeft n)
    (primaryTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperRight n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointLowerRight n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (controlTailCut : Real)
    (controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight :
        CoeffIndex23 → Real)
    (controlTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= controlTailCut)
    (controlTailCutRight : controlTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (controlTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        controlTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperLeft n)
    (controlTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperRight n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointLowerRight n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailWindowProofRemainderRecenterWithCenterError
    primary_hA_finite
    (primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
      primaryTailCut
      primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight
      primaryTailCutLeft primaryTailCutRight
      primaryTailLowerLeft primaryTailUpperLeft
      primaryTailLowerRight primaryTailUpperRight
      primaryTailWindowLower primaryTailWindowUpper)
    control_hA_finite
    (controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPiecePointwiseLocalLogTail
      controlTailCut
      controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight
      controlTailCutLeft controlTailCutRight
      controlTailLowerLeft controlTailUpperLeft
      controlTailLowerRight controlTailUpperRight
      controlTailWindowLower controlTailWindowUpper)

/-- Local-log-tail closure bridge with pointwise constant finite-window
payloads and two-piece pointwise positive-tail-window payloads.  This is the
direct mixed surface for a generator that only needs one finite-window constant
enclosure but still wants to split the positive tail window. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePointwisePositiveTailTwoPiecePointwiseLocalLogTailRecenterWithCenterError
    (primaryFinitePointLower primaryFinitePointUpper : CoeffIndex23 → Real)
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpper n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointLower n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * primaryFinitePointUpper n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailCut : Real)
    (primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight :
        CoeffIndex23 → Real)
    (primaryTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= primaryTailCut)
    (primaryTailCutRight : primaryTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (primaryTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        primaryTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperLeft n)
    (primaryTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperRight n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointLowerRight n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFinitePointLower controlFinitePointUpper : CoeffIndex23 → Real)
    (controlFiniteLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLower n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpper n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointLower n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (2 * Q3.PSDpd.archAFiniteTailCutoff) * controlFinitePointUpper n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailCut : Real)
    (controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight :
        CoeffIndex23 → Real)
    (controlTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= controlTailCut)
    (controlTailCutRight : controlTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (controlTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        controlTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperLeft n)
    (controlTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperRight n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointLowerRight n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailTwoPiecePointwiseLocalLogTailRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_pointwiseBounds
      primaryFinitePointLower primaryFinitePointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      primaryFiniteLower primaryFiniteUpper
      primaryFiniteLowerBound primaryFiniteUpperBound)
    primaryTailCut
    primaryTailPointLowerLeft primaryTailPointUpperLeft
    primaryTailPointLowerRight primaryTailPointUpperRight
    primaryTailCutLeft primaryTailCutRight
    primaryTailLowerLeft primaryTailUpperLeft
    primaryTailLowerRight primaryTailUpperRight
    primaryTailWindowLower primaryTailWindowUpper
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_pointwiseBounds
      controlFinitePointLower controlFinitePointUpper
      (by norm_num [Q3.PSDpd.archAFiniteTailCutoff])
      controlFiniteLower controlFiniteUpper
      controlFiniteLowerBound controlFiniteUpperBound)
    controlTailCut
    controlTailPointLowerLeft controlTailPointUpperLeft
    controlTailPointLowerRight controlTailPointUpperRight
    controlTailCutLeft controlTailCutRight
    controlTailLowerLeft controlTailUpperLeft
    controlTailLowerRight controlTailUpperRight
    controlTailWindowLower controlTailWindowUpper

/-- Local-log-tail closure bridge with two-piece pointwise finite-window
payloads and two-piece pointwise positive-tail-window payloads.  This is the
most flexible two-piece checked landing surface currently needed by the
Step33A.1-A generator path. -/
def psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTwoPiecePointwisePositiveTailTwoPiecePointwiseLocalLogTailRecenterWithCenterError
    (primaryFiniteCut primaryFinitePointLowerLeft primaryFinitePointUpperLeft
      primaryFinitePointLowerRight primaryFinitePointUpperRight :
        CoeffIndex23 → Real)
    (primaryFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= primaryFiniteCut n)
    (primaryFiniteCutRight : ∀ n : CoeffIndex23,
      primaryFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (primaryFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        primaryFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (primaryFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperLeft n)
    (primaryFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        primaryFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (primaryFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryFinitePointUpperRight n)
    (primaryFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointLowerRight n)
    (primaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (primaryFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            primaryFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - primaryFiniteCut n) *
            primaryFinitePointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primaryTailCut : Real)
    (primaryTailPointLowerLeft primaryTailPointUpperLeft
      primaryTailPointLowerRight primaryTailPointUpperRight :
        CoeffIndex23 → Real)
    (primaryTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= primaryTailCut)
    (primaryTailCutRight : primaryTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (primaryTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        primaryTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff primaryTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperLeft n)
    (primaryTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        primaryTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc primaryTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryTailPointUpperRight n)
    (primaryTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticATailWindowLower n <=
        (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointLowerRight n)
    (primaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            primaryTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - primaryTailCut) *
            primaryTailPointUpperRight n <=
        Q3.PSDpd.primaryK11AnalyticATailWindowUpper n)
    (controlFiniteCut controlFinitePointLowerLeft controlFinitePointUpperLeft
      controlFinitePointLowerRight controlFinitePointUpperRight :
        CoeffIndex23 → Real)
    (controlFiniteCutLeft : ∀ n : CoeffIndex23,
      -Q3.PSDpd.archAFiniteTailCutoff <= controlFiniteCut n)
    (controlFiniteCutRight : ∀ n : CoeffIndex23,
      controlFiniteCut n <= Q3.PSDpd.archAFiniteTailCutoff)
    (controlFiniteLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        controlFinitePointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) (controlFiniteCut n),
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperLeft n)
    (controlFiniteLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        controlFinitePointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlFiniteUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc (controlFiniteCut n) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlFinitePointUpperRight n)
    (controlFiniteLowerBound : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointLowerLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointLowerRight n)
    (controlFiniteUpperBound : ∀ n : CoeffIndex23,
      (controlFiniteCut n + Q3.PSDpd.archAFiniteTailCutoff) *
            controlFinitePointUpperLeft n +
          (Q3.PSDpd.archAFiniteTailCutoff - controlFiniteCut n) *
            controlFinitePointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (controlTailCut : Real)
    (controlTailPointLowerLeft controlTailPointUpperLeft
      controlTailPointLowerRight controlTailPointUpperRight :
        CoeffIndex23 → Real)
    (controlTailCutLeft : Q3.PSDpd.archAFiniteTailCutoff <= controlTailCut)
    (controlTailCutRight : controlTailCut <= Q3.PSDpd.archAPositiveTailWindowEnd)
    (controlTailLowerLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        controlTailPointLowerLeft n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperLeft : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc Q3.PSDpd.archAFiniteTailCutoff controlTailCut,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperLeft n)
    (controlTailLowerRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        controlTailPointLowerRight n <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlTailUpperRight : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Ioc controlTailCut Q3.PSDpd.archAPositiveTailWindowEnd,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlTailPointUpperRight n)
    (controlTailWindowLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticATailWindowLower n <=
        (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointLowerLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointLowerRight n)
    (controlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlTailCut - Q3.PSDpd.archAFiniteTailCutoff) *
            controlTailPointUpperLeft n +
          (Q3.PSDpd.archAPositiveTailWindowEnd - controlTailCut) *
            controlTailPointUpperRight n <=
        Q3.PSDpd.controlK9AnalyticATailWindowUpper n) :=
  psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartPositiveTailTwoPiecePointwiseLocalLogTailRecenterWithCenterError
    (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
      primaryFiniteCut
      primaryFinitePointLowerLeft primaryFinitePointUpperLeft
      primaryFinitePointLowerRight primaryFinitePointUpperRight
      primaryFiniteCutLeft primaryFiniteCutRight
      primaryFiniteLowerLeft primaryFiniteUpperLeft
      primaryFiniteLowerRight primaryFiniteUpperRight
      primaryFiniteLowerBound primaryFiniteUpperBound)
    primaryTailCut
    primaryTailPointLowerLeft primaryTailPointUpperLeft
    primaryTailPointLowerRight primaryTailPointUpperRight
    primaryTailCutLeft primaryTailCutRight
    primaryTailLowerLeft primaryTailUpperLeft
    primaryTailLowerRight primaryTailUpperRight
    primaryTailWindowLower primaryTailWindowUpper
    (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_twoPiecePointwiseBounds
      controlFiniteCut
      controlFinitePointLowerLeft controlFinitePointUpperLeft
      controlFinitePointLowerRight controlFinitePointUpperRight
      controlFiniteCutLeft controlFiniteCutRight
      controlFiniteLowerLeft controlFiniteUpperLeft
      controlFiniteLowerRight controlFiniteUpperRight
      controlFiniteLowerBound controlFiniteUpperBound)
    controlTailCut
    controlTailPointLowerLeft controlTailPointUpperLeft
    controlTailPointLowerRight controlTailPointUpperRight
    controlTailCutLeft controlTailCutRight
    controlTailLowerLeft controlTailUpperLeft
    controlTailLowerRight controlTailUpperRight
    controlTailWindowLower controlTailWindowUpper

/-- Generated-P0 plus generated A arithmetic closure bridge whose remaining
inputs are finite-window bounds and checked tail-growth comparisons. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartTailGrowthBaseScalarBoundsCertWithCenterError
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primary_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATailGrowthBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff C0 C1
        Q3.PSDpd.primaryK11AnalyticATailRadius)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (control_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATailGrowthBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff C0 C1
        Q3.PSDpd.controlK9AnalyticATailRadius) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
            hC0 hC1 hgrowth primary_hA_finite primary_hA_tail),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
            hC0 hC1 hgrowth control_hA_finite control_hA_tail),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
      (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
        hC0 hC1 hgrowth primary_hA_finite primary_hA_tail)
      (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth
        hC0 hC1 hgrowth control_hA_finite control_hA_tail)

/-- Generated-P0 plus generated A arithmetic closure bridge with one scalar
tail-growth comparison for primary and one for control.  The generated A tail
radii are common across all 23 absolute distances. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartCommonTailGrowthBaseScalarBoundsCertWithCenterError
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (primary_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.primaryK11AnalyticAFiniteLower
        Q3.PSDpd.primaryK11AnalyticAFiniteUpper)
    (primary_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        11 ((3 : Real) / (10 : Real)) Q3.PSDpd.archAFiniteTailCutoff C0 C1 <=
        Q3.PSDpd.primaryK11AnalyticATailRadiusCommon)
    (control_hA_finite :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert
        Q3.PSDpd.archAFiniteTailCutoff
        Q3.PSDpd.controlK9AnalyticAFiniteLower
        Q3.PSDpd.controlK9AnalyticAFiniteUpper)
    (control_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        9 ((3 : Real) / (10 : Real)) Q3.PSDpd.archAFiniteTailCutoff C0 C1 <=
        Q3.PSDpd.controlK9AnalyticATailRadiusCommon) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
            hC0 hC1 hgrowth primary_hA_finite primary_hA_tail),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
            hC0 hC1 hgrowth control_hA_finite control_hA_tail),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
      (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
        hC0 hC1 hgrowth primary_hA_finite primary_hA_tail)
      (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
        hC0 hC1 hgrowth control_hA_finite control_hA_tail)

/-- Generated-P0 plus A comparison-integral finite-window closure bridge.
This is the proof-producing landing surface for a compact A generator: it may
provide lower/upper comparison functions and their certified integrals, then
reuse the common generated tail-growth radii. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0AComparisonIntegralCommonTailGrowthBaseScalarBoundsCertWithCenterError
    {C0 C1 : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)
    (primaryLowerF primaryUpperF controlLowerF controlUpperF :
      CoeffIndex23 → Real → Real)
    (primaryLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (primaryLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        primaryLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (primaryUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            11 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          primaryUpperF n t)
    (primaryFiniteLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.primaryK11AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryLowerF n t)
    (primaryFiniteUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          primaryUpperF n t <= Q3.PSDpd.primaryK11AnalyticAFiniteUpper n)
    (primary_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        11 ((3 : Real) / (10 : Real)) Q3.PSDpd.archAFiniteTailCutoff C0 C1 <=
        Q3.PSDpd.primaryK11AnalyticATailRadiusCommon)
    (controlLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlLowerF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlUpperF n)
        (Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff))
    (controlLower : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        controlLowerF n t <=
          CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t)
    (controlUpper : ∀ n : CoeffIndex23,
      ∀ t ∈ Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
        CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileIntegrand
            9 ((3 : Real) / (10 : Real)) ((n.1 : Real) / (4 : Real)) t <=
          controlUpperF n t)
    (controlFiniteLower : ∀ n : CoeffIndex23,
      Q3.PSDpd.controlK9AnalyticAFiniteLower n <=
        ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlLowerF n t)
    (controlFiniteUpper : ∀ n : CoeffIndex23,
      ∫ t in Set.Icc (-Q3.PSDpd.archAFiniteTailCutoff) Q3.PSDpd.archAFiniteTailCutoff,
          controlUpperF n t <= Q3.PSDpd.controlK9AnalyticAFiniteUpper n)
    (control_hA_tail :
      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound
        9 ((3 : Real) / (10 : Real)) Q3.PSDpd.archAFiniteTailCutoff C0 C1 <=
        Q3.PSDpd.controlK9AnalyticATailRadiusCommon) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.primaryK11AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
            hC0 hC1 hgrowth
            (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
              primaryLowerF primaryUpperF primaryLowerInt primaryUpperInt
              primaryLower primaryUpper primaryFiniteLower primaryFiniteUpper)
            primary_hA_tail),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (Q3.PSDpd.controlK9AnalyticAFiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth
            hC0 hC1 hgrowth
            (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
              controlLowerF controlUpperF controlLowerInt controlUpperInt
              controlLower controlUpper controlFiniteLower controlFiniteUpper)
            control_hA_tail),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFinitePartCommonTailGrowthBaseScalarBoundsCertWithCenterError
      hC0 hC1 hgrowth
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
        primaryLowerF primaryUpperF primaryLowerInt primaryUpperInt
        primaryLower primaryUpper primaryFiniteLower primaryFiniteUpper)
      primary_hA_tail
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFinitePartBoundsCert_of_comparisonIntegrals
        controlLowerF controlUpperF controlLowerInt controlUpperInt
        controlLower controlUpper controlFiniteLower controlFiniteUpper)
      control_hA_tail

/-- Generated-P0 plus A pointwise finite/tail closure bridge for the active
Step33A.1 base scalar gate.  This is the proof-producing landing surface for
the next A generator: pointwise finite-window bounds plus a tail bound imply
the finite/tail certs consumed by the checked A distance-bound bridge. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0APointwiseFiniteTailBaseScalarBoundsCertWithCenterError
    {primaryT controlT : Real}
    {primaryPointLower primaryPointUpper primaryFiniteLower primaryFiniteUpper
      primaryTailRadius : CoeffIndex23 → Real}
    {controlPointLower controlPointUpper controlFiniteLower controlFiniteUpper
      controlTailRadius : CoeffIndex23 → Real}
    (primary_hA_pointwise :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAPointwiseFiniteTailBoundsCert
        primaryT primaryPointLower primaryPointUpper primaryFiniteLower primaryFiniteUpper
        primaryTailRadius)
    (control_hA_pointwise :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAPointwiseFiniteTailBoundsCert
        controlT controlPointLower controlPointUpper controlFiniteLower controlFiniteUpper
        controlTailRadius) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
            primary_hA_pointwise),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
            control_hA_pointwise),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
        primary_hA_pointwise)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert_of_pointwiseFiniteTailBoundsCert
        control_hA_pointwise)

/-- Generated-P0 plus A two-piece pointwise finite/tail closure bridge for the
active Step33A.1 base scalar gate.  This is the chunked proof-producing
landing surface for the next A generator: one finite window may now be split at
a generated cut point before landing in the same finite/tail bridge. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedP0ATwoPiecePointwiseFiniteTailBaseScalarBoundsCertWithCenterError
    {primaryT controlT : Real}
    {primaryCut primaryPointLowerLeft primaryPointUpperLeft primaryPointLowerRight
      primaryPointUpperRight primaryFiniteLower primaryFiniteUpper primaryTailRadius :
        CoeffIndex23 → Real}
    {controlCut controlPointLowerLeft controlPointUpperLeft controlPointLowerRight
      controlPointUpperRight controlFiniteLower controlFiniteUpper controlTailRadius :
        CoeffIndex23 → Real}
    (primary_hA_two_piece :
      CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticATwoPiecePointwiseFiniteTailBoundsCert
        primaryT primaryCut primaryPointLowerLeft primaryPointUpperLeft
        primaryPointLowerRight primaryPointUpperRight primaryFiniteLower
        primaryFiniteUpper primaryTailRadius)
    (control_hA_two_piece :
      CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticATwoPiecePointwiseFiniteTailBoundsCert
        controlT controlCut controlPointLowerLeft controlPointUpperLeft
        controlPointLowerRight controlPointUpperRight controlFiniteLower
        controlFiniteUpper controlTailRadius) :
    RationalDeltaLiveBaseScalarBoundsClosure
      ⟨CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
            primary_hA_two_piece),
        Q3.PSDpd.primaryK11AnalyticP0AbsDistanceBoundsCert_generated,
        CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAAbsDistanceBoundsCert_of_finiteTailBoundsCert
          (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
            control_hA_two_piece),
        Q3.PSDpd.controlK9AnalyticP0AbsDistanceBoundsCert_generated⟩ := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFiniteTailBaseScalarBoundsCertWithCenterError
      (CenteredCoeffAnalyticABoundsBackend.primaryK11AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
        primary_hA_two_piece)
      (CenteredCoeffAnalyticABoundsBackend.controlK9AnalyticAFiniteTailBoundsCert_of_twoPiecePointwiseFiniteTailBoundsCert
        control_hA_two_piece)

/-- Option-B closure surface after generated zero-off-declared split-`R`
support facts are closed.  The remaining analytic obligations are exactly the
four compact nonzero-side `HboxOnDeclaredByDelta` facts. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndDeclaredSplitRHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hminus :
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (primary_hplus :
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hminus :
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (control_hplus :
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryMinus :=
      primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primary_hminus
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let primaryPlus :=
      primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primary_hplus
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let controlMinus :=
      controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        control_hminus
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let controlPlus :=
      controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        control_hplus
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primaryMinus primaryPlus
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        controlMinus controlPlus
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndByDeltaSplitRHboxes
      primary_hA
      (primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primary_hminus
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated)
      (primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primary_hplus
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated)
      primary_hP0
      control_hA
      (controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        control_hminus
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated)
      (controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        control_hplus
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated)
      control_hP0

/-- Option-B closure surface after generated split-`R` hboxes and
zero-off-declared support facts are closed.  The remaining assumptions are the
base `A/P0` matrix hboxes, not the prime-profile payload hboxes. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedSplitRHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryMinus :=
      primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let primaryPlus :=
      primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let controlMinus :=
      controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let controlPlus :=
      controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primaryMinus primaryPlus
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        controlMinus controlPlus
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndDeclaredSplitRHboxes
      primary_hA
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      primary_hP0
      control_hA
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      control_hP0

/-- Raw-Omega finite analytic positivity after the generated prime and `P0`
payloads have been inserted.  The remaining assumptions are exactly the
primary/control raw-Omega `A` hboxes. -/
theorem psd_step33_rawOmega_finite_analytic_weil_positivity_of_generated_prime_and_p0
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAnalyticA
      primaryK11A primaryK11ARadius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAnalyticA
      controlK9A controlK9ARadius) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_weil_positivity_of_base_hboxes
      primary_hA
      (primaryK11AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
        primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated)
      primaryK11AnalyticP0_entry_hbox_generated
      control_hA
      (controlK9AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
        controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated)
      controlK9AnalyticP0_entry_hbox_generated

/-- Raw-Omega finite analytic positivity after generated prime/`P0` payloads
and compressed raw-Omega `A` distance hbox certs have been inserted.  This is
the current Step33A.1-A receiver surface: the remaining numerical work is
exactly 23 primary and 23 control raw-Omega distance inequalities. -/
theorem psd_step33_rawOmega_finite_analytic_weil_positivity_of_rawOmegaAAbsDistanceCerts
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceHboxCert)
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceHboxCert) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity := by
  exact
    psd_step33_rawOmega_finite_analytic_weil_positivity_of_generated_prime_and_p0
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA)
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
        control_hA)

/-- Generated raw-Omega Step33A package after generated prime/`P0` payloads
and compressed raw-Omega `A` distance certs have been inserted. -/
theorem activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAAbsDistanceCerts
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceHboxCert)
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceHboxCert) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert := by
  exact
    { primary :=
        { hA :=
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
              primary_hA
          hP :=
            primaryK11AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
              primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
          hP0 := primaryK11AnalyticP0_entry_hbox_generated }
      control :=
        { hA :=
            Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAnalyticA_entry_hbox_of_abs_distance_cert
              control_hA
          hP :=
            controlK9AnalyticP_entry_hbox_of_delta_live_payload_with_center_error
              controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
          hP0 := controlK9AnalyticP0_entry_hbox_generated } }

/-- Generated raw-Omega Step33A package from interval-form raw-Omega `A`
distance certs.  This is the preferred receiver for the next generator: it only
has to prove lower/upper bounds for the 23 primary and 23 control distance
profiles. -/
theorem activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAIntervalCerts
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceIntervalCert)
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceIntervalCert) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert := by
  exact
    activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAAbsDistanceCerts
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceHboxCert_of_interval_cert
        primary_hA)
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceHboxCert_of_interval_cert
        control_hA)

/-- Generated raw-Omega Step33A package from finite/tail raw-Omega `A`
distance certs.  The remaining analytic payload can now target finite-window
and tail bounds for the 23 primary and 23 control distance profiles. -/
theorem activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
    {primaryT controlT : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailRadius :
      CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailRadius :
      CoeffIndex23 → Real}
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
        primaryT primaryFiniteLower primaryFiniteUpper primaryTailRadius)
    (hControlT : 0 <= controlT)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
        controlT controlFiniteLower controlFiniteUpper controlTailRadius) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert := by
  exact
    activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAIntervalCerts
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceIntervalCert_of_finiteTailBoundsCert
        hPrimaryT hPrimaryInt primary_hA)
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceIntervalCert_of_finiteTailBoundsCert
        hControlT hControlInt control_hA)

/-- Generated raw-Omega Step33A package from comparison-integral finite-window
payloads and tail absolute bounds.  This is the concrete next generator
contract: lower/upper comparison functions for `(0,T]`, scalar integral
containments, tail bounds, and arithmetic containment into the raw-Omega
payload interval. -/
theorem activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailBounds
    {primaryT controlT : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailRadius :
      CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailRadius :
      CoeffIndex23 → Real}
    (primaryLowerF primaryUpperF controlLowerF controlUpperF :
      CoeffIndex23 → Real → Real)
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryLowerF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryUpperF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        primaryLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryUpperF n eta)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      primaryFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) primaryT, primaryLowerF n eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) primaryT, primaryUpperF n eta) <=
        primaryFiniteUpper n)
    (hPrimaryTail : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) primaryT| <=
        primaryTailRadius n)
    (hPrimaryLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
        primaryFiniteLower n - primaryTailRadius n)
    (hPrimaryUpperArith : ∀ n : CoeffIndex23,
      primaryFiniteUpper n + primaryTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n)
    (hControlT : 0 <= controlT)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlLowerF n) (Set.Ioc (0 : Real) controlT))
    (hControlUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlUpperF n) (Set.Ioc (0 : Real) controlT))
    (hControlLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        controlLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlUpperF n eta)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      controlFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) controlT, controlLowerF n eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) controlT, controlUpperF n eta) <=
        controlFiniteUpper n)
    (hControlTail : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) controlT| <=
        controlTailRadius n)
    (hControlLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
        controlFiniteLower n - controlTailRadius n)
    (hControlUpperArith : ∀ n : CoeffIndex23,
      controlFiniteUpper n + controlTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert := by
  have primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
        primaryT primaryFiniteLower primaryFiniteUpper primaryTailRadius :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailBounds
      primaryLowerF primaryUpperF
      (fun n => (hPrimaryInt n).mono_set (by intro eta heta; exact heta.1))
      hPrimaryLowerInt hPrimaryUpperInt hPrimaryLower hPrimaryUpper
      hPrimaryFiniteLower hPrimaryFiniteUpper hPrimaryTail
      hPrimaryLowerArith hPrimaryUpperArith
  have control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
        controlT controlFiniteLower controlFiniteUpper controlTailRadius :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailBounds
      controlLowerF controlUpperF
      (fun n => (hControlInt n).mono_set (by intro eta heta; exact heta.1))
      hControlLowerInt hControlUpperInt hControlLower hControlUpper
      hControlFiniteLower hControlFiniteUpper hControlTail
      hControlLowerArith hControlUpperArith
  exact
    activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
      hPrimaryT hPrimaryInt primary_hA hControlT hControlInt control_hA

/-- Generated raw-Omega Step33A package from comparison-integral finite-window
payloads, finite tail-window payloads, and tail remainders.  This is the
preferred generator contract when the tail absolute bound is itself obtained
from a finite `(T,U]` comparison window plus a remainder. -/
theorem activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
    {primaryT primaryU controlT controlU : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailWindowLower
      primaryTailWindowUpper primaryTailRemainderRadius primaryTailRadius :
        CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailWindowLower
      controlTailWindowUpper controlTailRemainderRadius controlTailRadius :
        CoeffIndex23 → Real}
    (primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryTailWindow : primaryT <= primaryU)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        primaryFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpperF n eta)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) primaryT, primaryFiniteLowerF n eta)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) primaryT, primaryFiniteUpperF n eta) <=
        primaryFiniteUpper n)
    (hPrimaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n) (Set.Ioc primaryT primaryU))
    (hPrimaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n) (Set.Ioc primaryT primaryU))
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc primaryT primaryU,
        primaryTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc primaryT primaryU,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpperF n eta)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryTailWindowLower n <=
        ∫ eta in Set.Ioc primaryT primaryU, primaryTailLowerF n eta)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc primaryT primaryU, primaryTailUpperF n eta) <=
        primaryTailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) primaryU| <=
        primaryTailRemainderRadius n)
    (hPrimaryTailLowerArith : ∀ n : CoeffIndex23,
      -primaryTailRadius n <=
        primaryTailWindowLower n - primaryTailRemainderRadius n)
    (hPrimaryTailUpperArith : ∀ n : CoeffIndex23,
      primaryTailWindowUpper n + primaryTailRemainderRadius n <=
        primaryTailRadius n)
    (hPrimaryLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
        primaryFiniteLower n - primaryTailRadius n)
    (hPrimaryUpperArith : ∀ n : CoeffIndex23,
      primaryFiniteUpper n + primaryTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n)
    (hControlT : 0 <= controlT)
    (hControlTailWindow : controlT <= controlU)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n) (Set.Ioc (0 : Real) controlT))
    (hControlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n) (Set.Ioc (0 : Real) controlT))
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        controlFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpperF n eta)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) controlT, controlFiniteLowerF n eta)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) controlT, controlFiniteUpperF n eta) <=
        controlFiniteUpper n)
    (hControlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n) (Set.Ioc controlT controlU))
    (hControlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n) (Set.Ioc controlT controlU))
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc controlT controlU,
        controlTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc controlT controlU,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpperF n eta)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlTailWindowLower n <=
        ∫ eta in Set.Ioc controlT controlU, controlTailLowerF n eta)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc controlT controlU, controlTailUpperF n eta) <=
        controlTailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) controlU| <=
        controlTailRemainderRadius n)
    (hControlTailLowerArith : ∀ n : CoeffIndex23,
      -controlTailRadius n <=
        controlTailWindowLower n - controlTailRemainderRadius n)
    (hControlTailUpperArith : ∀ n : CoeffIndex23,
      controlTailWindowUpper n + controlTailRemainderRadius n <=
        controlTailRadius n)
    (hControlLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
        controlFiniteLower n - controlTailRadius n)
    (hControlUpperArith : ∀ n : CoeffIndex23,
      controlFiniteUpper n + controlTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert := by
  have primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
        primaryT primaryFiniteLower primaryFiniteUpper primaryTailRadius :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
      primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
      hPrimaryTailWindow
      (fun n => (hPrimaryInt n).mono_set (by intro eta heta; exact heta.1))
      (fun n => (hPrimaryInt n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt hPrimaryT heta))
      hPrimaryFiniteLowerInt hPrimaryFiniteUpperInt
      hPrimaryFiniteLower hPrimaryFiniteUpper
      hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
      hPrimaryTailLowerInt hPrimaryTailUpperInt
      hPrimaryTailLower hPrimaryTailUpper
      hPrimaryTailWindowLower hPrimaryTailWindowUpper
      hPrimaryTailRemainder hPrimaryTailLowerArith hPrimaryTailUpperArith
      hPrimaryLowerArith hPrimaryUpperArith
  have control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
        controlT controlFiniteLower controlFiniteUpper controlTailRadius :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert_of_comparisonIntegralsAndTailWindow
      controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF
      hControlTailWindow
      (fun n => (hControlInt n).mono_set (by intro eta heta; exact heta.1))
      (fun n => (hControlInt n).mono_set (by
        intro eta heta
        exact lt_of_le_of_lt hControlT heta))
      hControlFiniteLowerInt hControlFiniteUpperInt
      hControlFiniteLower hControlFiniteUpper
      hControlFiniteLowerBound hControlFiniteUpperBound
      hControlTailLowerInt hControlTailUpperInt
      hControlTailLower hControlTailUpper
      hControlTailWindowLower hControlTailWindowUpper
      hControlTailRemainder hControlTailLowerArith hControlTailUpperArith
      hControlLowerArith hControlUpperArith
  exact
    activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
      hPrimaryT hPrimaryInt primary_hA hControlT hControlInt control_hA

/-- Raw-Omega Step33B/Step33C closure surface directly from
comparison-integral finite-window payloads, finite tail-window payloads, and
tail remainders. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailWindow
    {primaryT primaryU controlT controlU : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailWindowLower
      primaryTailWindowUpper primaryTailRemainderRadius primaryTailRadius :
        CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailWindowLower
      controlTailWindowUpper controlTailRemainderRadius controlTailRadius :
        CoeffIndex23 → Real}
    (primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
      controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF :
        CoeffIndex23 → Real → Real)
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryTailWindow : primaryT <= primaryU)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteLowerF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryFiniteUpperF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        primaryFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpperF n eta)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) primaryT, primaryFiniteLowerF n eta)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) primaryT, primaryFiniteUpperF n eta) <=
        primaryFiniteUpper n)
    (hPrimaryTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailLowerF n) (Set.Ioc primaryT primaryU))
    (hPrimaryTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryTailUpperF n) (Set.Ioc primaryT primaryU))
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc primaryT primaryU,
        primaryTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc primaryT primaryU,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpperF n eta)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryTailWindowLower n <=
        ∫ eta in Set.Ioc primaryT primaryU, primaryTailLowerF n eta)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc primaryT primaryU, primaryTailUpperF n eta) <=
        primaryTailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) primaryU| <=
        primaryTailRemainderRadius n)
    (hPrimaryTailLowerArith : ∀ n : CoeffIndex23,
      -primaryTailRadius n <=
        primaryTailWindowLower n - primaryTailRemainderRadius n)
    (hPrimaryTailUpperArith : ∀ n : CoeffIndex23,
      primaryTailWindowUpper n + primaryTailRemainderRadius n <=
        primaryTailRadius n)
    (hPrimaryLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
        primaryFiniteLower n - primaryTailRadius n)
    (hPrimaryUpperArith : ∀ n : CoeffIndex23,
      primaryFiniteUpper n + primaryTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n)
    (hControlT : 0 <= controlT)
    (hControlTailWindow : controlT <= controlU)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlFiniteLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteLowerF n) (Set.Ioc (0 : Real) controlT))
    (hControlFiniteUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlFiniteUpperF n) (Set.Ioc (0 : Real) controlT))
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        controlFiniteLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpperF n eta)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) controlT, controlFiniteLowerF n eta)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) controlT, controlFiniteUpperF n eta) <=
        controlFiniteUpper n)
    (hControlTailLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailLowerF n) (Set.Ioc controlT controlU))
    (hControlTailUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlTailUpperF n) (Set.Ioc controlT controlU))
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc controlT controlU,
        controlTailLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc controlT controlU,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpperF n eta)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlTailWindowLower n <=
        ∫ eta in Set.Ioc controlT controlU, controlTailLowerF n eta)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc controlT controlU, controlTailUpperF n eta) <=
        controlTailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) controlU| <=
        controlTailRemainderRadius n)
    (hControlTailLowerArith : ∀ n : CoeffIndex23,
      -controlTailRadius n <=
        controlTailWindowLower n - controlTailRemainderRadius n)
    (hControlTailUpperArith : ∀ n : CoeffIndex23,
      controlTailWindowUpper n + controlTailRemainderRadius n <=
        controlTailRadius n)
    (hControlLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
        controlFiniteLower n - controlTailRadius n)
    (hControlUpperArith : ∀ n : CoeffIndex23,
      controlFiniteUpper n + controlTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n) :
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
        primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
        controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF
        hPrimaryT hPrimaryTailWindow hPrimaryInt
        hPrimaryFiniteLowerInt hPrimaryFiniteUpperInt
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLowerInt hPrimaryTailUpperInt
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder hPrimaryTailLowerArith hPrimaryTailUpperArith
        hPrimaryLowerArith hPrimaryUpperArith
        hControlT hControlTailWindow hControlInt
        hControlFiniteLowerInt hControlFiniteUpperInt
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLowerInt hControlTailUpperInt
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder hControlTailLowerArith hControlTailUpperArith
        hControlLowerArith hControlUpperArith
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
      (activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
        primaryFiniteLowerF primaryFiniteUpperF primaryTailLowerF primaryTailUpperF
        controlFiniteLowerF controlFiniteUpperF controlTailLowerF controlTailUpperF
        hPrimaryT hPrimaryTailWindow hPrimaryInt
        hPrimaryFiniteLowerInt hPrimaryFiniteUpperInt
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLowerInt hPrimaryTailUpperInt
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder hPrimaryTailLowerArith hPrimaryTailUpperArith
        hPrimaryLowerArith hPrimaryUpperArith
        hControlT hControlTailWindow hControlInt
        hControlFiniteLowerInt hControlFiniteUpperInt
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLowerInt hControlTailUpperInt
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder hControlTailLowerArith hControlTailUpperArith
        hControlLowerArith hControlUpperArith)

def rawOmegaAComparisonTailWindowPayloadActiveCert
    (primary : PrimaryK11RawOmegaAComparisonTailWindowPayload)
    (control : ControlK9RawOmegaAComparisonTailWindowPayload) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert :=
  activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailWindow
    (primaryT := primary.cutoff) (primaryU := primary.tailEnd)
    (controlT := control.cutoff) (controlU := control.tailEnd)
    (primaryFiniteLower := primary.finiteLower)
    (primaryFiniteUpper := primary.finiteUpper)
    (primaryTailWindowLower := primary.tailWindowLower)
    (primaryTailWindowUpper := primary.tailWindowUpper)
    (primaryTailRemainderRadius := primary.tailRemainderRadius)
    (primaryTailRadius := primary.tailRadius)
    (controlFiniteLower := control.finiteLower)
    (controlFiniteUpper := control.finiteUpper)
    (controlTailWindowLower := control.tailWindowLower)
    (controlTailWindowUpper := control.tailWindowUpper)
    (controlTailRemainderRadius := control.tailRemainderRadius)
    (controlTailRadius := control.tailRadius)
    primary.finiteLowerF primary.finiteUpperF primary.tailLowerF primary.tailUpperF
    control.finiteLowerF control.finiteUpperF control.tailLowerF control.tailUpperF
    primary.hCutoff_nonneg primary.hTailWindow primary.hProfileInt
    primary.hFiniteLowerInt primary.hFiniteUpperInt
    primary.hFiniteLower primary.hFiniteUpper
    primary.hFiniteLowerBound primary.hFiniteUpperBound
    primary.hTailLowerInt primary.hTailUpperInt
    primary.hTailLower primary.hTailUpper
    primary.hTailWindowLower primary.hTailWindowUpper
    primary.hTailRemainder primary.hTailLowerArith primary.hTailUpperArith
    primary.hPayloadLowerArith primary.hPayloadUpperArith
    control.hCutoff_nonneg control.hTailWindow control.hProfileInt
    control.hFiniteLowerInt control.hFiniteUpperInt
    control.hFiniteLower control.hFiniteUpper
    control.hFiniteLowerBound control.hFiniteUpperBound
    control.hTailLowerInt control.hTailUpperInt
    control.hTailLower control.hTailUpper
    control.hTailWindowLower control.hTailWindowUpper
    control.hTailRemainder control.hTailLowerArith control.hTailUpperArith
    control.hPayloadLowerArith control.hPayloadUpperArith

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
    (primary : PrimaryK11RawOmegaAComparisonTailWindowPayload)
    (control : ControlK9RawOmegaAComparisonTailWindowPayload) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert primary control) := by
  simpa [rawOmegaAComparisonTailWindowPayloadActiveCert] using
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailWindow
      (primaryT := primary.cutoff) (primaryU := primary.tailEnd)
      (controlT := control.cutoff) (controlU := control.tailEnd)
      (primaryFiniteLower := primary.finiteLower)
      (primaryFiniteUpper := primary.finiteUpper)
      (primaryTailWindowLower := primary.tailWindowLower)
      (primaryTailWindowUpper := primary.tailWindowUpper)
      (primaryTailRemainderRadius := primary.tailRemainderRadius)
      (primaryTailRadius := primary.tailRadius)
      (controlFiniteLower := control.finiteLower)
      (controlFiniteUpper := control.finiteUpper)
      (controlTailWindowLower := control.tailWindowLower)
      (controlTailWindowUpper := control.tailWindowUpper)
      (controlTailRemainderRadius := control.tailRemainderRadius)
      (controlTailRadius := control.tailRadius)
      primary.finiteLowerF primary.finiteUpperF primary.tailLowerF primary.tailUpperF
      control.finiteLowerF control.finiteUpperF control.tailLowerF control.tailUpperF
      primary.hCutoff_nonneg primary.hTailWindow primary.hProfileInt
      primary.hFiniteLowerInt primary.hFiniteUpperInt
      primary.hFiniteLower primary.hFiniteUpper
      primary.hFiniteLowerBound primary.hFiniteUpperBound
      primary.hTailLowerInt primary.hTailUpperInt
      primary.hTailLower primary.hTailUpper
      primary.hTailWindowLower primary.hTailWindowUpper
      primary.hTailRemainder primary.hTailLowerArith primary.hTailUpperArith
      primary.hPayloadLowerArith primary.hPayloadUpperArith
      control.hCutoff_nonneg control.hTailWindow control.hProfileInt
      control.hFiniteLowerInt control.hFiniteUpperInt
      control.hFiniteLower control.hFiniteUpper
      control.hFiniteLowerBound control.hFiniteUpperBound
      control.hTailLowerInt control.hTailUpperInt
      control.hTailLower control.hTailUpper
      control.hTailWindowLower control.hTailWindowUpper
      control.hTailRemainder control.hTailLowerArith control.hTailUpperArith
      control.hPayloadLowerArith control.hPayloadUpperArith

def rawOmegaAComparisonTailWindowPayloadActiveCert_of_generated_arithmetic_and_analytic
    (primaryAnalytic :
      PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated)
    (controlAnalytic :
      ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.ActiveRawOmegaCoeffEntryHboxCert :=
  rawOmegaAComparisonTailWindowPayloadActiveCert
    (primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
      primaryAnalytic)
    (controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
      controlAnalytic)

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAnalyticTailWindowPayloads
    (primaryAnalytic :
      PrimaryK11RawOmegaAComparisonTailWindowAnalyticPayload
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated)
    (controlAnalytic :
      ControlK9RawOmegaAComparisonTailWindowAnalyticPayload
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated) :
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert_of_generated_arithmetic_and_analytic
          primaryAnalytic controlAnalytic) := by
  exact
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
      (primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
        primaryAnalytic)
      (controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_analytic
        controlAnalytic)

/-- Raw-Omega Step33B/Step33C closure from the single bundled generated-import
target for direct analytic finite/tail-window payloads. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAnalyticTailWindowInputs
    (inputs : RawOmegaAAnalyticTailWindowInputs) :
    let payloads := inputs.toPayloads
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  simpa [RawOmegaAAnalyticTailWindowInputs.toPayloads,
    rawOmegaAComparisonTailWindowPayloadActiveCert_of_generated_arithmetic_and_analytic] using
    (psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAnalyticTailWindowPayloads
      inputs.primaryAnalytic inputs.controlAnalytic)

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (hPrimaryProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlProfileInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    let payloads :=
      rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        hPrimaryProfileInt
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder
        hControlProfileInt
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  dsimp
  exact
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
      (primaryK11RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        hPrimaryProfileInt
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder)
      (controlK9RawOmegaAComparisonTailWindowPayload_of_generated_arithmetic_and_const_comparison
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        hControlProfileInt
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder)

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads_builtin_integrability
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4)
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainder : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4)
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd| <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    let payloads :=
      rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  dsimp
  exact
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
      (rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder).1
      (rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainder
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainder).2

/-- Raw-Omega Step33B/Step33C closure from constant finite/tail comparisons
and direct tail-remainder bounds, using the built-in raw-Omega integrability
facts. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonDirectTailInputs
    (inputs : RawOmegaAConstComparisonDirectTailInputs) :
    let payloads := inputs.toPayloads
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  simpa [RawOmegaAConstComparisonDirectTailInputs.toPayloads] using
    (psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads_builtin_integrability
      inputs.primaryFiniteLower inputs.primaryFiniteUpper
      inputs.primaryTailLower inputs.primaryTailUpper
      inputs.controlFiniteLower inputs.controlFiniteUpper
      inputs.controlTailLower inputs.controlTailUpper
      inputs.hPrimaryFiniteLower inputs.hPrimaryFiniteUpper
      inputs.hPrimaryFiniteLowerBound inputs.hPrimaryFiniteUpperBound
      inputs.hPrimaryTailLower inputs.hPrimaryTailUpper
      inputs.hPrimaryTailWindowLower inputs.hPrimaryTailWindowUpper
      inputs.hPrimaryTailRemainder
      inputs.hControlFiniteLower inputs.hControlFiniteUpper
      inputs.hControlFiniteLowerBound inputs.hControlFiniteUpperBound
      inputs.hControlTailLower inputs.hControlTailUpper
      inputs.hControlTailWindowLower inputs.hControlTailWindowUpper
      inputs.hControlTailRemainder)

theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads_builtin_integrability_and_tail_growth
    (primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper :
      CoeffIndex23 → Real)
    (controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper :
      CoeffIndex23 → Real)
    (C0 C1 : Real)
    (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hgrowth : ∀ eta : Real,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta| <=
        C0 + C1 * |eta|)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        primaryFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryFiniteUpper n)
    (hPrimaryFiniteLowerBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteLower n)
    (hPrimaryFiniteUpperBound : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          primaryFiniteUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hPrimaryTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        primaryTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryTailUpper n)
    (hPrimaryTailWindowLower : ∀ n : CoeffIndex23,
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailLower n)
    (hPrimaryTailWindowUpper : ∀ n : CoeffIndex23,
      (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          primaryTailUpper n <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hPrimaryTailRemainderRadius : ∀ n : CoeffIndex23,
      (|primaryK11Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (Q3.PSDpd.bsplineScale 11 *
            Q3.PSDpd.bsplineAutocorrNorm 11))⁻¹| ^ 2 *
          (|(primaryK11Ell /
            (2 * Q3.PSDpd.bsplineScale 11))|⁻¹) ^ 4)) *
        (primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
          (-2 : ℝ) / 2) <=
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        controlFiniteLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real)
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlFiniteUpper n)
    (hControlFiniteLowerBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteLower n)
    (hControlFiniteUpperBound : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff *
          controlFiniteUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper n)
    (hControlTailLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        controlTailLower n <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlTailUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlTailUpper n)
    (hControlTailWindowLower : ∀ n : CoeffIndex23,
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower n <=
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailLower n)
    (hControlTailWindowUpper : ∀ n : CoeffIndex23,
      (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd -
          controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.cutoff) *
          controlTailUpper n <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper n)
    (hControlTailRemainderRadius : ∀ n : CoeffIndex23,
      (|controlK9Ell / Real.pi| *
        ((C0 + C1) *
          |(Real.sqrt (Q3.PSDpd.bsplineScale 9 *
            Q3.PSDpd.bsplineAutocorrNorm 9))⁻¹| ^ 2 *
          (|(controlK9Ell /
            (2 * Q3.PSDpd.bsplineScale 9))|⁻¹) ^ 4)) *
        (controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailEnd ^
          (-2 : ℝ) / 2) <=
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailRemainderRadius n) :
    let payloads :=
      rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        C0 C1 hC0 hC1 hgrowth
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainderRadius
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainderRadius
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  dsimp
  exact
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaATailWindowPayloads
      (rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        C0 C1 hC0 hC1 hgrowth
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainderRadius
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainderRadius).1
      (rawOmegaAComparisonTailWindowPayloads_of_generated_arithmetic_and_const_comparison_builtin_integrability_and_tail_growth
        primaryFiniteLower primaryFiniteUpper primaryTailLower primaryTailUpper
        controlFiniteLower controlFiniteUpper controlTailLower controlTailUpper
        C0 C1 hC0 hC1 hgrowth
        hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryFiniteLowerBound hPrimaryFiniteUpperBound
        hPrimaryTailLower hPrimaryTailUpper
        hPrimaryTailWindowLower hPrimaryTailWindowUpper
        hPrimaryTailRemainderRadius
        hControlFiniteLower hControlFiniteUpper
        hControlFiniteLowerBound hControlFiniteUpperBound
        hControlTailLower hControlTailUpper
        hControlTailWindowLower hControlTailWindowUpper
        hControlTailRemainderRadius).2

/-- Raw-Omega Step33B/Step33C closure from the single bundled generated-import
target for constant comparison plus structural tail-growth domination. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonTailGrowthInputs
    (inputs : RawOmegaAConstComparisonTailGrowthInputs) :
    let payloads := inputs.toPayloads
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        (rawOmegaAComparisonTailWindowPayloadActiveCert payloads.1 payloads.2) := by
  simpa [RawOmegaAConstComparisonTailGrowthInputs.toPayloads] using
    (psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAConstComparisonPayloads_builtin_integrability_and_tail_growth
      inputs.primaryFiniteLower inputs.primaryFiniteUpper
      inputs.primaryTailLower inputs.primaryTailUpper
      inputs.controlFiniteLower inputs.controlFiniteUpper
      inputs.controlTailLower inputs.controlTailUpper
      inputs.C0 inputs.C1 inputs.hC0 inputs.hC1 inputs.hgrowth
      inputs.hPrimaryFiniteLower inputs.hPrimaryFiniteUpper
      inputs.hPrimaryFiniteLowerBound inputs.hPrimaryFiniteUpperBound
      inputs.hPrimaryTailLower inputs.hPrimaryTailUpper
      inputs.hPrimaryTailWindowLower inputs.hPrimaryTailWindowUpper
      inputs.hPrimaryTailRemainderRadius
      inputs.hControlFiniteLower inputs.hControlFiniteUpper
      inputs.hControlFiniteLowerBound inputs.hControlFiniteUpperBound
      inputs.hControlTailLower inputs.hControlTailUpper
      inputs.hControlTailWindowLower inputs.hControlTailWindowUpper
      inputs.hControlTailRemainderRadius)

/-- Raw-Omega Step33B/Step33C closure surface directly from the
comparison-integral finite-window payloads and tail absolute bounds. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAComparisonIntegralsAndTailBounds
    {primaryT controlT : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailRadius :
      CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailRadius :
      CoeffIndex23 → Real}
    (primaryLowerF primaryUpperF controlLowerF controlUpperF :
      CoeffIndex23 → Real → Real)
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hPrimaryLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryLowerF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (primaryUpperF n) (Set.Ioc (0 : Real) primaryT))
    (hPrimaryLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        primaryLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta)
    (hPrimaryUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) primaryT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            11 primaryK11Ell ((n.1 : Real) / 4) eta <=
          primaryUpperF n eta)
    (hPrimaryFiniteLower : ∀ n : CoeffIndex23,
      primaryFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) primaryT, primaryLowerF n eta)
    (hPrimaryFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) primaryT, primaryUpperF n eta) <=
        primaryFiniteUpper n)
    (hPrimaryTail : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        11 primaryK11Ell ((n.1 : Real) / 4) primaryT| <=
        primaryTailRadius n)
    (hPrimaryLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
        primaryFiniteLower n - primaryTailRadius n)
    (hPrimaryUpperArith : ∀ n : CoeffIndex23,
      primaryFiniteUpper n + primaryTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n)
    (hControlT : 0 <= controlT)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (hControlLowerInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlLowerF n) (Set.Ioc (0 : Real) controlT))
    (hControlUpperInt : ∀ n : CoeffIndex23,
      IntegrableOn (controlUpperF n) (Set.Ioc (0 : Real) controlT))
    (hControlLower : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        controlLowerF n eta <=
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta)
    (hControlUpper : ∀ n : CoeffIndex23,
      ∀ eta ∈ Set.Ioc (0 : Real) controlT,
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
            9 controlK9Ell ((n.1 : Real) / 4) eta <=
          controlUpperF n eta)
    (hControlFiniteLower : ∀ n : CoeffIndex23,
      controlFiniteLower n <=
        ∫ eta in Set.Ioc (0 : Real) controlT, controlLowerF n eta)
    (hControlFiniteUpper : ∀ n : CoeffIndex23,
      (∫ eta in Set.Ioc (0 : Real) controlT, controlUpperF n eta) <=
        controlFiniteUpper n)
    (hControlTail : ∀ n : CoeffIndex23,
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaATailPart
        9 controlK9Ell ((n.1 : Real) / 4) controlT| <=
        controlTailRadius n)
    (hControlLowerArith : ∀ n : CoeffIndex23,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
        controlFiniteLower n - controlTailRadius n)
    (hControlUpperArith : ∀ n : CoeffIndex23,
      controlFiniteUpper n + controlTailRadius n <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n) :
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailBounds
        primaryLowerF primaryUpperF controlLowerF controlUpperF
        hPrimaryT hPrimaryInt hPrimaryLowerInt hPrimaryUpperInt
        hPrimaryLower hPrimaryUpper hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryTail hPrimaryLowerArith hPrimaryUpperArith
        hControlT hControlInt hControlLowerInt hControlUpperInt
        hControlLower hControlUpper hControlFiniteLower hControlFiniteUpper
        hControlTail hControlLowerArith hControlUpperArith
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
      (activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAComparisonIntegralsAndTailBounds
        primaryLowerF primaryUpperF controlLowerF controlUpperF
        hPrimaryT hPrimaryInt hPrimaryLowerInt hPrimaryUpperInt
        hPrimaryLower hPrimaryUpper hPrimaryFiniteLower hPrimaryFiniteUpper
        hPrimaryTail hPrimaryLowerArith hPrimaryUpperArith
        hControlT hControlInt hControlLowerInt hControlUpperInt
        hControlLower hControlUpper hControlFiniteLower hControlFiniteUpper
        hControlTail hControlLowerArith hControlUpperArith)

/-- Raw-Omega Step33B/Step33C closure surface after generated prime/`P0`
payloads and compressed raw-Omega `A` distance certs have been inserted. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAAbsDistanceCerts
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceHboxCert)
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceHboxCert) :
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAAbsDistanceCerts
        primary_hA control_hA
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
      (activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAAbsDistanceCerts
        primary_hA control_hA)

/-- Raw-Omega Step33B/Step33C closure surface from interval-form raw-Omega
`A` distance certs.  This keeps the remaining generated payload target at
lower/upper profile inequalities rather than an opaque absolute-value theorem. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAIntervalCerts
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceIntervalCert)
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceIntervalCert) :
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAIntervalCerts
        primary_hA control_hA
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
      (activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAIntervalCerts
        primary_hA control_hA)

/-- Raw-Omega Step33B/Step33C closure surface from finite/tail raw-Omega `A`
distance certs. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAFiniteTailBoundsCerts
    {primaryT controlT : Real}
    {primaryFiniteLower primaryFiniteUpper primaryTailRadius :
      CoeffIndex23 → Real}
    {controlFiniteLower controlFiniteUpper controlTailRadius :
      CoeffIndex23 → Real}
    (hPrimaryT : 0 <= primaryT)
    (hPrimaryInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          11 primaryK11Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (primary_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAFiniteTailBoundsCert
        primaryT primaryFiniteLower primaryFiniteUpper primaryTailRadius)
    (hControlT : 0 <= controlT)
    (hControlInt : ∀ n : CoeffIndex23,
      IntegrableOn
        (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
          9 controlK9Ell
          ((n.1 : Real) / 4))
        (Set.Ioi (0 : Real)))
    (control_hA :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAFiniteTailBoundsCert
        controlT controlFiniteLower controlFiniteUpper controlTailRadius) :
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
        hPrimaryT hPrimaryInt primary_hA hControlT hControlInt control_hA
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff cert := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_entryHboxCert
      (activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
        hPrimaryT hPrimaryInt primary_hA hControlT hControlInt control_hA)

/-- Raw-Omega Step33B/Step33C closure from the single bundled direct
finite/tail-window integral input.  This is the all-the-way consumer surface
for a future Arb-backed direct chunk-integral generator. -/
theorem psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs
    (inputs : RawOmegaADirectTailWindowInputs) :
    let certs := inputs.toFiniteTailBoundsCerts
    let cert :=
      activeRawOmegaCoeffEntryHboxCert_of_generated_prime_p0_and_rawOmegaAFiniteTailBoundsCerts
        primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
        certs.1
        controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
        certs.2
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaFiniteAnalyticPositivity ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.PsdStep33RawOmegaSingletonDirectedFamilyHandoff
        cert := by
  exact
    psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaAFiniteTailBoundsCerts
      primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAIntegrand_integrableOn_Ioi
      (RawOmegaADirectTailWindowInputs.toFiniteTailBoundsCerts inputs).1
      controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.hCutoff_nonneg
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAIntegrand_integrableOn_Ioi
      (RawOmegaADirectTailWindowInputs.toFiniteTailBoundsCerts inputs).2

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
