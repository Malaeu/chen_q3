import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

/-!
Step33A.1-A endpoint v18 Aristotle pilot.

This file is an Aristotle input file, not a project proof import.  The two
`sorry` proofs below are the proof-bearing analytic endpoint packages missing
from the checked rational endpoint layer:

* Omega: `Step22OmegaClosedFormEndpointBoundsCert`
* ShapeSq: `ShapeSqEndpointBoundsCert`

The final definition is already pure local plumbing through the checked
`primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated`.

Preferred proof route:
* for Omega, use
  `Step22OmegaClosedFormEndpointBoundsCert
    .of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`;
* for ShapeSq, use
  `primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_of_value_deriv_bounds_generated`;
  this generated helper closes the rational `2 * E * E'` derivative-square
  corner comparisons, while the tight `E(anchor)^2` lower/upper facts remain
  analytic endpoint facts to prove directly.

Policy for Aristotle output:
* replace both `sorry` blocks with Lean proofs;
* do not add axioms, unsafe code, or trusted numerical black boxes;
* use the real imported Q3 definitions, not local replacements;
* if this first row cannot be proved, report the exact missing analytic lemma.
-/

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

#check Step22OmegaClosedFormEndpointBoundsCert
#check Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
#check step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs
#check ShapeSqEndpointBoundsCert
#check ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals
#check primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_of_value_deriv_bounds_generated
#check centeredBSplineImagTransformRealClosedForm
#check centeredBSplineImagTransformRealClosedFormDerivClosedForm
#check primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated

/-
Target 1.  Prove the Omega endpoint package for the first v18 refined
subchunk.  This should instantiate the checked re-series-anchor/trigamma
receiver above, not introduce a new Omega definition or trusted numeric axiom.
-/
theorem primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_aristotle_v18 :
    Step22OmegaClosedFormEndpointBoundsCert
      ((499999999999999999999 : Real) /
        (10000000000000000000000 : Real))
      ((1 : Real) / (20 : Real))
      ((1 : Real) / (20 : Real))
      ((158505952906660723821263128341789211522648013468721929299728671434816372504101837787327827 : Real) /
        (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((3170119058133214476431664946316801151647880016814754257913171534756799214149224661058141 : Real) /
        (2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((-106643293527304552591821287391961407544994279623740339344557023924606219973211357305502357 : Real) /
        (20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((-106643293527304552591821287391961407544994279623740339344557023924606219973211356905502357 : Real) /
        (20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) := by
  sorry

/-
Target 2.  Prove the ShapeSq endpoint package for the same subchunk.  The
intended route is the checked E/E' closed-form interval receiver with rational
corner comparisons for `2 * E * E'` already discharged by the generated helper.
Do not derive the tight anchor-square bounds from full-subchunk `E` corners;
prove the two `E(anchor)^2` endpoint facts directly.
-/
theorem primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18 :
    ShapeSqEndpointBoundsCert
      11
      ((3 : Real) / (10 : Real))
      ((499999999999999999999 : Real) /
        (10000000000000000000000 : Real))
      ((1 : Real) / (20 : Real))
      ((1 : Real) / (20 : Real))
      ((-46448578038952412672149872160407802487877144879577655939872927993464875466132202360827276104665062142415173687016462681408869026457238530060336008763092149959616648869724829277353 : Real) /
        (312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((-3715886243116193013422691188469113889347186857741575631430658701842124693104660254420490862373908779177392095867429176165007789167568948045769667316015512783831667117451096516791 : Real) /
        (25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((37158858560446920756861350578635783668117859273616803460403855154979728937804568063431171 : Real) /
        (62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((37158858560446920756861350578635783668117859273616803460403855154979728937804569313431171 : Real) /
        (62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) := by
  sorry

def primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_aristotle_v18 :=
  primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated
    primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_aristotle_v18
    primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
