import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-bearing coefficient rows for the active Step33A.1-A ShapeSqDeriv
Taylor interval certificate.

This file is intentionally isolated from `Q3.Main`: it imports the generated
endpoint package and the high-order power-series bridge, then closes only the
first coefficient row.  It does not claim the full ShapeSqDeriv Taylor payload;
rows `1..15` and the full-cell order-16 bound remain open obligations.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated :
    Real :=
  ((-46448578038952412672149872160407802487877144879577655939872927993464875466132202360827276104665062142415173687016462681408869026457238530060336008763092149959616648869724829277353 : Real) /
    (312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated :
    Real :=
  ((-3715886243116193013422691188469113889347186857741575631430658701842124693104660254420490862373908779177392095867429176165007789167568948045769667316015512783831667117451096516791 : Real) /
    (25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))

/-- First proof-grade coefficient row for the active ShapeSqDeriv center
power series.

The generated endpoint package already proves a derivative interval for
`deriv (fun t => E(t)^2)` at the row anchor `1/20`.  The high-order support
file proves that the zeroth coefficient of the chosen local ShapeSqDeriv
power series is the zeroth normalized center jet.  This lemma performs only
that transfer for `j = 0`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 ∧
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated := by
  have hCoeff :
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter.coeff 0 =
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv ((1 : Real) / 20) := by
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff
        ⟨0, by norm_num⟩
    simpa using h.symm
  have hCenterMem :
      ((1 : Real) / 20) ∈
        Set.Icc
          ((499999999999999999999 : Real) /
            (10000000000000000000000 : Real))
          ((1 : Real) / 20) := by
    constructor <;> norm_num
  constructor
  · rw [hCoeff]
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated] using
      primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hDerivLower
        ((1 : Real) / 20) hCenterMem
  · rw [hCoeff]
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated] using
      primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated.hDerivUpper
        ((1 : Real) / 20) hCenterMem

end Step33
end PSDpd
end Q3
