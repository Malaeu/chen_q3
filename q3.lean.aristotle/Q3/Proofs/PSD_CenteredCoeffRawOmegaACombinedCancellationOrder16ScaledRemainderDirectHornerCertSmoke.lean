import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Smoke check for the direct Horner receiver surface.

This file does not provide concrete Horner rows and does not claim Step33A.1-A
closure.  It only verifies that a valid direct Horner family in the canonical
residual budget reaches the exact nonzero-model source proposition consumed by
the existing scaled-remainder payload route.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- A valid direct Horner family feeds the exact current nonzero-model source
proposition for the Step33A.1-A sub0 scaled-remainder target. -/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (hValid : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  exact hValid.to_nonzeroModelSourceProp hResidualAbs

end Step33
end PSDpd
end Q3
