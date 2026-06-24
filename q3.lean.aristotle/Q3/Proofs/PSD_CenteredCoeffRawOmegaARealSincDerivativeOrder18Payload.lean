import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincDerivativeCert19

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Standalone `realSinc` row-18 payload surface for the RawProduct18 source.

The internal Fin19 certificate supplies the proof-grade row; this file exposes
the smaller API requested by the active route: a named row-18 theorem and a
through-18 theorem for downstream ShapeSq code.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem primaryFiniteRow0Parent0Split100Sub0_realSinc_iteratedDeriv18_norm_le_two :
    ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
      ‖iteratedDeriv 18 realSinc u‖ <= (2 : Real) := by
  intro u hu
  have h :=
    Step33Sub0RealSincDerivativeMajorantCert19.coarseTwoBaseAbs_providesAnalyticMajorant
      u hu ⟨18, by norm_num⟩
  simpa [Step33Sub0RealSincDerivativeMajorantCert19.coarseTwoBaseAbs] using h

theorem primaryFiniteRow0Parent0Split100Sub0_realSinc_derivative_abs_through18 :
    ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
      ∀ k : Fin 19,
        ‖iteratedDeriv k.1 realSinc u‖ <= (2 : Real) := by
  intro u hu k
  have h :=
    Step33Sub0RealSincDerivativeMajorantCert19.coarseTwoBaseAbs_providesAnalyticMajorant
      u hu k
  simpa [Step33Sub0RealSincDerivativeMajorantCert19.coarseTwoBaseAbs] using h

end Step33
end PSDpd
end Q3
