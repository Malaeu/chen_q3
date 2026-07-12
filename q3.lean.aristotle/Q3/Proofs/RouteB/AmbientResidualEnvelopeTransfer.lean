import Q3.Proofs.RouteB.AmbientResidualSplit

set_option linter.mathlibStandardSet false

open Filter

noncomputable section

namespace Q3.RouteB

/-- The ambient residual norm is bounded by the sum of the compressed residual
and projection-leakage norms. -/
theorem ambient_residual_norm_le_compressed_add_leakage
    {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) (mu : 𝕜) :
    ‖ambientResidual A v mu‖ ≤
      ‖compressedResidual A P v mu‖ + ‖projectionLeakage A P v‖ := by
  rw [ambient_residual_eq_compressed_residual_add_leakage A P v mu]
  exact norm_add_le _ _

/-- Componentwise envelopes transfer to an ambient-residual envelope. -/
theorem ambient_residual_envelope_of_component_envelopes
    {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) (mu : 𝕜)
    (compressedBound leakageBound : ℝ)
    (hcompressed : ‖compressedResidual A P v mu‖ ≤ compressedBound)
    (hleakage : ‖projectionLeakage A P v‖ ≤ leakageBound) :
    ‖ambientResidual A v mu‖ ≤ compressedBound + leakageBound := by
  exact (ambient_residual_norm_le_compressed_add_leakage A P v mu).trans
    (add_le_add hcompressed hleakage)

/-- Squared version of the component-envelope transfer, suitable for the
weighted Temple receiver. -/
theorem ambient_residual_sq_envelope_of_component_envelopes
    {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A P : E →ₗ[𝕜] E) (v : E) (mu : 𝕜)
    (compressedBound leakageBound : ℝ)
    (hcompressed : ‖compressedResidual A P v mu‖ ≤ compressedBound)
    (hleakage : ‖projectionLeakage A P v‖ ≤ leakageBound) :
    ‖ambientResidual A v mu‖ ^ 2 ≤
      (compressedBound + leakageBound) ^ 2 := by
  have hsum : ‖ambientResidual A v mu‖ ≤
      compressedBound + leakageBound :=
    ambient_residual_envelope_of_component_envelopes
      A P v mu compressedBound leakageBound hcompressed hleakage
  simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) hsum

/-- Under the compressed Ritz equation, a leakage envelope alone controls the
ambient residual. -/
theorem ambient_residual_envelope_of_leakage_envelope
    {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A P : E →ₗ[𝕜] E} {v : E} {mu : 𝕜} {bound : ℝ}
    (hritz : P (A v) = mu • v)
    (hleakage : ‖projectionLeakage A P v‖ ≤ bound) :
    ‖ambientResidual A v mu‖ ≤ bound := by
  rw [ambient_residual_norm_eq_leakage_norm_of_compressed_eigen hritz]
  exact hleakage

/-- Nonvacuous filter wrapper for two component envelopes on one family. -/
theorem eventually_ambient_residual_envelope_of_components
    {ι 𝕜 E : Type*} {l : Filter ι} [NeBot l]
    [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A P : ι → E →ₗ[𝕜] E) (v : ι → E) (mu : ι → 𝕜)
    (compressedBound leakageBound : ι → ℝ)
    (hcompressed : ∀ᶠ i in l,
      ‖compressedResidual (A i) (P i) (v i) (mu i)‖ ≤ compressedBound i)
    (hleakage : ∀ᶠ i in l,
      ‖projectionLeakage (A i) (P i) (v i)‖ ≤ leakageBound i) :
    ∀ᶠ i in l,
      ‖ambientResidual (A i) (v i) (mu i)‖ ≤
        compressedBound i + leakageBound i := by
  filter_upwards [hcompressed, hleakage] with i hci hli
  exact ambient_residual_envelope_of_component_envelopes
    (A i) (P i) (v i) (mu i) (compressedBound i) (leakageBound i) hci hli

/-- Nonvacuous filter wrapper for a compressed Ritz equation plus leakage
envelope on the same family. -/
theorem eventually_ambient_residual_envelope_of_leakage_envelope
    {ι 𝕜 E : Type*} {l : Filter ι} [NeBot l]
    [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A P : ι → E →ₗ[𝕜] E) (v : ι → E) (mu : ι → 𝕜)
    (bound : ι → ℝ)
    (hritz : ∀ᶠ i in l, P i (A i (v i)) = mu i • v i)
    (hleakage : ∀ᶠ i in l,
      ‖projectionLeakage (A i) (P i) (v i)‖ ≤ bound i) :
    ∀ᶠ i in l,
      ‖ambientResidual (A i) (v i) (mu i)‖ ≤ bound i := by
  filter_upwards [hritz, hleakage] with i hri hli
  exact ambient_residual_envelope_of_leakage_envelope hri hli

#print axioms ambient_residual_norm_le_compressed_add_leakage
#print axioms ambient_residual_envelope_of_component_envelopes
#print axioms ambient_residual_sq_envelope_of_component_envelopes
#print axioms ambient_residual_envelope_of_leakage_envelope
#print axioms eventually_ambient_residual_envelope_of_components
#print axioms eventually_ambient_residual_envelope_of_leakage_envelope

end Q3.RouteB
