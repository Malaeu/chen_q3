import Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable

/-!
# Goal 057 B3.0D: source archimedean mode-pairing kernel Hermitianity

This file materializes the fixed-mode archimedean pairing kernel whose
integrability was proved in B3.0C, and proves its exact conjugate symmetry.

The result is only the archimedean fixed-mode kernel.  It does not identify an
integral value, a CCM matrix entry, the full source Weil form, or an associated
operator graph.
-/

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace Q3.RouteB.D0Pstar

/--
The exact archimedean pairing kernel on two fixed production modes, with the
source convention antilinear in the first slot and linear in the second.
-/
noncomputable def sourceArchimedeanModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ t : ℝ,
    conj (𝓕 (logWindowZeroExtendedMode i n) t) *
      (sourceArchimedeanMultiplier t : ℂ) *
      𝓕 (logWindowZeroExtendedMode i r) t

/--
The fixed-mode archimedean pairing kernel is Hermitian in its two mode
indices.
-/
theorem sourceArchimedeanModePairing_conj_symm
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i r n =
      conj (sourceArchimedeanModePairing i n r) := by
  unfold sourceArchimedeanModePairing
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_mul, conj_conj, conj_ofReal]
  ring

end Q3.RouteB.D0Pstar
