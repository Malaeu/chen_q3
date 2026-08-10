import Q3.Proofs.RouteB.D0PstarArchSesquilinearFormIntegral
import Q3.Proofs.RouteB.D0PstarShiftedArchFiniteModeDomain
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.D0PstarSourceArchFiniteFormCCMWRCrosswalk

noncomputable section

open Complex MeasureTheory

namespace Q3.RouteB.D0Pstar

/-- A literal production mode, carried by the exact shifted archimedean form
domain proved at B3.0Q. -/
noncomputable def sourceArchimedeanModeInShiftedFormDomain
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanShiftedFormDomain i :=
  ⟨V_n_m i n, V_n_m_mem_sourceArchimedeanShiftedFormDomain i n⟩

/-- The unshifted archimedean form on two literal modes is the exact source
archimedean mode-pairing kernel. -/
theorem sourceArchimedeanSesquilinearForm_apply_mode
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanSesquilinearForm i
        (sourceArchimedeanModeInShiftedFormDomain i n)
        (sourceArchimedeanModeInShiftedFormDomain i r) =
      sourceArchimedeanModePairing i n r := by
  rw [sourceArchimedeanSesquilinearForm_eq_integral,
    sourceArchimedeanModePairing]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourceLogWindowFourierL2Isometry_apply_mode i n,
      coeFn_sourceLogWindowFourierL2Isometry_apply_mode i r] with t hn hr
  change
    star
          (((sourceLogWindowFourierL2Isometry i (V_n_m i n) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) *
        (sourceArchimedeanMultiplier t : ℂ) *
        (((sourceLogWindowFourierL2Isometry i (V_n_m i r) :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) = _
  rw [hn, hr]
  rw [starRingEnd_apply]

private theorem ccmFiniteSynthesis_mem_E_m_N
    (i : PairIndex) (c : CCMModeFinite i.N → ℂ) :
    ccmFiniteSynthesis i c ∈ E_m_N i := by
  change (∑ j, c j • V_n_m i (ccmModeFinite i.N j)) ∈ E_m_N i
  apply Submodule.sum_mem
  intro j _hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨ccmModeFinite i.N j, by
    simpa [modeSet] using ccmModeFinite_range i.N j, rfl⟩

/-- The existing literal CCM synthesis, lifted without changing its carrier or
order into the exact shifted form domain through the closed B3.0R inclusion. -/
noncomputable def ccmFiniteShiftedFormDomainSynthesis
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) →ₗ[ℂ]
      sourceArchimedeanShiftedFormDomain i where
  toFun c :=
    ⟨ccmFiniteSynthesis i c,
      E_m_N_le_sourceArchimedeanShiftedFormDomain i
        (ccmFiniteSynthesis_mem_E_m_N i c)⟩
  map_add' := by
    intro c d
    apply Subtype.ext
    exact (ccmFiniteSynthesis i).map_add c d
  map_smul' := by
    intro a c
    apply Subtype.ext
    exact (ccmFiniteSynthesis i).map_smul a c

/-- The lifted synthesis is literally the pre-existing CCM synthesis in
`H_m i`; no duplicate finite carrier is introduced. -/
@[simp]
theorem coe_ccmFiniteShiftedFormDomainSynthesis
    (i : PairIndex) (c : CCMModeFinite i.N → ℂ) :
    (ccmFiniteShiftedFormDomainSynthesis i c : H_m i) =
      ccmFiniteSynthesis i c := by
  rfl

private theorem ccmFiniteShiftedFormDomainSynthesis_eq_sum
    (i : PairIndex) (c : CCMModeFinite i.N → ℂ) :
    ccmFiniteShiftedFormDomainSynthesis i c =
      ∑ j, c j •
        sourceArchimedeanModeInShiftedFormDomain i (ccmModeFinite i.N j) := by
  apply Subtype.ext
  simp [ccmFiniteShiftedFormDomainSynthesis, ccmFiniteSynthesis,
    sourceArchimedeanModeInShiftedFormDomain]

/-- Finite sesquilinear expansion of the unshifted archimedean form in the
literal CCM order. -/
theorem sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchimedeanSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k := by
  classical
  rw [ccmFiniteShiftedFormDomainSynthesis_eq_sum,
    ccmFiniteShiftedFormDomainSynthesis_eq_sum]
  change
    sourceArchimedeanSesquilinearForm i
        (∑ j, c j • sourceArchimedeanModeInShiftedFormDomain i
          (ccmModeFinite i.N j))
        (∑ k, d k • sourceArchimedeanModeInShiftedFormDomain i
          (ccmModeFinite i.N k)) = _
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  simp only [starRingEnd_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul,
    sourceArchimedeanSesquilinearForm_apply_mode, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact finite restriction: on the existing literal CCM carrier, the
unshifted archimedean form is the negative CCM-WR matrix form. -/
theorem sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchimedeanSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  rw [sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis,
    sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm]

#print axioms sourceArchimedeanModeInShiftedFormDomain
#print axioms sourceArchimedeanSesquilinearForm_apply_mode
#print axioms ccmFiniteShiftedFormDomainSynthesis
#print axioms coe_ccmFiniteShiftedFormDomainSynthesis
#print axioms sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis
#print axioms sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR

end Q3.RouteB.D0Pstar
