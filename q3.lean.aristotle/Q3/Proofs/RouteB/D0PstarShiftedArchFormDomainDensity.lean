import Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The exact shifted archimedean form-domain carrier is dense in `H_m i`.
This uses only literal-mode membership and the complete literal Hilbert basis.
It does not identify the domain with D0.2 or construct a form or operator. -/
theorem sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top
    (i : PairIndex) :
    (sourceArchimedeanShiftedFormDomain i).topologicalClosure = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← (V_n_m_hilbertBasis i).dense_span]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.2
    rintro x ⟨n, rfl⟩
    rw [V_n_m_hilbertBasis_apply]
    exact V_n_m_mem_sourceArchimedeanShiftedFormDomain i n

#print axioms sourceArchimedeanShiftedFormDomain_topologicalClosure_eq_top

end Q3.RouteB.D0Pstar
