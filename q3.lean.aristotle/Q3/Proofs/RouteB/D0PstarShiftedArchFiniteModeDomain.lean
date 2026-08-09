import Q3.Proofs.RouteB.D0PstarShiftedArchModeDomain

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Every vector in the exact finite Galerkin carrier belongs to the shifted
archimedean form-domain Submodule.  This is finite-span inclusion only; it is
not density, equality with D0.2, or operator-domain membership. -/
theorem E_m_N_le_sourceArchimedeanShiftedFormDomain
    (i : PairIndex) :
    E_m_N i ≤ sourceArchimedeanShiftedFormDomain i := by
  unfold E_m_N
  refine Submodule.span_le.2 ?_
  rintro x ⟨n, _hn, rfl⟩
  exact V_n_m_mem_sourceArchimedeanShiftedFormDomain i n

#print axioms E_m_N_le_sourceArchimedeanShiftedFormDomain

end Q3.RouteB.D0Pstar
