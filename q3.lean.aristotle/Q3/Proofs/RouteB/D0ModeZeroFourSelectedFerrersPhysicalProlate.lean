import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalProlateScaling
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierToDLMF3035EvenL2

/-!
# Goal 058 G3: selected mode-zero/mode-four Ferrers solutions

The strict finite-limit carrier theorem now identifies zero-based even indices
`0` and `2`, while the root-conditioned Ferrers constructor already turns an
exact matching root into a normalized regular solution and its physical
scaling.  This leaf composes those two accepted surfaces.

The output is deliberately the pair of existing
`Mode4FerrersRegularEvenProlateSolution` objects, not a parallel replacement
for the production `ProlatePair`.  It proves neither the exact interior zero
counts nor a finite-Fourier eigenrelation, CCM Lemma 7.2, a denominator floor,
Goal 058 G3, Route B, or RH.

Supplier preflight receipt: at clean HEAD `d14af9e5`, the exact query
`mode zero degree four selected classical even carrier indices zero two
Ferrers regular physical prolate solutions strict eigenvalue order below
twenty` completed all registered shelves and the enabled `zeta23` base.  The
fresh Route B environment covered 256/256 source modules and 2334 declarations
with zero proof holes or nonstandard axioms.  It returned `CANDIDATE_ONLY`: the existing
hits were the separate carrier and root-conditioned Ferrers suppliers, not the
paired theorem below.
-/

namespace Q3.RouteB

noncomputable section

private theorem
    mode4ClassicalEvenEigenvalue_rootFunction_eq_zero_of_lt_three
    (mProject K p : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hp : p < 3) :
    mode4RootFunction mProject K
        (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p) = 0 := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hlt :
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p < 20 :=
    mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
      (mode4JacobiG mProject) hG p hp
  have hdet :=
    mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
      mProject K p
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p)
      hm hK hsep hlt rfl
  have hprod :
      mode4JacobiUpperProd (mode4JacobiG mProject) K *
          mode4RootFunction mProject K
            (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p) = 0 := by
    rw [← det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
          mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p)
          hm (by omega),
      ← det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
          mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p)
          hm (by omega)]
    exact hdet
  exact (mul_eq_zero.mp hprod).resolve_left
    (ne_of_gt (mode4JacobiUpperProd_pos mProject K hm))

/-- The selected lowest and third zero-based even carriers construct actual
normalized regular Ferrers solutions, with the exact strict spectral order
`Lambda_0 < Lambda_2 < 20`.  The imported physical-scaling methods apply to
both witnesses without adding another hypothesis. -/
theorem
    exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    Nonempty
        (Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0)) ∧
      Nonempty
        (Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2)) ∧
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 <
          mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 ∧
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 < 20 := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have h0lt :
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 < 20 :=
    mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three
      (mode4JacobiG mProject) hG 0 (by omega)
  have h4lt :
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 < 20 :=
    mode4ClassicalEvenEigenvalue_two_lt_twenty
      (mode4JacobiG mProject) hG
  have hroot0 :=
    mode4ClassicalEvenEigenvalue_rootFunction_eq_zero_of_lt_three
      mProject K 0 hm hK hsep (by omega)
  have hroot4 :=
    mode4ClassicalEvenEigenvalue_rootFunction_eq_zero_of_lt_three
      mProject K 2 hm hK hsep (by omega)
  have hS0 := exists_mode4FerrersRegularEvenProlateSolution_of_root
    mProject K
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0)
      hm hK hsep h0lt.le hroot0
  have hS4 := exists_mode4FerrersRegularEvenProlateSolution_of_root
    mProject K
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2)
      hm hK hsep h4lt.le hroot4
  have horder :
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 <
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 :=
    mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty
      mProject K 0 2 hm hK hsep (by omega) h4lt
  exact ⟨hS0, hS4, horder, h4lt⟩

#print axioms
  exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions

end

end Q3.RouteB
