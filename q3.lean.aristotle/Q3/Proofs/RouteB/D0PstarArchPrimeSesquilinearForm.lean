import Q3.Proofs.RouteB.D0PstarArchSesquilinearFormFiniteRestriction
import Q3.Proofs.RouteB.D0PstarPrimeAmbientSesquilinearForm

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- The bounded ambient prime form restricted to the dense shifted
archimedean form domain. -/
noncomputable def sourcePrimeShiftedDomainSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => sourcePrimeSesquilinearForm i x.1 y.1)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun x y z => by
      change
        sourcePrimeSesquilinearForm i x.1 (y + z).1 =
          sourcePrimeSesquilinearForm i x.1 y.1 +
            sourcePrimeSesquilinearForm i x.1 z.1
      rw [Submodule.coe_add, map_add])
    (fun _ _ _ => by simp)

@[simp]
theorem sourcePrimeShiftedDomainSesquilinearForm_apply
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourcePrimeShiftedDomainSesquilinearForm i x y =
      sourcePrimeSesquilinearForm i x.1 y.1 := by
  rfl

theorem sourcePrimeShiftedDomainSesquilinearForm_conj_symm
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourcePrimeShiftedDomainSesquilinearForm i x y =
      star (sourcePrimeShiftedDomainSesquilinearForm i y x) := by
  simp only [sourcePrimeShiftedDomainSesquilinearForm_apply]
  exact sourcePrimeSesquilinearForm_conj_symm i x.1 y.1

/-- Exact dense-domain partial Weil ledger before the bounded rank-two W02
component is added: `Arch - Prime`. -/
noncomputable def sourceArchPrimeSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  sourceArchimedeanSesquilinearForm i -
    sourcePrimeShiftedDomainSesquilinearForm i

@[simp]
theorem sourceArchPrimeSesquilinearForm_apply
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchPrimeSesquilinearForm i x y =
      sourceArchimedeanSesquilinearForm i x y -
        sourcePrimeSesquilinearForm i x.1 y.1 := by
  rfl

theorem sourceArchPrimeSesquilinearForm_conj_symm
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchPrimeSesquilinearForm i x y =
      star (sourceArchPrimeSesquilinearForm i y x) := by
  rw [sourceArchPrimeSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply]
  change
    sourceArchimedeanSesquilinearForm i x y -
        sourcePrimeSesquilinearForm i x.1 y.1 =
      (starRingEnd ℂ)
        (sourceArchimedeanSesquilinearForm i y x -
          sourcePrimeSesquilinearForm i y.1 x.1)
  rw [map_sub]
  have ha := sourceArchimedeanSesquilinearForm_conj_symm i x y
  change
    sourceArchimedeanSesquilinearForm i x y =
      (starRingEnd ℂ) (sourceArchimedeanSesquilinearForm i y x) at ha
  have hp := sourcePrimeSesquilinearForm_conj_symm i x.1 y.1
  change
    sourcePrimeSesquilinearForm i x.1 y.1 =
      (starRingEnd ℂ) (sourcePrimeSesquilinearForm i y.1 x.1) at hp
  rw [← ha, ← hp]

theorem sourcePrimeShiftedDomainSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourcePrimeShiftedDomainSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmPrimeEntryN1
            i.m (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k := by
  rw [sourcePrimeShiftedDomainSesquilinearForm_apply,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmPrime]

theorem sourceArchPrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_modeLedger
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchPrimeSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      (∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k) -
      (∑ j, ∑ k,
        star (c j) *
          sourcePrimeModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k) := by
  rw [sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis]

theorem sourceArchPrimeSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchPrimeSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k) -
      (∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmPrimeEntryN1
            i.m (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  rw [sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    coe_ccmFiniteShiftedFormDomainSynthesis,
    sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmPrime]

#print axioms sourcePrimeShiftedDomainSesquilinearForm
#print axioms sourcePrimeShiftedDomainSesquilinearForm_conj_symm
#print axioms sourceArchPrimeSesquilinearForm
#print axioms sourceArchPrimeSesquilinearForm_conj_symm
#print axioms sourceArchPrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_modeLedger
#print axioms sourceArchPrimeSesquilinearForm_apply_ccmFiniteSynthesis

end Q3.RouteB.D0Pstar
