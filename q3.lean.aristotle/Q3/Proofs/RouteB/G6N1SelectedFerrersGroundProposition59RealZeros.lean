import Q3.Proofs.RouteB.G6N1SelectedFerrersGroundParityRealification
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Matrix
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — real zeros of the selected finite ground Proposition-59 transform

Verdict `REQ-2026-08-26-N` closeout.  The ratified ground parity /
realification / eta-normalization node is invoked exactly once; its witnesses
are retained unchanged, the quotient basis is constructed internally, and the
existing Lagrange / Proposition-59 bridge delivers reality of the zeros.

No second ground row, no quotient-basis input, no trial-equals-ground
assumption, no residual/floor or compact-tracking hypothesis, no asymptotic
transfer of finite real-rootedness, no schedule change, and no cofinal H2a,
SlotS2, route-promotion or RH claim.
-/

set_option maxHeartbeats 8000000 in
/-- **Real zeros of the selected finite ground transform.**  From exactly the
inputs of the ratified ground node, the same real eta-normalized even simple
bottom eigenvector also has an entirely real Proposition-59 zero set. -/
theorem selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) (beta0 beta : ℝ)
    (hbeta0 : 0 < beta0) (hbeta : 0 < beta)
    (hm : 2 ≤ ((selectedFerrersCofinalSourceData P).index k).m)
    (hN : 1 ≤ ((selectedFerrersCofinalSourceData P).index k).N)
    (hoddFloor :
      ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ,
        ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
        beta0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
                  (CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) ℂ)) *ᵥ x)).re)
    (hfloor :
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
        beta) :
    ∃ (epsilon : ℝ)
      (xiC : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℂ)
      (xiR : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ)
      (c : ℂ),
        c ≠ 0 ∧
        (∀ j, ((xiR j : ℝ) : ℂ) = c * xiC j) ∧
        Matrix.mulVec (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) xiR =
          epsilon • xiR ∧
        (∀ j, xiR (ccmNegFinite ((selectedFerrersCofinalSourceData P).index k).N j) = xiR j) ∧
        ccmEtaFinite ((selectedFerrersCofinalSourceData P).index k).N ⬝ᵥ xiR = 1 ∧
        (∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ,
          epsilon * (x ⬝ᵥ x) ≤
            x ⬝ᵥ Matrix.mulVec
              (ccmWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N) x) ∧
        Module.finrank ℝ
          ((ccmWeilOpFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N).eigenspace epsilon) = 1 ∧
        ZerosRealOn Set.univ
          (proposition59CCMTransform (ccmL ((selectedFerrersCofinalSourceData P).index k).m)
            ((selectedFerrersCofinalSourceData P).index k).N xiR) := by
  classical
  obtain ⟨epsilon, xiC, xiR, c, hc, hcast, heig, heven, hnorm, hbottom,
      hsimple⟩ :=
    selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor
      P k beta0 beta hbeta0 hbeta hm hN hoddFloor hfloor
  refine ⟨epsilon, xiC, xiR, c, hc, hcast, heig, heven, hnorm, hbottom,
    hsimple, ?_⟩
  -- the quotient basis is built internally, never taken as an input
  exact Proposition59GroundLagrangeZeroSetBridge
    ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N epsilon xiR hm hN heig hnorm hbottom hsimple
    (Module.Basis.ofVectorSpace ℝ
      ((CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N → ℝ) ⧸
        LinearMap.ker
          (Matrix.toBilin'
            (ccmShiftedWeilMatFinite ((selectedFerrersCofinalSourceData P).index k).m ((selectedFerrersCofinalSourceData P).index k).N epsilon))))

#print axioms selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors

end Q3.RouteB.D0Pstar
