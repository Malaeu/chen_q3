PACKET 6 FOR MYTHOS — INSTANTIATION_CHOICE answered by sources + 045 closed
Repo: Malaeu/chen_q3 · rh_clean · HEAD ff0045b22181f42ddabb4322e4861cda212befb6
Built: 2026-07-31 by conductor-CLI (Linux). UTF-8, LF.

FLASH: GOAL 045 CLOSED in 3m48s — HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES.
21-line wrapper (SHA 49283d50…), passage Differentiable.differentiableOn →
DifferentiableOn.analyticOnNhd, NO domain bridge (your P045-2 CONFIRMED), P045-1
CONFIRMED (21 ≤ 40). Sealed R6Export SHAs unchanged, taint 0, triple, 8040 jobs.
P-SUP-ALL = 2/4 (hRm byte-audited PROVED by you; hRp bytes in this packet).

COVER NOTE — your INSTANTIATION_CHOICE question is answered by the sources herein:
(1) PSTAR-INSTANCE: D0CanonicalApproximation.lean — the ACTUAL fixed instantiation.
    Seven-gates registry names it as G1/G4 evidence:
      G1 PROVED (COFINAL_FAMILY, LEAN): differentiable_centeredPstarFamily,
        canonicalApproximation_slotH1
      G4 PROVED (ABSTRACT, LEAN): canonicalApproximation_slotAnchor + D0AnchorFloor
    i.e. G1/G4 are closed for the SPECTRAL/D0 side (centered Pstar,
    Q3.RouteB.D0Pstar.canonicalApproximation) — NOT for a windowed G_m instance.
    Per your three outcomes this points to: the beam needs the bridge
    Hfam ↔ G_m (our analogue of their k_λ ≈ ξ_λ step-2) — unless you rule the
    windowed side can be a SECOND instantiation feeding SlotS2 directly.
(2) ROOF-IMPORT: SoftL2Round13Integration.lean (the third ROOF import) for
    completeness of the skeleton context.
(3) GATES-JSON: full seven-gates registry with statuses and smallest gaps:
    G2 OPEN (H2A_EXACT_SECTOR_ORDERING_MISSING; 026 covers n=0,4, m=13/53/257,
    not cofinal), G3 OPEN (H2B_EXACT_THEOREM510_FACTORIZATION_MISSING), G5/G6
    per registry. Use for canvas v3 coloring and the card's G-slot targets.
(4) 045ANSWER in bytes — closes your hRp byte-audit.

QUEUE NOTE: your 046 candidate gwin_entire (double harvest: hG + SlotH1) is now
even more attractive: with hRm+hRp discharged, hG closes 3/4 and its SlotH1 face
touches the roof for the FIRST time. Awaiting your 046 contour (or dispatch of
the Hfam↔G_m bridge question first — your call, K2).

VERIFICATION CONTRACT: payloads strictly between BEGIN/END markers (markers
excluded); payload = source file byte-exact (incl. repeated trailing newlines).
SHA-256 over exactly those bytes = on-disk SHA.

MANIFEST (label · bytes · sha256):
  PSTAR-INSTANCE: docs/routeB_bus/D0CanonicalApproximation.lean · 7212 · 60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
  ROOF-IMPORT: docs/routeB_bus/SoftL2Round13Integration.lean · 4441 · 10bb78e28abc8309b2aad50ed87046cb6b4d80405e1c8c8a37eca5fc749aa43b
  GATES-JSON: PROOF_COMPILER_SEVEN_GATES_2026-07-27.json · 7663 · 40ebd0d306be8dd1c0c574b189b8b7d1122a259b2ebefa74203a82ebf40f2062
  045ANSWER: docs/routeB_bus/045_muntz_v3_supplier_hrp.answer.md · 7212 · e6d1730994714ef9005bf9a9149beb4dd9e06e746c4cbde666675821a2f78f93

═══ FILE BEGIN: PSTAR-INSTANCE: docs/routeB_bus/D0CanonicalApproximation.lean ═══
import Q3.Proofs.RouteB.CanonicalRHRouteSkeleton
import Q3.Proofs.RouteB.RawIntegralRhsCrosswalk

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-- The independent D0 parameters.  The lower bound `m ≥ 2` ensures that the
logarithmic window has positive length. -/
structure PairIndex where
  m : ℕ
  N : ℕ
  hm : 2 ≤ m

/-- The D0 logarithmic window length `L_m = log m`. -/
def logLength (i : PairIndex) : ℝ :=
  Real.log i.m

/-- The D0 Galerkin sector `{-N, ..., N}`. -/
def modeSet (i : PairIndex) : Finset ℤ :=
  Finset.Icc (-(i.N : ℤ)) (i.N : ℤ)

/-- The D0 `kTrial_(m,N)` coefficient row used by the finite transform.
Stage 3 of the kTrial realization supplies this field from the normalized
projected vector, rather than leaving an unrelated free `coeff` selector.
This record still does not assert that an arbitrary row is a ground family. -/
structure CoefficientFamily where
  kTrial : PairIndex → ℤ → ℂ

/-- The raw D0 family
`Fplus_(m,N)(z) = T_m(k_(m,N))(-z)`, in removable Proposition-5.9 form. -/
def rawFplus (D : CoefficientFamily) (i : PairIndex) (z : ℂ) : ℂ :=
  proposition59RawTransform (logLength i) (modeSet i) (D.kTrial i) (-z)

/-- The SOFT-1 bare transform
`B_(m,N)(z) = lambda_m^(i*z) Fplus_(m,N)(z)`.
Since `L_m = 2 log lambda_m`, the multiplier is `exp(i*z*L_m/2)`. -/
def bareTransform (D : CoefficientFamily) (i : PairIndex) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (logLength i : ℂ) / 2) * rawFplus D i z

/-- The exact central-nonzero locus needed for normalization.  It is not
silently inferred from `TrialNonzero`. -/
def CentralIndex (D : CoefficientFamily) :=
  {i : PairIndex // bareTransform D i 0 ≠ 0}

/-- Legacy uncentered candidate.  The 2026-07-27 S1 verdict kills this family:
its factor `exp(i*z*L_m/2)` forces polynomial growth in `m` even inside the
centered critical strip.  It is retained only as a no-go witness. -/
def pstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) (z : ℂ) : ℂ :=
  (centeredXi 0 / bareTransform D i.1 0) * bareTransform D i.1 z

/-- The centered canonical D0 family, verbatim from section iii of
`PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md`. -/
def centeredPstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) (z : ℂ) : ℂ :=
  (centeredXi 0 / rawFplus D i.1 0) * rawFplus D i.1 z

/-- Cofinality means that both independent D0 coordinates tend to infinity. -/
def PairCofinal {D : CoefficientFamily} (p : ℕ → CentralIndex D) : Prop :=
  Tendsto (fun k => (p k).1.m) atTop atTop ∧
    Tendsto (fun k => (p k).1.N) atTop atTop

/-- Data not yet supplied by D0: the exact coefficient selector, a cofinal
path in the central-nonzero locus, and the one nested extraction. -/
structure CanonicalData where
  kTrial : CoefficientFamily
  parent : ℕ → CentralIndex kTrial
  parentCofinal : PairCofinal parent
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- Hole-free structural realization of `CanonicalApproximation` for the raw,
central-normalized D0 family. -/
def canonicalApproximation (D : CanonicalData) :
    CanonicalApproximation (CentralIndex D.kTrial) where
  Pstar := ⟨centeredPstarFamily D.kTrial⟩
  parent := D.parent
  parentCofinal := PairCofinal D.parent
  parentCofinalProof := D.parentCofinal
  extract := D.extract
  extractStrictMono := D.extractStrictMono

theorem logLength_pos (i : PairIndex) :
    0 < logLength i := by
  unfold logLength
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)

theorem rawFplus_eq_D0_integral
    (D : CoefficientFamily) (i : PairIndex) (z : ℂ) :
    finiteFplusCenteredIntegral
        (logLength i) (modeSet i) (D.kTrial i) z =
      rawFplus D i z := by
  rw [finiteFplusCenteredIntegral_eq_proposition59RawTransform_neg
    (logLength_pos i).ne']
  rfl

theorem differentiable_rawFplus
    (D : CoefficientFamily) (i : PairIndex) :
    Differentiable ℂ (rawFplus D i) := by
  have hneg : Differentiable ℂ (fun z : ℂ => -z) := by fun_prop
  simpa [rawFplus, Function.comp_def] using
    (differentiable_proposition59RawTransform
      (logLength i) (modeSet i) (D.kTrial i)).comp hneg

theorem differentiable_bareTransform
    (D : CoefficientFamily) (i : PairIndex) :
    Differentiable ℂ (bareTransform D i) := by
  have hphase :
      Differentiable ℂ
        (fun z : ℂ => Complex.exp (Complex.I * z * (logLength i : ℂ) / 2)) := by
    fun_prop
  exact hphase.mul (differentiable_rawFplus D i)

@[simp] theorem pstarFamily_zero
    (D : CoefficientFamily) (i : CentralIndex D) :
    pstarFamily D i 0 = centeredXi 0 := by
  unfold pstarFamily
  field_simp [i.property]

theorem differentiable_pstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) :
    Differentiable ℂ (pstarFamily D i) := by
  have hbare := differentiable_bareTransform D i.1
  have hscaled :
      Differentiable ℂ
        (fun z =>
          (centeredXi 0 / bareTransform D i.1 0) * bareTransform D i.1 z) :=
    hbare.const_mul _
  exact hscaled

/-- The central locus defined through `bareTransform` is exactly sufficient
for the centered denominator because the phase equals one at zero. -/
theorem rawFplus_zero_ne
    (D : CoefficientFamily) (i : CentralIndex D) :
    rawFplus D i.1 0 ≠ 0 := by
  simpa [bareTransform] using i.property

@[simp] theorem centeredPstarFamily_zero
    (D : CoefficientFamily) (i : CentralIndex D) :
    centeredPstarFamily D i 0 = centeredXi 0 := by
  unfold centeredPstarFamily
  field_simp [rawFplus_zero_ne D i]

theorem differentiable_centeredPstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) :
    Differentiable ℂ (centeredPstarFamily D i) := by
  exact (differentiable_rawFplus D i.1).const_mul _

/-- Under the classical nonvanishing of `Xi(0)`, the centered canonical
family has exactly the zeros of the raw transform. -/
theorem centeredPstarFamily_eq_zero_iff
    (D : CoefficientFamily) (i : CentralIndex D)
    (hXi : centeredXi 0 ≠ 0) (z : ℂ) :
    centeredPstarFamily D i z = 0 ↔ rawFplus D i.1 z = 0 := by
  simp [centeredPstarFamily, div_eq_mul_inv, hXi, rawFplus_zero_ne D i]

/-- Legacy zero-set statement for the killed uncentered witness. -/
theorem pstarFamily_eq_zero_iff
    (D : CoefficientFamily) (i : CentralIndex D)
    (hXi : centeredXi 0 ≠ 0) (z : ℂ) :
    pstarFamily D i z = 0 ↔ rawFplus D i.1 z = 0 := by
  have hraw0 : rawFplus D i.1 0 ≠ 0 := by
    intro h
    apply i.property
    simp [bareTransform, h]
  simp [pstarFamily, bareTransform, div_eq_mul_inv, hXi, hraw0]

theorem canonicalApproximation_slotH1 (D : CanonicalData) :
    SlotH1 (canonicalApproximation D) := by
  intro i
  exact differentiable_centeredPstarFamily D.kTrial i

theorem canonicalApproximation_slotAnchor (D : CanonicalData) :
    SlotAnchor (canonicalApproximation D) 0 := by
  intro i
  exact centeredPstarFamily_zero D.kTrial i

#print axioms rawFplus_eq_D0_integral
#print axioms centeredPstarFamily_eq_zero_iff
#print axioms pstarFamily_eq_zero_iff
#print axioms canonicalApproximation_slotH1
#print axioms canonicalApproximation_slotAnchor

end Q3.RouteB.D0Pstar
═══ FILE END: PSTAR-INSTANCE: docs/routeB_bus/D0CanonicalApproximation.lean ═══

═══ FILE BEGIN: ROOF-IMPORT: docs/routeB_bus/SoftL2Round13Integration.lean ═══
import Mathlib

set_option linter.mathlibStandardSet false

open Filter

noncomputable section

namespace Q3.RouteB

/-- Typed form of the Round-13 quantifier guard.  `S2` is allowed to pass to
the nested sequence `parent (extract k)` only; it cannot introduce an
independent cofinal carrier. -/
structure SoftSameCofinalSubsequence
    (Index : Type*) (H2a S1 : Index → Prop) where
  parent : ℕ → Index
  parentCofinal : Prop
  h2aOnParent : ∀ k, H2a (parent k)
  s1OnParent : ∀ k, S1 (parent k)
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- The actual sequence consumed by `S2` after the Round-13 guard. -/
def SoftSameCofinalSubsequence.s2Sequence
    {Index : Type*} {H2a S1 : Index → Prop}
    (G : SoftSameCofinalSubsequence Index H2a S1) : ℕ → Index :=
  fun k => G.parent (G.extract k)

/-- Autocorrelation in an abstract complex Hilbert carrier. -/
def HilbertAutocorrelation
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : T → H →L[ℂ] H) (q : H) (t : T) : ℂ :=
  inner ℂ (U t q) q

/-- A typed abstraction of one-dimensional normalized ground-space
uniqueness: any two normalized ground representatives differ by a unit
complex scalar. -/
def SimpleNormalizedGroundPhaseUnique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ground : H → Prop) : Prop :=
  ∀ p q, Ground p → Ground q →
    ∃ c : ℂ, starRingEnd ℂ c * c = 1 ∧ p = c • q

/-- Round-13 derived corollary: a simple normalized complex ground space has
one canonical phase-independent autocorrelation.  Isolation is not consumed
by this short corollary. -/
theorem simpleGround_canonicalPhaseIndependentAutocorrelation
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ground : H → Prop) (U : T → H →L[ℂ] H)
    (hsimple : SimpleNormalizedGroundPhaseUnique Ground)
    {p q : H} (hp : Ground p) (hq : Ground q) (t : T) :
    HilbertAutocorrelation U p t = HilbertAutocorrelation U q t := by
  rcases hsimple p q hp hq with ⟨c, hc, rfl⟩
  simp only [HilbertAutocorrelation, map_smul, inner_smul_left,
    inner_smul_right]
  calc
    c * (starRingEnd ℂ c * inner ℂ (U t q) q) =
        (starRingEnd ℂ c * c) * inner ℂ (U t q) q := by ring
    _ = inner ℂ (U t q) q := by rw [hc, one_mul]

/-- The five input slots of the frozen L2.2 contract.  The distribution type
is abstract here: analytic realization in `D'(ℝ)` is a downstream
instantiation, not an assumption hidden in this interface. -/
structure GlobalPositiveDefiniteUniquenessInputs
    (Index Dist : Type*) [SMul ℝ Dist] (A APhi : Dist) where
  diagonal : ℕ → Index
  scale : ℝ
  oneDiagonalSubsequenceOnEveryCompact : Prop
  convergenceInDPrime : Prop
  positiveDefiniteLimit : Prop
  limitingEquationInDPrime : Prop

/-- Typed, deliberately unproved L2.2 statement from Round 13.

The output is exactly `A = c • AΦ` in the eventual distribution instance. -/
def GlobalPositiveDefiniteUniqueness
    (Index Dist : Type*) [SMul ℝ Dist] (A APhi : Dist) : Prop :=
  ∀ input : GlobalPositiveDefiniteUniquenessInputs Index Dist A APhi,
    input.oneDiagonalSubsequenceOnEveryCompact →
    input.convergenceInDPrime →
    input.positiveDefiniteLimit →
    input.limitingEquationInDPrime →
    0 < input.scale →
    A = input.scale • APhi

/-- The two inputs of the optional source-level compactness leaf. -/
structure SourceCompactnessInputs (Source : Type*) where
  family : ℕ → Source
  spatialTightness : Prop
  uniformTranslationContinuity : Prop

/-- Output carrier of the optional source reconstruction leaf. -/
structure SourceCompactnessOutput (Source : Type*) where
  limitSource : Source
  subsequence : ℕ → ℕ
  subsequenceStrictMono : StrictMono subsequence
  strongL2Convergence : Prop
  uniformFullAutocorrelationConvergence : Prop

/-- Optional Round-13 theorem type.  It is not an input to L2.2. -/
def SourceCompactnessToFullAutocorrelation (Source : Type*) : Prop :=
  ∀ input : SourceCompactnessInputs Source,
    input.spatialTightness →
    input.uniformTranslationContinuity →
    Nonempty (SourceCompactnessOutput Source)

#check SoftSameCofinalSubsequence
#check simpleGround_canonicalPhaseIndependentAutocorrelation
#check GlobalPositiveDefiniteUniqueness
#check SourceCompactnessToFullAutocorrelation

#print axioms simpleGround_canonicalPhaseIndependentAutocorrelation

end Q3.RouteB
═══ FILE END: ROOF-IMPORT: docs/routeB_bus/SoftL2Round13Integration.lean ═══

═══ FILE BEGIN: GATES-JSON: PROOF_COMPILER_SEVEN_GATES_2026-07-27.json ═══
{
  "schema": "route_b_proof_compiler_seven_gates.v1",
  "date": "2026-07-27",
  "architecture_status": "CHALLENGER_NOT_RH",
  "public_mainline_unchanged": "T0-pd -> H-bridge -> H4 -> RH",
  "carrier_guard": {
    "object": "Q3.RouteB.D0Pstar.canonicalApproximation",
    "subsequence_guard": "SOFT_SAME_COFINAL_SUBSEQUENCE",
    "status": "LEAN_PROVED"
  },
  "compiler_order_semantics": "cumulative obligations, not pairwise logical implications",
  "ledger_field_contract": {
    "scope": [
      "ABSTRACT",
      "FINITE_CELL",
      "COFINAL_FAMILY"
    ],
    "verifier": [
      "LEAN",
      "ARB_INTERVAL",
      "PAPER",
      "CONDITIONAL"
    ]
  },
  "abstract_lean_certificates": [
    {
      "transaction": "032_bridge_reverification",
      "claim": "RiemannBoundaryCellBridge",
      "status": "PROVED",
      "scope": "ABSTRACT",
      "verifier": "LEAN",
      "unconditional": true,
      "theorems": [
        "riemannBoundaryCellBridge_finiteReduction",
        "riemannBoundaryCellBridge_main",
        "riemannBoundaryCellBridge_zeroMass",
        "riemannBoundaryCellBridge_Estar"
      ],
      "contract": "ARISTOTLE_TASK_RiemannBoundaryCellBridge.md",
      "contract_sha256": "7161d7376c3d9c7142c9a92a89a9ec8434fe73260019837de2d2f7b95749d039",
      "source": "aristotle_bridge/RequestProject/RiemannBoundaryCellBridge.lean",
      "source_sha256": "d47a0e1d1c3aa81b7f140db6103c64e553085df5542678c87c96c4cbbe19d3c7",
      "axioms": [
        "propext",
        "Classical.choice",
        "Quot.sound"
      ]
    }
  ],
  "finite_cell_certificates": [
    {
      "transaction": "026_lambda_bracket_resume",
      "claim": "G3ExactModeIntervalEnclosure",
      "status": "PROVED",
      "scope": "FINITE_CELL",
      "cells": [
        13,
        53,
        257
      ],
      "verifier": "ARB_INTERVAL",
      "not_lean": true,
      "not_cofinal_family": true
    },
    {
      "transaction": "027_hlambda_outer_lobe_gate",
      "claim": "HlambdaLastPositiveZeroLtOne",
      "status": "PROVED",
      "scope": "FINITE_CELL",
      "cells": [
        13,
        53,
        257
      ],
      "verifier": "PAPER",
      "input_verifier": "ARB_INTERVAL",
      "not_lean": true,
      "not_cofinal_family": true
    },
    {
      "transaction": "028_finite_core_theta_order",
      "claim": "FiniteCoreThetaOrderWithTailBudget",
      "status": "FIXED_K_SUFFICIENT_CONTRACT_FAILED",
      "scope": "FINITE_CELL",
      "cells": [
        257
      ],
      "verifier": "ARB_INTERVAL",
      "certificate_backend": "EXACT_RATIONAL_BERNSTEIN",
      "evidence": [
        "FINITE_CORE_THETA_CERT.json",
        "check_finite_core_theta_certificate.py"
      ],
      "not_lean": true,
      "not_cofinal_family": true,
      "termination": "the locked K truncation fails its sufficient lower-bound contract on r=255; this does not determine the sign of full S_lambda or kill DualThetaDominance"
    },
    {
      "transaction": "029_decisive_k_escalation",
      "claim": "DecisiveFiniteCoreThetaOrderKEscalation",
      "status": "K_ESCALATION_INCONCLUSIVE",
      "scope": "FINITE_CELL",
      "cells": [
        257
      ],
      "priority_bands": [
        256,
        255
      ],
      "authorized_extra_K": [
        20,
        40
      ],
      "verifier": "ARB_INTERVAL",
      "certificate_backend": "EXACT_RATIONAL_BERNSTEIN",
      "evidence": [
        "029_decisive_k_escalation.answer.md",
        "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json",
        "check_decisive_finite_core_theta_k_escalation.py"
      ],
      "not_lean": true,
      "not_cofinal_family": true,
      "termination": "neither L>=0 nor U<0 is certified at either owner-authorized cut; DualThetaDominance remains open"
    }
  ],
  "gates": [
    {
      "id": "G1",
      "name": "H1_CANONICAL_HOLOMORPHY",
      "status": "PROVED",
      "scope": "COFINAL_FAMILY",
      "verifier": "LEAN",
      "evidence": [
        "Q3/Proofs/RouteB/D0CanonicalApproximation.lean:differentiable_centeredPstarFamily",
        "Q3/Proofs/RouteB/D0CanonicalApproximation.lean:canonicalApproximation_slotH1"
      ],
      "smallest_gap": null
    },
    {
      "id": "G2",
      "name": "H2A_EXACT_SELECTED_GROUND",
      "status": "OPEN_GENERIC_CORE_AND_SIX_EXACT_MODES_PROVED",
      "scope": "ABSTRACT",
      "verifier": "CONDITIONAL",
      "evidence": [
        "Q3/Proofs/RouteB/SectorIsolationRadius.lean",
        "026_lambda_bracket_resume.answer.md",
        "LAMBDA_BRACKET_RESUME_AUDIT.json"
      ],
      "smallest_gap": "H2A_EXACT_SECTOR_ORDERING_MISSING",
      "scope_guard": "026 covers n=0,4 and m=13,53,257; it is not a cofinal selected-family theorem"
    },
    {
      "id": "G3",
      "name": "H2B_THEOREM510_REAL_ZERO_BRIDGE",
      "status": "OPEN_GENERIC_CORE_PROVED_EXACT_BIND_OPEN",
      "scope": "ABSTRACT",
      "verifier": "CONDITIONAL",
      "evidence": [
        "Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean",
        "Q3/Proofs/RouteB/RankOneCorrectionWeightedSymmetry.lean",
        "Q3/Proofs/RouteB/RankOneCorrectionDeterminant.lean",
        "Q3/Proofs/RouteB/RankOneCorrectionQuotientDescent.lean"
      ],
      "smallest_gap": "H2B_EXACT_THEOREM510_FACTORIZATION_MISSING"
    },
    {
      "id": "G4",
      "name": "ANCHOR_CANONICAL_NONZERO_NORMALIZATION",
      "status": "PROVED",
      "scope": "ABSTRACT",
      "verifier": "LEAN",
      "evidence": [
        "Q3/Proofs/RouteB/D0CanonicalApproximation.lean:canonicalApproximation_slotAnchor",
        "Q3/Proofs/RouteB/D0AnchorFloor.lean",
        "006_anchor_floor.answer.md",
        "008_anchor_ratio_receiver.answer.md"
      ],
      "smallest_gap": null
    },
    {
      "id": "G5",
      "name": "S1_MONTEL_NONZERO_CLUSTER",
      "status": "OPEN_MONTEL_CORE_PROVED_SIGN_SUPPLIER_OPEN",
      "scope": "ABSTRACT",
      "verifier": "CONDITIONAL",
      "evidence": [
        "Q3/Proofs/RouteB/MontelNormalFamilies.lean",
        "TWO_SIGN_LEMMAS_VERDICT_2026-07-27.md",
        "029_decisive_k_escalation.answer.md"
      ],
      "smallest_gap": "CENTERED_S1_WEIGHTED_PROJECTION_GAP",
      "closed_subgap": "HlambdaOuterLobeGate",
      "open_subgap": "DualThetaDominanceRepresentationShiftOrOneSidedTail"
    },
    {
      "id": "G6",
      "name": "S2_SAME_SUBSEQUENCE_CLUSTER_IDENTIFICATION",
      "status": "OPEN_TYPED_ONLY",
      "scope": "ABSTRACT",
      "verifier": "CONDITIONAL",
      "evidence": [
        "Q3/Proofs/RouteB/SoftL2Round13Integration.lean",
        "Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:sameCofinalGuard"
      ],
      "smallest_gap": "GLOBAL_POSITIVE_DEFINITE_UNIQUENESS_BODY_MISSING",
      "optional_supplier": "SourceCompactnessToFullAutocorrelation"
    },
    {
      "id": "G7",
      "name": "HURWITZ_XI_RH_ROOF",
      "status": "PROVED_CONDITIONAL_ON_G1_TO_G6",
      "scope": "ABSTRACT",
      "verifier": "LEAN",
      "evidence": [
        "Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:rh_of_canonical_strip_slots",
        "Q3/Proofs/RouteB/ClassicalXiInterface.lean"
      ],
      "smallest_gap": null
    }
  ],
  "single_compiler_arrow": [
    "G1:H1",
    "G2:H2a",
    "G3:H2b",
    "G4:ANCHOR",
    "G5:S1+Montel",
    "G6:S2",
    "G7:Hurwitz+Xi->RH"
  ],
  "current_first_open_gate": "G2",
  "next_queued_transaction": null,
  "sign_verdicts": {
    "HlambdaLastPositiveZeroLtOne": "PROVED_ON_CELLS_13_53_257",
    "DualThetaDominance": "OPEN_K_ESCALATION_INCONCLUSIVE",
    "killed": []
  },
  "guards": {
    "route_promoted_to_mainline": false,
    "unconditional_RH_claimed": false,
    "STATE_mutated_by_026": false,
    "BUS_010_created": false
  }
}
═══ FILE END: GATES-JSON: PROOF_COMPILER_SEVEN_GATES_2026-07-27.json ═══

═══ FILE BEGIN: 045ANSWER: docs/routeB_bus/045_muntz_v3_supplier_hrp.answer.md ═══
HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

```yaml
PRIMARY: HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
PRIMARY_COUNT: 1
SCOPE: ABSTRACT_SUPPLIER_CONSUMPTION
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
R6EXPORT_FILES_CHANGED: 0
MUNTZ_R6_FILES_CHANGED: 0

GOAL_VERSION_CONSUMED:
  FILE: 045_muntz_v3_supplier_hrp.goal.md
  SHA256: 90413b99281a29e0bd3fc734b9640b10973113ad0e6d8b4ee4babc717a5eb30c

TARGET:
  THEOREM: rplus_analyticOnNhd_shiftedHalfPlane
  MATERIALIZED: true
  WRAPPER_LINES: 21
  WRAPPER_SHA256: 49283d50602d5f792b91bf3f84c2c523575d5ba9ace1f9400e69b4cf2062d17e
  HAS_HMASS_HYPOTHESIS: false
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

HONESTY_INTERFACE:
  NAME: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
  STATUS: OPEN
```

All theorem claims are `[ABSTRACT][LEAN]`; hashes are `[CONTROL][SHA256]`,
while route, bus, submission, sealed, and frozen-file fields are
`[CONTROL][LOCAL]`.

## PHASE 0-lite

The exported supplier compiles with the exact type:

```lean
R6Export.Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (R6Export.Rplus h Λ)
```

There is no `hmass` input. The conclusion is global differentiability, so no
half-plane equality bridge is needed. `[ABSTRACT][LEAN]`

The exact pinned Mathlib passage is:

```lean
DifferentiableOn.analyticOnNhd
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s
```

The global supplier is first restricted with
`Differentiable.differentiableOn`. The suggested name
`Differentiable.analyticOnNhd` does not exist in the pinned Mathlib.
`[ABSTRACT][LEAN_API]`

## PHASE 1 — thin hRp wrapper

The new file `RequestProject/MuntzV3R6HrpWrapper.lean` proves:

```lean
theorem rplus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

The proof performs only:

1. a definitional `change` from the v3 `Rplus` to the byte-identical exported
   `R6Export.Rplus`;
2. exact consumption of `R6Export.Rplus_differentiable`;
3. `.differentiableOn.analyticOnNhd` with
   `isOpen_lt continuous_const Complex.continuous_re`.

The hypothesis list is exactly R6's list and contains no mass hypothesis.
`[ABSTRACT][LEAN]`

## Sealed-certificate audit

The seven `R6Export/` SHA-256 values remain exactly those registered by
Goal 044:

```text
ConcreteAnalyticity.lean        6e765f8ea67aabd13e22d2e832a00dd0283dd483f93fa136fbeba3fb07ba9554
IntegralAnalyticity.lean        d64d5de884a597785a358d400d04de70246593c75155f4f480963d86369374ce
Main.lean                       2a4beee999d0613eb2ae0e2ecbf67986ed5c3f4415e2dc1d42e2da979baca29d
PoleSubtracted.lean             7daace344032ba7eb130146394a7d23b97c910896901bd3e75367bcba0151eca
RiemannBoundaryCellBridge.lean b0c3a16db5627f4b3fbbc785ac7dc446d84a20975aa19b6296a4c25ccef65ce6
TailAnalyticity.lean            18d7e0cafb3cae5001367dbe741919e89be3b594ad2040f05fbd2c93ca97507a
WindowAnalyticity.lean          ce279d4214569b0767b54e1ae0b8aa63544f7a481c7c04e749b4e4d4c7eb04b9
```

No file in `R6Export/`, either `muntz_r6/` tree, or the frozen v3 source set
was edited. `[CONTROL][GIT_SHA256]`

## WITNESS_CLASS_VS_R6_HYPOTHESES_GAP

**OPEN.** hRp is discharged only under R6 hypotheses. The v3 witness class
allows support touching zero and supplies only
`LipschitzOnWith K h (Ico 0 b)`; it does not supply positive lower support
plus global `LipschitzWith K h`. No bridge is claimed or repaired.
`[ABSTRACT][OPEN_INTERFACE]`

## Validation ledger

```text
[ABSTRACT][LEAN] exported Rplus_differentiable signature                    PASS; no hmass
[ABSTRACT][LEAN] exact Mathlib API                                          DifferentiableOn.analyticOnNhd
[ABSTRACT][LEAN] lake env lean RequestProject/MuntzV3R6HrpWrapper.lean      PASS
[ABSTRACT][LEAN] full v3 lake build                                         PASS (8040 jobs)
[ABSTRACT][LEAN] #check wrapper signature                                   EXACT R6 INPUT LIST
[ABSTRACT][LEAN] #print axioms wrapper                                      [propext, Classical.choice, Quot.sound]
[CONTROL][TAINT] new Lean file                                              0 matches
[CONTROL][SHA256] sealed R6Export hashes                                    UNCHANGED
[CONTROL][MIRROR] canon versus mirror wrapper                               IDENTICAL
[CONTROL][GIT] frozen and muntz_r6 files changed                            0
[CONTROL][LOCAL] Aristotle submissions                                      0
```

## Prediction score

- `P045-1`: **HIT**. The wrapper is 21 lines and uses zero new analysis.
- `P045-2`: **HIT**. The supplier is entire; no half-plane equality/domain
  bridge is used.

## ACTIONS LOG

```text
1.  [CONTROL][GIT] Checked rh_clean and ran git pull --ff-only first.              PASS
2.  [CONTROL][SHA256] Locked both Goal 045 copies at 90413b99...a5eb30c.           PASS
3.  [CONTROL][LOCAL] Read Route B state/control and ran status check.              PASS
4.  [ABSTRACT][LEAN] Confirmed exported supplier signature as read.                PASS
5.  [ABSTRACT][LEAN_API] Rejected nonexistent Differentiable.analyticOnNhd.        DONE
6.  [ABSTRACT][LEAN_API] Confirmed DifferentiableOn.analyticOnNhd exact type.       PASS
7.  [ABSTRACT][LEAN] Added the 21-line wrapper canon+mirror without hmass.          DONE
8.  [ABSTRACT][LEAN] Ran direct wrapper check and full v3 build.                    PASS
9.  [CONTROL][TAINT] Scanned the new Lean file.                                    ZERO
10. [ABSTRACT][LEAN] Audited final theorem signature and axioms.                    PASS
11. [CONTROL][SHA256] Rechecked the sealed R6Export certificate.                   UNCHANGED
12. [CONTROL][GIT] Verified frozen and both muntz_r6 trees untouched.              PASS
13. [CONTROL][MIRROR] Verified canon/mirror wrapper byte identity.                 PASS
14. [CONTROL][LOCAL] Emitted no Aristotle submission or route promotion.           PASS
15. [CONTROL][STATE] Added one non-promoting success-history row last.             DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: HRP_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES
GOAL_SHA256: 90413b99281a29e0bd3fc734b9640b10973113ad0e6d8b4ee4babc717a5eb30c
SUPPLIER: R6Export.Rplus_differentiable
SUPPLIER_SCOPE: global Differentiable / entire
PASSAGE: Differentiable.differentiableOn -> DifferentiableOn.analyticOnNhd
DOMAIN_BRIDGE: none
WRAPPER: rplus_analyticOnNhd_shiftedHalfPlane
WRAPPER_LINES: 21
HMASS: absent
R6_INPUTS: 0<a; a≤b; support Icc a b; global LipschitzWith; 1≤Λ
LEAN: direct wrapper PASS; full build PASS (8040 jobs)
TAINT: zero
AXIOMS: [propext, Classical.choice, Quot.sound]
SEALED_R6EXPORT: unchanged
OPEN_INTERFACE: WITNESS_CLASS_VS_R6_HYPOTHESES_GAP
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
```

═══ FILE END: 045ANSWER: docs/routeB_bus/045_muntz_v3_supplier_hrp.answer.md ═══

