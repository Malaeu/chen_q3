# Goal 046 — MuntzV3 hRp on the EXACT v3 class (Proshka directive, verbatim contract)

ISSUED: 2026-07-31 · ORIGIN: Proshka CODEX DIRECTIVE in verdict
  proshka/PROSHKA_VERDICT_044_R6_LIBRARY_ONLY_CANONICAL_HRM_OPEN_2026-07-31.md
  (her target label "045_MuntzV3_Hrp_ExactClass" was written before Goal 045 closed;
  045 is immutable, so her directive is transcribed as Goal 046 — content verbatim).
MODE: LOCAL_FIRST · NO_ARISTOTLE · SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
LEDGER CONTEXT (binding, from the same verdict): 044/045 are RATIFIED as R6-LIBRARY
suppliers only; canonical D0-class hRm/hRp remain OPEN. This goal discharges hRp on
the exact v3 hypothesis class (no 0<a, no global Lipschitz, no zero-mass).
NAMING NOTE: "P045-1/P045-2" below are Proshka's MANDATORY PLANT ids quoted
verbatim; they are distinct from the Mythos predictions P045-1/2 already scored in
045.answer.

## PRIMARY THEOREM (verbatim)

```lean
theorem rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane
```

FILE: new file under muntz_v3/RequestProject/.

## INPUTS (verbatim)

- muntz_v3/RequestProject/Main.lean
- muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean
- muntz_v3/RequestProject/R6Export/TailAnalyticity.lean — as proof TEMPLATE only
- Goal 044 answer

## PROOF ROUTE (verbatim)

1. Preserve exact v3 definitions of Estar and Rplus.
2. Derive an a.e. finite bound for h on Icc 0 b from LipschitzOnWith on Ico 0 b,
   treating {b} as a null endpoint.
3. Prove measurability/local integrability of Estar on Ioi Λ.
4. Prove Estar h u = 0 for u > b.
5. Rewrite Rplus as the Mellin transform of a function supported in the bounded
   interval (Λ, b].
6. Prove Differentiable ℂ, then restrict to shiftedHalfPlane with .analyticOnNhd.

## FORBIDDEN (verbatim)

- no hypothesis 0 < a;
- no support replacement Icc 0 b → Icc a b;
- no global LipschitzWith;
- no zero-mass hypothesis;
- no modification of Main.lean;
- no mutation of Goal 044;
- no Aristotle;
- no sorry/admit/axiom/native_decide/exact?.

## MANDATORY PLANTS (verbatim; K1 judge-before-player)

P045-1 (plant): instantiate the theorem on the PL1 witness h(u) = 1_Ioc(0,1)(u)·u;
  it touches zero, has an endpoint jump, and has nonzero mass. The theorem must
  accept it.
P045-2 (plant): dependency audit must show no use of hmass, positive lower
  support, or global Lipschitz.

## VALIDATION (verbatim)

```text
lake env lean <new-file>
lake build
taint scan
#print axioms rplus_analyticOnNhd_shiftedHalfPlane_v3Class
expected axioms: [propext, Classical.choice, Quot.sound]
```

## SUCCESS

HRP_SUPPLIER_DISCHARGED_FOR_V3_CLASS

## FAILURE (exactly one, fail-closed)

HRP_V3CLASS_ESTAR_MEASURABILITY_GAP
HRP_V3CLASS_ESTAR_LOCAL_INTEGRABILITY_GAP
HRP_V3CLASS_ENDPOINT_AE_GAP
HRP_OBJECT_MISMATCH
PLANT_NOT_DETECTED
LEAN_BUILD_FAIL

## NEXT AFTER SUCCESS (registered, not part of this goal)

Load-bearing Müntz gap (Proshka):
  EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz → canonical-class hRm
  (endpoint-aware Riemann-sum estimate; the jump at b handled explicitly).

## Registered predictions (before execution)

P046-C1 (conductor): the endpoint-a.e. technique from the T4a bridge file
  transfers directly; friction concentrates in step 3 (Estar local integrability
  on Ioi Λ), not in step 6.
P046-C2 (conductor): the PL1 plant passes on first build once the main theorem
  compiles (no witness-specific work needed).

## Answer requirements

046_muntz_v3_hrp_exact_class.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG;
plant results explicit (accept/reject per plant); dependency audit listed;
scoring P046-C1..C2; goal consumed by SHA-256; WITNESS_CLASS ledger restated
(R6-library vs canonical); one non-promoting state row; ROUTE_B_STATE last;
canon+mirror one transaction; report — do not repair — divergences.
