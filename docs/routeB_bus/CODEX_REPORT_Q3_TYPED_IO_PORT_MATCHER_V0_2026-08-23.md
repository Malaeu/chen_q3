# CODEX REPORT — Q3 TYPED I/O PORT MATCHER V0 (T2)

STATUS: PASS
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_V0
BODY: Linux (Claude); owner goal-scoped grant relayed 2026-08-23 (execution
  command quoted from the authoritative verdict, relayed by the owner)
AUTHORITATIVE_SOURCE: docs/routeB_bus/proshka/PROSHKA_VERDICT_TYPED_IO_MEET_IN_THE_MIDDLE_GAP_ALGEBRA_2026-08-23.md (commit 545cc3f9)
MODE: BOUNDED_EXPLORATION / NO_LIVE_ROUTE_MUTATION — honored: no production
  Lean touched, no goals/answers/runtime/state files touched; harnesses and
  the matcher live in the session scratchpad only; this report is the single
  repository write.
BASE_HEAD: 4984a1071b6728ab64fee318ebaf0e3ee07bf5fb

## PHASE 1 — SCHEMA (attachment form, per the directive's either/or)

PORT_SPEC_V1 / MODULE_SPEC_V1 / ADAPTER_SPEC_V1 / PORT_MATCH_RESULT_V1 are
used exactly as defined in the authoritative verdict sections 3-7; this
report does not fork them (no second schema source).  V0 additions, both
restriction-only:

1. ADAPTABLE_PAIRS — a declared list of identity pairs that are known
   adapter TARGETS: an edge between them WITHOUT a registered verified
   adapter classifies as ADAPTER_REQUIRED (a named missing wire); any
   UNDECLARED identity pair stays HARD_MISMATCH.  This implements the
   verdict's distinction between P3 (adapter class) and P5 (category error).
2. Registry snapshots — a match runs against an explicit adapter registry;
   P3 is evaluated against the pre-W1 snapshot (the adapter theorem did not
   exist when the plant was frozen), NC1 against the current registry that
   contains the kernel-green W1 crosswalk (commit 4984a107).

Kernel type rule honored: every kernel_type string in the port specs is
PASTED from the H1 harness `#check` output below — never reconstructed.

## PHASE 2 — HARNESSES AND PLANTS

### H1 kernel-type extraction (temporary Lean harness, scratchpad)

Command (WORKDIR q3.lean.aristotle):
  lake env lean <scratchpad>/tio_harness/H1_kernel_types.lean   — EXIT 0

Extracted (verbatim, abbreviated here to the load-bearing lines):
  prolateCombination : ProlatePair → ℝ → ℂ
  explicitCCMLimitH : ℝ → ℂ
  ccmWeilMatFinite_centrosymmetric : ∀ (mProject N : ℕ), 2 ≤ mProject → 1 ≤ N →
    ∀ (i j : CCMModeFinite N), ccmWeilMatFinite ... (ccmNegFinite ...) ... = ccmWeilMatFinite ... i j
  selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates : ... ∀ᶠ (k : ℕ) in Filter.atTop, ...
  sourceLogWindowFourierL2Isometry : (i : PairIndex) → ↥(H_m i) →ₗᵢ[ℂ] ↥(Lp ℂ 2 volume)
  coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension :
    ∀ (i) (x), ↑↑((sourceLogWindowFourierL2Isometry i) x) =ᵐ[volume]
      fun t => FourierTransform.fourier (sourceLogWindowZeroExtension i x) t
  sourceLogWindowZeroExtension : (i : PairIndex) → ↥(H_m i) → ℝ → ℂ
  selectedFerrersFiniteCCMRayleigh : CCMLemma73PreAnchorPort ... → ℕ → ℝ
  selectedFerrersFiniteCCMCommutatorResidualDefect : (P : ...) → (k : ℕ) → CCMModeFinite ... → ℂ

### Plant runs (matcher output, verbatim)

  P1 same surface / wrong source family            expected=HARD_MISMATCH   got=HARD_MISMATCH   PASS
      why: source_family: selected-Ferrers-prolate-pair vs explicit-CCM-limit-target
  P2 FINITE_CELL offered to COFINAL_FAMILY         expected=HARD_MISMATCH   got=HARD_MISMATCH   PASS
      why: scope FINITE_CELL offered to COFINAL_FAMILY consumer
  P3 L2 isometry offered as pointwise Fourier      expected=ADAPTER_REQUIRED got=ADAPTER_REQUIRED PASS
      why: declared adaptable pair has no verified adapter registered (pre-W1 snapshot)
  P4 midpoint demanded, full-endpoint offered      expected=REFINEMENT_LOSS  got=REFINEMENT_LOSS  PASS
      why: representative: full-endpoint-production vs required midpoint-pointwise
  P5 Rayleigh scalar offered as residual           expected=HARD_MISMATCH   got=HARD_MISMATCH   PASS
      why: object rayleigh-scalar-value is not residual-defect-norm; no adapter; pair undeclared
  NC1 lawful adapter edge (W1 crosswalk)           expected=EXPLICIT_ADAPTER_MATCH got=same     PASS
      chain: A_ISOMETRY_TO_POINTWISE_FOURIER (LEAN, theorem_ref = the kernel-green
      coeFn_..._eq_fourier_... of commit 4984a107; loss ledger: a.e. only)
  NC2 lawful exact self edge                       expected=EXACT_MATCH      got=EXACT_MATCH     PASS

WRONG_OBJECT_ESCAPE = 0.  Matcher development log: two internal defects were
found and fixed BY the plants before the final run (gate-found adapters were
dropped before classification; adaptable-pair gradation was missing) — the
plants did their job on the matcher itself.

## PHASE 3 — PASS CRITERIA AUDIT

- all five plants classified exactly: YES (5/5)
- wrong-object escape = 0: YES (P1/P2/P5 rejected at hard gates; nothing
  wrong-object was ever classified as any MATCH class)
- no candidate called a supplier without a verified edge: YES — the only
  accepted adapter edge carries the kernel-green W1 theorem reference;
  negative controls prove the matcher is not a reject-everything detector
- schema does not duplicate theorem statements manually: YES — kernel types
  pasted from `#check`; refinements only restrict composability
- DO_NOT_EDIT list: fully honored (git diff shows this file only)

## ADAPTER REGISTRY V0 (session state, recorded for T3)

  A_L2_TO_L1_FINITE_WINDOW      (LEAN; eLpNorm compare + restrictL2_l1_le; loss sqrt(L_m))
  A_ISOMETRY_TO_POINTWISE_FOURIER (LEAN; W1 crosswalk 4984a107; loss: a.e. only)
  A_AE_TO_LP_CLASS              (LEAN; MeasureTheory.Lp.ext; loss: null-set data)

## MATCHER SOURCE (attachment; scratchpad file tio_harness/port_matcher_v0.py)

The full V0 source (140 lines) is retained in the session scratchpad and is
reproducible from this report's specification: hard gates in the verdict's
order (trust floor -> source_family/scope/quantifier/normalization/units/
object_identity) -> kernel comparison -> soft refinements with adapter
lookup -> closed-enum classification.  V0 is a session tool, deliberately
NOT installed into the repository: per the verdict, T3 will integrate the
gap signature into cheap.py as the durable home.

CLOSES: [T2_PORT_MATCHER_LOCAL_PLANTS]
OPENS: []
NEXT_IF_PASS: T3_TYPED_GAP_VECTOR_IN_CHEAP (awaits owner grant)
PREDICTION_NOTE: P_TIO_1 (>=95% naive-edge rejection) remains UNTESTED —
  it needs a real depth-2 candidate corpus, which is T3/T4 material; the
  plants test exactness, not volume.

ROUTE: CHALLENGER_NOT_RH · BUS_010: VOID · ROUTE_PROMOTION: false · RH_CLAIM: false
