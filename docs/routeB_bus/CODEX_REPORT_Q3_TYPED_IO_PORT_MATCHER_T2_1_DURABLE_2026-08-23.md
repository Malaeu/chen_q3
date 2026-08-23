# CODEX REPORT — Q3 TYPED I/O PORT MATCHER T2.1 DURABLE

STATUS: PASS
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_T2_1_DURABLE
BODY: Linux (Claude); owner goal-scoped grant («И! Го!!!», 2026-08-23 night)
AUTHORITATIVE_SOURCE: docs/routeB_bus/proshka/PROSHKA_ADDENDUM_SPEC_011_T2_V0_CONCURRENCY_2026-08-23.md (commit a1ed346b) + base audit dbf09fa3
MODE: BOUNDED_EXPLORATION / NO_LIVE_ROUTE_MUTATION — honored; only the
  WRITE_ONLY paths of the directive were touched.
BASE_HEAD: 032bffd9b5896a13175a09217cf829470b631cbe

## MATERIALIZED ARTIFACTS (all in the WRITE_ONLY list)

  docs/cartographer/typed_io_schema_v1_1.yaml       — schema v1.1: PORT_SPEC/
    ADAPTER_SPEC (evidence-bearing), ADAPTABLE_PAIRS, REPRESENTATIVE_SEMANTICS
    (the a.e./pointwise firewall), HYPEREDGE_MATCH_RULE (one substitution
    environment), RECEIPT_V1
  docs/cartographer/comparator/port_matcher.py       — durable matcher:
    hard gates -> representative firewall -> soft refinements -> closed enum;
    match_hyperedge builds ONE substitution environment per AND-edge
  docs/cartographer/comparator/test_port_matcher.py  — replay suite
  docs/cartographer/comparator/fixtures/
    adapter_registry.json   — 3 evidence-bearing entries (theorem name,
      file, line, commit, blob, pasted #check type, loss ledger, scope,
      verifier, shared parameter context); the W1 adapter is REGISTERED AS
      A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE with the explicit DROPS line
      "pointwise evaluation at any selected frequency" (mandatory repair)
    adaptable_pairs.json    — declared adapter-target classes
    plants.json             — frozen P1-P6, NC1-NC3, C2, C2_POS with pasted
      kernel types from the V0 H1 harness

## MANDATORY REPLAY + NEW PLANTS (verbatim suite output)

  P1      wrong source family                 expected=HARD_MISMATCH          got=HARD_MISMATCH          PASS
  P2      FINITE_CELL -> COFINAL_FAMILY       expected=HARD_MISMATCH          got=HARD_MISMATCH          PASS
  P3      isometry, pre-W1 registry           expected=ADAPTER_REQUIRED       got=ADAPTER_REQUIRED       PASS
  P4      full-endpoint vs midpoint strict    expected=REFINEMENT_LOSS        got=REFINEMENT_LOSS        PASS
  P5      Rayleigh scalar as residual         expected=HARD_MISMATCH          got=HARD_MISMATCH          PASS
  P6      a.e. adapter to POINTWISE consumer  expected=REFINEMENT_LOSS        got=REFINEMENT_LOSS        PASS
  NC1     lawful W1 adapter edge (ae target)  expected=EXPLICIT_ADAPTER_MATCH got=EXPLICIT_ADAPTER_MATCH PASS
  NC2     lawful exact self edge              expected=EXACT_MATCH            got=EXACT_MATCH            PASS
  NC3     ae feeds Lp-class (lawful weakening) expected=EXACT_MATCH           got=EXACT_MATCH            PASS
  C2      SHARED_CONTEXT_INCOHERENCE          expected=HARD_MISMATCH          got=HARD_MISMATCH          PASS
  C2_POS  coherent hyperedge control          expected=EXACT_MATCH            got=EXACT_MATCH            PASS

  FAILURES=0  WRONG_OBJECT_ESCAPE=0  FALSE_REJECTION=0

C2 details: three providers with contexts (m1,N1),(m2,N2),(m3,N3) offered to
a consumer edge requiring shared (m,N) — killed by the single-environment
unification with reason SHARED_CONTEXT_INCOHERENCE, even though every
pairwise surface matches; the coherent control (same (m7,N7) everywhere)
passes.  Pairwise matching alone would have accepted the incoherent edge —
the plant demonstrates exactly the C04 failure the addendum predicted.

## PASS CRITERIA AUDIT (T2.1)

- all prior controls preserve their outcomes: YES (P1-P5, NC1-NC2 unchanged)
- C2 is HARD_MISMATCH: YES
- a.e. adapter accepted only for a.e./Lp consumer: YES (NC1, NC3);
  pointwise consumer remains unclosed: YES (P6 -> REFINEMENT_LOSS with the
  C04/C10 reason line)
- matcher source and fixtures committed: YES (this commit)
- content-addressed receipt complete: YES (below)
- wrong-object escape = 0: YES;  false rejection = 0: YES

## T2_PORT_MATCHER_RECEIPT_V1

{
  "RECEIPT": "T2_PORT_MATCHER_RECEIPT_V1",
  "schema_sha256": "8a309650caba11ad4d456a8c73a5e66b6033bc381820c60921399292e70b225c",
  "matcher_sha256": "1cb863fda6235d28f4d7880269329809451d3048e0ab3406010ca17fc01cf455",
  "tests_sha256": "21dbe9091cee1ad729d09937f0235bdee277894a367744dc5226606133c8ec26",
  "fixture_manifest": {
    "adaptable_pairs.json": "8f0ee7eb5ce9576deb4f8c8d47800765e168748070286fc383ea06b095fc5f5e",
    "adapter_registry.json": "cf525edfe749366f004b0cf109a86652aa8e42edc65c26e93d35ed18f861466a",
    "plants.json": "ec77d8c18c4eafd27ba27ef7ff66df1bc77699dd9fb0dc60f1aa0391efa46913"
  },
  "replay_command": "python3 docs/cartographer/comparator/test_port_matcher.py"
}

toolchain note: kernel types in fixtures were pasted from the V0 H1 harness
run (lake env lean, mathlib v4.26.0 rev 2df2f015..., recorded in the V0
report); the W1 adapter evidence is pinned to commit 4984a107 with the exact
Lean blob in the registry entry.

CLOSES: [T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT]
OPENS: []
NEXT_IF_PASS: T3_TYPED_GAP_SIGNATURE_IN_CHEAP (awaits owner grant)

ROUTE: CHALLENGER_NOT_RH · BUS_010: VOID · ROUTE_PROMOTION: false · RH_CLAIM: false
