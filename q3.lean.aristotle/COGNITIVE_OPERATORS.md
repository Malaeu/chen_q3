# Cognitive Operator Registry

```json cognitive_operator_registry
{
  "schema": "q3_cognitive_operator_registry.v1",
  "canonical_enum": {
    "name": "PROSHKA_M2",
    "field": "cognitive_operator_used",
    "operators": [
      {"token": "REPRESENTATION_SHIFT", "description": "Reformulate the same source-faithful target in a representation that exposes a smaller proof obligation."},
      {"token": "COUNTEREXAMPLE_HUNT", "description": "Try to falsify or narrow the active theorem shape before adding proof infrastructure."},
      {"token": "DUALIZE", "description": "Move to the exact dual formulation while preserving source object, consumer, units, and quantifiers."},
      {"token": "BOUNDARY_CASE", "description": "Isolate and test the load-bearing endpoint, seam, extremal, or first omitted case."},
      {"token": "UNIT_AUDIT", "description": "Audit normalization, measure, scale, dimensions, and object identity before accepting a bridge."},
      {"token": "MINIMAL_LEMMA", "description": "Select the smallest named theorem that a current downstream consumer can spend."},
      {"token": "LITERATURE_BRIDGE", "description": "Import a primary-source theorem only through an explicit source-to-project interface audit."},
      {"token": "ABANDON_ROUTE", "description": "Terminate the active route at M2 scope after its theorem shape is falsified or made non-executable."}
    ]
  },
  "legacy_enum": {
    "name": "LEGACY_CONTROL_ACTION",
    "field": "legacy_control_action",
    "live_write_allowed": false,
    "operators": [
      {"token": "ContinueLocal", "description": "Keep the active route and make the next smallest proof patch."},
      {"token": "EscapeLoop", "description": "Stop local bisection and classify the blocker after repeated non-progress."},
      {"token": "RepresentationShift", "description": "Reformulate as operator, kernel, Loewner order, energy, duality, or certificate."},
      {"token": "CertificateShift", "description": "Move finite computation into an interval or rational generator with a small Lean receiver."},
      {"token": "CounterexampleSearch", "description": "Try to falsify a theorem shape before adding more lemmas."},
      {"token": "RouteKill", "description": "Write a kill certificate and return to the last branch point."},
      {"token": "ProshkaReview", "description": "Invoke the historical Proshka review control action at a real route fork."},
      {"token": "MemoryConsolidation", "description": "Persist a failed strategy or reusable invariant after reasoning."},
      {"token": "ReceiverMinimize", "description": "Build the smallest Lean receiver before generating more payload."}
    ]
  },
  "crosswalk": [
    {"legacy_token": "ContinueLocal", "relation": "LEGACY_ONLY", "canonical_token": null, "note": "Executor continuation state, not a cognitive transformation."},
    {"legacy_token": "EscapeLoop", "relation": "LEGACY_ONLY", "canonical_token": null, "note": "Loop-control trigger requiring a subsequent M2 choice."},
    {"legacy_token": "RepresentationShift", "relation": "DIRECT_ALIAS", "canonical_token": "REPRESENTATION_SHIFT", "note": "Same strategy transformation; spelling and namespace differ."},
    {"legacy_token": "CertificateShift", "relation": "LEGACY_ONLY", "canonical_token": null, "note": "Specialized proof-backend change; not necessarily a mathematical representation change."},
    {"legacy_token": "CounterexampleSearch", "relation": "DIRECT_ALIAS", "canonical_token": "COUNTEREXAMPLE_HUNT", "note": "Same falsification operation."},
    {"legacy_token": "RouteKill", "relation": "RELATED_NOT_EQUIVALENT", "canonical_token": "ABANDON_ROUTE", "note": "May kill one theorem family and roll back; M2 ABANDON_ROUTE terminates the active route."},
    {"legacy_token": "ProshkaReview", "relation": "LEGACY_ONLY", "canonical_token": null, "note": "Channel action governed by delegated review, not a reasoning operator."},
    {"legacy_token": "MemoryConsolidation", "relation": "LEGACY_ONLY", "canonical_token": null, "note": "Persistence action after reasoning."},
    {"legacy_token": "ReceiverMinimize", "relation": "RELATED_NOT_EQUIVALENT", "canonical_token": "MINIMAL_LEMMA", "note": "Specialized application of minimal-lemma discipline, not its full meaning."}
  ]
}
```

```json historical_cognitive_operator_receipts
{
  "schema": "q3_historical_cognitive_operator_receipts.v1",
  "live_write_allowed": false,
  "normalization_allowed": false,
  "receipts": [
    {
      "artifact_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_STURM_WEIGHTED_ENERGY_AND_EDGE_CONSUMER_2026-08-25.md",
      "artifact_blob": "e76fdc4e49cad08570b5a50acd0e5b0bf9d772c4",
      "original_token": "CONSUMER_STRENGTH_REDUCTION",
      "relation": "RELATED_NOT_EQUIVALENT",
      "related_canonical_token": "MINIMAL_LEMMA",
      "ratifying_verdict_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_A_STURM_CERTIFICATE_REGISTRY_SHADOW_2026-08-26.md",
      "ratifying_verdict_blob": "0f52763de5723b1d6faa91e302aa5f4a801ec195"
    },
    {
      "artifact_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_DERIVATIVE_H_SPLIT_AND_L2_STURM_PRIMARY_2026-08-25.md",
      "artifact_blob": "a6388d27b0104062d16b76baed8b2f050ea5d6c5",
      "original_token": "ENERGY_REPRESENTATION",
      "relation": "RELATED_NOT_EQUIVALENT",
      "related_canonical_token": "REPRESENTATION_SHIFT",
      "ratifying_verdict_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_A_STURM_CERTIFICATE_REGISTRY_SHADOW_2026-08-26.md",
      "ratifying_verdict_blob": "0f52763de5723b1d6faa91e302aa5f4a801ec195"
    },
    {
      "artifact_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_POST_FIRST_ORDER_FAMILY_CROSSWALK_FORK_2026-08-25.md",
      "artifact_blob": "b58136d3be6edc692d31afde6c1b14b981db4cac",
      "original_token": "TYPE_BOUNDARY",
      "relation": "RELATED_NOT_EQUIVALENT",
      "related_canonical_token": "UNIT_AUDIT",
      "ratifying_verdict_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_A_STURM_CERTIFICATE_REGISTRY_SHADOW_2026-08-26.md",
      "ratifying_verdict_blob": "0f52763de5723b1d6faa91e302aa5f4a801ec195"
    },
    {
      "artifact_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_POST_W5_PHYSICAL_ENERGY_FRONT_2026-08-25.md",
      "artifact_blob": "0cd7061221c3de95c59545c435c576fdb54f7ca4",
      "original_token": "FUNCTIONAL_AUDIT",
      "relation": "RELATED_NOT_EQUIVALENT",
      "related_canonical_token": "UNIT_AUDIT",
      "ratifying_verdict_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_A_STURM_CERTIFICATE_REGISTRY_SHADOW_2026-08-26.md",
      "ratifying_verdict_blob": "0f52763de5723b1d6faa91e302aa5f4a801ec195"
    },
    {
      "artifact_path": "docs/routeB_bus/proshka/PROSHKA_VERDICT_OWNER_NEXT_STEP_WEIGHTED_DIRICHLET_AND_VITALI_LITERATURE_TRIAGE_2026-08-27.md",
      "artifact_blob": "8cc3bd491381030464d414bb6d391ae11db27b0a",
      "original_token": "SOURCE_ACQUISITION",
      "relation": "RELATED_NOT_EQUIVALENT",
      "related_canonical_token": "LITERATURE_BRIDGE",
      "ratifying_verdict_path": "docs/routeB_bus/proshka/CODEX_ADJUDICATION_SOURCE_ACQUISITION_OPERATOR_2026-08-27.md",
      "ratifying_verdict_blob": "9430e0ec63c39c5d05bac880139fe7880f7dcf2d"
    }
  ]
}
```

These receipts are exact historical exceptions, not aliases or replacement
rules.  They do not make the original tokens canonical, legacy,
query-groupable, or valid for new writes.  Each receipt is consumed only by
the exact pinned occurrence in the named immutable Git blob.

Status: versioned registry for `COGNITIVE_KERNEL.md` and Proshka M2. These
values guide strategy selection and executor control; they do not prove
mathematics. `PROSHKA_M2` is the sole live enum for
`cognitive_operator_used`. `LEGACY_CONTROL_ACTION` is frozen provenance and
must never be silently normalized into M2.

## Canonical M2 Operators

| Operator | Binding role |
| --- | --- |
| `REPRESENTATION_SHIFT` | Change the mathematical representation without changing the source-faithful target. |
| `COUNTEREXAMPLE_HUNT` | Falsify or narrow the theorem shape before building more. |
| `DUALIZE` | Move to the exact dual formulation with invariants preserved. |
| `BOUNDARY_CASE` | Isolate the load-bearing endpoint, seam, extremal, or first omitted case. |
| `UNIT_AUDIT` | Check units, normalization, measure, scale, and object identity. |
| `MINIMAL_LEMMA` | Select the smallest theorem with a named downstream consumer. |
| `LITERATURE_BRIDGE` | Import a primary-source theorem through an explicit interface audit. |
| `ABANDON_ROUTE` | Terminate the active M2 route after a decisive kill. |

## Frozen Legacy Control-Action Table

| Operator | Trigger | Action | Required output |
| --- | --- | --- | --- |
| `ContinueLocal` | One live gap and the last iteration gave `PROOF_PROGRESS` or `GAP_SHRINK`. | Keep the active route and make the next smallest proof patch. | theorem/certificate/file + validation command |
| `EscapeLoop` | 3 iterations with no checked theorem, no smaller gap, and no counterexample. | Stop local bisection and classify the blocker. | gap class + failed strategy entry |
| `RepresentationShift` | Same object fails because the proof lives in a different norm/space/operator. | Reformulate as operator, kernel, Loewner order, energy, duality, or certificate. | new bridge theorem/cert target |
| `CertificateShift` | Lean arithmetic or row replay is growing but the statement is finite. | Move computation into interval/rational generator and leave Lean a small receiver. | generator + checkable certificate schema |
| `CounterexampleSearch` | A theorem shape may be false or too broad. | Try to falsify the shape before adding more lemmas. | witness, negative certificate, or narrowed theorem |
| `RouteKill` | A theorem shape is falsified in the intended class. | Write a kill certificate and registry pointer, then return to the last branch point. | killed route entry + next live route |
| `ProshkaReview` | Route fork, theorem statement uncertainty, generated payload ambiguity, or kernel trigger with browser available. | Ask Proshka through Computer Use with options A/B/C. | advisory choice + local acceptance/rejection |
| `MemoryConsolidation` | A failed strategy or reusable trick appears. | Record it in active failed-strategy memory and `INSIGHTS` if project-reusable. | grep-friendly failed_strategy entry |
| `ReceiverMinimize` | Many generated facts exist but no receiver can spend them. | Build the smallest Lean receiver theorem before more payload generation. | isolated receiver theorem |

Only `RepresentationShift` and `CounterexampleSearch` are direct aliases of
M2 values. `RouteKill` and `ReceiverMinimize` are related but non-equivalent;
the remaining five are legacy-only. Original tokens are always retained.

## Failed Strategy Schema

Use this YAML shape in `ACTIVE/FAILED_STRATEGIES.yaml` or the active report:

```yaml
- name: short_grep_friendly_name
  context: route / node / theorem family
  symptom: repeated behavior that did not create proof progress
  cause: exact blocker, not a vague diagnosis
  failed_strategy: what not to keep doing
  legacy_control_action: one of the frozen legacy control actions above
  cognitive_operator_used: one canonical M2 operator
  next_action: smallest artifact that would be real progress
  evidence:
    files:
      - path
    failure_codes:
      - EXACT_FAILURE_CODE
  status: active | killed | avoided | superseded
```

## Representation Shift Checklist

When invoking `RepresentationShift`, try these translations in order:

1. scalar inequality -> quadratic form;
2. pointwise majorant -> operator/Loewner domination;
3. float eigenvalue -> interval/rational PSD certificate;
4. local row family -> receiver-spendable budget theorem;
5. finite LP slack -> same-unit analytic budget comparison;
6. repeated Lean arithmetic -> compact certificate receiver;
7. theorem-shape failure -> route-kill certificate.

## Bisection Trap Test

Local bisection is healthy only while at least one is true:

- the next sublemma has a named receiver already waiting for it;
- the new artifact reduces a failure code to a smaller failure code;
- the generated payload is directly spendable by a checked theorem;
- a negative result kills a class;
- the work removes a hidden axiom or narrows a theorem statement.

Otherwise invoke `EscapeLoop`.
