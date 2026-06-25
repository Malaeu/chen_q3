# Cognitive Operators

Status: operator catalog for `COGNITIVE_KERNEL.md`.  These operators guide
strategy selection; they do not prove mathematics.

## Operator Table

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

## Failed Strategy Schema

Use this YAML shape in `ACTIVE/FAILED_STRATEGIES.yaml` or the active report:

```yaml
- name: short_grep_friendly_name
  context: route / node / theorem family
  symptom: repeated behavior that did not create proof progress
  cause: exact blocker, not a vague diagnosis
  failed_strategy: what not to keep doing
  escape_operator: one of the operators above
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

