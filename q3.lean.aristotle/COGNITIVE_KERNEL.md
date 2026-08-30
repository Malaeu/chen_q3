# Cognitive Kernel v1

Status: control-plane guard / meta-learning layer.  This file is not a proof
source, not a theorem-status ledger, and not a replacement for
`PROJECT_ORCHESTRATOR.md`, active monitors, Lean, Aristotle, or certificate
checks.

## Purpose

The kernel prevents the autonomous proof loop from spending many iterations on
a strategy that no longer reduces the real mathematical gap.

It stores and invokes *ways of thinking*, not theorem claims:

```text
Task loop
  -> progress audit
  -> failure classification
  -> cognitive operator selection
  -> route review / local patch
  -> memory update
  -> next attempt
```

The main failure mode it targets is endless local bisection: splitting a proof
into smaller and smaller sublemmas without producing a checked theorem, a
certificate, a counterexample, a route kill, or a smaller named gap.

## Precedence

The kernel is subordinate to the project control-plane:

1. `PROJECT_ORCHESTRATOR.md` decides route/frontier.
2. Active monitors decide the current operational node.
3. Lean / hole-free Aristotle output / interval-rational certificates decide
   proof truth.
4. `COGNITIVE_KERNEL.md` decides when the current *strategy* should be audited.

It must not reopen killed routes, rename active goals, switch test classes, or
turn advisory model output into proof evidence.

## Trigger

Invoke the kernel when any of these are true:

- 3 consecutive iterations produce no new checked Lean theorem, certificate,
  counterexample, route-kill certificate, or strictly smaller named gap.
- The same theorem shape fails twice with only local payload changes.
- A patch keeps creating row/source fragments but no receiver can spend them.
- A route fork appears and both options are plausible.
- The active file starts accumulating diagnostic artifacts that are not proof
  objects.

The trigger does not mean "stop the project".  It means "stop the current way
of thinking and choose a more appropriate operator".

## Progress Audit

Each iteration must classify its result as exactly one of:

```text
PROOF_PROGRESS      Lean theorem / certificate / receiver closed.
GAP_SHRINK          same blocker reduced to a smaller exact interface.
COUNTEREXAMPLE      theorem-shape falsified or class killed.
ROUTE_KILL          branch killed with exact obstruction and registry pointer.
DIAGNOSTIC_ONLY     useful numbers/logs, not proof progress.
NO_PROGRESS         no new artifact that changes the proof state.
```

`DIAGNOSTIC_ONLY` repeated without `GAP_SHRINK` counts toward the loop trigger.

## Failure Classes

When the kernel triggers, the blocker must be classified:

```text
DEFINITIONAL_GAP          missing or wrong definition/interface.
COMPUTATIONAL_GAP         certificate/payload not yet generated or too large.
LOGICAL_GAP               theorem does not follow from available assumptions.
LITERATURE_GAP            needs an external theorem/source check.
REPRESENTATION_MISMATCH   wrong space/norm/operator/language for the target.
```

Representation mismatch is the most common expensive failure in this repo:
pointwise inequalities, scalar budgets, or local row bounds often do not
transport to the operator / cone / packet object that the proof actually needs.

## Proshka review hook

All review transport is governed exclusively by `docs/CODEX_CONTROL.md` and the
registered `workflow_runtime.py review-plan` / receipt lifecycle. This kernel
does not create a direct browser prompt, a new call class, or an INSIGHTS-based
queue. Before any eligible review, bind the exact downstream consumer, its
minimal sufficient interface, the necessity status of any named theorem, and
at least one weaker-interface probe. Reuse the living phase chat and the exact
UTF-8 attachment only when the canonical gate authorizes dispatch.

## After-Iteration Hook

At the end of each meaningful iteration:

```text
run_progress_audit()
if loop_or_bisection_trap_detected:
  classify_gap()
  select_cognitive_operator()
  if canonical_review_gate_is_eligible:
    run_registered_review_plan_and_living_chat_lifecycle()
  update_failed_strategy_memory()
  choose_smallest_next_proof_artifact()
```

The output of this hook is not a plan by itself.  It must name the next file,
the next theorem/certificate, and the validation command that would make the
next proof state more true.
