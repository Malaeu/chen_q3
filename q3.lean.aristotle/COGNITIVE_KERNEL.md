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

## Proshka / Computer Use Hook

In Codex Desktop sessions where the in-app browser is open to the ChatGPT
Pro/Louise project chat, Computer Use is part of the route-review loop.

When the kernel trigger fires and the browser is available:

1. Ask Proshka before changing strategy.
2. Send a compact self-contained prompt:
   - route;
   - current theorem/file;
   - exact blocker and failure code;
   - what was tried;
   - options A/B/C;
   - Codex recommendation;
   - one concrete question.
3. Treat the answer as advisory only.
4. Accept only the theorem shape after local verification.
5. Record the accepted route choice in the active report/monitor or
   `docs/INSIGHTS.md`.

If the browser is unavailable or not confirmed in the current session, write
the existing `PRO_REVIEW_REQUEST` block instead.  Do not claim automatic
external access.

## After-Iteration Hook

At the end of each meaningful iteration:

```text
run_progress_audit()
if loop_or_bisection_trap_detected:
  classify_gap()
  select_cognitive_operator()
  if route_fork_or_strategy_change and browser_available:
    ask_Proshka_via_Computer_Use()
  else if route_fork_or_strategy_change:
    write_PRO_REVIEW_REQUEST()
  update_failed_strategy_memory()
  choose_smallest_next_proof_artifact()
```

The output of this hook is not a plan by itself.  It must name the next file,
the next theorem/certificate, and the validation command that would make the
next proof state more true.

