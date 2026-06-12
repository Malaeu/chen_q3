# RH Trick Workflow

Date: 2026-06-12

Purpose: define how Q3 uses `docs/RH_TRICK_ATLAS.md` when a proof route hits a
wall.  The workflow turns a blocker into a small mathematical probe without
mutating the active route or claiming theorem progress.

This is documentation only.  It does not edit Lean files, does not touch
`Q3.Main`, and does not change the active Step33 route.

## Separation of Layers

- `RH_TRICK_ATLAS.md` is the toolbox: reusable mathematical transformations.
- A probe is route-local: one blocker, one primary trick, one minimal
  experiment, one success/failure check.
- Track B is research: it may search for a new object or theorem family, but it
  is not itself an atlas card.
- Proof status changes only after Lean validation or a hole-free theorem output
  is integrated through the project workflow.

## Wall-to-Door Protocol

When a route hits a wall, do this before expanding brute-force payloads.

1. Name the exact wall.

   Record the target theorem or receiver, file, object, missing field, active
   budget, and current validation status.  If this is Step33, preserve the
   active monitor and request/report discipline.

2. Classify the wall shape.

   Useful wall shapes include:

   - many scalar inequalities or chunks;
   - wrong coordinate or normalization;
   - hard integral over a continuous interval;
   - positivity over a large class of objects;
   - transform-side expression looks simpler than source-side expression;
   - bad cells or large values form a structured family;
   - boundary/cap leakage;
   - route may be proving the right inequality for the wrong object.

3. Scan the atlas.

   Pick one primary trick and at most one control-surface trick.  Write why the
   trick preserves the exact object required by the route.

4. Write a route-local probe.

   A probe must include:

   - atlas anchor;
   - exact target theorem or receiver;
   - transformed object;
   - preserved structure;
   - dropped structure / danger;
   - minimal experiment;
   - success check;
   - failure check;
   - rollback or false-for-now condition.

5. Run the smallest experiment.

   Use one cell, one window, one finite `K`, or one compressed family first.
   Do not scale to all rows/chunks until the first probe produces a theorem
   shape that could feed the existing receiver.

6. Decide.

   Mark the probe as:

   - `checked`: Lean receiver compiles without holes and validation is recorded;
   - `promising`: theorem-shaped but not integrated;
   - `false-for-now`: it loses structure, fails the budget, or proves a nearby
     object;
   - `needs-review`: the theorem statement or route fork needs Pro/Louise.

7. Log without overclaiming.

   Route-local reports may say that a trick produced a receiver, a theorem
   shape, or a kill certificate.  They must not say Step33, L3, Q3, or RH moved
   unless the corresponding formal gate actually moved.

## Probe Template

```md
# Experiment Card EC-XXX -- <short name>

Status:
Atlas anchor:
Active route:
Exact target:
Current blocker:

## Trick

Transformed object:
Preserved structure:
Dropped structure / danger:

## Minimal Experiment

Input:
Output wanted:
Theorem-shaped receiver:

## Success Check

- no axiom/sorry/admit/exact?;
- lands in the existing receiver without changing its statement;
- validation command:

## Failure Check

- proves a nearby object;
- consumes more margin than available;
- depends on the original blocker;
- requires a route fork.
```

## Current Probe Index

- `EC-001`: A-side interpolation replacement probe.
  Path:
  `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_side_interpolation_replacement_probe.md`.
  Atlas anchors: card 2 `Cohn-Kumar-Miller-Radchenko-Viazovska
  Interpolation` and card 5 `Margin Ledger`.
  Target: first raw-Omega Step33A.1-A worst cell, replacing scalar
  Taylor/interval replay by a finite rational interpolation or jet certificate
  for `hRawCenterCoeffAbs` and `hResidualDerivBoundOnCell`.

## Rule of Thumb

If a blocker asks for "more rows", "more chunks", "more intervals", or "more
generated scalar facts", pause and ask which atlas trick could turn that work
into a structural identity, interpolation theorem, dual certificate,
Fourier-side rewrite, positivity cone, or budgeted ratchet.
