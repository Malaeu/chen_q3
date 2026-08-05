# Q3 Obstruction Atlas

> **FROZEN 2026-08-05 — migrated to `knowledge.db`.**
> All 8 walls now live in `q3.lean.aristotle/aristotle_db/knowledge.db`
> (table `kill`, `unit_type='wall'`, `status='standing'`). Query with
> `./orchestrator/kb.py list --unit-type wall`; add new walls with
> `./orchestrator/kb.py add --unit-type wall`, **not** by editing this file.
> Note the content itself says "As of 2026-05-26" while `AGENTS.md` still cites this
> atlas as current — that drift is exactly why the walls were moved into a queryable table.

This atlas is repo-level guidance for the Q3 PSD-pd Step32 proof loop. It is
not a proof of RH and must not be used to bypass Lean validation.

## Scope

Step32 is the finite certified B-spline packet block route. The local target is
to connect analytic Weil-form objects to concrete finite certificates with
checked Lean proofs.

## Current Frontier

As of 2026-05-26, these Step32 gates are closed and should not be reopened
without new evidence:

- Arch integrability and packet-expansion preliminaries.
- Analytic kernel / coefficient receivers used by the centered B-spline route.
- The concrete matrix-identification bridge:
  `centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm`.
- Boundary row identification:
  `centeredBSplineBoundaryRows_identify_Q`.
- Q-row hboxes, boundary Gram radius import, penalty radius dominance import,
  base matrix hbox receiver, analytic P0 receiver, entry hbox bundle scaffold,
  prime dictionary bounds, and centered B-spline R nonnegativity.

The active PSD monitor is:

`q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`

The H1/PO3 `PHASE_MONITOR.md` is a separate route monitor and is parked for the
current PSD Step33 bootstrap unless explicitly requested.

The live PSD gate is now the generated Step21/Step22 entry-hbox certificate
layer:

- `PrimaryK11BaseEntryHboxCert`
- `ControlK9BaseEntryHboxCert`
- `ActiveCenteredCoeffEntryHboxCert`

The concrete Lean surfaces are:

- `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`
- `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean`

## Walls

### Matrix-identification wall

The matrices `A`, `P`, and `Q` must be identified as analytic Weil-form
matrices on the centered B-spline packet basis. Numerical tables alone are not
enough. Reuse the closed matrix bridge instead of rebuilding it.

### Coordinate wall

Do not prove PSD directly in raw coordinates if the route requires a Gram
correction. The proof must respect the certified basis and coefficient model
already wired into Step32.

### Boundary leakage wall

Boundary-null claims must pass through the established boundary-row machinery.
Do not replace boundary control with an informal endpoint argument.

### Prime-side wall

The finite prime-side matrix `P` must come from the analytic/dictionary/hbox
route. A positive table or scalar mirror is not a proof of the imported prime
form.

### Step33 scalar replay swamp wall

Do not close Step33A.1 by manually sweeping entries or scalar summands one by
one.  The `(0,0)` direct-profile support-zero certificate is only a pilot.  The
prime profile must first be compressed by packet center difference, then by a
compact-support live prime-shift filter, and only live terms should receive
generated hbox payloads.  If truncated-power summands create cancellation-heavy
obligations, add a piecewise-polynomial/segment receiver for the centered
cardinal B-spline instead of expanding all summands.

### P0 enclosure wall

The `P0` hbox fields in the active entry certificate must be real enclosure
proofs for the analytic base entries. They cannot be filled by weakening the
theorem statement or by asserting table equality without bounds.

### Finite-certificate wall

Finite certificates such as `FinitePenaltyCert` and certified coefficient
blocks must remain proof-side objects. Do not introduce fake axioms, trusted
payload shortcuts, or generated declarations with holes.

### Finite-to-global wall

Step32 closes a finite certified block in the Q3 chain. It does not by itself
claim or prove a global RH theorem.

## Acceptance Checks

- Run `lake env lean <touched Lean file>` from `q3.lean.aristotle`.
- Run `scripts/q3_check.sh <touched Lean file>` from the repo root.
- Search touched Lean files for `sorry`, `exact?`, and `admit`.
- Do not edit `Q3.Main` for Step32 local gates.
- Do not add axioms or weaken theorem statements to make a gate compile.
