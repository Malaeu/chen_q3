# Aristotle channel

Aristotle takes informal math (markdown+LaTeX) and returns Lean 4. It is the 4th lane —
used only on an escalation trigger, not by default (Mythos routes finite/decidable goals
to Codex's local Lean as the cheapest decisive channel).

## Two access paths

**CLI / Python (primary, scriptable — this is what the conductor drives):**
- From the repository root, activate the project environment: `source .venv/bin/activate`.
- Keep `ARISTOTLE_API_KEY` in env (never on the CLI arg line — leaks to history).
- Submit async and poll:
  ```python
  import asyncio
  from aristotlelib import Project
  from aristotlelib.local_file_utils import gather_file_imports

  ROOT = "<mac q3.lean.aristotle root>"
  # submit (auto_add_imports=False to avoid outermost-root resolution breakage; pass
  # transitive imports as context_file_paths):
  pid = await Project.prove_from_file(
      input_file_path="<task>.lean",
      auto_add_imports=False, validate_lean_project=False,
      context_file_paths=[...deps...], wait_for_completion=False,
      output_file_path="aristotle_output/<task>_aristotle.lean")
  # poll:
  p = await Project.from_id(pid); print(p.status, p.percent_complete)
  # download when COMPLETE:
  path = await p.get_solution("aristotle_output/<pid>-output.lean")
  ```
- **Always scan the result for holes** before integrating:
  `rg -n "sorry|exact\?|admit" <file>` — files with holes are DRAFT; extract only
  hole-free lemmas. Then `lake env lean <file>` to confirm it compiles.
- Informal submission for pure-math targets: `aristotle prove-from-file --informal --no-wait problem.md`.

**Browser dashboard (visibility only):** `aristotle.harmonic.fun/dashboard/requests/<id>`.
Now visible to the conductor via `list_pages` — use it to watch a run's status/percent,
not to submit (submit via the CLI so state is scriptable).

## Completion detection

Aristotle jobs are async (minutes–hours). The conductor polls `Project.from_id(pid).status`
until `COMPLETE`/`FAILED` — this is a clean programmatic signal (no DOM detection needed).
Cadence: match the job (start at ~5 min, back off).

## Rules (from the project workflow)

- One module = one focus; numbers explicit; name the Mathlib lemmas to use.
- Give FULL lemma statements (Aristotle doesn't know the LaTeX numbering).
- `negate_state` in output = REFORMULATE signal (counterexample), not "push harder".
- Review before submit (project rule): the conductor prepares the input and, for the
  unattended loop, submits only from a pre-approved batch or an opt-in AUTO mode with a
  spend cap — never silently in bulk.

## When Aristotle fires for goal 034

Per Mythos's distribution: Aristotle is **NOT engaged** for 034 (FiniteCell257 is finite/
decidable → Codex local Lean is cheapest). Trigger: if `lake build` of the detector fails
on an API gap / decidability blowup after two honest tries, assemble a standalone English
`ARISTOTLE_TASK_FiniteCell257ToothAtomicDetector.md` with the 035 ledger + SHA-256 and submit.
(Existing Aristotle queue: `H2bTransformLayer` waiting on Theorem 5.10 from arXiv 2511.22755.)
