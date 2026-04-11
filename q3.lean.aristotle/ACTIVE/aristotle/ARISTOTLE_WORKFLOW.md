# Aristotle workflow (Q3 canonical)

Status: canonical single source of truth for Aristotle usage in this repo.
Date: 2026-03-07

Goal: one clean workflow for Aristotle; all older Aristotle docs are archived.

---

## 0. Quick start (Q3)

1) Decide: manual proof vs Aristotle.
2) If Aristotle: prepare ONE target lemma/file. Keep it small.
3) Show the prompt to user and wait for OK.
4) Activate venv: `source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate`.
5) Submit (CLI or Python API).
6) Download result -> scan for holes -> integrate -> compile -> log to DB.

---

## 1. Install / Run (official)

Prereq: install `uv` (Linux/macOS only; Windows is not used in this repo).
We use uv globally; see `~/.claude/claude.md`.

Preferred (no install, uses uvx):
```
uvx --from aristotlelib@latest aristotle
```

Alternate (install into venv):
```
source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate
uv pip install -U aristotlelib
# or: pip install -U aristotlelib
aristotle  # opens TUI
```

API key (Linux):
```
export ARISTOTLE_API_KEY='arstl_{YOUR_API_KEY}'
```

Persist API key:
- Linux: add to `~/.bashrc`
- macOS: add to `~/.zshrc`

Note: Aristotle runs on fixed versions:
- Lean toolchain: leanprover/lean4:v4.24.0
- Mathlib: v4.24.0 (f897ebcf72cd16f89ab4577d0c826cd14afaafc7)

---

## 2. Modes (harmonics.fun)

1) Fill sorries in a Lean file
2) Upload math text (natural language)
3) Prompt Aristotle (freeform question)
4) Check active projects / history

Mode 1 rules:
- Aristotle sees ONLY transitive imports of the file.
- It does NOT add imports on its own.
- It modifies ONLY the specified file.
- Data/defs are not modified by default.

Selective filling:
- If you only want one sorry closed, replace other sorries with `admit`.

"PROVIDED SOLUTION" hints:
- Put the English sketch in the comment ABOVE the theorem.
- Aristotle will NOT read comments inside `by` blocks.

Counterexamples:
- If the statement is false, Aristotle can output a counterexample or a
  proof of the negation. This is a reformulation signal.

Warnings from aesop:
- `aesop: failed to prove the goal after exhaustive search` is OK when
  `aesop` is non-terminal (more tactics follow).
- Suppress with:
  `aesop (config := { warnOnNonterminal := false })`

TUI shortcuts (official):
- Ctrl+T: prompt mode (freeform question)
- Ctrl+L: Lean file context
- Ctrl+F: other context (English notes)

Data safety:
- Aristotle does NOT modify data/defs by default (e.g., `def foo := by sorry`).

Leaving sorries unfilled:
- Replace unrelated `sorry` with `admit` to focus budget on target lemma.

---

## 3. Q3-specific rules (must follow)

- Always wait for user OK before submitting to Aristotle.
- After download: run a hard-hole scan with
  `rg -n "sorry|admit" <file>`.
- Also run an advisory scan with
  `rg -n "exact\\?" <file> || true`.
- Treat any file with `sorry`/`admit` as DRAFT.
- `exact?` alone is not a blocker anymore; accept it if the file compiles and uses
  the real Q3 objects rather than sandbox-local replacements.
- Extract only compiling lemmas into Q3.
- Run `lake env lean <file>` after every integration.
- Keep new kernel (A3_FLOOR) separate from old RKHS.
- If lemma fails to integrate cleanly: revert that addition and re-request
  Aristotle for that lemma only.
- Log proof status in DB:
  `python3 q3.lean.aristotle/aristotle_db/parse_lean.py import <file>`

---

## 4. Submission options

### 4.1 CLI (current official surface, verified on 2026-04-11)

The current CLI is:
```
aristotle {submit,formalize,result,list,cancel}
```

Single-file route:
```
aristotle formalize input.md
aristotle formalize path/to/file.lean
```

Important:
- `formalize` uploads exactly one file, packed into a tar.gz archive;
- for a markdown/tex/txt request file this is now the clean Q3 default;
- Aristotle creates a project with prompt `Formalize <filename>`.

Directory-context route:
```
aristotle submit "Formalize the target in the provided context" --project-dir /abs/path/to/context_dir
```

This is the right choice only when one file is not enough and a whole directory
must be sent.

### 4.2 Status / results

Check status from CLI:
```
aristotle list --limit 10
aristotle list --status IN_PROGRESS QUEUED --limit 20
```

Check one project from Python:
```
import asyncio
from aristotlelib.project import Project

async def main():
    p = await Project.from_id("<project_id>")
    print(p.status, p.percent_complete)

asyncio.run(main())
```

Download result from CLI:
```
aristotle result <project_id> --wait --destination aristotle_output/<project_id>.tar.gz
```

Result format:
- current Aristotle returns a tar.gz archive;
- on our verified completed project the archive contained `output.lean`.

Extract and inspect:
```
mkdir -p aristotle_output/<project_id>
tar -xzf aristotle_output/<project_id>.tar.gz -C aristotle_output/<project_id>
rg -n "sorry|admit" aristotle_output/<project_id>/output.lean
rg -n "exact\\?" aristotle_output/<project_id>/output.lean || true
```

### 4.3 Python API (current, stable subset)

Verified imports:
```
from aristotlelib import Project, ProjectStatus, set_api_key
```
or explicitly:
```
from aristotlelib.project import Project, ProjectStatus
```

Useful methods verified locally:
- `Project.from_id`
- `Project.create`
- `Project.create_from_directory`
- `Project.get_solution`
- `Project.get_input`
- `Project.refresh`
- `Project.cancel`
- `Project.list_projects`
- `Project.wait_for_completion`

Minimal status snippet:
```
import asyncio
from aristotlelib.project import Project

async def main():
    p = await Project.from_id("<project_id>")
    print(p.status, p.percent_complete)

asyncio.run(main())
```

Minimal download snippet:
```
import asyncio
from aristotlelib.project import Project

async def main():
    p = await Project.from_id("<project_id>")
    path = await p.get_solution("aristotle_output/<project_id>.tar.gz")
    print(path)

asyncio.run(main())
```

### 4.4 Practical Q3 recommendation

For Q3, the default route is now:
1. prepare one request file in `aristotle_input/`;
2. show it to the user;
3. submit with `aristotle formalize <file>`;
4. record `project_id`;
5. later fetch with `aristotle result ... --destination <pid>.tar.gz`;
6. extract `output.lean`, scan holes, compile, integrate.

Use `submit --project-dir` only when extra context is genuinely needed.

---

## 5. Download + verification

- Use Aristotle TUI or Python API to download solutions.
- Save outputs in `q3.lean.aristotle/aristotle_output/`.
- Scan for hard holes:
  `rg -n "sorry|admit" aristotle_output/<file>.lean`
- Scan for advisory `exact?`:
  `rg -n "exact\\?" aristotle_output/<file>.lean || true`
- Integrate only compiling lemmas in the real project context.

---

## 6. Iteration protocol (если Aristotle вернул «дичь»)

Classify the outcome first, then act:

**A) COMPLETE + no `sorry`/`admit` + compiles**
- Integrate immediately (see checklist below).

**B) PARTIAL (есть `sorry` / `admit`)**
- Treat as draft; extract only hole‑free lemmas.
- Split the target lemma into smaller sub‑lemmas.
- Replace unrelated `sorry` with `admit` to focus budget.
- Add a short `PROVIDED SOLUTION` sketch and resubmit.

**B2) EXACT-SEARCH OUTPUT (`exact?`, но без `sorry` / `admit`)**
- Do not reject automatically.
- First compile it in the real Q3 project context.
- If it compiles and uses the real project objects, it is admissible for local
  integration or cleanup.
- If it only works with sandbox-local replacements, reject and narrow the target.

**C) COUNTEREXAMPLE / NEGATION (false statement)**
- Treat as *reformulation signal*.
- Check the counterexample locally; tighten hypotheses or correct statement.
- Resubmit with corrected statement and updated sketch.

**D) VALIDATION / IMPORT FAIL**
- For Q3, use Python API with `auto_add_imports=False`.
- Ensure the root is `.../q3.lean.aristotle`.

**E) “FILE NOT FOUND” in Aristotle output**
- Cause: submitted informal `.md` that references a Lean file/path not included.
- Fix: use **formal mode** on the `.lean` file with sorries, OR pass that file as
  `formal_input_context` (informal mode) and include needed context files.
- For Q3, prefer Python API with explicit `project_root` and context list.

**F) “Axioms were added during init_sorries”**
- Cause: imported files pull Q3 axioms into the environment.
- Fix: isolate a **minimal** file with only needed defs/lemmas (Mathlib + Q3.Basic.Defs
  + local defs), avoid importing heavy proof modules.
- If needed, create a sandbox file and re‑prove helper lemmas locally.

**G) SANDBOX REJECTION (unexpected axioms)**
- Remove `axiom`/`constant`/custom imports.
- Use only `import Mathlib`, `def`, `theorem ... := by sorry`.

Only after A) do we integrate into the main chain.

---

## 7. Integration checklist (short)

1) Copy lemma(s) into target Lean file.
2) `lake env lean <file>`.
3) Update DB: `aristotle_db/parse_lean.py import <file>`.
4) Update `docs/INSIGHTS.md` if any reusable patterns.
5) If axiom list changes: update `FORMALIZATION_STATS.md` and `check_axioms`.

---

## 8. Queue / automation

Queue generator:
```
python3 q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh --print-next 10
```

Outputs:
- `ACTIVE/aristotle/ARISTOTLE_QUEUE.json`
- `ACTIVE/aristotle/ARISTOTLE_QUEUE.md`
- `ACTIVE/aristotle/queue/<task>/PROMPT.txt`
- `ACTIVE/aristotle/queue/<task>/NODE_BRIEF.md`

---

## 9. Sandbox facts (learned)

- Aristotle rejects custom `axiom` in sandbox inputs.
- Safe sandbox: `import Mathlib`, `def`, `theorem ... := by sorry`.
- It creates new theorems with `_proof` suffix.
- It does NOT accept project imports outside Mathlib.

---

## 10. Hidden gems / control knobs

- Cancel a running project: `Project.cancel()` (TUI also supports cancel).
- Filter list_projects by status (queued / in-progress / complete).
- `wait_for_completion` uses backoff; you can set `polling_interval_seconds`.

---

## 11. Repo locations

- Inputs: `q3.lean.aristotle/aristotle_input/`
- Outputs: `q3.lean.aristotle/aristotle_output/`
- DB: `q3.lean.aristotle/aristotle_db/`
- Queue: `q3.lean.aristotle/ACTIVE/aristotle/queue/`
- Prompt policy: `q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`
