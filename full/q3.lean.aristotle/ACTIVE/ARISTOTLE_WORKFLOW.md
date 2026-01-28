# Aristotle workflow (Q3 canonical)

Status: canonical single source of truth for Aristotle usage in this repo.
Date: 2026-01-28

Goal: one clean workflow for Aristotle; all older Aristotle docs are archived.

---

## 0. Quick start (Q3)

1) Decide: manual proof vs Aristotle.
2) If Aristotle: prepare ONE target lemma/file. Keep it small.
3) Show the prompt to user and wait for OK.
4) Activate venv: `source .venv/bin/activate`.
5) Submit (CLI or Python API).
6) Download result -> scan for holes -> integrate -> compile -> log to DB.

---

## 1. Install / Run (official)

Prereq: `uv` is required (we use uv globally; see `~/.claude/claude.md`).

Preferred (no install, uses uvx):
```
uvx --from aristotlelib@latest aristotle
```

Alternate (install into venv):
```
source .venv/bin/activate
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
- After download: scan for holes with
  `rg -n "sorry|exact\\?" <file>`.
- Treat any file with holes as DRAFT.
- Extract only hole-free lemmas into Q3.
- Run `lake env lean <file>` after every integration.
- Keep new kernel (A3_FLOOR) separate from old RKHS.
- If lemma fails to integrate cleanly: revert that addition and re-request
  Aristotle for that lemma only.
- Log proof status in DB:
  `python3 full/q3.lean.aristotle/aristotle_db/parse_lean.py import <file>`

---

## 4. Submission options

### 4.1 CLI (simple cases)

Informal (markdown):
```
aristotle prove-from-file --informal --no-validate-lean-project --no-wait input.md
```

Formal (Lean file with sorries):
```
aristotle prove-from-file path/to/file.lean --no-wait
```

### 4.2 Python API (preferred for Q3)

Reason: CLI auto-imports may pick the wrong outermost project root.
Use Python API with explicit context and `auto_add_imports=False`.

Template (Linux paths):
```
from pathlib import Path
from aristotlelib import Project
from aristotlelib.local_file_utils import gather_file_imports
import asyncio

ROOT = Path("/mnt/hdd01/Soft/GitHub/chen_q3/sandboxes/projekt_2/full/q3.lean.aristotle")
INPUT = ROOT / "Q3/Proofs/QSpec.lean"  # change to your file

context = [str(p) for p in gather_file_imports(INPUT, project_root=ROOT)]
context += [
    str(ROOT / "ACTIVE/aristotle_queue/<task>/PROMPT.txt"),
    str(ROOT / "ACTIVE/aristotle_queue/<task>/NODE_BRIEF.md"),
]

async def main():
    pid = await Project.prove_from_file(
        input_file_path=INPUT,
        auto_add_imports=False,
        context_file_paths=context,
        validate_lean_project=False,
        wait_for_completion=False,
        output_file_path=ROOT / "aristotle_output/<task>_aristotle.lean",
    )
    print(pid)

asyncio.run(main())
```

Limits and quirks (from package inspection):
- Max 10 files per request; use batched `add_context` for more.
- Context file extensions allowed: .lean .md .txt .tex
- `formal_input_context` works only in informal mode.
- `auto_add_imports=True` requires `validate_lean_project=True`.
- `context_is_folder=True` uploads all allowed files under a folder.
- `find_lean_project_root` returns the OUTERMOST root (can break Q3 imports).

---

## 5. Download + verification

- Use Aristotle TUI or Python API to download solutions.
- Save outputs in `full/q3.lean.aristotle/aristotle_output/`.
- Scan for holes:
  `rg -n "sorry|exact\\?" aristotle_output/<file>.lean`
- Only integrate hole-free lemmas.

---

## 6. Iteration protocol (если Aristotle вернул «дичь»)

Classify the outcome first, then act:

**A) COMPLETE + hole‑free + compiles**
- Integrate immediately (see checklist below).

**B) PARTIAL (есть `sorry` / `exact?`)**
- Treat as draft; extract only hole‑free lemmas.
- Split the target lemma into smaller sub‑lemmas.
- Replace unrelated `sorry` with `admit` to focus budget.
- Add a short `PROVIDED SOLUTION` sketch and resubmit.

**C) COUNTEREXAMPLE / NEGATION (false statement)**
- Treat as *reformulation signal*.
- Check the counterexample locally; tighten hypotheses or correct statement.
- Resubmit with corrected statement and updated sketch.

**D) VALIDATION / IMPORT FAIL**
- For Q3, use Python API with `auto_add_imports=False`.
- Ensure the root is `.../full/q3.lean.aristotle`.

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
python3 full/q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh --print-next 10
```

Outputs:
- `ACTIVE/ARISTOTLE_QUEUE.json`
- `ACTIVE/ARISTOTLE_QUEUE.md`
- `ACTIVE/aristotle_queue/<task>/PROMPT.txt`
- `ACTIVE/aristotle_queue/<task>/NODE_BRIEF.md`

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

- Inputs: `full/q3.lean.aristotle/aristotle_input/`
- Outputs: `full/q3.lean.aristotle/aristotle_output/`
- DB: `full/q3.lean.aristotle/aristotle_db/`
- Queue: `full/q3.lean.aristotle/ACTIVE/aristotle_queue/`
- Prompt policy: `full/q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`
