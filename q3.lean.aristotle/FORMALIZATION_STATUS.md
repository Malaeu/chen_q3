# Q3 Formalization Status (Derived)

Entry point: `PROJECT_ORCHESTRATOR.md` (canonical).
This file is intentionally minimal to avoid drift.

## Quick Checks

```bash
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1 | rg -v "^info:"
```

```bash
python3 aristotle_db/parse_lean.py list-docs
```

## Current Status

- Axiom count and next actions are tracked in `PROJECT_ORCHESTRATOR.md`.
- Do not update this file with status tables; update the orchestrator instead.
