Project workflow: `full/q3.lean.aristotle/PROJECT_WORKFLOW.md`
Aristotle workflow and scripts: `~/.claude/skills/aristotle/`

Aristotle integration rules (project workflow):
- Activate venv before any Aristotle script: `source .venv/bin/activate`.
- Check status with `python ~/.claude/skills/aristotle/scripts/status.py <project_id>` and download with `download.py`.
- Always scan downloaded files for holes: `rg -n "sorry|exact\\?" <file>`.
- Treat files with holes as drafts; extract only hole-free lemmas or use as structure guidance.
- Run `lake env lean <file>` after every integration to ensure the project still compiles.
- Keep new kernel (A3_FLOOR) and old RKHS results separated; do not mix proof strategies.
- When a lemma fails to integrate cleanly, revert its addition and request Aristotle iteration on that lemma only.
- Log proof status in the DB by re-importing with `aristotle_db/parse_lean.py` and update notes if a lemma is no longer conditional.
- Prefer small, targeted Aristotle requests with explicit lemma statements and no `exact?` or `sorry`.
