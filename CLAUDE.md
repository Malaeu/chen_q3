# Project Memory (short pointer)

This file was intentionally minimized to reduce context usage.

## Key Documentation:
- **PROJECT_STATUS**: `/full/q3.lean.aristotle/PROJECT_STATUS.md`
- **ARISTOTLE_GUIDE**: `/ARISTOTLE_GUIDE.md` ← 🔥 READ THIS FOR ARISTOTLE WORKFLOW!

## Quick Reference:
```python
# Aristotle API
from aristotlelib import Project, ProjectInputType, ProjectStatus

# Для .md файлов ОБЯЗАТЕЛЬНО:
project_input_type=ProjectInputType.INFORMAL
validate_lean_project=False

# Атрибуты:
p.percent_complete  # НЕ p.progress!
p.status            # ProjectStatus enum
```

## Backups:
- /Users/emalam/Documents/GitHub/chen_q3/CLAUDE.md.bak_20251220_103658
