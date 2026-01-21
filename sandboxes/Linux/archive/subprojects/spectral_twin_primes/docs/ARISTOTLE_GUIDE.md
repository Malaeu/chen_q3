# 🔧 Aristotle API Guide (Reverse Engineered)

**Version:** aristotlelib 0.6.0
**Company:** Harmonic AI
**Website:** https://aristotle.harmonic.fun
**Capabilities:** IMO Gold Medal level formal theorem proving

---

## 1. Installation

```bash
# Via uv (recommended)
uv pip install aristotlelib

# Via pip
pip install aristotlelib
```

## 2. API Key Setup

```bash
# Set environment variable
export ARISTOTLE_API_KEY="your_key_here"

# Or add to ~/.zshrc for permanent use
echo 'export ARISTOTLE_API_KEY="your_key"' >> ~/.zshrc
```

## 3. Two Operating Modes

### 3.1 FORMAL MODE (Lean file with `sorry`)

Input: Lean4 file with `sorry` placeholders
Output: Lean4 file with proofs filled in

```bash
aristotle prove-from-file theorem.lean
```

### 3.2 INFORMAL MODE (Math in English/LaTeX) ⭐

Input: Markdown/LaTeX file with theorem statement
Output: Complete Lean4 proof

```bash
aristotle prove-from-file --informal --no-validate-lean-project theorem.md
```

## 4. Input File Format (Informal Mode)

```markdown
# Theorem Name

## Setup (definitions)
Let $X$ be a set...
Define $f: X \to Y$ by...

## Theorem (what to prove)
Prove that $f$ is continuous.

## Proof Sketch (optional but helps!)
By definition of continuity...
Consider any open set U...
```

**Accepted formats:**
- LaTeX formulas ($...$, $$...$$)
- Markdown formatting
- English mathematical prose
- Proof sketches (greatly help Aristotle find the path)

## 5. CLI Options

```bash
aristotle prove-from-file [OPTIONS] INPUT_FILE

Options:
  --informal              # Use English/LaTeX instead of Lean
  --no-validate-lean-project  # Skip Lean project validation
  --no-wait               # Don't wait for completion (async)
  --polling-interval N    # Check status every N seconds (default: 30)
  --output-file FILE      # Custom output filename
  --context-files F1 F2   # Additional context files
  --context-folder DIR    # Folder with .lean/.md/.txt/.tex context
```

## 6. Parallel Execution

**YES, you can run MANY proofs in parallel!**

```bash
# Terminal 1
aristotle prove-from-file --informal --no-validate-lean-project lemma1.md &

# Terminal 2
aristotle prove-from-file --informal --no-validate-lean-project lemma2.md &

# Terminal 3
aristotle prove-from-file --informal --no-validate-lean-project theorem.md &
```

Each gets its own Project ID.

## 7. Project Status API

### List All Projects
```python
import asyncio
from aristotlelib import Project, set_api_key
import os

set_api_key(os.environ['ARISTOTLE_API_KEY'])

async def list_projects():
    result = await Project.list_projects()
    projects = result[0] if isinstance(result, tuple) else result
    for p in projects:
        print(f"{p.project_id}: {p.status} ({p.percent_complete}%)")

asyncio.run(list_projects())
```

### Check Specific Project
```python
async def check_project(project_id):
    project = await Project.from_id(project_id)
    print(f"Status: {project.status}")
    print(f"Progress: {project.percent_complete}%")

    if "COMPLETED" in str(project.status):
        solution = await project.get_solution()
        print(solution)

asyncio.run(check_project("dad24643-db59-487c-a2d8-695141aa9169"))
```

## 8. Project Statuses

| Status | Meaning |
|--------|---------|
| `QUEUED` | Waiting in queue |
| `IN_PROGRESS` | Actively working (has percent_complete) |
| `COMPLETED` | Done! Proof available |
| `FAILED` | Could not find valid proof |

## 9. Output Files

After completion, creates:
```
{input_name}_aristotle.md  # Contains Lean4 proof
```

Example: `cone_kernel.md` → `cone_kernel_aristotle.md`

## 10. Python API (Async!)

```python
import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key

set_api_key("your_key")

async def prove_theorem():
    # Create project
    project = await Project.create(
        context_file_paths=['theorem.md'],
        validate_lean_project_root=False,
        project_input_type=ProjectInputType.INFORMAL
    )

    print(f"Project ID: {project.id}")

    # Start solving
    await project.solve()

    # Wait for completion
    await project.wait_for_completion()

    # Get result
    solution = await project.get_solution()
    return solution

result = asyncio.run(prove_theorem())
```

## 11. Timing Expectations

| Proof Complexity | Expected Time |
|-----------------|---------------|
| Simple lemma | 5-15 minutes |
| Medium theorem | 15-60 minutes |
| Complex (IMO-level) | 1-8 hours |

Our Cone-Kernel lemma: **~20 minutes**

## 12. Tips for Best Results

1. **Provide proof sketch** - Helps Aristotle find the right approach
2. **Be precise with definitions** - Use standard mathematical notation
3. **Include all hypotheses** - Don't assume anything implicit
4. **Use LaTeX for formulas** - Better parsing than plain text
5. **Name your objects** - "Let K be a symmetric matrix" not "Let K..."

## 13. Utility Scripts

### check_aristotle.py
```bash
# List all projects
python check_aristotle.py

# Check specific project
python check_aristotle.py PROJECT_ID
```

---

## References

- [Aristotle API](https://aristotle.harmonic.fun)
- [Aristotle Paper (arXiv)](https://arxiv.org/html/2510.01346v1)
- [Harmonic News](https://harmonic.fun/news)
- [TechCrunch Article](https://techcrunch.com/2025/07/28/harmonic-the-robinhood-ceos-ai-math-startup-launches-an-ai-chatbot-app/)

---

*Last updated: December 2025*
*Reverse engineered by Ылша & Claude*
