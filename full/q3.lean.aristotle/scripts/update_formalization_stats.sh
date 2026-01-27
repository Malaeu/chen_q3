#!/bin/bash
# update_formalization_stats.sh - refresh FORMALIZATION_STATS.md with latest snapshot

set -euo pipefail
cd "$(dirname "$0")/.."

stats_output=$(./scripts/contribution_stats.sh)
run_date=$(date +%Y-%m-%d)
export stats_output run_date

python3 - <<'PY'
import os
import re
from pathlib import Path

stats_output = os.environ["stats_output"]
run_date = os.environ["run_date"]

path = Path("FORMALIZATION_STATS.md")
text = path.read_text(encoding="utf-8")

text = re.sub(r"^Last updated:.*$", f"Last updated: {run_date}", text, flags=re.M)

block = "```\n" + stats_output.strip() + "\n```\n"
pattern = r"<!-- stats:start -->.*?<!-- stats:end -->"
replacement = "<!-- stats:start -->\n" + block + "<!-- stats:end -->"

if re.search(pattern, text, flags=re.S):
    text = re.sub(pattern, replacement, text, flags=re.S)
else:
    text += "\n\n## Raw Script Output (auto)\n\n" + replacement + "\n"

path.write_text(text, encoding="utf-8")
print("Updated FORMALIZATION_STATS.md")
PY

# Refresh main dependency tree (authoritative main-chain deps)
python3 ../sandboxes/projekt_2/scripts/build_dependency_tree.py

# Refresh proof graph (deps + alternatives)
python3 ../sandboxes/projekt_2/scripts/build_proof_graph.py
