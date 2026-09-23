#!/bin/bash
# install-global.sh — make the Astra/Luna/Sol orchestration the global Codex default.
#
# Root: gpt-6-astra (low). Subagents: gpt-6-luna (max), up to 6 at once, depth 1.
# Escalation: the "escalation" agent (gpt-6-sol, xhigh) when a Luna subagent fails.
#
# Copies this project's agent definitions to ~/.codex/agents/ and the
# astra-orchestrator skill to ~/.codex/skills/ (Codex-only: ~/.agents/skills is
# shared with Claude Code), sets the global keys in ~/.codex/config.toml (backup next to it) and adds a pointer to ~/.codex/AGENTS.md.
# Idempotent: safe to run again after a git pull. Works on Linux and macOS.
#
# Usage: bash .codex/install-global.sh   (from the chen_q3 checkout)

set -euo pipefail

SRC=$(cd "$(dirname "$0")" && pwd)            # <repo>/.codex
REPO=$(dirname "$SRC")
CODEX_HOME=${CODEX_HOME:-$HOME/.codex}
CFG=$CODEX_HOME/config.toml
AGENTS=(worker explorer researcher tester reviewer escalation)

mkdir -p "$CODEX_HOME/agents" "$CODEX_HOME/skills"

for a in "${AGENTS[@]}"; do
    cp "$SRC/agents/$a.toml" "$CODEX_HOME/agents/$a.toml"
done
echo "agents -> $CODEX_HOME/agents: ${AGENTS[*]}"

rm -rf "$CODEX_HOME/skills/astra-orchestrator.tmp"
cp -R "$REPO/.agents/skills/astra-orchestrator" "$CODEX_HOME/skills/astra-orchestrator.tmp"
rm -rf "$CODEX_HOME/skills/astra-orchestrator"
mv "$CODEX_HOME/skills/astra-orchestrator.tmp" "$CODEX_HOME/skills/astra-orchestrator"
echo "skill  -> $CODEX_HOME/skills/astra-orchestrator"

touch "$CFG"
BAK="$CFG.bak-$(date +%Y%m%d-%H%M%S)-$$"   # PID suffix: two runs in one second must not overwrite
cp -p "$CFG" "$BAK"
python3 - "$CFG" <<'PY'
import re, sys
p = sys.argv[1]
lines = open(p).read().split("\n")

def set_key(section, key, value):
    """Set key = value inside [section] ('' = top level); add it if missing."""
    start, end = 0, len(lines)
    if section:
        hdr = [i for i, l in enumerate(lines) if l.strip() == f"[{section}]"]
        if not hdr:
            lines.extend(["", f"[{section}]"])
            hdr = [len(lines) - 1]
        start = hdr[0] + 1
    for i in range(start, len(lines)):
        if re.match(r"\s*\[", lines[i]):
            end = i
            break
    for i in range(start, end):
        if re.match(rf"\s*{re.escape(key)}\s*=", lines[i]):
            lines[i] = f"{key} = {value}"
            return
    # insert after the last non-empty line of the section
    j = end
    while j > start and not lines[j - 1].strip():
        j -= 1
    lines.insert(j, f"{key} = {value}")

set_key("", "model", '"gpt-6-astra"')
set_key("", "model_reasoning_effort", '"low"')
set_key("agents", "enabled", "true")
set_key("agents", "max_depth", "1")
set_key("agents", "max_concurrent_threads_per_session", "6")
set_key("agents", "default_subagent_model", '"gpt-6-luna"')
set_key("agents", "default_subagent_reasoning_effort", '"max"')
set_key("features", "multi_agent", "true")
open(p, "w").write("\n".join(lines))
PY
echo "config -> $CFG (root gpt-6-astra/low, subagents gpt-6-luna/max x6, depth 1)"

MARK="<!-- astra-orchestrator -->"
if ! grep -qF "$MARK" "$CODEX_HOME/AGENTS.md" 2>/dev/null; then
    cat >> "$CODEX_HOME/AGENTS.md" <<EOF

$MARK
## Orchestration (Astra / Luna / Sol)
For complex multi-step coding or research tasks use the \`astra-orchestrator\` skill.
Delegate bounded work to Luna subagents (worker, explorer, researcher, tester), up to 6 in parallel.
If a Luna subagent fails or asks for deeper reasoning, re-delegate that task once to the \`escalation\` agent (GPT-6 Sol, xhigh); if that also fails, handle it at the root or report the blocker.
Do not delegate trivial work. User instructions take precedence.
EOF
    echo "AGENTS.md -> pointer added"
else
    echo "AGENTS.md -> pointer already present"
fi
