# Possible Solutions — System Optimierung

Collection of potential system improvements, tool integrations, and workflow optimizations.

---

## 2026-01-19: UI-TARS Desktop Analysis

**Source:** [bytedance/UI-TARS-desktop](https://github.com/bytedance/UI-TARS-desktop)

### What is UI-TARS?

**Multimodal AI Agent** from ByteDance for GUI automation:
- Vision models for screenshot understanding
- Action execution (clicks, keyboard)
- **Plugin architecture** — modular system
- **MCP Protocol** — standardized tools
- **Event-driven** — pub-sub event system

### Synergy Concepts with Q3 Workflow

| UI-TARS Concept | Q3 Application | Benefit |
|-----------------|----------------|---------|
| **ComposableAgent + Plugins** | `AristotlePlugin`, `LakePlugin`, `SearchPlugin` | Modular orchestration of proof workflow |
| **MCP Protocol** | `q3search`, `websearch`, `lake build` as MCP servers | Standard API for all proof tools |
| **AgentEventStream** | Tracking proof attempts, sorry counts, axiom state changes | Real-time monitoring of proof progress |
| **Session Persistence (SQLite)** | Axiom closure history, attempt logs | Replaces manual ORCHESTRATOR.md updates |
| **Vision + GUI Control** | Lean IDE automation (VS Code + infoview) | Automatic proof state verification |

### Proposed Architecture: Q3-TARS Integration

```
┌─────────────────────────────────────────────────────────────────┐
│                    Q3-TARS Agent Stack                          │
└─────────────────────────────────────────────────────────────────┘

┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│ SearchPlugin│    │AristotlePlugin│  │  LakePlugin │
│ (q3search)  │    │ (prove-from-file)│ │(lake build) │
└──────┬──────┘    └──────┬──────┘    └──────┬──────┘
       │                  │                  │
       └──────────────────┼──────────────────┘
                          │
              ┌───────────▼───────────┐
              │   ComposableAgent     │
              │   (AgentComposer)     │
              │   System 1 + System 2 │
              └───────────┬───────────┘
                          │
              ┌───────────▼───────────┐
              │   AgentEventStream    │
              │ • proof_attempt       │
              │ • axiom_closed        │
              │ • sorry_detected      │
              │ • build_success/fail  │
              └───────────┬───────────┘
                          │
              ┌───────────▼───────────┐
              │  SQLite Persistence   │
              │ • sessions            │
              │ • axiom_history       │
              │ • proof_attempts      │
              └───────────────────────┘
```

### Top 3 Actionable Synergies

**1. MCP Server for Proof Tools**
```typescript
// mcp-server-q3proof/
export const tools = {
  q3search: "Search project knowledge base",
  websearch: "Search arxiv, MathOverflow",
  lake_build: "Build Q3.Main, check axioms",
  aristotle_submit: "Submit proof request",
  check_sorry: "Scan for sorry/exact?"
}
```
→ Unified API, works from CLI and Web UI

**2. Event-Driven Axiom Tracking**
```typescript
interface ProofEvent {
  type: 'axiom_attempt' | 'axiom_closed' | 'sorry_found';
  axiom: string;
  file: string;
  timestamp: Date;
  context: { previousCount: number; newCount: number };
}
```
→ Automatic ORCHESTRATOR.md without manual updates

**3. Vision Mode for Lean IDE**
```typescript
// GuiAgentPlugin for VS Code
async verifyProofState() {
  const screenshot = await this.operator.screenshot();
  const infoview = await this.vlm.analyze(screenshot,
    "Is there 'sorry' or errors in Lean infoview?");
  return { hasSorry: infoview.includes("sorry"), errors: infoview.errors };
}
```
→ Automatic proof state verification visually

### Challenges / Concerns

| Issue | Mitigation |
|-------|------------|
| Heavy setup (Electron, Node 22+) | Start with CLI-only (`@agent-tars/cli`) |
| Vision model cost | Use only for verification, not exploration |
| Complexity overhead | Implement incrementally, plugin by plugin |
| Our workflow is simple enough | Keep manual workflow, use TARS only for repetitive tasks |

### Verdict

**Relevance Score: 7/10**

Useful for:
- ✅ Automating repetitive tasks (check axioms, run lake)
- ✅ Standardized tool API (MCP)
- ✅ Persistent proof history

Overkill for:
- ❌ Core proof work (Aristotle + Claude + manual)
- ❌ Simple sequential workflow

**Recommendation:** Study MCP Protocol separately — it's the most portable concept. Can write `mcp-server-q3` for our tools without the entire stack.

**References:**
- [GitHub - bytedance/UI-TARS-desktop](https://github.com/bytedance/UI-TARS-desktop)
- [UI-TARS AI - Overview](https://ui-tarsai.com/)
- [VentureBeat - ByteDance's UI-TARS](https://venturebeat.com/ai/bytedances-ui-tars-can-take-over-your-computer-outperforms-gpt-4o-and-claude)

---

## 2026-01-19: Everything Claude Code — Configuration Collection

**Source:** [Malaeu/everything-claude-code](https://github.com/Malaeu/everything-claude-code) (fork of [affaan-m/everything-claude-code](https://github.com/affaan-m/everything-claude-code))

### What is it?

**Production-ready configs for Claude Code** from Anthropic hackathon winner:
- 10+ months battle-tested usage
- Agents, Skills, Commands, Rules, Hooks, MCP configs
- Ready templates for copy-paste

### Repository Structure

| Category | Contents | Purpose |
|----------|----------|---------|
| **agents/** | planner, architect, code-reviewer, security-reviewer, e2e-runner, build-error-resolver, tdd-guide | Specialized subagents |
| **skills/** | coding-standards, backend-patterns, frontend-patterns, tdd-workflow, security-review | Workflow definitions |
| **commands/** | /tdd, /plan, /e2e, /code-review, /build-fix, /refactor-clean | Slash commands |
| **rules/** | security, coding-style, testing, git-workflow, performance | Always-follow guidelines |
| **hooks/** | hooks.json | Trigger-based automations |
| **mcp-configs/** | GitHub, Supabase, Vercel, Railway | MCP server configs |

### Direct Mapping to Q3 Workflow

#### 1. Agents → Q3-Specific Agents

| Their Agent | Our Q3 Agent | Purpose |
|-------------|--------------|---------|
| `planner.md` | `axiom-planner.md` | Plan axiom closure strategy |
| `architect.md` | `proof-architect.md` | Design proof structure |
| `code-reviewer.md` | `lean-reviewer.md` | Review Lean code quality |
| `build-error-resolver.md` | `lake-error-resolver.md` | Fix lake build errors |
| `tdd-guide.md` | `aristotle-guide.md` | Aristotle prompt best practices |
| — | `mathlib-searcher.md` | **NEW:** Explore Mathlib for lemmas |
| — | `axiom-tracker.md` | **NEW:** Track closure progress |

**Example: `axiom-planner.md`**
```markdown
# Axiom Planner Agent

## Role
Plan strategy for closing axioms in Q3 formalization.

## Tools
- Read, Grep, Glob (codebase search)
- Task (spawn Explore subagent)

## Workflow
1. Read PROJECT_ORCHESTRATOR.md for current status
2. Identify blocking axiom
3. Search for existing theorems that could wire
4. Search Mathlib for relevant lemmas
5. Propose closure plan with file:line references

## Output
Structured plan with:
- Target axiom
- Dependencies
- Proof strategy
- Required lemmas (with signatures)
```

#### 2. Skills → Q3-Specific Skills

| Their Skill | Our Q3 Skill | Purpose |
|-------------|--------------|---------|
| `tdd-workflow/` | `axiom-closure-workflow/` | Our closure loop |
| `coding-standards.md` | `lean-standards.md` | Lean4 coding style |
| `backend-patterns.md` | `mathlib-patterns.md` | Common Mathlib patterns |
| — | `aristotle-prompting/` | **NEW:** Prompt guidelines |

**Example: `axiom-closure-workflow/skill.md`**
```markdown
# Axiom Closure Workflow

## Trigger
/close-axiom [axiom_name]

## Steps
1. READ: PROJECT_ORCHESTRATOR.md → find axiom status
2. SEARCH: q3search "axiom description" -c
3. SEARCH: websearch "mathematical formulation"
4. ANALYZE: synthesize approach
5. IMPLEMENT: replace `axiom X` with `theorem X := <proof>`
6. VERIFY: lake build Q3.Main && ./scripts/check_axioms.sh
7. UPDATE: ORCHESTRATOR, commit with axiom count
```

#### 3. Commands → Q3-Specific Commands

| Their Command | Our Q3 Command | Purpose |
|---------------|----------------|---------|
| `/tdd` | `/prove` | Submit to Aristotle |
| `/build-fix` | `/lake-fix` | Fix lake build errors |
| `/code-review` | `/lean-review` | Review Lean proof |
| `/plan` | `/plan-axiom` | Plan axiom closure |
| — | `/check-axioms` | **NEW:** Run check_axioms.sh |
| — | `/search-mathlib` | **NEW:** Explore Mathlib |
| — | `/wire-theorem` | **NEW:** Wire theorem to axiom |

**Example: `/check-axioms.md`**
```markdown
# /check-axioms

Run axiom verification for Q3.Main.

## Steps
1. Run: `lake build Q3.Main`
2. Run: `./scripts/check_axioms.sh`
3. Parse output for axiom count
4. Compare with CLAUDE.md count
5. Report: increased/decreased/same
```

#### 4. Rules → Q3-Specific Rules

| Their Rule | Our Q3 Rule | Purpose |
|------------|-------------|---------|
| `security.md` | `philosophy-of-proof.md` | Axiom criteria |
| `testing.md` | `no-sorry-main.md` | No sorry in main chain |
| `git-workflow.md` | `axiom-commit.md` | Commit with axiom count |
| — | `aristotle-limits.md` | **NEW:** Prompt guidelines |
| — | `explore-before-guess.md` | **NEW:** Use Explore, don't guess lemmas |

**Example: `no-sorry-main.md`**
```markdown
# No Sorry in Main Chain

## Rule
NEVER commit code with `sorry` or `exact?` in the main proof chain.

## Verification
Before every commit:
- `rg -n "sorry|exact\\?" Q3/`
- If found in Main.lean or Proofs/, STOP

## Exception
Draft files in `aristotle_output/` may contain sorry.
```

#### 5. Hooks → Q3-Specific Hooks

```json
{
  "hooks": {
    "post-edit": [
      {
        "pattern": "**/*.lean",
        "command": "rg -n 'sorry|exact\\?' $FILE",
        "onMatch": "warn: Found sorry/exact? in $FILE"
      }
    ],
    "pre-commit": [
      {
        "command": "./scripts/check_axioms.sh",
        "onFail": "block: Axiom count increased!"
      }
    ]
  }
}
```

### Implementation Priority

| Priority | Item | Effort | Impact |
|----------|------|--------|--------|
| 🔴 HIGH | `/check-axioms` command | 10 min | Daily use |
| 🔴 HIGH | `no-sorry-main.md` rule | 5 min | Prevents mistakes |
| 🟡 MED | `axiom-closure-workflow/` skill | 30 min | Standardizes workflow |
| 🟡 MED | `mathlib-searcher.md` agent | 20 min | Stops guessing lemmas |
| 🟢 LOW | Hooks for sorry detection | 15 min | Nice automation |
| 🟢 LOW | `aristotle-guide.md` agent | 30 min | Encodes GUIDELINES |

### Critical Warning

> **Context window management:** Your 200k context window can shrink to 70k with too many MCPs enabled!

**Recommendation:**
- Keep <10 MCPs enabled per project
- Keep <80 active tools total
- Use `disabledMcpServers` in project config

### Verdict

**Relevance Score: 9.5/10** 🔥

Directly applicable to our workflow:
- ✅ Ready structure for agents/skills/commands/rules
- ✅ Battle-tested patterns
- ✅ Copy-paste and adapt
- ✅ Hooks for automated checks

**Immediate Action:**
1. Clone repo
2. Study structure
3. Create Q3-specific versions of key configs
4. Add to `~/.claude/` and `.claude/`

**References:**
- [GitHub - Malaeu/everything-claude-code](https://github.com/Malaeu/everything-claude-code)
- [GitHub - affaan-m/everything-claude-code](https://github.com/affaan-m/everything-claude-code)
- [Claude Code customization guide](https://alexop.dev/posts/claude-code-customization-guide-claudemd-skills-subagents/)
- [Understanding Claude Code's Full Stack](https://alexop.dev/posts/understanding-claude-code-full-stack/)

---

## Template for Future Entries

```markdown
## YYYY-MM-DD: [Topic Name]

**Source:** [link]

### Summary
[Brief description]

### Synergy with Q3
[How it relates to our workflow]

### Actionable Items
[Concrete next steps]

### Verdict
[Relevance score and recommendation]
```
