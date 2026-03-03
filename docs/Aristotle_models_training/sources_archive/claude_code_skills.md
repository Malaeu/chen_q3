# Claude Code Skills: Документация

**Источник:** https://code.claude.com/docs/en/skills

## Обзор

Skills расширяют возможности Claude. Создаётся файл `SKILL.md` с инструкциями, и Claude добавляет его в свой toolkit. Claude использует skills когда это релевантно, или можно вызвать напрямую через `/skill-name`.

Claude Code skills следуют **Agent Skills open standard**, который работает across multiple AI tools. Claude Code расширяет стандарт дополнительными features: invocation control, subagent execution, и dynamic context injection.

## Структура Skill

### Базовая структура директории

```
my-skill/
├── SKILL.md           # Main instructions (required)
├── template.md        # Template for Claude to fill in
├── examples/
│   └── sample.md      # Example output showing expected format
└── scripts/
    └── validate.sh    # Script Claude can execute
```

### Формат SKILL.md

Каждый skill нуждается в файле `SKILL.md` с двумя частями:
1. **YAML frontmatter** (между `---` markers) — когда использовать skill
2. **Markdown content** — инструкции для Claude

### Пример SKILL.md

```markdown
---
name: explain-code
description: Explains code with visual diagrams and analogies. Use when explaining how code works, teaching about a codebase, or when the user asks "how does this work?"
---

When explaining code, always include:

1. **Start with an analogy**: Compare the code to something from everyday life
2. **Draw a diagram**: Use ASCII art to show the flow, structure, or relationships
3. **Walk through the code**: Explain step-by-step what happens
4. **Highlight a gotcha**: What's a common mistake or misconception?

Keep explanations conversational. For complex concepts, use multiple analogies.
```

## Где хранить Skills

| Location | Path | Applies to |
|----------|------|------------|
| Enterprise | See managed settings | All users in organization |
| Personal | `~/.claude/skills/<skill-name>/SKILL.md` | All your projects |
| Project | `.claude/skills/<skill-name>/SKILL.md` | This project only |
| Plugin | `<plugin>/skills/<skill-name>/SKILL.md` | Where plugin is enabled |

Project skills override personal skills с тем же именем.

## Типы Skill Content

### 1. Reference Content
Добавляет knowledge, которое Claude применяет к текущей работе: conventions, patterns, style guides, domain knowledge.

```markdown
---
name: api-conventions
description: API design patterns for this codebase
---

When writing API endpoints:
- Use RESTful naming conventions
- Return consistent error formats
- Include request validation
```

### 2. Task Content
Step-by-step инструкции для конкретного action (deployments, commits, code generation).

```markdown
---
name: deploy
description: Deploy the application to production
context: fork
disable-model-invocation: true
---

Deploy the application:
1. Run the test suite
2. Build the application
3. Push to the deployment target
```

## Frontmatter Reference

| Field | Required | Description |
|-------|----------|-------------|
| `name` | No | Display name for skill. Lowercase letters, numbers, hyphens (max 64 chars) |
| `description` | Recommended | What skill does and when to use it |
| `argument-hint` | No | Hint for expected arguments, e.g. `[issue-number]` |
| `disable-model-invocation` | No | `true` prevents Claude from auto-loading. Default: `false` |
| `user-invocable` | No | `false` hides from / menu. Default: `true` |
| `allowed-tools` | No | Tools Claude can use without asking permission |
| `model` | No | Model to use when skill is active |
| `context` | No | Set to `fork` to run in forked subagent context |
| `agent` | No | Which subagent type when `context: fork` |
| `hooks` | No | Hooks scoped to skill's lifecycle |

## String Substitutions

| Variable | Description |
|----------|-------------|
| `$ARGUMENTS` | All arguments passed when invoking skill |
| `$SELECTION` | Currently selected text in editor |
| `$CURRENT_FILE` | Path to currently open file |
| `$CURRENT_DIRECTORY` | Path to current working directory |
| `$PROJECT_ROOT` | Path to project root |

## Advanced Patterns

### Inject Dynamic Context
Можно добавить динамический контекст через hooks.

### Run Skills in Subagent
Установить `context: fork` для запуска в отдельном subagent context.

### Restrict Tool Access
Использовать `allowed-tools` для ограничения доступных инструментов.

## Invocation

### Автоматический вызов
Claude загружает skill автоматически когда запрос соответствует description.

### Ручной вызов
```
/skill-name [arguments]
```

Пример:
```
/explain-code src/auth/login.ts
```

## Ключевые моменты для создания Skill

1. **Description критична** — Claude использует её для решения когда применять skill
2. **Specific conditions** — описывайте конкретные условия активации
3. **Focused skills** — один skill = одна задача
4. **Supporting files** — используйте templates, examples, scripts для сложных skills
5. **Test thoroughly** — проверяйте как автоматический, так и ручной вызов


---

# Существующий Skill для Lean 4: lean4-theorem-proving

**Источник:** https://github.com/cameronfreer/lean4-skills

## Обзор

Это наиболее развитый существующий skill для работы с Lean 4 в Claude Code. Он предоставляет:

- **Lean LSP integration** — Sub-second feedback vs 30s builds
- **8 slash commands** — `/build-lean`, `/fill-sorry`, `/repair-file`, `/golf-proofs`, `/check-axioms`, `/analyze-sorries`, `/refactor-have`, `/search-mathlib`
- **5 specialized agents** — Proof repair, sorry filling (fast + deep), axiom elimination, proof golfing
- **16 automation scripts** — Search, analysis, verification
- **mathlib patterns** — Type class management, domain-specific tactics

## Структура Skill

```
lean4-theorem-proving/
├── .claude-plugin/
├── commands/           # 8 slash commands
├── config/
├── docs/               # Reference guides
├── hooks/
├── scripts/            # 16 automation tools
├── skills/lean4-theorem-proving/
│   └── SKILL.md        # Main skill file
├── tests/
├── COMMANDS.md
├── FUTURE-FEATURES.md
└── README.md
```

## Ключевые элементы SKILL.md

### Frontmatter
```yaml
---
name: lean4-theorem-proving
description: Use when working with Lean 4 (.lean files), writing mathematical proofs, seeing "failed to synthesize instance" errors, managing sorry/axiom elimination, or searching mathlib for lemmas - provides build-first workflow, haveI/letI patterns, compiler-guided repair, and LSP integration
---
```

### Основные принципы

1. **Build-First Principle** — ALWAYS compile before committing
2. **4-Phase Workflow:**
   - Structure Before Solving
   - Helper Lemmas First
   - Incremental Filling
   - Type Class Management

### Compiler-Guided Proof Repair

Вдохновлено APOLLO (https://arxiv.org/abs/2505.05758):
1. Compile → extract structured error
2. Try automated solver cascade: `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → aesop`
3. If solvers fail → call lean4-proof-repair agent:
   - Stage 1: Haiku (fast) - 6 attempts
   - Stage 2: Sonnet (precise) - 18 attempts
4. Apply minimal patch, recompile, repeat (max 24 attempts)

### Reference Files

- **Core:** lean-phrasebook.md, mathlib-guide.md, tactics-reference.md
- **Domain-specific:** domain-patterns.md, measure-theory.md
- **Optimization:** proof-golfing.md, proof-refactoring.md
- **Automation:** compiler-guided-repair.md, lean-lsp-server.md

---

## Сравнение с Aristotle

| Аспект | lean4-theorem-proving | Aristotle (Harmonic) |
|--------|----------------------|---------------------|
| Тип | Claude Code Skill | Standalone AI System |
| Архитектура | Rule-based + LLM | MCGS + RL + Hidden CoT |
| Поиск доказательств | Solver cascade | Monte Carlo Graph Search |
| Тренировка | Нет (prompts) | RL на synthetic data |
| Lemma reasoning | Manual | Automatic lemma generation |
| Geometry | Нет | Yuclid (500x faster than AlphaGeometry-1) |
| Test-time training | Нет | Да |
| Результаты | Помощь разработчику | IMO Gold level (5/6 problems) |
