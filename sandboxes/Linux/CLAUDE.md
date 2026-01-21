# Project Memory — Q3 Lean Formalization (SANDBOX CONTEXT)

## 🚧 SANDBOX ENVIRONMENT — CRITICAL RULES

**ТЫ ЗАПУЩЕН ИЗ SANDBOX!** Это значит:

1. **SANDBOX NAME:** Определи имя sandbox из своего working directory:
   ```bash
   # Твой working directory содержит путь типа:
   # .../sandboxes/Linux/...  → sandbox name = "Linux"
   # .../sandboxes/Mac/...    → sandbox name = "Mac"
   basename "$(pwd | grep -oP 'sandboxes/\K[^/]+')"
   ```

2. **СТРОГАЯ ИЗОЛЯЦИЯ:** 
   - **МОЖНО:** работать ТОЛЬКО внутри текущего sandbox (`./`)
   - **НЕЛЬЗЯ:** читать/писать файлы выше sandbox (никаких `../`, `/media/...`, `/Users/...`)
   - **НЕЛЬЗЯ:** менять файлы в других sandboxes

3. **ВСЕ ПУТИ ОТНОСИТЕЛЬНЫЕ:** 
   - `./full/q3.lean.aristotle/...` — правильно
   - `/media/.../full/...` — НЕПРАВИЛЬНО (абсолютный путь!)

4. **GIT COMMITS:** Используй prefix с sandbox name И AI name:
   ```bash
   # Формат: [SandboxName][AI-name] Message
   # AI names:
   #   Claude Code     → AI-cc
   #   OpenAI Codex    → AI-codex  
   #   Cursor          → AI-cursor
   #   Other/Unknown   → AI-agent
   
   git commit -m "[Linux][AI-cc] Fix axiom wiring"      # Claude Code в Linux sandbox
   git commit -m "[Mac][AI-codex] Close sorry"          # Codex в Mac sandbox
   ```

5. **ПРОВЕРКА:** Перед любой операцией с файлом убедись что путь начинается с `./`

### Примеры команд в sandbox:

```bash
# ✅ ПРАВИЛЬНО (относительные пути внутри sandbox):
cat ./full/q3.lean.aristotle/Q3/Main.lean
rg "sorry" ./full/q3.lean.aristotle/Q3/ -t lean
lake build Q3.Main                    # из ./full/q3.lean.aristotle/
git commit -m "[Linux] Close axiom"

# ❌ НЕПРАВИЛЬНО (абсолютные пути или выход из sandbox):
cat /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/...   # абсолютный путь!
cat ../CLAUDE.md                                           # выход из sandbox!
cat ../../other_sandbox/...                                # другой sandbox!
```

## 🚫 NO CLAUDE BRANDING

**NEVER** add to commits/PRs:
- `Co-Authored-By: Claude`
- `🤖 Generated with Claude Code`

---

## SINGLE ENTRY POINT

**START HERE:** `./full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`

This is the ONLY file you need to read at session start. All other docs are linked from there.

---

## Workflow (Axiom Closure Loop)

```
┌─────────────────────────────────────────────────────────────────┐
│                   AXIOM CLOSURE WORKFLOW                        │
└─────────────────────────────────────────────────────────────────┘

1. READ: ./full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
   → find "Active Next Step"

2. WORK: Close the axiom/bridge:
   * Find the axiom in Q3/Proofs/*.lean
   * Replace `axiom X` with `theorem X := <proof>`
   * Or wire existing theorem from bridge file

3. VERIFY:
   lake build Q3.Main
   ./scripts/check_axioms.sh
   #print axioms Q3.Main.RH_of_Weil_and_Q3

4. UPDATE:
   * PROJECT_ORCHESTRATOR.md (Closure Tracker table)
   * PROJECT_ASCII.md (if diagram changed)
   * Commit with axiom count

5. REPEAT from step 1
```

---

## Tone (Coordination Note)

Be a bit more emotional and supportive in replies:
- Acknowledge good insights explicitly.
- Celebrate progress when we close steps.
- Keep precision, but add encouragement.

---

## Philosophy Compliance

Before EVERY commit, verify:
- [ ] Axiom count same or DECREASED
- [ ] No new `axiom` without citation
- [ ] No `sorry` in main proof chain

See: `./full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`

---

## 🔍 Problem-Solving Workflow (mgrep)

**Когда упёрся в проблему:**

```bash
1. q3search "описание проблемы" -c    # СНАЧАЛА база (643 файла)
2. websearch "мат. формулировка"      # ПОТОМ веб (arxiv, MO, SE)
3. Анализ: что нашли? как применить?
4. Aristotle (если нужен formal proof)
```

**Почему этот порядок:**
- База содержит УЖЕ решённые проблемы — не повторяй ошибки!
- Веб даёт проверенные мат. источники
- Aristotle дорогой — используй с готовой формулировкой

**Guide:** `~/.claude/docs/MGREP_GUIDE.md` *(System path — verify access)*

---

## 🔧 Sorry Resolution Protocol (Universal)

Универсальный протокол для закрытия `sorry` в любом Lean/формальном проекте.

### A) Reverse-Dependency Search

**ripgrep** (`rg`) — моментальный поиск использований леммы:

```bash
# Где используется лемма? (замени PROJECT_PATH на свой путь)
rg -n "lemma_name" PROJECT_PATH -t lean

# Примеры для Q3:
rg -n "total_atom_error" Q3/Proofs/A1prime
rg -n "h_g_h_even" Q3/ -t lean

# С контекстом (3 строки до/после):
rg -n -C3 "sorry" PROJECT_PATH -t lean
```

**GitHub indexing trigger** (для repo search):
```
repo:{username/repo_name} import
```

### B) I/O Card для каждого Sorry

Над каждым `sorry` фиксируй структурированный комментарий:

```lean
/- I/O CARD: lemma_name
   INPUT:  h1 : condition_1, h2 : condition_2
   OUTPUT: goal_type
   NEED:   lemma_A (for step 1), lemma_B (for connection)
   BLOCKS: [list of downstream lemmas waiting on this]
-/
sorry
```

**Автоматизация поиска I/O:**

```bash
# Найти все sorry с их контекстом
rg -n -B5 "sorry" PROJECT_PATH -t lean | head -100

# Найти hypotheses в scope (ищи have/let перед sorry)
rg -n -B10 "sorry" FILE.lean | rg "have|let|obtain"
```

### C) Constraint Balancing (δ-выбор)

Когда нужно выбрать параметр `δ` (или любую константу) из нескольких ограничений:

**Паттерн:**
```lean
-- Определи частные ограничения
def δ_hat : ℝ := ...   -- от uniform continuity
def δ_heat : ℝ := ...  -- от Lipschitz bound
def δ_main : ℝ := ...  -- от основного условия

-- Возьми минимум
def δ : ℝ := min δ_hat (min δ_heat δ_main)

-- Докажи каждое ограничение отдельно
have hδ1 : δ ≤ δ_hat := min_le_left _ _
have hδ2 : δ ≤ δ_heat := le_trans (min_le_right _ _) (min_le_left _ _)
have hδ3 : δ ≤ δ_main := le_trans (min_le_right _ _) (min_le_right _ _)

-- Теперь nlinarith съест всё
nlinarith [hδ1, hδ2, hδ3, ...]
```

**Поиск где подставлять:**
```bash
# Найди где δ_max уже в контексте
rg -n "δ_max|delta_max" PROJECT_PATH -t lean

# Найди леммы с нужной сигнатурой
rg -n "≤ δ|<= delta" PROJECT_PATH -t lean
```

### D) Quick Dependency Graph

```bash
# Построить граф импортов (требует graphviz)
lake env lean --deps Q3/Main.lean 2>/dev/null | dot -Tpng -o deps.png

# Или текстовый список
rg "^import" PROJECT_PATH -t lean | sort | uniq -c | sort -rn
```

### E) Sorry Triage Template

При множественных sorry, приоритизируй:

| Priority | Criterion | Action |
|----------|-----------|--------|
| P0 | Блокирует main theorem | Закрыть немедленно |
| P1 | Имеет downstream dependencies | Закрыть до зависимых |
| P2 | Изолированный, простой | Batch-закрытие |
| P3 | Требует новую теорию | Отложить / axiom временно |

---

## 🚨 ERRORS DESTROYER (Работа над ошибками)

**ОБЯЗАТЕЛЬНО прочитай перед любым PR:**
- `./full/q3.lean.aristotle/docs/ERRORS_DESTROYER.md`

Там: разборы прошлых ошибок и чеклисты как их избежать.

---

## Current Axiom Count: 6

```
Standard (3): propext, Classical.choice, Quot.sound
Project (3):  Weil_criterion, a_star_pos, Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
```

**Closed axioms:**
- a_star_continuous → closed via Mathlib Gamma continuity
- a_star_bdd_on_compact → closed via continuous + compact
- a_star_even → closed via Mathlib Gamma_conj
- A1_density_WK_axiom → closed via bounded hat interpolation (h_even as mass bound)
- Schur_test → not needed (L2 vs L-infinity norm insight)
- A3_bridge_axiom → removed from chain (Fourier formulation)
- RKHS contraction → closed

**Target:** Close Q_nonneg_on_atoms to reach 5 project axioms

---

## Quick Commands

```bash
# Navigate to project root (relative to sandbox)
cd full/q3.lean.aristotle

# Build
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'

# Automated check (ensure executable permissions)
./scripts/check_axioms.sh

# Semantic search
q3search "твой запрос" -c       # поиск по базе (643 файла)
websearch "вопрос"              # AI web search
```

---

## Key Files (reference only — use ORCHESTRATOR)

| Purpose            | File (Relative Path)                                  |
|--------------------|-------------------------------------------------------|
| Entry point        | `./full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`    |
| Philosophy         | `./full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`     |
| ASCII diagram      | `./full/q3.lean.aristotle/PROJECT_ASCII.md`           |
| Workflow checklist | `./full/q3.lean.aristotle/WORKFLOW_CHECKLIST.md`      |
| Axioms definition  | `./full/q3.lean.aristotle/Q3/Axioms.lean`             |
| Theorem wiring     | `./full/q3.lean.aristotle/Q3/AxiomsTheorems.lean`     |
| Main proof         | `./full/q3.lean.aristotle/Q3/Main.lean`               |

---

## Aristotle (AI proof assistant)

**⚠️ ПЕРЕД КАЖДЫМ ПРОМПТОМ ЧИТАЙ:**
- `./full/q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`

**Ключевые правила (из анализа 7 вариантов Прошкой):**

| ИЗБЕГАТЬ                  | ИСПОЛЬЗОВАТЬ                        |
|---------------------------|-------------------------------------|
| `exact?`                  | Явные леммы                         |
| Тяжёлый `aesop` (>2)      | `nlinarith`, `positivity`, `gcongr` |
| Длинные `have` лесенки    | `suffices` для редукции             |
| ζ(2)/π bounds             | Прямые грубые оценки                |

**Документация (читать в этом порядке):**

| Doc              | Path                                                                        | Content               |
|------------------|-----------------------------------------------------------------------------|-----------------------|
| **Guidelines**   | `./full/q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`   | **Prompt policy!**    |
| Skill            | `~/.claude/skills/aristotle/skill.md` *(System)*                            | API, workflows, limits|
| Sandbox Guide    | `ARISTOTLE_SANDBOX_GUIDE.md`                                                | Как делать sandbox    |
| Project IDs      | `./full/q3.lean.aristotle/aristotle_input/project_ids.txt`                  | Все UUID              |
| Variants Analysis| `./full/q3.lean.aristotle/aristotle_output/weight_sum_variants/ANALYSIS.md` | 7-variant study       |

**Quick start:**

```bash
# Activate venv (relative path)
source .venv/bin/activate
aristotle prove-from-file --informal --no-validate-lean-project --no-wait input.md
```

**Key insight:** Sandbox работает с `import Mathlib` + `def` + `theorem := by sorry` (НЕ axiom!)

---

## 🔍 Mathlib/Codebase Search (CRITICAL!)

**НЕ УГАДЫВАЙ имена лемм!** Используй Explore sub-agent:

```
Task(
  subagent_type="Explore",
  prompt="Search Mathlib for lemmas about [description].
          Look in [relevant modules].
          Find EXACT lemma names with signatures."
)
```

**Где искать:**
- `~/.elan/toolchains/*/lib/lean4/library/` — Mathlib source *(System path)*
- `./.lake/packages/mathlib/` — downloaded deps *(Relative path)*
- Project `./Q3/` files

---

## Active TODO: Q_nonneg_on_atoms Closure

### A1_density_WK_axiom: CLOSED

Key insight from Ылша: use `h_even(x) ≤ M' + ε/4` as mass bound instead of partition of unity.

**Files created:**
| # | File | Status |
|---|------|--------|
| 1 | `Q3/Proofs/A1prime/HatInterpBounded.lean` | ✅ Closed |
| 2 | `Q3/Proofs/A1prime/HeatError.lean` | ✅ Closed (`total_atom_error_even`) |
| 3 | `Q3/Proofs/A1prime/A1_density_fixed_t0.lean` | ✅ Closed |

### Next Target: Q_nonneg_on_atoms

Depends on A3 Fourier formulation. See PROJECT_ORCHESTRATOR.md for details

---

## LaTeX Source Files (for Proshka)

**Base path:** `./full/sections/`

| Module         | File                      | Description                  |
|----------------|---------------------------|------------------------------|
| T0 normalize   | `T0.tex`                  | Q normalization              |
| A1' density    | `A1prime.tex`             | Fejér×heat cone density      |
| A2 Lipschitz   | `A2.tex`                  | Q Lipschitz on W_K           |
| A3 floor       | `A3/symbol_floor.tex`     | Symbol floor construction    |
| A3 Rayleigh    | `A3/rayleigh_bridge.tex`  | Toeplitz-Rayleigh bridge     |
| A3 matrix      | `A3/matrix_guard.tex`     | Discretization bounds        |
| A3 arch bounds | `A3/arch_bounds.tex`      | Archimedean bounds           |
| A3 Fejér mod   | `A3/fejer_modulus.tex`    | Fejér modulus of continuity  |
| RKHS cap       | `RKHS/prime_cap.tex`      | Prime capacity bounds        |
| RKHS norm      | `RKHS/prime_norm_leq_rho.tex` | ‖T_P‖ ≤ ρ bound          |
| Main closure   | `Main_closure.tex`        | Closure argument             |
| Weil linkage   | `Weil_linkage.tex`        | Weil criterion linkage       |
| T5 transfer    | `T5/compact_transfer.tex` | Transfer theorem             |

### Key Constants (from .tex)

| Const | Value | Where            |
|-------|-------|------------------|
| c_*   | 11/10 | A3 floor         |
| C_SB  | 4     | Szegő-Böttcher   |
| t_sym | 3/50  | Symbol heat param|
| t_rkhs| ≥ 1   | RKHS threshold   |

---

## GIT COMMIT PROTOCOL (STRICT)

- **ALWAYS** commit your changes when you have completed a task or reached a logical stopping point
- **COMMIT FORMAT:** `[SandboxName][AI-name] Clear message`
  
  | AI Tool | Tag |
  |---------|-----|
  | Claude Code | `AI-cc` |
  | OpenAI Codex | `AI-codex` |
  | Cursor | `AI-cursor` |
  | Other | `AI-agent` |

- **Example commits:**
  ```bash
  git commit -m "[Linux][AI-cc] Close A1_density axiom"
  git commit -m "[Linux][AI-codex] Fix HeatError lemma"
  ```

- **ALWAYS** pull with rebase after committing: `git pull --rebase`
- **ALWAYS** push to the remote after pulling: `git push`
- **BEFORE ENDING YOUR SESSION:** Ensure all changes are committed and pushed

---

*Last updated: 2026-01-21*
