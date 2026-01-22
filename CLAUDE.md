# Project Memory — Q3 Lean Formalization

## 🚫 NO CLAUDE BRANDING
**NEVER** add to commits/PRs:
- `Co-Authored-By: Claude`
- `🤖 Generated with Claude Code`

---

## SINGLE ENTRY POINT
**START HERE:** `/full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`

This is the ONLY file you need to read at session start. All other docs are linked from there.

---

## Workflow (Axiom Closure Loop)

```
┌─────────────────────────────────────────────────────────────────┐
│                    AXIOM CLOSURE WORKFLOW                       │
└─────────────────────────────────────────────────────────────────┘

1. READ: PROJECT_ORCHESTRATOR.md → find "Active Next Step"

2. WORK: Close the axiom/bridge:
   - Find the axiom in Q3/Proofs/*.lean
   - Replace `axiom X` with `theorem X := <proof>`
   - Or wire existing theorem from bridge file

3. VERIFY:
   lake build Q3.Main
   ./scripts/check_axioms.sh
   #print axioms Q3.Main.RH_of_Weil_and_Q3

4. UPDATE:
   - PROJECT_ORCHESTRATOR.md (Closure Tracker table)
   - PROJECT_ASCII.md (if diagram changed)
   - Commit with axiom count

5. REPEAT from step 1
```

---

## Tone (Coordination Note)

Be a bit more эмоциональный and supportive in replies:
- Acknowledge good insights explicitly.
- Celebrate progress when we close steps.
- Keep precision, but add encouragement.

---

## Philosophy Compliance

Before EVERY commit, verify:
- [ ] Axiom count same or DECREASED
- [ ] No new `axiom` without citation
- [ ] No `sorry` in main proof chain

See: `/full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`

---

## 🔍 Problem-Solving Workflow (mgrep)

**Когда уперся в проблему:**

```
1. q3search "описание проблемы" -c    ← СНАЧАЛА база (643 файла)
2. websearch "мат. формулировка"      ← ПОТОМ веб (arxiv, MO, SE)
3. Анализ: что нашли? как применить?
4. Aristotle (если нужен formal proof)
```

**Почему этот порядок:**
- База содержит УЖЕ решённые проблемы — не повторяй ошибки!
- Веб даёт проверенные мат. источники
- Aristotle дорогой — используй с готовой формулировкой

**Guide:** `~/.claude/docs/MGREP_GUIDE.md`

---

## 🚨 ERRORS DESTROYER (Работа над ошибками)

**ОБЯЗАТЕЛЬНО прочитай перед любым PR:**
- `/full/q3.lean.aristotle/docs/ERRORS_DESTROYER.md`

Там: разборы прошлых ошибок и чеклисты как их избежать.

---

## 🔧 Sorry Resolution Protocol (Universal)

### A) Reverse-Dependency Search

```bash
# Где используется лемма?
rg -n "lemma_name" Q3/Proofs/ -t lean

# С контекстом (3 строки до/после):
rg -n -C3 "sorry" Q3/ -t lean
```

### B) I/O Card для каждого Sorry

```lean
/- I/O CARD: lemma_name
   INPUT:  h1 : condition_1, h2 : condition_2
   OUTPUT: goal_type
   NEED:   lemma_A (for step 1), lemma_B (for connection)
   BLOCKS: [list of downstream lemmas waiting on this]
-/
sorry
```

### C) Constraint Balancing (δ-выбор)

Когда нужно выбрать параметр из нескольких ограничений:

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
-- nlinarith съест всё
```

### D) Quick Dependency Graph

```bash
# Построить граф импортов (требует graphviz)
lake env lean --deps Q3/Main.lean 2>/dev/null | dot -Tpng -o deps.png

# Или текстовый список
rg "^import" Q3/ -t lean | sort | uniq -c | sort -rn
```

### E) Sorry Triage Template

| Priority | Criterion | Action |
|----------|-----------|--------|
| P0 | Блокирует main theorem | Закрыть немедленно |
| P1 | Имеет downstream dependencies | Закрыть до зависимых |
| P2 | Изолированный, простой | Batch-закрытие |
| P3 | Требует новую теорию | Отложить / axiom временно |

### F) Автоматизация поиска I/O

```bash
# Найти все sorry с их контекстом
rg -n -B5 "sorry" Q3/ -t lean | head -100

# Найти hypotheses в scope (ищи have/let перед sorry)
rg -n -B10 "sorry" FILE.lean | rg "have|let|obtain"

# GitHub indexing trigger (для repo search)
repo:{username/repo_name} import
```

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
cd /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle

# Build
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'

# Automated check
./scripts/check_axioms.sh

# Semantic search (НОВОЕ!)
q3search "твой запрос" -c       # поиск по базе (643 файла)
websearch "вопрос"              # AI web search
```

---

## CLI Tools (IMPORTANT!)

- **ALWAYS use `rg` (ripgrep) instead of `grep` in Bash!**
  - `rg` is 10-100x faster than GNU grep
  - Installed at: `/usr/bin/rg` (v14.1.0)
  - Wrong: `grep -r "pattern" dir/`
  - Right: `rg "pattern" dir/`
- Claude's built-in `Grep` tool already uses ripgrep under the hood
- For simple pipes, `grep` is acceptable (e.g., `| grep -E "error"`)
- For file searches, ALWAYS prefer `rg`:
  ```bash
  rg -n "sorry" Q3/           # line numbers
  rg -C3 "pattern" file.lean  # with context
  rg -t lean "theorem"        # by file type
  ```

---

## Key Files (reference only - use ORCHESTRATOR)

| Purpose | File |
|---------|------|
| Entry point | `full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` |
| Philosophy | `full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md` |
| ASCII diagram | `full/q3.lean.aristotle/PROJECT_ASCII.md` |
| Workflow checklist | `full/q3.lean.aristotle/WORKFLOW_CHECKLIST.md` |
| Axioms definition | `full/q3.lean.aristotle/Q3/Axioms.lean` |
| Theorem wiring | `full/q3.lean.aristotle/Q3/AxiomsTheorems.lean` |
| Main proof | `full/q3.lean.aristotle/Q3/Main.lean` |

---

## Aristotle (AI proof assistant)

**⚠️ ПЕРЕД КАЖДЫМ ПРОМПТОМ ЧИТАЙ:**
- `full/q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`

**Ключевые правила (из анализа 7 вариантов Прошкой):**
| ИЗБЕГАТЬ | ИСПОЛЬЗОВАТЬ |
|----------|--------------|
| `exact?` | Явные леммы |
| Тяжёлый `aesop` (>2) | `nlinarith`, `positivity`, `gcongr` |
| Длинные `have` лесенки | `suffices` для редукции |
| ζ(2)/π bounds | Прямые грубые оценки |

**Документация (читать в этом порядке):**
| Doc | Path | Content |
|-----|------|---------|
| **Guidelines** | `aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md` | **Prompt policy!** |
| Skill | `~/.claude/skills/aristotle/skill.md` | API, workflows, limits |
| Sandbox Guide | `ARISTOTLE_SANDBOX_GUIDE.md` | Как делать sandbox |
| Project IDs | `aristotle_input/project_ids.txt` | Все UUID |
| Variants Analysis | `aristotle_output/weight_sum_variants/ANALYSIS.md` | 7-variant study |

**Quick start:**
```bash
source /media/chirurgie/hdd01/Soft/GitHub/chen_q3/.venv/bin/activate
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

**Почему это важно:**
- Из 3 агентов только 1 догадался использовать Explore
- Остальные гадали имена или спрашивали юзера
- Explore agent грепает по `.elan/toolchains/` и `.lake/packages/`

**Паттерн:**
```
WRONG: "I think it's called `intervalIntegral_add_adjacent`..."
WRONG: exact?  (timeout на сложных goals)
WRONG: "Can you tell me the lemma name?"

RIGHT: Task(Explore, "Search Mathlib for adjacent interval lemmas...")
       → Returns EXACT names with signatures
```

**Где искать:**
- `~/.elan/toolchains/*/lib/lean4/library/` — Mathlib source
- `.lake/packages/mathlib/` — downloaded deps
- Project `Q3/` files

---

## Active TODO (from Orchestrator)

1. ~~**A1_density_WK**~~ → CLOSED via h_even as mass bound approach
2. **Q_nonneg_on_atoms** → IN PROGRESS via MatrixBridge (Variant B)

### Current Work: MatrixBridge (Q_nonneg via Finite Matrix Cap)

**File:** `sandboxes/projekt_2/full/q3.lean.aristotle/Q3/Proofs/MatrixBridge.lean`

**Strategy:** Instead of RKHS, use finite Toeplitz matrices:
- T_M[P_A] — Toeplitz matrix of symbol P_A
- T_P^{(M)} — prime operator compressed to ℂ^{2M+1}
- Chain: λ_min(A) ≥ c*/2, ‖B‖ ≤ c*/4 → λ_min(A-B) ≥ c*/4 > 0 → Q ≥ 0

**Closed lemmas:**
- `T_M_P_A_symm` — Toeplitz symmetry (P_A even)
- `T_M_P_A_lambda_min_ge_B_min` — RQ ≥ c*/2 at B_min
- `lambda_min_diff_ge`, `Q_nonneg_via_matrix` — main chain (from sorries)

**Remaining sorries (5):**
- `P_A_continuous_t_crit` — technical
- `P_A_ge_c_star_t_crit` — numerical (min=1.66 > 1.1)
- `T_P_rayleigh_le` — row sum bound
- `rayleigh_identity` — Fourier matching

### Previous Victory: A1_density Closure
Key insight from Ылша: use `h_even(x) ≤ M' + ε/4` as mass bound instead of partition of unity.
Files created:
- `Q3/Proofs/A1prime/HatInterpBounded.lean` - hat interpolation
- `Q3/Proofs/A1prime/HeatError.lean` - `total_atom_error_even` lemma
- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean` - main theorem

---

## LaTeX Source Files (for Proshka)

**Base path:** `/media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/sections/`

| Module | File | Description |
|--------|------|-------------|
| T0 nормировка | `T0.tex` | $\xi_n = \log n/(2\pi)$, $a_* = 2\pi a$ |
| A1' density | `A1prime.tex` | Fejér×heat cone density |
| A2 Lipschitz | `A2.tex` | Q Lipschitz on W_K |
| A3 floor | `A3/symbol_floor.tex` | $P_A(\theta) \geq c_* = 11/10$ |
| A3 Rayleigh | `A3/rayleigh_bridge.tex` | Toeplitz-Rayleigh bridge |
| A3 matrix | `A3/matrix_guard.tex` | Discretization bounds |
| A3 arch bounds | `A3/arch_bounds.tex` | Archimedean bounds |
| A3 Fejér mod | `A3/fejer_modulus.tex` | Fejér modulus of continuity |
| RKHS cap | `RKHS/prime_cap.tex` | $\rho(1) < 1/25$ |
| RKHS norm | `RKHS/prime_norm_leq_rho.tex` | ‖T_P‖ ≤ ρ bound |
| Main closure | `Main_closure.tex` | Closure argument |
| Weil linkage | `Weil_linkage.tex` | $Q \geq 0 \Leftrightarrow RH$ |
| T5 transfer | `T5/compact_transfer.tex` | Transfer theorem |

### Key Constants (from .tex)
| Const | Value | Where |
|-------|-------|-------|
| c_* | 11/10 | A3 floor |
| C_SB | 4 | Szegő-Böttcher |
| t_sym | 3/50 | Symbol heat param |
| t_rkhs | ≥ 1 | RKHS threshold |

---

## GIT COMMIT PROTOCOL

- **COMMIT FORMAT:** `[AI-name] Clear message` (в root) или `[SandboxName][AI-name] Message` (в sandbox)
  
  | AI Tool | Tag |
  |---------|-----|
  | Claude Code | `AI-cc` |
  | OpenAI Codex | `AI-codex` |
  | Cursor | `AI-cursor` |
  | Other | `AI-agent` |

- **Examples:**
  ```bash
  # Root repo:
  git commit -m "[AI-cc] Close A1_density axiom (7->6)"
  
  # From sandbox:
  git commit -m "[Linux][AI-cc] Fix HeatError lemma"
  ```

- **ALWAYS** include axiom count change in message if relevant: `(7->6 axioms)`
- **ALWAYS** pull with rebase after committing: `git pull --rebase`
- **ALWAYS** push after pulling: `git push`

---

*Last updated: 2026-01-22*
