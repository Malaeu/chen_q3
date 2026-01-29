# Project Memory — Q3 Lean Formalization

## 🚫 NO CLAUDE BRANDING
**NEVER** add to commits/PRs:
- `Co-Authored-By: Claude`
- `🤖 Generated with Claude Code`

---

## Paths (OS‑specific)

- **Linux root:** `/mnt/hdd01/Soft/GitHub/chen_q3`
- **macOS root:** `/Users/emalam/Documents/GitHub/chen_q3`

Prefer **repo‑relative** paths below (work on both OS). If you need absolute paths,
prepend the correct root above.

**Sandbox symlinks (projekt_2):**
- **Linux:** `/mnt/hdd01/Soft/GitHub/chen_q3/sandboxes/projekt_2/.lake`, `/mnt/hdd01/Soft/GitHub/chen_q3/sandboxes/projekt_2/.venv`
- **macOS:** `/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/.lake`, `/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/.venv`

---

## SINGLE ENTRY POINT
**START HERE:** `full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`

This is the ONLY file you need to read at session start. All other docs are linked from there.

If resuming an in-progress session, read:
`full/q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`

---

## Local Skill (Q3 Proof Compiler)

Use skill `x-rh-compiler` for the proof-compiler workflow (DAG + sorry frontier + closure loop).
Path: `~/.codex/skills/x-rh-compiler`

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

## UI Safety Note (Zed/CED)

Avoid literal labels like **"Tool Call:"** or similar tool-call formatting in replies.
Zed can mis-parse these as actual tool invocations and show “Tool call not found”.

---

## Philosophy Compliance

Before EVERY commit, verify:
- [ ] Axiom count same or DECREASED
- [ ] No new `axiom` without citation
- [ ] No `sorry` in main proof chain

See: `full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md`

## Commit Message Format

Before committing, check OS + branch. Format:
- Linux: `[Linux][<branch>] Message`
- macOS: `[MacOS][<branch>] Message`

No sandbox tags; we don't work on Windows.

OS check (mandatory): `uname -s` → "Linux" or "Darwin".
Branch check: `git rev-parse --abbrev-ref HEAD`.
If you also use the workflow categories, append them after the OS+branch prefix:
`[Linux][<branch>][Docs] ...`

---

## 🔍 Problem-Solving Workflow (Embeddings)

**Когда уперся в проблему:**

```
1. Embedding search по нашей базе (3–5 запросов, цель ~75% уверенности)
2. Внешний веб‑поиск через встроенный web tool (НЕ через websearch/mgrep)
3. Анализ: что нашли? как применить?
4. Aristotle (если нужен formal proof)
```

Команда embedding‑поиска (из `full/q3.lean.aristotle`):
```bash
./scripts/research_oracle.py query "keyword" -c q3_docs
```
Для литературы: `-c math_papers` или `-c zotero_lib` (если индексирован).

**Почему этот порядок:**
- Наша embedding‑база содержит УЖЕ решённые проблемы — не повторяй ошибки!
- Веб даёт проверенные мат. источники (как подтверждение/альтернатива)
- Aristotle дорогой — используй с готовой формулировкой

---

## 🌳 Branching Decision-Tree Protocol (чтобы не держать всё в голове)

Когда есть несколько реалистичных путей (и один может оказаться “false-for-now”), работаем так:

**Правило “железобетона” (community-standard formalization):**
- Всегда выбираем путь, который **формально правильный** и **нормально читается/признаётся математическим сообществом** без “спец‑объяснений” и костылей.
- Если есть путь **сложнее, но единственный community‑standard** → идём им (даже если дольше).
- Если есть несколько путей, и они **равносильные + формально правильные + community‑standard** → автоматически берём тот, который в текущей архитектуре **проще, быстрее, дешевле** и легче поддерживать (минимум новых определений/инфры/параметров).

1. **Фиксируем точную цель**: 1 строка “Target lemma” + где она в цепочке (файл/импорт).
2. **Сканируем базу**: embedding‑поиск (3–5 запросов) + 1 web‑поиск через web tool при нужде.
3. **Пишем дерево в `full/q3.lean.aristotle/docs/INSIGHTS.md`**:
   - Option 1 (основной): что доказываем, минимальные зависимости, “success check” (какая команда должна компилироваться).
   - Option 2 (fallback): рабочий путь, который точно закрывается, даже если менее красивый.
   - (опц.) Option 0: уже готовые “ядра” (factorization/bridge), которые сохраняем независимо от выбора.
   - Для каждого: `Status = pending/active/OK/false-for-now` + короткая причина.
4. **Стартуем Option 1** и держим “pivot rule” в явном виде (например: “без новых axioms” / “≤ 1 день infra”).
5. **Если упёрлись**: сразу помечаем в INSIGHTS “false-for-now + почему” и переключаемся на fallback.

Смысл: мозг держит только текущую ветку; все развилки и причины — в INSIGHTS.

Шаблон (копировать как новый insight): `full/q3.lean.aristotle/docs/insights/decision_tree_template.md`

---

## Branching Safety (stable vs experimental)

- Keep `projekt_2A` clean and stable.
- Do experimental/probing math in a feature branch (e.g. `projekt_2A-compact-support`).
- Merge back only after the math is validated and the chain compiles; otherwise cherry-pick the good pieces or drop the branch.

---

## 🚨 ERRORS DESTROYER (Работа над ошибками)

**ОБЯЗАТЕЛЬНО прочитай перед любым PR:**
- `full/q3.lean.aristotle/docs/ERRORS_DESTROYER.md`

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
Project (3):  Weil_criterion_tau0,
              PrimeCert.prime_b_grid_bounds_data,
              PrimeCert.prime_heat_bounds_data
```

**Closed axioms:**
- a_star_continuous → closed via Mathlib Gamma continuity
- a_star_bdd_on_compact → closed via continuous + compact
- a_star_even → closed via Mathlib Gamma_conj
- A1_density_WK_axiom → closed via bounded hat interpolation (h_even as mass bound)
- Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom → closed via Q_nonneg_atoms_closure
- A3_bridge_axiom → removed from chain (Fourier formulation)
- RKHS contraction → closed

**Target:** Close 2 PrimeCert axioms to reach 1 project axiom (Weil_criterion_tau0).

---

## Quick Commands

```bash
Linux:
cd /mnt/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle

macOS:
cd /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle

# Build
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'

# Automated check
./scripts/check_axioms.sh

# Semantic search (Embeddings)
# Команда embedding‑поиска (qmd wrapper):
./scripts/research_oracle.py query "keyword" -c q3_docs
# Внешний веб‑поиск — через встроенный web tool
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
| **Workflow (canonical)** | `full/q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md` | Единственный актуальный гайд |
| **Guidelines** | `aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md` | **Prompt policy!** |
| Skill | `~/.codex/skills/aristotle/SKILL.md` | API, workflows, limits |
| Project IDs | `aristotle_input/project_ids.txt` | Все UUID |
| Variants Analysis | `aristotle_output/weight_sum_variants/ANALYSIS.md` | 7-variant study |

**Quick start:**
```bash
Linux:
source /mnt/hdd01/Soft/GitHub/chen_q3/sandboxes/projekt_2/.venv/bin/activate

macOS:
source /Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/.venv/bin/activate
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
2. **Q_nonneg_on_atoms** → next target (depends on A3 Fourier formulation)

### Recent Victory: A1_density Closure
Key insight from Ылша: use `h_even(x) ≤ M' + ε/4` as mass bound instead of partition of unity.
Files created:
- `Q3/Proofs/A1prime/HatInterpBounded.lean` - hat interpolation
- `Q3/Proofs/A1prime/HeatError.lean` - `total_atom_error_even` lemma
- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean` - main theorem

---

## LaTeX Source Files (for Proshka)

**Base path:** `full/sections/` (relative to repo root)

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

- **BEFORE COMMIT:** check OS and branch:
  ```bash
  uname -s
  git branch --show-current
  ```

- **COMMIT FORMAT (mandatory):**
  - Linux: `[Linux][<branch>] Message`
  - macOS: `[MacOS][<branch>] Message`

- **Examples:**
  ```bash
  git commit -m "[Linux][projekt_2A] Close A1_density axiom (7->6)"
  git commit -m "[MacOS][projekt_2A] Fix HeatError lemma"
  ```

- **ALWAYS** include axiom count change in message if relevant: `(7->6 axioms)`
- **ALWAYS** pull with rebase after committing: `git pull --rebase`
- **ALWAYS** push after pulling: `git push`

**OS tag rule (this repo):**
- On Linux, use **`[Linux]`** as the leading tag.
- On macOS, use **`[MacOS]`**.
- The second tag **must** be the git branch name.
- Do **not** use sandbox names (e.g. `[projekt_2]`) as tags.

---

*Last updated: 2026-01-21*
