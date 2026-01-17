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

## 🚨 ERRORS DESTROYER (Работа над ошибками)

**ОБЯЗАТЕЛЬНО прочитай перед любым PR:**
- `/full/q3.lean.aristotle/docs/ERRORS_DESTROYER.md`

Там: разборы прошлых ошибок и чеклисты как их избежать.

---

## Current Axiom Count: 10

```
Standard (3): propext, Classical.choice, Quot.sound
Level 1 (4):  Weil_criterion, a_star_pos, a_star_bdd_on_compact, a_star_continuous
Level 2 (3):  A1_density_WK_axiom, A3_bridge_axiom, Q_nonneg_on_atoms_of_A3_RKHS_axiom
```

Note: arch/prime Lipschitz bridges CLOSED (was 12 → 11), RKHS contraction closed (11 → 10).
Target: Reduce Level 2 to 0 (or minimal classical results)

---

## Quick Commands

```bash
cd /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle

# Build
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'

# Automated check
./scripts/check_axioms.sh
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
source /Users/emalam/Documents/GitHub/chen_q3/.venv/bin/activate
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

1. **A1_density_WK** → 1 sorry remains: `h_approx` (triangle ineq)
2. **A3_bridge_axiom** → prove via A3_FLOOR + Szegő (BLOCKED on Szegő)
3. **Q_nonneg** → rewrite after A3 closed (BLOCKED)

### A1_density Definitional Issue
AtomCone_K requires `support g ⊆ [-K, K]`, but atoms with τ ∈ [-K,K] and B ≤ K have support in [-2K, 2K].
Options: (1) modify AtomCone_K, (2) use B + |τ| ≤ K, (3) add truncation.

---

## LaTeX Source Files (for Proshka)

**Base path:** `/Users/emalam/Documents/GitHub/chen_q3/full/sections/`

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

*Last updated: 2026-01-14*
